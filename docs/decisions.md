# Design decisions on the `lean-kernel` branch

This file records decisions that settle a question the specifications leave
open, or that deliberately depart from them. Read it before changing the
kernel. Where it disagrees with a specification in the repository root, this
file is the current intent for this branch.

## Resumptions are one-shot

**Decision (user, with the kernel rewrite).** A resumption can be used at most
once: resumed once, or cancelled once. There is no multi-shot resumption. An
operation may say how often its resumption is used, but the most is always
one: `[0, 1]`, which is what an operation that says nothing has, or `[1, 1]`
(see "How often a value is used"). Any other quantity is refused.

This departs from the language specification §10.6, which admits exact finite
`[n, n]`, and from the usage-multiplication rules in the kernel draft §3.6.
Those parts of the specifications do not apply on this branch.

**Why.**

- Multi-shot was needed only by handlers that run the rest of a computation
  more than once: backtracking and exhaustive exploration. Exceptions, state,
  generators, async, schedulers and early exit are all one-shot. One example
  and four tests used it.
- A second resume re-ran the captured frames but shared every mutable cell with
  the first run, so it was only correct for code that mutates nothing.
- A scope resumed twice ends twice. Freeing a mutable variable's cell at the end
  of its scope would be a double free, and a `defer` ran once per resume.
- The usage-multiplication machinery in the ownership rules exists only because
  a continuation can run a suffix several times. With one-shot resumptions a
  value used once in the source is used once at run time.
- The VM had to copy the captured frames on every resume but the last. A
  one-shot resume moves them back.

**What to do instead.** Write backtracking as ordinary recursion over the
alternatives, and report each solution through an effect or a callback. See
`examples/backtracking.glorious`.

**Do not reintroduce** use counts, a `shots` field on `perform`, or frame
copying on resume without revisiting the points above. A middle option was
considered and rejected for now: multi-shot only for continuations shown to
capture no mutable cells, cleanups or owned resources. It keeps pure
backtracking but adds a second kind of resumption and a new analysis.

## The compiler knows no control flow

**Decision (user).** There are no `if`, `else`, `match`, loop or boolean
constructs in the compiler. They are functions and operators defined in the
language, in `Glorious/Prelude.lean`, and so are `true`, `false`, `Some`,
`None`, `Result` and the arithmetic and comparison operators.

The only words the parser treats specially are `fn`, `let`, `mut`, `enum`,
`struct`, `effect`, `handle`, `tail`, `defer`, `coerce`, `_`, and the fixity
words `infixl`, `infixr`, `infix`, `prefix`. The elaborator and checker additionally
know `cancel`, `replace`, `Int`, the machine intrinsics (`int_add` and so on)
and the two host operations. A word operator such as `else` or `and` is declared with a
fixity like any other operator.

Do not add a parser rule, a checker rule or an error message that names a
prelude function. If a prelude construct is awkward to type or to use, fix it
in the prelude or with a general language rule.

## A trailing `;` discards a value

**Decision (user).** A block yields the value of its last expression. Ending
that expression with `;` discards the value, and the block yields `()`.

This matters because `if(c) { a }` is a library function that returns a
`Result`, which `else` unwraps: the body's value on success, and on failure the
body itself, which was not run (see "Blocks that share an environment"). An
`if` with no `else` at the end of a body therefore makes the body's value that
`Result`. In a recursive function that is a type containing itself; and since
the value holds the body, a body that uses a `let mut` variable or a label of
the enclosing block would carry it out of that block, which the checker
rejects. Write `if(c) { a };` when the `if` is run only for its effect, or
declare the function's result an option (`-> Result<T, ()>`), to which the
value is then converted (see "Coercions are declared by the program").
Function results stay inferred; there is no `return` keyword, and
`@function_name(value)` leaves a function early.

Do not "fix" this by making `if` a special form or by giving unannotated
functions a unit result.

## A mutable variable ends with its block

**Decision.** `let mut x` lasts until the end of the block it is written in,
and its storage is released there, however the block is left. The checker
rejects any program in which a reference to `x`, a callable that uses `x`, or a
resumption whose computation or handler uses `x` could outlive that block.
Lifetimes are never written: they are inferred as capture sets, the same way as
for labels.

In the kernel a cell is made and released by a scope, `cell init thunk`: the
callable `thunk` runs with a reference to a fresh cell, on top of a frame that
releases the cell when it is removed, by a return, an exit or a cancellation.
There is no operation that allocates or frees. So a cell is released exactly
when its scope ends, and never twice, whatever the program; what remains to be
shown is that no reference is used after that (see "Borrow checking").

Consequences to keep in mind:

- A function cannot return a closure over its own `let mut`. State that must
  outlive a call belongs to the caller, or to a handler around the computation.
- A `tail` call cannot be written directly after a `let mut` or a `defer` in
  the same block, because the release or the deferred call still has to happen.
- Passing `&mut x`, or a block that uses `x`, to a top-level function is fine.
  Passing it to a function received as a parameter is rejected: nothing says
  that function will not keep it. Lifting this needs function types that are
  polymorphic in what their arguments capture.
- One-shot resumptions are what make the release sound: a block ends once.
- A resumption that is neither resumed nor cancelled is never unwound, so the
  variables of the computation it captured are not released. That is a leak,
  not a dangling reference.

## Values that hold a resumption are used at most once

**Decision.** The checker rejects a second use of a resumption, and of anything
that holds one: data it is stored in, and a callable that captured it. Whether a
function may be given such a value is inferred from how it uses its parameters
and checked at each call. Nothing is annotated.

- Reading a mutable variable copies its value, so a variable that holds a
  resumption is read with `replace(reference, new_value)`, which takes the value
  out. `replace` is known to the compiler, like `cancel`; it is a load followed
  by a store, not a new kernel operation.
- Uses are counted along the paths a program can take (language specification
  section 7.4). The checker runs the code abstractly: it follows constructors,
  callables and calls into top-level functions, and chooses clauses by the
  constructor of the value they are applied to. That is how it sees that a
  function given two blocks runs only one of them, so resuming in both blocks
  of a conditional is accepted without the compiler knowing any conditional.
- What the count cannot follow is treated as using everything handed to it: a
  call of a function value held in a variable or received as a parameter, a
  value stored in a mutable variable, an operation's payload. A path cut short
  by leaving through a label is counted as if it continued. Recursion is
  followed to a fixed depth, and if the count runs out of budget the coarse
  count (one use per callable that mentions the binding) stands.
- The check is "at most once". A resumption that is dropped is accepted; it
  leaks the computation it captured and skips that computation's cleanups.

## An exit runs each cleanup in place

**Decision.** Leaving for a label, performing a terminal operation and
cancelling a resumption are all the same thing: an exit towards a target frame.
The exit drops frames until it meets a cleanup, runs that cleanup with
everything below it still on the stack and still working, and then carries on.
When it reaches its target it removes it and does what comes after: delivers a
value, or runs the handler's arm.

- A cleanup can therefore jump to an enclosing label and perform an operation an
  enclosing handler serves, exactly as it could on a normal return.
- A cleanup that starts an exit of its own replaces the one in progress.
- A pending exit sits on the stack as a frame. If a cleanup performs an
  operation whose arm resumes it, that frame is part of the resumption, and when
  the cleanup finishes the exit continues through the arm's own frames. The arm
  never receives a result.
- Handlers carry an identity, so that an exit can name the one it is going to.
- **A cleanup performs no effects** (language specification section 7.7: an
  effectful close must be called explicitly). The checker rejects a `defer`
  whose expression performs an operation or calls something that might. A
  cleanup may still jump to an enclosing label and use the host. Without this
  rule a cleanup's operation could capture the pending exit in a resumption,
  and resuming it later, after the exit's target had gone, went wrong.
- **`cancel` gives up any callable taking one value.** For a resumption it runs
  the captured computation's cleanups; for a function or a label there is
  nothing to do. Before, `cancel` of anything but a resumption went wrong, and
  the checker could not tell the two apart.
- **`cancel` leaves a fresh label scope, not the captured handler.** The
  captured computation is put back above a frame that discards whatever it
  delivers, inside a label scope made for the purpose, and that scope is left at
  once with unit. If one of the cleanups jumps to a label inside the computation
  and it runs on to completion, the canceller still receives unit. Before, the
  exit was aimed at the handler at the base of the captured computation, which
  is only right if no other frame carries that handler's identity; a fresh
  label needs no such fact, and a resumption no longer records its handler.
- **A label scope runs any callable taking one value**, as a call does: a
  function, a resumption or another label. Before, only a function was
  accepted, and a scope given a resumption went wrong although nothing in its
  type says it is not a function.
- **`cancel` needs the callable's effects handled where it is cancelled**, as a
  call would. A cleanup of the cancelled computation can jump to a label inside
  it; the computation then runs on from there, at the canceller, and may perform
  anything its type allows. Before, the checker accepted a `cancel` outside the
  handlers the resumption needed, and such a program went wrong.

Two earlier designs were wrong, and both let a program the checker accepts go
wrong at run time. Six further faults (the five rules above, and the discarding
frame) were found the same way as the second: by trying to say what type each
stack has.

1. Unwinding removed every abandoned frame and then ran the cleanups, so a
   cleanup found its enclosing handlers and labels gone. A random search for
   accepted programs that go wrong found this.
2. The first fix kept abandoned handlers on the stack in a "passive" form that
   passed results through. A cleanup's operation could then be resumed by an arm
   that expected the handled computation's result and received the cleanup's
   instead. Working out how such a stack could be given a type found this; the
   random search had not.

The compiler proof held throughout, since both machines agreed each time. It is
a statement about the compiler, not about whether the rules are right.

## Core has types, and typed programs do not go wrong

**Decision.** `Glorious/Typing/` gives Core a type system and proves it sound
for the machine in `Core/Semantics.lean`. This, not the test corpus, is what
says the kernel rules fit together. Change a kernel rule and this proof has to
be redone; that is its purpose.

What is proved (`Typing/Safety.lean`, `Typing/Compiled.lean`,
`Typing/Certify.lean`):

- `type_safety`: if a well-typed program goes wrong, the state it could not
  step from is one of four named faults.
- `compiled_type_safety`: the same for its compiled bytecode, by way of
  `compile_correct`.
- `checked_safety` and `checked_compiled_safety`: the same for any program the
  function `checkProgram` accepts, with nothing else assumed.
- `Typing/Witness.lean` runs the checker, in the kernel, on a program with
  nested handlers, a resumptive and a terminal operation, so the theorems are
  not about an empty set of programs.

The four faults are what types alone do not rule out: integer overflow, use of
a released cell, a second use of a resumption, and a label applied after its
scope ended. The third is ruled out by the ownership rules below, and the
second and fourth by the region rules (see "Borrow checking"), for programs
that follow them. The front-end has checks of its own for the second and
fourth (scoped `let mut`, capture sets), which give the errors a programmer
sees. Those checks are not proved; the region rules are what is.

How the typing is set up, and why:

- **Types are monomorphic.** A function has a set of signatures and must be
  typed at each. A polymorphic source function is a function with several
  signatures. This avoids type variables and substitution in the proof.
- **A callable's type carries a row**: the operations it may perform, each
  named, with the type arguments of its effect. What an operation takes and
  gives back is looked up in the declarations, not written in the row. An
  earlier version wrote those types in the row; then an operation whose payload
  is a callable performing the same operation, such as spawning a task, had no
  finite type. A row is ordered nearest handler first, so looking an operation
  up in a row finds the handler the machine finds on the stack.
- **`never` is the type of a call that does not return**, and no value has it.
  A call or tail call of something that returns `never` can stand where any
  type is expected. A label's result type is `never` unless the label is also
  used as an ordinary callable. Without this one label could not be applied in
  two places that expect different types, which the surface checker allows.
- **A stack has a type**: what it takes and what it serves. A handler frame
  serves its own operations and, of what is below, only what the handler was
  installed among. That is what lets captured frames be put back on a different
  stack and stay typed.
- **An exit in progress serves nothing.** A cleanup performs no operations, so
  nothing running above a pending exit can capture it.
- **A stored continuation is typed by what it does when put back**: on any later
  stack that takes the handler's result and serves what the handler needs, it
  gives a typed stack.

**The checker takes a certificate and does not trust it.** `checkProgram` is
given the program and a `Cert`: the signatures of each function, the data types
used at each instance, the type of each `let`, and what each handler yields and
serves. Everything else it works out. It also checks that each function's
clauses cover its parameters (`covers`, proved in `Typing/Covers.lean`), which
`type_safety` on its own has to assume. A wrong certificate is rejected or
describes some other valid typing; it cannot make an ill-typed program pass.
This is the reason for the split: finding types is hard and stays unproved in
the front-end, checking them is easy and is proved.

**Certificates are found by a separate unproved pass, `Glorious/Infer.lean`.**
It works on the Core the elaborator produced, not on the surface program, so it
shares nothing with the surface checker and what it finds is checked whatever
the surface checker did. It infers each group of mutually recursive functions
once, then gives each function a signature for every ground type it is used
at. Two things in the elaborator exist for its sake: a name bound by `let` to a
callable literal is built again at each use, so that it can be used at several
types; and a handler arm that cannot fail has no forwarding clause, which
would otherwise make the arm need its own operation from outside.

**Compiling a program checks its Core.** `compileSource` runs the certificate
search on the elaborated Core and then `checkProgram`, and fails if either
does. So for every program that compiles, `checked_safety` and
`checked_compiled_safety` apply to the Core and to the bytecode it is compiled
to. If the surface checker accepts a program and this step refuses it, that is
reported as a defect in the compiler. `check := false` skips both checks, for
running programs that are meant to go wrong.

What the theorems do not say:

- The statement is about the Core program. That the Core means what the source
  says is the elaborator's job, and the elaborator is not proved.
- The check is run by compiled Lean code. The proof is about the function
  `checkProgram`; that the compiled code computes it is trusted.
- `covers` is proved sound, not complete. It searches to a bounded depth, and
  a set of clauses that covers its parameters could in principle be turned away.
- Overflow remains possible for every program. A second use of a resumption
  remains possible, as far as any proof goes, for a program compiled without
  the ownership rules; use of a released cell and a jump to a label whose
  scope ended, for one compiled without the region rules.

## Ownership: a resumption is held in one place

**Decision.** The ownership rules are part of Core's typing, and their
soundness is proved: `owned_safety` and `checked_owned_safety`. This is the
affine part of the language specification's section 7 (use at most once), for
the one kind of value the kernel makes that must not be duplicated: a
resumption, and anything that holds one.

What the rules are:

- A callable's type says whether it may be called once only. A resumption may,
  and so may a function that captured something that cannot be duplicated.
- A type is duplicable or not. Integers, references, labels and callables that
  may be called many times are; a tuple or a declared type is if all its fields
  are. Nothing is declared: it follows from the types.
- A step of a computation moves the locals it passes on, stores, captures or
  calls. A local whose type is not duplicable is moved at most once by a step
  and not mentioned by the steps after it.
- Reading a field or a cell copies, so what is read must be duplicable. A value
  that is not is taken out of a cell with `replace`, which is why the kernel has
  a `swap` operation.
- A function whose type states its environment can give it to another function
  written against the same environment (`rebind`); the first is moved.
- A handler's functions can run many times with the same captures, so a
  handler's captures are duplicable.
- A clause's body uses what its patterns bind, not also the argument they took
  apart.

What is proved: count, for a resumption, the places in a machine state that
hold it and can still use it: locals the rest of the computation mentions,
frames, memory, frames captured in other resumptions. Under the rules that
count never exceeds one, and a resumption that is held has not been used. So
whatever is about to resume or cancel one finds it unused. "Still mentions" is
the whole of liveness; no dead-variable sets are carried in the typing.

**Two tiers.** A program whose Core follows the rules is certified with them
(`Cert.strict`), and the stronger theorem applies. A program that only the
surface checker's path-following accepts still compiles, certified as well
typed only, and for it a second use of a resumption is excluded by the unproved
surface check alone. `glorious certify FILE` says which. Of the 140 accepted
programs in the corpus 136 are in the first tier, and so are all five examples.

What the rules do not cover, and why those four programs fall back:

- **Two callables that each captured the resumption**, of which a function then
  runs one: `let a = { k(1) }; let b = { k(2) }; if(c) { a() } else { b() }`,
  or a function `pick(c, a, b)` that calls `a()` or `b()`. Each owns `k`, so
  `k` is moved twice. The specification says the same of bodies stored as
  independent closures (section 8.3). Two blocks written where a function can
  hand one to the other share an environment instead; see below.
- **A resumption moved into a block and also used after the call the block was
  passed to**: `match(if(c) { Some(k) } else { None }) { ..., None => k(2) }`.
- **Taking apart a tuple that holds a resumption with `let`**: the elaborator
  reads each field, and reading copies. This needs partial moves (section 7.5).

Not attempted: the exact-once class (a value that must be used), `Drop`, moves
out of references, user-declared resource types, and any ownership for
references themselves. A reference stays freely copyable; what keeps a cell
alive long enough is still the unproved scoping check.

## Blocks that share an environment

**Decision (user).** The two blocks of `if(c) { a } else { b }` may both use a
value that can be used once, because they are two bodies over one environment
of which at most one runs. That is the specification's environment sharing
(branded-environment core specification, section 8). Since `if` and `else` are
two separate calls, what tells `else` that the environment is still unspent
travels in the value `if` returns, not in a rule about the expression.

How it is built, without the compiler knowing `if` or `else`:

- **Core.** A callable's type may state its environment: the types of what the
  function captured (`Ty.fn ... (env : Option (List Ty))`). The kernel has one
  more control-free computation, `rebind a fn`: the closure `a` is given up and
  `fn` gets what it captured. It is typed when `a`'s type states exactly the
  environment `fn` is written against. `a` is moved, so the captures are still
  owned once. The ownership proof covers it; nothing else in the proof changed.
- **Prelude.** On failure `if` returns `Err(body)`: the body it did not run.
  `else` gives the failure's payload to its fallback: `Err(failure) => tail
  fallback(failure)`. Both are ordinary definitions.
- **Language rule, part one.** A block written without parameters, where a
  callable taking one argument is expected, takes that argument without naming
  it. This is decided by the expected type, at any call. So `x else { 0 }`
  works on any `Result`, and `x else { e => ... }` can name the failure.
- **Language rule, part two.** If that argument is itself a block that was not
  run, and the checker can tell which block of the program it is, the second
  block runs in the first one's environment: the names both mention are taken
  from what the first captured instead of being captured again. Names only the
  second mentions it captures itself.

A function a program defines gets the same treatment by being written the same
way: `fn pick(c, a, b) { match(c) { Ok(_) => a(), Err(_) => b(a) } }` hands the
block it did not run to the one it runs, and `pick(c, { k(1) }, { k(2) })` is
then well owned.

Consequences to know about:

- `if(c) { a }` with no `else` is a `Result<T, fn() -> T>`. Its failure can be
  matched and the body still called. Where an option is expected, as when it is
  matched against `Some` and `None`, it is converted to one by the prelude's
  coercion (next section).
- That value holds the body, so it holds what the body captured: see "A
  trailing `;` discards a value".

How this differs from the specification:

- There is no erased `Available` witness. The environment is what the first
  block captured, and the block that was not run is itself the evidence that
  the environment is unspent. It is a real value at run time. `Fn`, `RunsIn`
  and `Environment` can be written of a function's type parameters since: see
  "A callable can be asked for by a bound".
- There are no post-environments (`After`): nothing describes what a body
  that ran has left for the next. What is covered is alternatives, including
  chains of them. `or` gives what failed to its right operand as `else` does,
  so in `if(a) { .. } or { if(b) { .. } } else { .. }` each block runs in the
  place of the one before; a block may take over from one that was made
  inside another block's run, from what that one had itself taken over. Two
  bodies that both run, one after the other, each capture what they mention,
  so a value that can be used once can be mentioned by only one of them.
- Bodies stored as independent closures follow normal capture rules, as in the
  specification.

What is and is not proved: the typing rule for `rebind` is part of the proved
type system, and every compiled program's Core is checked against it. Which
block a block is given is found by the unproved surface checker from its
capture variables, and the rewriting is done by the unproved elaborator. They
link two blocks only when exactly one block of the program can be what is
given, and a name both mention stands for the same local: in the activation
both are built in, or, for a block built inside one that ran in another's
place, the local the name was taken from. If the linked Core cannot be
typed, as when the value may also be a function that is not a block, the
program is compiled again with every block capturing for itself.

A program the checker rejects can still be elaborated and run to see it go
wrong. There are no types then, so whether a block takes an argument is read
off the definition of the function it is passed to (`Elab.givesOne`).

## Coercions are declared by the program

**Decision (user).** A function can be declared a coercion: `coerce name`, next
to an ordinary `fn name`. Where a value does not have the type expected of it,
and a declared coercion takes what was found to what is expected, the function
is applied as if the call had been written. The compiler knows no coercion by
name; the prelude declares one, and a program declares its own the same way.

The prelude's is `option`: it takes any `Result<T, E>` to `Result<T, ()>`,
dropping what failed. So a `Result` is an option wherever one is expected, and
`if(c) { a }` without `else` can be matched against `Some` and `None`.

This overrides the specifications, which make `Option<T>` an alias of
`Result<T, ()>` and rule out conversions between `Result` instantiations
(language specification sections 4.3 and 14; standard library conformance row
S02). Their one automatic conversion, `available_to_unit` (section 8.5), drops
the witness of an unspent environment; with environments carried in values
here, forgetting a failure covers that case and every other.

The rules, chosen to keep it predictable:

- **Where.** At an argument of a call, and at the value a clause ends with, for
  a callable written in braces or a top-level function (so also against a
  declared result type). Not at an assignment, not at the result of a `tail`
  call, which has to stay the last thing done, and not in a handler's arms.
- **Which.** Exactly one declared coercion must fit. If several do, none is
  applied and the mismatch is reported, naming them.
- **One step.** Coercions are not chained.
- **By name.** A coercion is not applied where a local has taken its name.
- **Order.** An argument, or a clause, that does not fit is looked at first on
  a second attempt, so that the others can be converted to what it needs. That
  is how the subject of `match(x) { Some(v) => ..., None => ... }` is converted
  although the mismatch only shows in the second argument.
- A coercion is checked before every function that is not part of its own
  definition; inside those, none is applied.

It is a rule of the unproved surface checker, which tells the elaborator where
to write the calls. Core never sees a coercion, only the call, so the proofs
are untouched. A program the checker rejects is elaborated without them.

To know about: this drops errors silently. A `Result<T, IoError>` passed where
an option is expected loses its error with nothing written at the call.

## Borrow checking

**Decision (user): a borrow checker, proved.** Done in stages, each one a
theorem about Core that the checker in `Typing/Checker.lean` establishes for
the programs it accepts.

1. **Cells are scoped in the kernel.** Done: see "A mutable variable ends with
   its block". A cell cannot be released twice or left unreleased by a scope
   that ends.
2. **Regions.** Done in Core, in the checker and in the proofs
   (`Typing/Witness.lean` has four programs with certificates written by hand:
   two accepted, two that go wrong and are turned away). A reference's type
   names the region (the cell) it
   points into; a callable's type lists the regions it may touch when called,
   and may be polymorphic in regions; code may read or write a cell only if its
   region is among those the code was given. A cell's scope gives its body the
   new region and requires that nothing typed outside the scope mentions it.
   The theorem: a program checked this way never reads or writes a released
   cell. The invariant is that every region the running code was given is the
   cell of a scope still on its stack. The theorems are `borrow_safety` (no
   reachable state is about to read or write a released cell), and for the
   checker `checked_borrow_safety`, `checked_scoped_safety` and their compiled
   forms.

   What this is not. A region is one cell: there is no outlives relation, no
   region that stands for several cells, and so no reference that may point to
   one cell or another (a reference stored in a data structure with others of
   different cells cannot be typed with regions). Holding a dangling reference
   is allowed; using it is what is ruled out. References are still freely
   copied: nothing here says a writer is alone (stage 5).

   How it is set up (so that the work can be picked up from here):

   - `Rgn` is `var i` (a region of the function being typed), `bound k` (bound
     by the nearest callable type that binds regions, de Bruijn) or `cell a` (at
     run time, the cell at that address). `Ty.ref ρ t`; `Ty.fn rgns params ret
     eff once env acc` binds `rgns` regions and lists in `acc` the regions a
     call may touch.
   - `FnSig` gains `crgns` (regions fixed when a closure is made, `var i`),
     `rgns` (regions chosen at each call, `bound k`) and `acc`. A body is typed
     with its call regions opened to the variables after the capture regions.
   - The typing judgment carries the regions the code may touch,
     `HasTm Δ ϕ Γ tm τ ε`. A call opens the callee's type with region
     arguments and needs the callee's regions among `ϕ`. Reading or writing
     through `ref ρ τ` needs `ρ` among `ϕ`. `cell init thunk` needs `thunk`
     polymorphic in one region, the cell's, with a result type, row and cell
     type that do not mention it.
   - Typing is closed under instantiating region variables (a substitution
     lemma), so run-time typing stays as it was, on types whose regions are
     cells: entering a function instantiates its body's typing once.
   - Stack typing carries the regions granted to the code on top: a cell frame
     adds its cell, a handler frame keeps what its handled computation was
     given, and a resumption's type lists the regions its frames need below
     them.
   - That every cell frame's cell is live, and that no two frames are for the
     same cell, is an invariant of the machine alone (`Owns`), proved without
     types. Granted regions are cells of frames on the stack; hence live.
   - Declared data types and effects are looked up by the shape of their type
     arguments with the regions taken out, so that a lookup commutes with
     instantiating regions.
   - A certificate has a flag for whether the region rules are to hold
     (`Cert.regions`), as it has for ownership. Without it references are typed
     as before and the theorem does not apply.
   - The checker is told the regions it cannot read off the program: a closure
     hint carries the regions the closure is made with, a call of a callable
     that binds regions is preceded by a hint with its region arguments, and a
     handler hint carries what the handler may touch and the regions each of
     its functions is entered with.
3. **Inference of regions** for the certificate. Done, in `Infer.lean`, which
   is not proved and need not be: what it finds goes to the checker. A program
   whose regions it cannot find is still compiled, with a certificate without
   the region rules, as a program that does not meet the ownership rules is;
   `glorious certify` says which a program got. Of the 140 test programs that
   compile, 137 get the region rules, and so the theorems; of the five
   examples, four.

   **Decision: a failure to find regions is not an error of the program.** The
   surface checker already rejects, with the variable named, a program in
   which something that can reach a mutable variable outlives its block. The
   region rules are stricter in ways that are artefacts of how they are
   written, so a program they turn away may be a good one, and it keeps
   compiling without the theorem. What they have no type for:

   - a reference that may be to one variable or to another;
   - a function that passes a reference to its own variable to itself: a
     function's regions are the same throughout its recursive group;
   - a variable that holds something whose type mentions the variable's own
     region, such as a queue of tasks that use the queue;
   - a callable given the same type as another that uses a variable declared
     later, or made before a block and given, inside it, something that uses
     the block's variable or label: two callables of one type touch the same
     regions, and a callable made by a block is not polymorphic in regions;
   - a reference, or a callable that touches a variable, kept in a declared
     type whose field is written as `&T`, as a `fn` type, or left to be
     inferred, rather than as a type parameter.

   How it works. Regions and "what a callable touches" are two more kinds of
   unknown beside types, rows and call-once flags. A cell's scope makes a
   region that is equal to no other; the callable the scope runs is marked as
   binding it. What a callable touches is a set with inclusions, solved when
   types are written out. A function is written with its regions numbered in
   the order its cells were made, so that two functions that share cells write
   their lists in the same order; a use of a function carries the cells its
   numbered regions are at that use. A declared type is recorded once for each
   shape of its arguments, with a region variable for each region in them.
4. **Labels as regions.** Done, by the same rule. A label scope has a region
   (`Rgn.lab id` at run time); the callable the scope runs is polymorphic in
   it; the label's type says that applying the label touches it; a label frame
   grants it to the code above. So a label can be applied only where its
   scope's region was granted, which is only above its frame:
   `label_safety`, `checked_label_safety`. Unlike cells this needs no
   invariant of the machine: the frame the region was granted by is the one
   the jump looks for.

   With both sets of rules, three of the four faults are ruled out, and the
   theorem is the one the work was for. `checked_full_safety`: **if the
   checker accepts a program with the ownership rules and the region rules,
   and the program goes wrong, then it is at an arithmetic operation whose
   result does not fit in 64 bits.** `checked_compiled_full_safety` says the
   same of its bytecode. 133 of the 140 test programs get this.
5. **Exclusive references.** Done for borrows written as arguments of calls
   of functions: see "References are exclusive" below. The surface checker
   enforces the rule for every borrow; Core has rules for it, a theorem about
   them, and the elaborator uses them for those borrows.

The specification's lifetimes (language specification section 9) are the
surface form of this. Written lifetimes, bounds between them and variance are
in the checker of source text: see "Lifetimes can be written". Core's regions
know nothing of them.

## References are exclusive

**Decision (user): `&mut x` is exclusive, as in Rust.** `&x` and `&mut x` are
different types. While a `&mut` borrow of a variable lasts, the variable is
used only through it; while a `&` borrow lasts, the variable is not assigned
and not borrowed with `&mut`. Writing through a reference needs `&mut`.

- **A borrow lasts while something that holds it may still be used**: the
  reference, a value it was put in, a callable that captured it, a variable it
  was assigned to. "May still be used" is: is mentioned by the rest of the
  block it is in, or of a block around that; and, inside a callable, anything
  the callable mentions from outside, since the callable may run again. A
  value an expression has computed and not yet used, such as an earlier
  argument of a call, holds what it holds until the expression is done.
- **A `&mut` reference used as a value is lent, not copied.** What receives it
  borrows from it, and the reference cannot be used until that is over. So
  `incr(p); incr(p)` is fine, and so is `let q = p; *q = 1; *p = 2`, where
  Rust would call `p` moved; `let q = p; *p = 1; *q = 2` is an error. A `&mut`
  where a `&` is wanted is lent for reading.
- **A function that only reads through a reference takes either kind.** The
  kind is inferred like a type, and a function is polymorphic in it.

**Decision: a callable that mentions a mutable variable does not borrow it.**
It uses the variable when it runs, so what a borrow forbids is *calling* it,
and passing it to a call that might. This departs from Rust, where a closure
borrows what it mentions for as long as the closure lives. The reason is the
rule that the compiler knows no control flow: `while({ i < 5 }) { i = i + 1 }`
is a call given two callables, one that reads `i` and one that assigns it, both
alive throughout. Under Rust's rule that is an error unless the checker is
taught what `while` does. Under this rule nothing needs teaching: neither
callable holds a reference, and they do not run at the same time. What is lost
is only that two callables over one variable may exist together; no reference
can be made to see a change it should not.

What is proved, and of what. Core has rules for borrows
(`Glorious/Typing/Loans.lean`, `checked_exclusive_safety`): a program whose
Core is accepted with them never reaches a state about to read, write or lend a
variable through a reference that a newer borrow in scope excludes, or through
a borrow whose scope has ended; and no borrow's scope is ever set aside in a
resumption. The machine does not enforce any of this: the theorem is about
what an accepted program does.

What a borrow costs at run time. Nothing reads what a scope adds, and the
compiled code does not keep it: the frame that marks where a borrow ends is in
the Core machine only, and `compile_correct` is proved with the bytecode having
no such frame. What is left in the bytecode is the counter that gives a borrow
its identity, one addition, because the proof relates the two machines' values
exactly and a reference says which borrow it is; the Rust VM's references do
not carry it. So a call with one borrow among its arguments is a call: `lend`
takes the other arguments and calls the function itself. A second borrow in the
same call, and a borrow given a name, each make one callable and one more call,
as a mutable variable's block does. A borrow that is not a scope is the copy of
an address.

- **In Core a borrow is a scope.** A reference value carries the borrow it is
  (zero for a variable's own), and `lend` runs a callable with a reference that
  is a new borrow, inside a frame that marks where the borrow ends. The
  callable is polymorphic in the borrow's region, as the callable a variable's
  block runs is in the variable's, so the borrow cannot leave; and of the
  regions around it the callable may touch none that was lent.
- **Leave to write a region is a region.** What a computation may touch is a
  list of regions, as before; `wr r` in the list is leave to write `r`. A
  variable's block grants both, a borrow for writing takes both away and grants
  both of the borrow's, and a borrow for reading takes away only leave to write.
- **Regions that a function touches are different regions where it is
  called.** Taking a region away means nothing if the same variable can be
  reached under another name. Region inference already gives a function a
  signature for each pattern of regions it is used at, so this costs nothing.
- **The callable a borrow's scope runs performs no operation it does not
  handle itself.** Otherwise a handler outside the scope could run while the
  borrow is set aside in a resumption, and use the variable.
- **Which borrows are scopes.** The elaborator makes a borrow a scope where
  the program's Core then passes every rule, deciding each place alone and
  then taking the places one at a time.
  - Written as an argument of a call of a function, `f(&mut x)`: the scope is
    the call.
  - Given a name, `let p = &mut x`: the scope is the statements up to the last
    that mentions `p`, run in a callable that is given the borrow and gives
    back what they bound that the rest of the block uses. If that does not
    pass, the scope is tried again taking in the statements that mention
    anything made from `p`.
  - Given to a function whose result is given a name, or put straight in a
    tuple or a constructor that is given a name: each borrow is named first
    and is a scope that lasts while the result is used.

  A scope is statements, and scopes nest; the elaborator arranges the code so
  that this costs little. A named borrow is made just before the first
  statement that mentions it, since making a reference does nothing: so two
  borrows written together and used one after the other do not overlap, and a
  `defer` or an operation between a borrow and its first use is outside the
  scope. Where the last statement of a scope is a call whose later arguments
  do not mention the borrow, the arguments up to the last that does are
  computed first and the scope ends with them: so the variable can be borrowed
  again later in that statement. A trait's function, where the implementation
  is known, is called by name, so a borrow passed to it is a scope like any
  other.

  What is still not a scope: a borrow that is in use across an operation
  handled outside it (the rule above); a reference that may be to one of two
  variables, and a function that passes a reference to its own variable to
  itself, for neither of which the region rules have a type; and a borrow
  passed in a `tail` call or to a callable made before it. Such a borrow is,
  in Core, the variable's own reference: the theorem says nothing of it, and
  only the check of the source text keeps it exclusive.
  `glorious certify` lists every one, and `glorious certify --strict` fails if
  there is any. Of the 33 programs in the corpus that borrow, 29 have every
  borrow a scope; 35 borrows are scopes and 6 are not.
- **`replace(&mut x, v)` is not a borrow.** It puts a value in the variable and
  gives back the old one, as an assignment does; nothing outlasts it.

What the rule is not:

- **The check of the source text is not proved.** It is a check in
  `Check.lean`, like the checks on scopes that it sits beside. It is what
  rejects a program; the Core rules never do, and a borrow they cannot accept
  is simply not made a scope.
- An operation performed while a borrow is held runs a handler's arm. The
  check of the source text now covers this: a resumption holds the borrows the
  computation it suspended had made (those written in the handled expression,
  and those any callable it mentions makes while it runs), so an arm that uses
  what they exclude while the resumption is still to be used is refused; and
  performing an operation counts as calling whatever callables it is given. In
  Core such a borrow is still not a scope.
- The theorem is stated of the Core machine. The bytecode machine is shown to
  compute what the Core machine does, but the statement about borrows is not
  carried over to its states.
- A `&mut` reference is lent only where its type is known when it is used. One
  copied before that, or inside a tuple or a declared type, or by a function
  generic in its type, is copied: the copies are one borrow.
- "Still to be used" is read off the text, not the paths through it: a name
  mentioned later in any branch counts.
- A value that is either what a body gave or the body that was not run, which
  is what `if` gives `else`, is understood: its alternatives are not both
  there. Two separate values that are never both live are not.

How it works. A borrow is one more thing a capture variable can capture, so a
type says which borrows a value of it holds, in the way it already says which
labels and variables it can reach. Each use of a variable, each use through a
reference and each call is recorded with the names the rest of the computation
mentions and the values the expression had in hand, and all are checked at the
end of the function, when the types are known. A use of a function inside its
own recursive group is given captures of its own, related to the function's as
any other use is, so that what a function passes to itself is not taken to be
what it was passed.

## A callable can be asked for by a bound

**Decision: `Fn`, `RunsIn` and `Environment` are the compiler's, and say
what the checker already had ways to say.** They are written of a function's
type parameters, in `<..>` or after `where`. They are not traits a program
can implement, and there is no general trait with parameters or associated
types behind them.

`F: Fn<(A, B), Output = R, Effects = {E}>` says the type parameter `F` is a
callable of those arguments, result and effects: it is `fn(A, B) -> R / {E}`.
Without `Effects`, what it performs is inferred, as for `fn(A, B) -> R`. One
argument is written `(A,)`.

`E: Environment<'e>` names an environment, and `F: RunsIn<E, (A, B), Output =
R>` says `F` is such a callable and runs in it. Given `E` itself, a callable
uses the environment up, so of the callables given one environment at most
one is called on any path; with `E: Use<[1, 1]>` exactly one is. Given `&E` or
`&mut E`, a callable may be called again. The function's body is counted
against this as a value used once is counted: each such callable is taken to
use the environment when called, and the uses are counted along every path.

This states in a signature what `if` and `else` do by handing a block that
was not run to another. And it is built the same way: where blocks are
written for callables that share an environment and take no arguments, the
first holds what it captured and each other is built over that, so a value
used once that several of them mention is captured once; in the function, a
call of one that does not hold the environment gives it the one that does.
Core's ownership rules accept the result: `pick(c, { k(1) }, { k(2) })` with
`pick`'s two callables in one environment is well owned in Core, where
without the bound it is only well typed. With `Use<[1, 1]>` the blocks may
hold a value that has to be used, if every one of them holds it.

`After = E2` says what a callable leaves: an environment in which others
run only once it has. The function's body is followed along each path up to
the first call that leaves `E2`, and no call of one that runs in `E2` may be
on it. `L: Label<T>` is a label that takes a `T`.

Limits. A function with callables that share an environment is called where
it is named, and is given blocks or names for them. `After` orders the
calls and no more: what the first callable captured is not handed to the
second.
Since: a callable lent the environment, `&E` or `&mut E`, may be called any
number of times while it is there, and not once a callable given `E` has
been called (unless that one says `After = E`). The count follows each path
up to a call of one that is lent it, and no call of one given it may be on
it. A callable lent the environment that goes where the count does not
follow, into a variable or out of the function, is refused as not shown.
And the count no longer follows a function into itself: what the function
is given then goes where the count does not follow, which says of every
later round what the first said. So a loop in a function that is given an
environment is counted, where before the count gave up.

The lifetime of `Environment<'e>` is read and not used. A
callable of a trait's function, `Label<T>`, and `unsafe Fn` are not built. An
ordinary trait written of a type parameter is checked to exist; which traits
a function needs is still inferred. The caller is still checked by following
the function's body, so the bound is checked of the function but not yet
relied on alone.

## `is` gives what it found to the block that runs

**Decision: an `is` is a pattern callable, and its names travel as a value.**
`subject is Pattern` is the subject given to a callable of two clauses: on a
match, `Ok` of what the pattern's new names stand for; else `Err(())`. So it
moves and lets go exactly as a pattern does, and the subject is computed
once. What it found has a type that carries the names, `%is:a,b`, which no
program can write.

The prelude's `if` gives its body what the test found: `()` for a comparison,
this for an `is`. A block written without parameters already took what it was
given without naming it; given what an `is` found, it has the names. That is
the whole rule, and it names no function: `and` gives its right operand what
its left found, `while` its body what its condition found, and a function a
program defines can do the same. In `if(v is Some(n)) { n } else { .. }` the
name is the body's and not the fallback's, because `if` gives the fallback
the body, not what was found.

This changed `if`: its body takes one argument, so a body that was not run is
a callable of one argument. A block given that takes over its environment as
before; the certifier is told how many arguments the block given up took.
What Core shows of the corpus is unchanged.

Departures from the specification's section 9.3. An `is` moves what it binds
out of the subject, rather than copying what can be copied and borrowing the
rest; so a subject that has to be used is refused, since a failed test would
let it go. `and` does not keep what its left operand found for the body of an
`if` after it, and there is no negative context. A name is told from another
by its spelling.

**Decision: an `is` that borrows is not built for now.** It would have the
block that is given the result make the names, from the reference and a
pattern carried in the result's type: a clause that is never reached for the
other constructors, and each pattern of an `and` matched twice. A callable
with a clause that binds by reference, `match(r) { &mut P => .. }`, does what
it would.

Limits. The test has to be written before the block in the arguments of a
call, since the block is read knowing what it is given. A program run without
the checker has no names from an `is`.

## A type's own functions are its module's, named after it

**Decision: `impl Type { fn f(..) }` declares a function of the module the
implementation is written in, named `Type::f`.** It is called `Type::f(..)`,
and is as private as it is written: without `pub`, the module's. The type's
parameters after `impl` are the function's first type parameters, and `Self`
in what the function takes and gives is the type. Two functions of one name
in a type's implementations are a function declared twice, whatever they
take, as the text asks. The call has an explicit receiver; there is no
`value.f(..)`.

A module for the type's functions, beside the type, was tried first and does
not work: it would use the module it is in, which uses it, and modules do not
use each other in a circle.

`Self` is also the type in the functions of `impl Trait for Type`.

`const NAME: Type = value;` and `let NAME: Type = value;` at the top of a
module are a value with a name, of that type; either can be a pattern.

Limits. `Self::f(..)` is not read where a function is called: the type is
written. `impl<T: Bound> Type<T>` is not; the bound is written on the
function. A constant is computed where it is named, each time.

## `(x,)`, `-> !`, and a row without braces

From the audit of the specification.

- **`(x,)` is a tuple of one part** in a value, a type and a pattern, and is
  not `x`; `(x)` is `x` in brackets. Before, the comma was dropped, and a
  function of one tuple took a plain value.
- **`fn f(..) -> ! { .. }`** is a function with a type parameter of its own
  for its result: it gives whatever is wanted where it is called, and only a
  body that does not come back has every type. So nothing new is typed.
- **What a function performs** may be written without a result,
  `fn log(x: Int) / {Diag}`, and one effect without braces, `/ Diag`.
- **`@name: T { .. }`** is the scope with its type written, as a `let` with a
  type is.
- **`[0, *]`** is `[0, infinity]`.

## A name that is two things is an error; an effect brings its operations

From the audit of the specification (2.3, 2.4).

- **Two meanings at once are not chosen between.** A name the module
  declares and also names in a `use`, or names in two `use`s of different
  things, or that two `use ..::*` both bring with nothing nearer, is refused
  where it is written, with both meanings. Before, the first was taken. What
  the module declares or names still comes before what `::*` brings, and
  that before the prelude; a local name still hides them all.
- **`use p::Effect;` brings the effect's operations** under their own names,
  whatever the effect is renamed to with `as`. Two effects with an operation
  of one name are then two meanings, and
  **`use p::Effect::{read, write as emit};`** brings only the operations
  named, as the way out. An arm of a handler is written with the name the
  operation has here. It is the same operation however it was brought.

## Attributes, and a program without the prelude

From the audit of the specification (2.5, 20).

- **`#![no_implicit_prelude]`** at the top of the first module: the modules
  of the program have the prelude's names only where they bring them in.
  **The prelude is the module `prelude`** where the program has no module of
  that name, so `use prelude::{if as when, else, <, +};` brings and renames
  what is wanted, and a program can give `if` a meaning of its own.
  **`#![no_std]`** is that, and the library's modules are not there.
- **`#[non_exhaustive]`, `#[repr(C)]`, `#[repr(transparent)]`,
  `#[export_name = ".."]`** are read before a type or a function and kept
  beside it. No other attribute is known, and one is an error.

Limits. What a text or a number written in the program is made of still
comes from the prelude, brought in or not. The prelude's operators are still
read as operators without being brought in; the function an operator stands
for has to be. `#[non_exhaustive]` changes nothing while there is one
package. The other three are kept for the C interface and do nothing yet.
When the library takes the shape its specification gives it, `core`, `alloc`
and `std`, the prelude's names will be theirs, and `prelude` a selection.

## Types written at a call

**Decision: `f<A, B>(args)` writes types for the first type parameters of the
function called, in the order the function declares them.** The rest are
found as before, so a prefix is enough (13.1). Lifetimes written there are
read and not used. It is for a function of a module that declares type
parameters, a type's own functions among them; written of anything else it
is an error, as is one type too many. With it `as<T>(value)` is a function
anyone can write, `fn as<T, S>(v: S) -> T where T: From<S>`.

`f<A>(x)` is read as that, and not as two comparisons, where what follows
`<` reads as types closed by `>` with `(` straight after. So `a < b` and
`both(a < b, c > d)` are comparisons still.

Limits. `both(a < b, c > (d))` is read as a call with types written, and is
then an error: the bracket after `>` is what decides. Types cannot be
written for a trait's function, an operation or a constructor.

## Clauses of one tuple for several arguments; types on `fn(..) { .. }`

From the audit of the specification (5.4, 6.1).

- **`{ (x, y) => .. }` given where a callable of two arguments is wanted
  takes them as `x` and `y`**: where every clause of a block is one tuple of
  as many parts as the callable wanted has parameters, the parts are the
  parameters. Where a callable of one tuple is wanted, the same text is that.
  The two stay different types; which is meant is decided where the block is
  an argument, by what the parameter asks.
- **`fn(a: A, b) -> R / {E} { .. }`** may write the type of a parameter, and
  what it gives and performs: it is then the callable, of the type those
  make, as a value written with its type is.

Limits. A block of one-tuple clauses is taken for several arguments only as
an argument of a call, not where a `let` says the type.

## `move`, a fixity's function by its path, `unsafe trait`

From the audit of the specification (5.3, 8.2, 14, 15.1).

- **`move x` is the value of `x`, and `x` is not used after**: in the
  statements that follow the one it is written in, a use of `x` is an error,
  whatever the type. A value that can be used once was already handed on by
  being named; `move` says it of one that could be copied.
- **`move (a, b) { body }`** is the block holding the values `a` and `b`
  have where it is written: a callable given them at once, which gives the
  block. A block that mentions a mutable variable otherwise uses the
  variable as it is when the block runs.
- **`infixl 30 <-> = numeric::sub;`**: the function a fixity names may be
  written with its module.
- **`unsafe trait`** is implemented with **`unsafe impl`**, and nothing else
  is: the two words are checked to go together, and say what the checker
  does not see.

Limits. `move x` of a mutable variable, and `move *reference`, are refused
with `replace` as what to write: a variable that holds nothing for a while is
not followed. A use of `x` later in the statement that moves it is not seen.

## What a function needs of a type parameter it wrote

**A hole, closed.** A function with its type parameters written,
`fn twice<T>(t: T) -> (T, T) { (t, t) }`, could use a `T` twice or let one go,
and be called with a type that has to be used exactly once: a `File` was
duplicated, or dropped (the specification's case L20). A type parameter that
is written was taken for a type already known, of which nothing more needed
asking. It is now what an unwritten one always was: what the body needs of it,
to go unused or to be used more than once, is part of the function's type and
is asked of the type it is at each call.

**Decision: `T: Use<[fewest, most]>` says it.** Written of a type parameter,
it is all the body may need: `Use<[1, 1]>` and the body can neither let a `T`
go nor use one twice; `Use<[0, 1]>` and it can let one go; `Use<[0, *]>` and
it can do both. And it is what a caller has to give, whether or not the body
makes use of it. Where nothing is written, what the body needs is found, as
the traits it needs are.

Limits. The specification has a type parameter with nothing written be one
that has to be used; here that is found from the body instead, so a function
may be given more freedom than it wrote down.

## A trait's type said in a bound; a trait's function for a type written

From the audit of the specification (13.2).

- **`T: Trait<Item = Type>`** says what the type the trait leaves to `T`'s
  implementation is: in the body `T::Item` is that type, and a caller's
  implementation has to say the same.
- **`<Type as Trait<A>>::f(args)`** is the trait's function for the type
  written, with the trait's arguments written; `Trait::f(args)` already named
  it by its trait and found the type.

## Operations as values; what a type asks of its parameters

From the audit of the specification (10.8, 20).

- **An operation named where it is not called is a callable that performs
  it** with what it is given, and a trait's function named so is a callable
  that calls it. The resolver writes the callable out; it is the same
  operation, and its effect is the callable's.
- **`struct W<T: Show>(T)`, `struct W<T> where T: Show { .. }`, and the same
  of an `enum`**: what is asked of a type parameter is asked where a value
  of the type is built, and nothing is handed to the constructor for it.
  `T: 'a` is read.

- **A function `main` does not reach is elaborated too**, for what only the
  elaborator refuses (`tail` out of place), and then left out of the program
  as before.

Limits. A function that needs a trait of a type it is generic in is still
called where it is named. A declared type's bounds are not assumed inside a
function that is given one: the function says them again. Only traits
without arguments of their own are asked of a type's parameter.

## What the specification's audit turned away

An audit of the language specification against the compiler, section by
section, is the source of these. Each was accepted before and is refused now,
as the text says:

- a byte literal or byte string with a character above 127 that is not
  written `\xNN` (and `\xNN` in one may now be any code that fits a byte);
- two operators of one precedence in a row where either is `infix`, or where
  they group opposite ways;
- a precedence above 255;
- a name bound twice by the patterns of one clause;
- what is unsafe, named in a callable written inside `unsafe { .. }`: the
  callable runs later, and `unsafe` is written again inside it.

A byte-order mark at the start of a text is skipped.

## Scalars are integers the checker tells apart

**Decision: Core gets primitives, not types.** A value of `i8 i16 i32 isize
u8 u16 u32 usize`, of `f32 f64`, or of `char` is an integer on both machines:
the number itself, the bits of the IEEE 754 encoding, the code. The checker
knows the eleven names as types and keeps them apart; Core and its typing see
integers. For each there are two names that do nothing, `i8_bits(x)`, the
`Int` an `i8` is held as, and `i8_of(n)`, the other way: with them the
prelude says what each type's operations are, in Glorious. `i64` is another
name for `Int`.

Core has sixteen more primitives, each two integers to an integer as the
five before: `intDiv` and `intRem` (towards zero), `intFit` (the integer, if
it fits a width), and thirteen for floating point. One that has no result
has no meaning there, as overflow already had none: a result that does not
fit its type, a zero divisor, the whole part of an infinity. The typing rule
for a primitive and every theorem are as they were.

**Decision: what floating point means is written out.** `Glorious/Float.lean`
defines each operation exactly, on natural numbers: the true result rounded
to the nearest number the format holds, a tie to the even one, and one NaN.
It is not Lean's `Float`: the kernel cannot compute with that, and its
equality would bring `Classical.choice` into theorems about one step. The
Rust VM uses native arithmetic; the two agree on every program of the corpus
that computes with floating point, and the definition agrees with native
arithmetic on 51120 pairs of special and random numbers. 32-bit operations
are the 64-bit ones brought back to 32 bits, which is the nearest to the true
result for these four.

**Decision: the operators are traits of the prelude.** `+ - * / %` and the
comparisons are functions of `Add`, `Sub`, `Mul`, `Div`, `Rem`, `Eq`, `Ord`,
which `Int` and each scalar type implement. Where the type is known the
implementation is called by name, as before; a function that adds what it is
given is now a function of any type with `Add`. No program of the corpus
changed its result or what Core could show of it. A program run without the
checker has no traits, so it is given a prelude whose operators are `Int`'s.

Literals. `5u8` is a whole number of that type and has to fit; `0x`, `0o`,
`0b` and `_` between digits; `1.5`, `2e-3`, `1.5f32` are the nearest number
of their type, and one too large is an error; `'a'` and its escapes; `-`
straight before a number is part of it. Each may be a pattern, but not a
floating point number.

Text. `"..."` is a `Str`, which the prelude declares as the characters one
after another; the compiler writes a literal with that type's two
constructors, which it names as the prelude's whatever the program declares.
`show` gives a value as text (`Show`), `say` writes it. A floating point
number is shown with the fewest digits that give it back, found in the
prelude with the primitives that give a number to so many digits and take
digits to a number. Where a value is shown, a `Str` is shown as its
characters: the two printers know its constructors by names no program can
write. `print` still writes a value as the machine holds it, so a floating
point number as its bits: `say` is for people.

The first module may declare a name the prelude has; the prelude's is then
`prelude::name` in the whole program. What only the prelude needs is in a
module inside it and cannot be named.

Since added (see "Wider integers and what was missing of scalars"): `u64`,
`i128`, `u128`, a `usize` of 64 bits, literals that take the type wanted of
them, `-` before any value, block comments, `b'x'`, operations on bits,
square root and rounding, `Show` for tuples and `Result`.

Not built. Conversion other than through `Int` (`u8(n)`, `int(x)`, `f64(n)`,
`widen`, `narrow`, `char(code)`). A `Str` is a list: there are no arrays, so
its length is counted.

## A `&mut` reference is not given to a resumption

**Decision: `k(&mut x)` in a handler's arm stays refused, because it is
wrong.** It was on the list of what the checker refuses without cause. It
has cause. A handler is deep: the computation `k` resumes runs under the same
handler, and may perform the operation again, when the arm runs again and
borrows `x` with `&mut` again, while the computation still holds the first
reference. `let a = ask(); let b = ask(); *a = 1; *b = 2` would then have two
`&mut` references to one variable. The message says as much: calling `k` may
borrow `x` while a value still in use holds a `&mut` reference to it. A
shared reference can be given (`k(&x)`), and a `&mut` reference can be the
operation's argument (`tick(&mut x)`), which is lent for the arm and no
longer.

## A callable's type binds a region where it has to

**Decision: when a certificate is looked for, a callable given a reference is
first taken to be one whose type binds the reference's region, `for<'a>
fn(&'a T)`; and if no certificate is found that way, as before.** Core's
callable types have always been able to bind regions (the callable a cell's
scope runs binds the cell's), a call chooses them, and the checker reads the
choice from a hint. What was missing was the search: a callable passed to a
function and given there a reference to one of the function's own variables
was taken to want a reference to one particular cell, which could then only
be that variable, whose region its own function's signature cannot mention.

What the search now does. A call whose callable is not yet known is kept
until it is, or until what it is given is. If what it is given has a
reference in it, the callable's type binds that reference's region: what the
call gives is the callable's result with the call's region for the bound one,
found from whichever of the two is known first. A callable literal that
takes a reference to a region nothing it captured mentions binds that region
too. What a function touches through such a call is what the callable
touches, with the same exchange. All of this is part of a function's general
type and is found again for each use of it. The regions bound are not cells:
they stand for whichever cell a call chooses.

Nothing here is trusted: the checker reads the certificate as before, and a
program for which this search finds none, or one the checker turns away, is
tried the old way.

Of the 451 test programs that compile, 437 are now shown to follow all of
Core's rules, from 432.

Since: a callable type binds as many regions as the references it is given
have (up to three), so `for<'a, 'b> fn(&'a T, &'b U)` is found.

And a function that calls itself with a reference to its own variable, where
the region differs at each depth, has a type that binds the region: a
function inside one whose type binds a region is told which region that is,
as it is told which cell.

A call whose callable takes a reference waits until what it is given there
is known: it may be a reference to a cell, and then the callable's type binds
the region. Before, the variable in a block of the function was taken to be
the one cell the function's parameter could point to.

A function may be lent to directly, `go(&mut y, n - 1)`: the scope of the
borrow runs the function itself. Then the region of the borrow is one the
function's type binds, not one borrow's own, since the function is lent to
from elsewhere too. A resumption lent to binds none. And the search with
borrows as scopes of their own is run with callables taken to bind regions
where it fails without. So such a function's borrows are scopes of their own.

`for<'a> fn(&'a T) -> R` written of a field of a declared type binds its
regions in the certificate as it does of a parameter; a callable kept there
may touch those regions and no other.

Limits. `for<..>` as an argument of another type in a function's signature,
`Option<for<'a> fn(&'a T)>`, is refused by the checker with a message: what
is given is held to every lifetime only where it is given to a parameter or
a field. With callables taken to bind regions, a handler whose operation
gives a reference of an effect's lifetime is not shown; it is without, so a
program that needs both is not.

## A lifetime of a declared type is an argument in Core

**Decision: Core's declared types and effects take no regions, and do not
need to: a lifetime parameter is a type argument that carries a region.**
`struct Holder<'a>(&'a Int)` is, for the certificate, a type of one argument,
and `Holder<'a>` at a variable `x` is that type at `&ρ ()`, with `ρ` the
region of `x`'s cell. The field is `&ρ Int`, where a certificate already
writes a declared type's fields: in terms of the regions of its arguments.
The same for `effect Reader<'a> { ask() -> &'a Int }`. Nothing in Core
changed; where certificates are found, a declaration's lifetimes are now
read (they used to be taken out with every other lifetime before that), and
a reference for a lifetime the declaration takes points where that argument
says.

Before this, a reference in a declared type was of one region for the whole
program, so a program that kept a borrow of a variable in a `struct`, or
handled an effect with one, could not be shown to follow the region rules.
Of the 451 test programs that compile, 432 are now shown to follow all of
Core's rules, from 424.

What was still not shown then, 19 programs: a callable given a reference to
a variable of the function it is passed to (six, `for<'a>`; five of them are
shown since, see above); a reference to one of two variables (four: Core has
no region that is either of two cells); a resumption kept in a pair or
taken by two callables of which one runs (four, ownership); a resumption or
a label kept in a variable (three); and two others.

## A program the checker rejects has no traits

**Decision: running a program without the checker stays what it is, a way
for the tests to watch a rejected program go wrong, and such a program has
no traits and no `is`.** Which implementation a call of a trait's function
means, and what names a block given the result of an `is` has, are decided
by types. A program the checker rejects has none: there is nothing to decide
them by, and no way to add them that would not be a second, weaker checker.
So an unchecked run uses the prelude of `Int` alone, as before, and a
program that needs a trait is one that has to pass the checker. The command
line always checks.

## What is unsafe

**Decision: `unsafe` marks what the proofs say nothing of, and a program
that does any of it has no certificate.** Three things are unsafe: calling a
function that is not written in the language, reading the bits at an address,
and writing them. The checker lets them be named only in `unsafe { .. }` or
in the body of an `unsafe fn`, which is itself unsafe to name. Everything
else about such a program is checked as before; its Core is not shown to
follow Core's rules, because Core's host has no such operations: on the
proved machines the program stops there, and says so. The Rust VM runs it.

- `extern "C" { fn strlen(s: usize) -> usize; }` declares functions by the
  names C has for them. Each is an ordinary function of the language whose
  body is one host operation: the name, how many bits come back, and the
  values. The VM finds the name among what the process has loaded and calls
  it. What goes across is whole numbers of a stated width, and addresses,
  which are `usize`; at most six.
- `ptr_read(at, width)` and `ptr_write(at, width, value)` read and write so
  many bits at an address: with a sign if the width is positive, without if
  negative.
- `unsafe { .. }` is a block run where it is written. `unsafe fn` is a
  function. There is no `unsafe Fn` bound: a function is unsafe to name, and
  once it is a value the one who named it has answered for it.
- `std::c` has `malloc`, `free`, `strlen`, bytes at an address, and texts as
  C has them (`c_string`, `text_at`), over `std::text::utf8` and `from_utf8`.

Why nothing in Lean. A foreign function is not something Core's host can be
said to do: `Host.call` is a function, and the proofs are about it. Giving
foreign calls a meaning there would be an axiom about C. So they have none,
and the line between what is proved and what is not is the word `unsafe`.

Limits, against the specification (15, 16): no typed pointers (`*T`), no
layouts (`repr`), no floating point or structures across the boundary, no
callbacks from C, no functions with a varying number of arguments, no
linking of a library by name (what the process has loaded is what there is),
and no rules for when unsafe code is sound: a safe function with an `unsafe`
block inside is trusted, as it is everywhere.

## The standard library is written in the language

**Decision: `std` is a module the compiler has the texts of, and a program
that names it has it.** The texts are in `Glorious/Std.lean`, one for each
module; a program that has the word `std` in it, and no module `std` of its
own, is compiled with them as files beside it, `pub mod std;` in its first
module. Nothing else is special about them: they are resolved, checked and
elaborated as the program's own modules are, and name each other and the
prelude as any module would. What nothing reaches is left out, so a program
pays for what it uses.

What is there: `std::option` and `std::result` (the usual functions over a
value that may not be there); `std::cmp` (`Ordering`, `compare`, `min`, `max`,
`clamp`); `std::int` (`abs`, `pow`, `gcd`, `lcm`, division rounding down,
`digits`, the whole root); `std::char` (what a character is, in ASCII);
`std::text` (searching, cutting, splitting and joining texts, `parse_int`,
padding); `std::vec` (arrays: `map`, `filter`, `sort`, `binary_search`, `zip`
and the rest); `std::map` and `std::set` (kept in order, in a balanced tree,
for keys with `<`); `std::iter` (values one at a time, made when asked for);
`std::hash` (the trait `Hash`, and a map over an array of buckets, which
arrays read in a step make worth having); `std::c` (see what is unsafe).
The prelude gained `Eq` for `()`, pairs, triples, `Result` and arrays, and
`Ord` for pairs and texts.

It is checked once, with the prelude, for as long as the compiler runs.

Found on the way. A default function of a trait was one function shared by
every implementation that took it, and each call in it was met once, by the
first implementation's types: `q` of a `char` called `p` of an `Int`. Each
implementation now has its own copy. Making a fresh variable copied the
whole table of variables, in the checker and where certificates are found:
the time went with the square of a program's size. A program of 150
functions took 3.9 s to certify and now takes 0.1 s.

Limits, against the specification of the library (3000 lines): this is a
tenth of it. No `String` that owns a buffer, no slices that borrow, no streams, files, paths, clocks or
processes, no formatting traits beyond `Show`, no generators or tasks, and
none of the structures for writing a compiler. A function in a trait cannot
have a type parameter of its own, so `map` over an iterator is a function
and not the trait's.

## What is a module's own

**Decision: a module that is not `pub`, an operator's fixity and a coercion
are each their module's, as a declaration is.**

- `mod b { .. }` written in `a` without `pub` is named by `a` and by what is
  written in `b`, and by no other module: not by a module beside it, nor by
  one written in a module beside it. As with a declaration, being written
  inside a module gives no right to what that module keeps to itself.
- A `pub` function's type has no type in it that is private to the
  function's module, whether the type was written or found. One who calls
  the function could not write it. A type whose inside is to be kept is a
  `pub struct` with fields that are not `pub`.
- A fixity holds in the module that declares it, and not in a module written
  inside that one. A module that brings in, with `use`, the function an
  operator stands for (the operator itself, unless the fixity says `=
  function`) has the operator with its fixity; two that disagree are an
  error. The prelude's hold in every module (specification 14).
- A coercion applies in the module that declares it and in a module that
  brings its function in with `use`. The prelude's apply in every module.

How. The fixities of every module are found from the tokens of all the texts
before any is parsed, and the parser changes table where a module begins. The
resolver says which modules are not `pub`, which functions are, which types
are not, and which coercions apply where; the checker reads that.

## The prelude is checked once

**Decision: the checker checks a list of items against what it already
knows, and a program is checked after the prelude, which is checked once for
as long as the compiler runs.** What the checker knows after the prelude is
kept; a program starts from there. So a program's functions are checked
against what the prelude declares and what was found of its functions, and
not with them. A program that declares a name the prelude has (the prelude's
is then `prelude::name` throughout) is checked with the prelude, as before.

And what nothing reaches from `main` is left out before Core is made: of the
prelude's nine hundred functions a small program keeps a few dozen. The
certificate is of the program that runs.

Measured on one small program: checking 42 ms, of which the prelude was
nearly all; making and certifying Core 16 ms before, 5 ms after. The 701
test programs on three machines: 17 s, from about 45 s.

Limits. This is one step towards modules compiled apart, not that: the
modules of a program are still resolved and checked together, in one list,
and nothing is written to a file between runs. Counting the uses of a value
still follows the bodies of the functions it is given to, in whatever module.

## Arrays are Core's

**Decision: an array is a value Core's machines build, read at a place in one
step.** It replaces the tree the prelude built (the decision this section
held before): the surface is the same, `[a, b, c]`, `[x; n]`, `a[i]`,
`a[i] = v`, `[T]`, `b"bytes"`, `len`, `push`, `pop`, `get`, `fold`, `each`,
`slice`, and `a[i]` is still `index(a, i)` of the trait `Index`.

What Core has. An array is a value made of fields, like any other; what makes
it an array is its constructor. One name is kept for the type of arrays, and
it has a constructor for every length: the one that takes `n` elements is
`arrayBase + n`, above any a program declares. So an array of any length is
built by the computation that builds every value, typed by the rule that
types it, and the empty array is the first of these with no fields. Core's
types did not change, nor what it is for a value to have a type.

Five intrinsics work on a value made of fields: the field at a place
(`arrGet`), the value with another field there (`arrSet`), how many
(`arrLen`), the value with one more, built by the next constructor
(`arrPush`), and the value without its last, built by the one before, with
the last (`arrPop`). None has a meaning at a place that is not there. Their
typing rules do not mention arrays: each asks of the type what it needs, that
every constructor's fields are of one type (`Uniform`), that after each
constructor comes one taking one more (`Grows`), that before each comes one
taking one fewer (`Shrinks`). The type of arrays meets all three, and that is
proved of the context a certificate describes. An intrinsic copies what it
reads, so the array and its elements are duplicable where the ownership rules
are checked.

What was proved again: that these computations give values of their types
(`rhs_ok`), hold no resumption they should not (`rhs_occ`), keep their typing
under other regions (`HasRhs.inst`); that the checker's reading of them is
sound; and the rest of type safety, which went through unchanged but for one
thing. A fault of an intrinsic used to be arithmetic on two integers that has
no result. It is now any intrinsic that has none: a place that is not there
is one. `compile_correct` needed nothing: both machines share what an
intrinsic means.

Changing an array where it is. An array is a value, and `a[i] = v` makes `a`
another array. For an array a `let mut` variable holds, the elaborator takes
it out of the variable with Core's `swap`, an empty array left in its place,
changes it, and stores it back: nothing else holds it meanwhile. The Rust VM
moves a local's value at its last reading instead of copying it (found when
a program is loaded: an instruction is followed by the next or by where its
test fails, always further on), and an intrinsic changes fields in place
when nothing else holds them. So a loop that pushes onto an array or writes
its places takes time in proportion to the work: 200 000 pushes, 200 000
writes and 200 000 more pushes in a function that calls itself, 1.3 s. The
Lean machines copy, as their definition says; they are what the VM is tested
against, on small programs.

Limits. `[T; N]` is not built. A slice is a new array. A `Str` is still a
list of characters. An array of values that cannot be copied in Core (it
holds a resumption) is not shown to follow the ownership rules: the
intrinsics copy. `pop` and `len` take the array, so of an array whose
elements can be used once they are of little use. The VM's moving is not
proved; nothing about the VM is.

## Traits, filled out

**Decision: every addition is settled before the solver, which is as it
was.** `Traits.solve` still finds an implementation by a trait's name and a
type's head, and its two theorems stand unchanged.

- **A trait can need another**, `trait Ord: Eq`. It means two things and no
  more: a type that has `Ord` must have `Eq`, on no more conditions; and to
  write `T: Ord` is to write `T: Eq` too. Evidence is not nested: a function
  that needs both is given both.
- **A function with a body in a trait** is given to every implementation that
  does not write it, as that implementation's own function. `!=`, `>`, `<=`,
  `>=` are such in the prelude.
- **Written bounds are all there is.** If a function writes a trait of one of
  its type parameters, its body may need of its declared type parameters only
  what is written, or what those traits need. A function that writes none is
  inferred, as before.
- **A trait can take types**, `trait From<T>`. `impl From<Int> for u8`
  implements the trait at those arguments, and that, `From<Int>`, is the name
  of what it implements from then on: to the solver it is a trait like any
  other. So an implementation's arguments are types without its own type
  parameters. A use asks for the trait at whatever its arguments turn out to
  be; a function generic in them asks its callers.
- **A trait can leave a type to its implementations**, `type Item;`, said by
  each with `type Item = ..;`. Where a function of the trait is used, the type
  is a variable with a question attached: what is `Item` for this type? Once
  the type is known the answer is the implementation's; until then the same
  question has one answer, and a function still generic in the type hands the
  question to its callers with its type. `T::Item` writes it of a type
  parameter.
- **`let x: Type = value`**, so that what a use is wanted at can be said.
- `to(x)` takes a whole number of one type to another, if it fits (`Whole`).
  `From<T>` is in the prelude with no implementations of its own.

Limits. A function of a trait cannot have type parameters of its own: its
evidence is one value, and Core has no value that is a function at every
type. A trait's lifetime, `trait Borrowed<'a>`, is a name its functions' types
may use, and each function is still taken alone. A trait a trait needs is
written without arguments. `T::Item` is of a trait without parameters, and a
trait cannot be written of it (`T::Item: Show`); what is needed of it is
inferred. A function generic in a type whose `Item` it fixes, by adding it to
an `Int` say, is accepted, and the callers it cannot serve are refused where
they call it.

## Wider integers and what was missing of scalars

**Decision: what holds an integer holds 128 bits; `Int` is still kept to 64.**
The five operations `Int` had still have no result outside 64 bits, so `Int`
is as it was and as fast. Three more (`wideAdd`, `wideSub`, `wideMul`) and
division have none outside 128. `u64`, `usize` and `i128` compute with those
and ask that the result fit, as every type of whole numbers does. A `u128`
does not fit 128 bits with a sign, so it is held as the same bits read with
one, and eight primitives read them without (`uwAdd` .. `uwShr`). The Rust VM
holds an `i128`.

Bits: `intAnd`, `intOr`, `intXor`, `intShl`, `intShr`, on the two's complement
of the integers; a shift that loses bits has no result. They are the functions
`bit_and`, `bit_or`, `bit_xor`, `shl`, `shr` of the trait `Bits`, not
operators: `&` is a borrow, `>>` closes two lists of type arguments, and `|`
and `^` alone would be half a set.

Floating point: `f64Sqrt`, by a whole square root of enough bits and one more
for what it leaves out, and `f64Round` (down, up, towards zero, to nearest),
both exact in `Glorious/Float.lean` and agreeing with native arithmetic on
4032 special and random numbers. `sqrt floor ceil trunc round abs` are the
trait `Real`.

A whole number written without a type has the type that is wanted of it, if
that is a type of whole numbers and it fits; else it is an `Int`. This is
settled when the function it is in is done, so a function is never generic
in what a literal is: `fn inc(x) { x + 1 }` is still of `Int`.

`prefix 9 - = negate` says which function an operator stands for in that
place, so `-` before a value is `negate` (trait `Neg`) and between two values
is `-`, with no function taking either one argument or two. `-` straight
before a number is still part of the number, so that the least value of a
type can be written.

`/* .. */`, which may hold others. `b'x'` is a `u8`. `p.0` reads a field of
what a reference `p` points to, as `p.name` did. `impl Trait for (A, B)`:
tuples can have traits, and `()`, pairs, triples and `Result` have `Show`.
Truth shows as `Ok(())`, since `Bool` is a `Result`.

A program told what went wrong is told which: a zero divisor, a value that
does not fit its type, or an overflow.

## A module is a unit, and modules have no cycle

**Decision (the user's): a module is like a crate.** A module is a file, or
`mod name { .. }`. What it declares is its own unless it says `pub`, and that
is the whole of privacy: a module written inside another sees no more of it
than a stranger does, and the outer one sees only what the inner says is
`pub`. A module uses another by naming what it declares, `a::b::name` or
`use a::b::name;`, and which module uses which must have no cycle, the first
module among them. So a module can be understood knowing only the public face
of those it uses, and they come first. Two things that refer to each other are
in one module.

This is not the language specification's section 2, where modules are a tree
in which a module sees the private names of those it is written in, and
modules beside each other may use each other freely. That design needs names
resolved to a fixed point; this one resolves them in one pass.

What is built. `mod name { .. }` and `mod name;`, the second the file
`D/name/name.glorious` where `D` is the directory of the module it is written
in. `pub`, `pub(crate)` (the same: there is one package) and `pub(super)`.
`use` with a path from `crate`, `self`, `super`, a module in scope or a module
of the first module; with `as`, with `{a, b}`, with `*`; `pub use` to name a
thing again as one's own. Paths in expressions, patterns and types. A
constructor of an enum, an operation of an effect and a function of a trait
are names of the module that declares them, as visible as the enum, effect or
trait, and are brought in by name like the rest. The prelude is a module
every module can name without `use`; what a module declares is meant before
it.

A field is private unless it is `pub`. A constructor with a private field can
be written, in an expression or a pattern, only in its module, and such a
field read or borrowed only there. That is what makes a type that has to be
used enforceable: `impl Use<..> for T` is written in the module of `T` and
nowhere else, and nobody outside can take a `T` apart to be rid of it.

An implementation is written in the module of its trait or of its type.

How. `Glorious/Syntax/Modules.lean` runs before the checker: it finds what
each name means, refuses what is private or circular, and writes the program
out as one list of items in which `name` of the module `a::b` is the name
`a::b::name`. The checker, the elaborator and Core see no modules. Only the
privacy of a field read with `.` needs the type, so the checker is told which
module each function is in and which fields are `pub`.

Limits. A module is not compiled alone: every module becomes part of one
Core program, since the checker's counting of uses follows calls into bodies
and Core's theorems are about whole programs. A module itself is not private:
any module can be named, only its items are `pub` or not. A private type can
appear in the type of a `pub` function. A coercion declared in any module
applies in all. Operators and their fixities are the whole program's.

## Fields have names, and a type can have another name

**Decision: a name for a field is the checker's; after it a field is a
number.** `struct Point { x: Int, y: Int }` and an enum's constructor
`Branch { left: Int, right: Int }` name their fields. A value is built by
name, `Point { x: 1, y: 2 }`, in any order, computed in the order written; a
pattern takes fields by name, `Point { x, y: p }`, with `..` for the rest;
`p.x` reads a field, and a field is borrowed and assigned by name as by
number. Building and patterns are settled where they are parsed, from the
declaration. Which field `p.x` is depends on the type of `p`: the checker
finds it and tells the elaborator, which sees only numbers. So the type has
to be known where a field is named.

`type Name<T> = Type;` gives a type another way to be written: it is written
out before the program is checked, and is the same type. `Bool` and
`Option<T>` are such names in the prelude.

Not built: control of layout (`#[repr(..)]` and the like). There is no native
code and no foreign interface for a layout to matter to; a value is a tagged
list of values on both machines.

## Lifetimes can be written

**Decision: a lifetime names what a reference may be holding borrows of.** The
checker already gave every reference type a variable for that, to be inferred.
`'a` names one: `&'a T`, `&'a mut T`, and as a parameter of a function or of a
declared type, `fn first<'a, 'b>(..)`, `struct Holder<'a>(&'a Int)`. A bound
`'b: 'a`, among the parameters or after `where`, says `'b` lasts at least as
long as `'a`. `'_` and an unwritten lifetime are inferred; `'static` is the
lifetime of nothing a program can borrow, since there are no statics.

- **A function is held to what it writes.** While it is checked, each
  lifetime it declares is itself and no other. A reference that lasts for one
  is not one that lasts for another, and what lasts for one may come to depend
  on what lasts for another only where a bound says so. Its callers then rely
  on it: the result of `first<'a, 'b>(x: &'a Int, y: &'b Int) -> &'a Int`
  borrows what `x` borrowed and nothing of `y`.
- **Variance, as Rust has it** (decision, user). Where a value is wanted at
  one type and has another that differs only in lifetimes, it will do if each
  pair of lifetimes is related as its position asks. A reference depends on
  its lifetime the same way round (a longer will do for a shorter), and a
  shared reference on what it points to; a `&mut` reference does not vary in
  what it points to; a callable depends on what it takes the other way round
  and on what it gives the same way; a tuple the same way. A declared type
  depends on each parameter as its fields make it, found from the fields and,
  for types that mention each other, by starting from no dependence and
  adding until nothing changes.
- **A declared type's lifetime is part of its type.** A value of
  `Holder<'a>` holds what `'a` says, so a borrow kept in one is seen wherever
  the value goes, and a `&T` field no longer has to be a type parameter.

What it is not:

- Variance is used where a value is fitted to a type that is wanted: an
  argument, a result, a pattern's type. Since "Lifetimes, finished" below it
  is tried first wherever a reference is involved.
- Elision is inference: an unwritten lifetime of a function is found from its
  body. Only a trait's function, which has none, has a rule.
- Lifetimes are taken out of the program once it is checked. Core's regions
  are found again from the code, and a program that keeps a reference in a
  declared type is, as before, not certified with the region rules.
- All of it is the unproved checker.

## Lifetimes, finished

What "Lifetimes can be written" left out.

- **Related, not made one.** Where a value that holds a reference is given
  for a type that is wanted, the lifetimes are related as their positions ask
  before anything is made equal. So a reference given beside another is no
  longer taken to borrow what the other borrows: after `same(r, &b)`, `b` can
  be assigned while `r` lives. What a callable captured is still made one
  with what it meets, since two blocks are told to be one block by it.
- **A trait's function** has no body its lifetimes could be found from. Its
  unwritten lifetimes are all one: what it gives may borrow whatever anything
  it takes borrows. A lifetime written with a name is its own, with no need
  to declare it. An implementation is held to them as a function is to its
  own. Before this, what a trait's function gave was taken to borrow nothing,
  and a variable could be assigned while a reference into it from such a
  call lived: that was a hole, and is closed.
- **`T: 'a`** says what lasts for `'a` may hold a `T`. A caller's `T` then
  has to last as long: whatever it borrows, `'a` is taken to borrow.
- **`for<'a> fn(&'a T) -> R`**, and `F: for<'a> Fn<(&'a T,), Output = R>`, is
  a callable for every lifetime. Each call of it is at lifetimes of that
  call's own, so a function can give it a reference to its own variable,
  which nothing else allows. What is given where one is wanted must do for
  any lifetime: it is checked at lifetimes that are each itself, and nothing
  in scope may come to hold one of them, so it cannot keep the reference. It
  is written of a parameter's type or of a function's result.
- **An effect can take a lifetime**, `effect Reader<'a> { ask() -> &'a T }`:
  given where the effect is handled, so what an operation gives may borrow
  from there, and each handling has its own.

Limits. Core has no callable type for every region, and no region in an
effect's type. A program that gives a callable a reference to a local of the
function it was given to, or resumes with a reference to a local of the
handler's function, is checked by the unproved checker and certified in Core
without the region rules: Core shows it well typed and well owned, not that
its variables are not used after their blocks. A resumption cannot be given
a `&mut` reference to a variable the handled computation may also reach,
which the checker cannot yet tell apart from two uses. `for<..>` cannot be
written inside another type. There is no `'a` on a trait itself.

## A field can be borrowed

**Decision: a borrow of a field is a variable of its own for as long as it
lasts.** `&x.0` and `&mut x.1.0` borrow a field of what a mutable variable
holds, or of what a reference points to (`&mut p.0`, or `&mut (*p).0` to say
so): a tuple's, or that of a declared type with one constructor. A field is
assigned with `x.0 = v` or `(*p).0 = v`, which is an assignment through such a
borrow; and `(*p).0` reads the one field. The checker
treats it as a borrow of the variable that is in the way only of that field,
of anything inside it, and of the variable as a whole; so two fields can be
borrowed at once, and another field can be read meanwhile. Reading `x.0` copies
only that field.

The machine's references are to whole variables, and stay so. Before
elaboration each such borrow is written out: the field is copied into a
variable declared for the purpose, the borrow is of that variable, and for
`&mut` a cleanup puts what that variable holds back into `x`, rebuilt around
it, when the borrow's extent is left, by whatever path. The extent is the
statements up to the last that mentions anything made from the borrow. Since
nothing else can use the field in that time, nothing can tell this from a
reference into the middle of the variable. The borrows that result are ordinary
ones, and are scopes in Core where any borrow would be.

What it is not:

- Since "Field borrows, finished" below, the reference gone through need not
  have a name, and a part of one of a type's several constructors is borrowed
  by a pattern that binds by reference.
- It costs a variable, a cleanup and a scope where a real reference into the
  value would cost nothing.
- Where the value holds something that can be used only once beside the
  field, the program's Core reads the other fields to rebuild it, and is then
  not accepted with the ownership rules.
- The writing-out is in the unproved elaborator.

## Field borrows, finished

- **Through any reference.** `&mut f(x).0`, `(*f(x)).0 = v`: the field of what
  an expression that gives a reference points to. Where the statement is
  read, the reference is given a name first and the borrow is through that
  name, as before. So the reference is computed before the rest of its
  statement, and that is allowed only where nothing else in the statement
  would have been computed before it; otherwise the program is told to give
  it a `let` of its own. In an assignment the place is found before the
  value is computed.
- **`p.name` where `p` is a reference** reads the field of what it points
  to, as `&mut p.name` already borrowed it.
- **A pattern that binds by reference.** As a parameter of a clause,
  `&mut Pattern` or `&Pattern` matches what a reference points to, and each
  name in the pattern is a reference to the part it names. The callable
  takes the reference, looks at what it points to to choose a clause, and in
  the clause each name is a borrow of its part through the reference, by the
  machinery there was. That is what lets a part of one of several
  constructors be borrowed: inside the clause the value is known to be made
  by that constructor, and nothing else can change it meanwhile. A step to
  such a part says which constructor, and where it is written out the part
  is taken by matching; the case that cannot be is a function that never
  comes back, so that Core's rule that clauses cover their parameters holds.
- **Borrows made one after another** are written out longest-lasting first,
  so that they can be done with in any order.

Since: such a pattern may give fields by name, stand beside a clause that
takes the reference whole (`_` or a name), and be written in a `let` if it
cannot fail (`let &mut (a, b) = p;`). A borrow of a field is kept until one
made while it lasts is done with, where nothing between looks at the
variable itself. `p.0` reads through a reference. And a borrow of a field
through a reference cannot be given back by the function that makes it or
kept in what it is given: it is a variable of that function's.

Since: what is pointed to is no longer copied to choose a clause. Core has
a memory operation, `tag`, that asks a cell which constructor built what it
holds, or the field of it a path of field numbers leads to, and reads nothing
out; it is typed like a read without the condition that the value can be
copied, and type safety, the region rules and the rules for borrows were
proved of it as of the other three. A callable whose clauses bind by
reference asks the cell each constructor its clauses name, and chooses a
clause by the answers. Whether the clauses cover every case is still said by
the patterns as written, which the checker reads beside them. So a `&mut`
pattern works on a value that cannot be copied, a resource or something that
holds a callable. A clause that asks for a number still reads the value.

Since: a borrow of a field cannot leave the block it is made in, as it could
not leave the function: not as what the block gives, nor kept in a variable
outside it. Before, `let r = { &x.0 }();` and a reference bound by a pattern
that was its clause's result were accepted and pointed at a variable that was
gone; the program then stopped at the read. And a callable given where one
for every lifetime is wanted, `for<'a> fn(&'a T) -> &'a T`, can give back
only what borrows from what it is given: not a borrow of a variable, nor
something that lasts for another lifetime of the function, since whoever
calls it chooses how long `'a` lasts.

Limits. A pattern that binds by reference is written around the whole
pattern. A reference bound by a pattern lasts for its
clause, and one to a field for its function. Two borrows of fields that
overlap, with a statement between them that looks at the variable, are
refused, with what to write instead.

## The conditions on a form of computation have names

**Decision: what a rule of the Core typing needs is a record, not a list.**
`CallOk`, `InstallOk`, `LabelOk`, `GuardOk`, `CellOk`, `LendOk` and `WriteOk`
in `Glorious/Typing/Static.lean` each gather the conditions on one form: what
the typing needs, what the region rules add, what the rules for borrows add.
A rule takes the record, then what the ownership rules need, then the typing
of what follows.

The reason is what adding the rules for borrows cost. Each new condition was
one more unnamed premise of a rule, and every proof that takes a rule apart
names its premises by position: about ninety places broke for each. Now a proof
names the conditions it uses, and a new condition is a new field: the two
places that build the record say what it is, and nothing else changes.

It is one record for each form, not one for each set of rules. A record for
each set of rules would make a new set of rules a new premise again. What the
ownership rules need stays beside the record because it is one condition, the
same for every form, and the proofs about it are about nothing else.

## Traits are settled before Core

**Decision: Core knows nothing of traits.** A trait is some functions a type
may have; `impl Trait for Head<T, ...> where T: Other` gives them for every
type made with `Head`. After the source text is checked a program has none:
a bound is met by a value, a tuple of the implementation's functions; a
function that needs a bound of a type it is generic in takes that value before
its own arguments; a call of it passes the value; a call of a trait's function
takes the function out of the value (`Elab.untrait`). What Core is then given is
checked like any other program's, so a wrong choice of value that is ill typed
is caught for each program.

- **Bounds are inferred.** A function that uses a trait's function at a type
  it is generic in needs the trait of that type; nothing is written. An
  implementation says its conditions after `where`, because they decide what
  the type has before any body is read.
- **Which implementation is found by a proved function.** `Traits.solve`
  (`Glorious/Traits.lean`) is what the checker calls. `solve_sound`: what it
  finds is evidence that the bound is met. `coherent`: a bound is met in at
  most one way, if no two implementations are for the same trait and head and
  nothing is assumed twice; the checker runs both checks. So which
  implementation runs does not depend on how it was looked for.
- **A trait's function performs nothing its caller would have to handle**, nor
  does a callable it is given. A trait says nothing of effects yet, and a use
  of its function cannot know which implementation it will get.

What it is not:

- The only type a trait is about is `Self`: no type parameters of a trait, no
  associated types, supertraits, default bodies, functions generic beyond
  `Self`, negative implementations or orphan rule. An implementation is for
  `Int` or a declared type applied to distinct type parameters.
- A trait's function, and a function that needs a bound, is called where it is
  named; to pass one, write a block that calls it. A local callable that uses a
  trait is used at one type.
- A borrow passed to a trait's function is not a scope in Core: the function
  called is taken from a value, not named.
- That the checker asks `Traits.solve` the right question, and that the
  rewriting passes the value it found, is not proved; nor that `solve` finds
  evidence whenever there is some.

## A variable destroys what it holds

**Decision: `Drop` is the compiler's trait, and a value is destroyed where a
variable holding it ends.** `impl Drop for T { fn drop(p) { ... } }` says what
is done to a `T` when it is destroyed; `p` is a `&mut T`. The function is run

- when a `let mut` variable's block is left, by any path, on what it then holds;
- likewise for a `let` whose name nothing afterwards uses: the name owns it;
- before a variable is assigned, on what it held, once the new value is computed.

`Drop` says nothing about how often a value is used; that is the type's `Use`
interval (next section), as the specification has it. A type that has `Drop`
and says no more can be copied, and each copy that comes to rest in a variable
is destroyed. A program does not call `drop`. Later variables end first.

It is built from what was there. Once the source text is checked, a place where
a value is destroyed is a cleanup (`defer`) that calls the implementation's
function with a borrow of the variable, written by the same rewriting that
removes traits; Core is told nothing new.

What it is not:

- **Since: a value is destroyed part by part.** `Drop`'s function for its
  type runs first, if it has one, and then each field that is, or holds, a
  value of a type with `Drop` is destroyed, the last declared first: so a
  pair, a `struct`, an `Option` or an array of such values is taken apart
  where it is destroyed. The checker writes down, once for each type that is
  destroyed somewhere, how; the elaborator makes a function of it. A part
  whose type the function is generic in is still not destroyed.
- **Since: as the specification has it (7.6, L23)**, a type that has to be
  used cannot have `Drop`, and a value of a type with `Drop` is taken apart
  by a pattern only in the module that declares the type, which stands in
  for the specification's unsafe code there.
- **Since: what a clause is given under a name and does not mention is
  destroyed when the clause is done**, a function's parameter or a name
  bound by a pattern, the last named first; and **the value of a statement
  that nothing takes is destroyed there**. Before, `fn eat(d: D) -> Int { 7 }`
  never ran `drop`.
- **Still not destroyed**: a value named on one path and not on another, in
  the paths that do not name it; what a callable holds when the callable is
  let go without being called; and a value whose type is a type parameter
  or is found only where the callable is used, as a parameter of
  `let f = fn(d) { .. }` is. The first two need a callable to say how it is
  destroyed, and the last needs a function to be given how to destroy a
  type it is generic in, as it is given a trait's functions.
- **A value that never comes to rest in a variable is not destroyed.** One
  given to a function that ignores it, one a function generic in its type puts
  in a variable, one put in a value that is forgotten, the unused result of a
  call, and one taken apart by a pattern all end without the function being
  run. Nothing is proved about how often it runs.
- **The word `defer` stays.** A guard written in the language
  (`struct Deferred(fn() -> ())` with `Drop`) works for a callable that touches
  no mutable variable. One that does cannot be kept in a declared type: the
  type would have to say which variable, and declared types have no way to.

## How often a value is used

**Decision (user): build the specification's `Use` intervals, with the lower
bound, before proving anything about dropped resumptions.**

What is built, in the checker for source text:

- `impl Use<[fewest, most]> for T {}` on a declared type, and `[fewest, most]`
  before a resumptive operation, for its resumption. The fewest is 0 or 1, the
  most 1 or `infinity` (a resumption's is always 1). So there are four kinds:
  any number of uses, at most one, exactly one, at least one.
- A type that says nothing has what its fields allow; one that says something
  may only narrow that. A tuple, a declared type and a callable hold what is
  in them: a callable that mentions a value that has to be used has to be
  called.
- **Fewest uses.** Wherever a value is let go without being used, its type
  must allow that: a name not used on some path, `_`, a statement's value, a
  field read that leaves the rest, a block that does not name what it is
  given, a mutable variable when it is assigned or ends, the result of `main`.
  For a type a function is generic in, this is part of the function's
  contract and is checked where it is called, as use more than once already
  was.
- **Paths.** Whether a name is used on every path is counted along the paths
  the program can take, through the functions and callables it goes to, as
  the most uses already were. A path that leaves (an operation that need not
  be resumed, a jump to a label, a call that may not come back) ends with the
  uses it has made. A call comes back if its type says its callee performs
  nothing and can jump to no label.
- **Taking a value apart is the use that ends it** (decision, user). There is
  no built-in that destroys a value: the specification's `destroy(value)` is
  deliberately not provided. A value that has to be used is ended by a
  pattern that takes it apart, so once fields can be private, only the code
  that can see them can end it, and everyone else has to hand the value to a
  function that code provides. A built-in anyone could call would defeat that.
- A program that declares nothing that has to be used is checked exactly as
  before, and pays nothing.

**Decision: an operation that says nothing has a resumption that may be let
go, `[0, 1]`.** The language specification makes `[1, 1]` the default. That
was tried: of the 76 test programs with effects that run, 12 are then refused.
Five of them do drop a resumption. The other seven are sound and are refused
because the rules for a value that has to be used are cautious: a resumption
taken out of a mutable variable again, two callables of which one runs, one
held across an operation that is handled. Until those rules are finer, making
every resumption subject to them would turn away ordinary handlers; and a
resumption an arm lets go is cancelled, so the common case loses nothing. An
operation says `[1, 1]` where it matters.

How this differs from the specification:

- Counting stops at one. `[2, 3]`, `[0, 0]` and the like are refused.
- A type's count is one of the specification's three (7.1, D19): any number,
  at most one, exactly one. A count such as `[2, 3]` is not something left to
  build: the language does not have it. Of a resumption the specification
  also admits exactly `n` uses for `n` above one; that needs a machine that
  can resume a computation twice, which Core's cannot (it takes the
  computation out of the store when it resumes it), and is not built.
- There is no `destroy`, as said above.
  Taking a value apart by a pattern does not run its `drop`. Since a value
  that has to be used cannot be let go, and letting go is the only thing that
  runs `drop`, a `drop` on such a type never runs.
- Fields cannot be made private yet (there are no modules), so today any code
  can take any value apart.
- A value let go where that is allowed is simply forgotten, except a
  resumption its arm does not use (cancelled) and a value at rest in a
  variable whose type has `Drop` (its function runs). The specification
  destroys at every such place.
- Nothing tracks what a mutable variable holds from one statement to the
  next. So a value that has to be used can be kept in one only on two
  conditions that need no tracking: the statement straight after the variable
  is a `defer` that takes what it holds out with `replace`, leaving a value
  written out that holds nothing, so that whatever is there when the block is
  left, by any path, is dealt with; and the variable is never assigned, only
  swapped with `replace`, which gives back what was there to be used. The
  specification's states of a place that differ from path to path are not
  built.
- A value that has to be used cannot wait across an operation, which may not
  be resumed. It can wait across a call of a callable the function was given
  only if that callable's type says it performs nothing (`/ {}`, see "What a
  callable performs can be written"); it is then part of the function's
  contract that what it is given holds no label to jump to.
- References are as before: `&mut` is not a use-once value.
- All of this is the unproved checker. Core is told nothing about it.

What this does for the examples: all three that use resumptions declare their
operations `[1, 1]`. For that, `find` in `generators` cancels the generator it
stops early and says its predicate performs nothing; and `tasks`, which keeps
resumptions in a mutable queue, swaps the queue rather than assigning it and
has a cleanup that runs whatever is left in it.

## What a callable performs can be written

**Decision: a written row is exact; an unwritten one is inferred.** After the
result of a callable, in a type or on a function, `/ {Effect, Other<T>}` says
what it performs: those effects and no others. `/ {}` is a callable that
performs nothing. The result may be left out before it when it is unit:
`fn(Int) -> / {Log}`. An effect's arguments may be left out and are inferred.

This departs from the specification (§2.2), where a signature without an
annotation performs nothing. Here annotations are optional throughout and what
is not written is inferred, so the same holds for effects: writing nothing
after a result asks nothing.

There is no way to write "these effects and possibly more".

## Cleanups are counted, and none is lost

**Decision: what is proved about cleanups is an account, and it is proved of
the machine, not of typed programs.** `Core.cleanup_accounting`: when a program
finishes, the guards it installed are the cleanups that were started plus the
guards left inside resumptions that were never resumed or cancelled. Each step
keeps the account (`Core.step_accounts`): a guard leaves the stack only by
having its cleanup started, and moves between the stack and a resumption only
whole. So the only way a cleanup fails to run in a program that finishes is a
resumption that is dropped, and `Core.cleanup_exact` says that with none
dropped, as many cleanups start as were installed.

It counts cleanups started; one that is started may not finish. It counts
guards and does not tell them apart. It is about the Core machine; the
bytecode machine agrees with it only through `compile_correct`, which relates
results and output, not these counts.

**An arm that does not use its resumption cancels it.** That closes the common
way to drop one. A resumption can still be dropped by passing it to something
that ignores it, by leaving it in a mutable variable, or by leaving the block
that holds it before it is used.

**What would rule the rest out in Core, measured and not proved.** Treating a
resumption as a value that must be used, a Core program never drops one if:
every local that holds one is handed on; no pattern ignores one; none is put
in a mutable variable; and while one is held, nothing is called that performs
an operation or touches an outside variable or label. Of the 180 test programs
certified strictly at the time, 173 obeyed these rules as written; of the five
examples, two. The source checker now has the corresponding rule (previous
section), which follows calls and so accepts more. Nothing connects the two
yet: that a program the source checker accepts with every operation `[1, 1]`
leaves no resumption untaken is not proved.

What stands between this and a proof, in order:

1. Core's regions do not say whether one is a variable or a label. The Core
   rule has to let a resumption wait across a call that touches a variable
   and refuse one that can jump to a label; as measured it refuses both, which
   is the only thing it holds against `backtracking`. Every other program the
   source checker accepted with `[1, 1]`, the state-threading fold included,
   the Core rules accept as written.
2. The rules have to become premises of Core's typing rules and of the typing
   of stack frames (what a call frame holds, what a pending result and an exit
   in progress carry), with the safety proofs repaired around them.
3. Then the invariant itself: every resumption not yet taken is held where it
   will still be handed on, and no frame holding one is ever left or captured.

## Other standing decisions

- **Branching is by pattern callables** (language specification §6), not by
  handler-based matching as in the kernel draft. `if`, `match`, loops and
  operators are written in the language, in `Glorious/Prelude.lean`.
- **Handlers are attached to `handle`**; an arm is a function. An arm whose
  payload patterns can fail is followed by a generated clause that performs the
  operation again outside the handler.
- **Labels and resumptions are ordinary callable values.** A label is found by
  unwinding the stack. The specification asks for direct jumps; that is a known
  gap, not a decision against it.
- **Types, effect rows and captures are inferred.** Annotations are optional. A
  declaration with type parameters is polymorphic; one with bare field names has
  a single inferred type for the whole program.
- **A callee may perform fewer effects than its caller permits.** Calls are
  checked by inclusion, not by making the two rows equal. A function value
  whose effects are unknown is given, at the end of the function, the most that
  every place it is called from permits.
- **Label lifetimes are checked by inferred capture sets** rather than written
  lifetimes. The check is conservative about callables received as parameters.
  A resumption counts as holding everything its computation and handler use.
- **What is proved** is that compiling Core to bytecode preserves behaviour, and
  that a typed Core program goes wrong only by a named fault (see above). The
  parser, checker, elaborator, binary decoder in the Rust VM and the VM itself
  are not proved; they are compared by running every test program three ways.
