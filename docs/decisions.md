# Design decisions on the `lean-kernel` branch

This file records decisions that settle a question the specifications leave
open, or that deliberately depart from them. Read it before changing the
kernel. Where it disagrees with a specification in the repository root, this
file is the current intent for this branch.

## Resumptions are one-shot

**Decision (user, with the kernel rewrite).** A resumption can be used at most
once: resumed once, or cancelled once. There is no multi-shot resumption, and
no `[n, n]` quantity on operation declarations.

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
scope ended. The third is ruled out by the ownership rules below, for programs
that follow them. The front-end has checks for the second and fourth (scoped
`let mut`, capture sets). Those checks are not proved.

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
- Overflow, use of a freed cell and a label applied after its scope ended remain
  possible as far as any proof goes; so does a second use of a resumption, for
  a program compiled without the ownership rules.

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

- There is no `Environment` or `RunsIn` trait and no erased `Available`
  witness. The environment is what the first block captured, and the block that
  was not run is itself the evidence that the environment is unspent. It is a
  real value at run time.
- There are no post-environments (`After`). So this covers alternatives, not a
  body that runs and then hands on what is left: `and`/`or` chains and
  sequential use are as before.
- Bodies stored as independent closures follow normal capture rules, as in the
  specification.

What is and is not proved: the typing rule for `rebind` is part of the proved
type system, and every compiled program's Core is checked against it. Which
block a block is given is found by the unproved surface checker from its
capture variables, and the rewriting is done by the unproved elaborator. They
link two blocks only when exactly one block of the program can be what is
given, and both are built in the same activation. If the linked Core cannot be
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
   checker `checked_borrow_safety`, `checked_scoped_safety`,
   `checked_full_safety` (with ownership too: a program that goes wrong
   overflowed or applied a dead label) and their compiled forms.

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
   compile, 138 get the region rules, and so the theorem.

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
     later: two callables of one type touch the same regions;
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
4. **Labels as regions**, by the same rule: a label is not applied after its
   scope has ended.
5. **Unique references**: a `&mut` is the only way to its cell while it lives.

The specification's lifetimes (language specification section 9) are the
surface form of this; written lifetime parameters, variance and reborrowing
are not part of the plan above.

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
