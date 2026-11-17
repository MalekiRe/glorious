# Design decisions on the `lean-kernel` branch

This file records decisions that settle a question the specifications leave
open, or that deliberately depart from them. Read it before changing the
kernel. Where it disagrees with a specification in the repository root, this
file is the current intent for this branch.

## covey's borrows shown exclusive

`emit` lent the app's systems and its world at once, both fields of what one
reference points to, and Core cannot yet lend two parts of one cell apart: so
no borrow of a covey program was shown to be the only way to what it borrows.
The systems are now copied out of the app first (`L: Use<[0, infinity]>`:
they are functions, which can be), and the copy and the world are each
borrowed alone. The simulation: 37 borrows shown exclusive where there were
none; the query and spawning examples 17 and 19. The one each then said was
not shown was: a borrow lent to a call that is also given a callable was
still listed as not lent, since elaborating the callable moved on the place
the list is kept by. Every borrow of the three is now shown exclusive. A fresh compile of the simulation
is quicker too (1.9 s to 1.2 s): every place passes at once.

## Systems that make entities

**`commands.reserve()` gives a system a new entity, there once the systems
have run;** it gives it components through the columns it has
(`column.give(entity, value)`). The entities a label's systems make are
numbered after those the world had, and the world takes them when the
systems are done, as it ends those the systems asked it to. A system has no
hold on the world itself, so it cannot give a new entity a component of a
column it was not given. `covey/spawning.glorious` is an example.

## Queries in covey, and what they needed of the checker

**covey has `Query<(&mut Position, &Velocity)>`** as a system's parameter: the
world's columns for each `&mut` or `&` written, taken out while the system
runs and put back, with `for_each` giving each entity that has every one of
them. Built from traits over lists of types: `Item` says what a column of a
query stores and what it gives for an entity (a lifetime GAT, `Got<'a>`);
the tuple's is written as head and rest, its columns as nested pairs, so that
each column is a field of its own to borrow; `Fill<S>` takes them out of a
world and puts them back. `Query<Q, St = <Q as Item>::Store>` says what it
holds with a default type parameter. `covey/query.glorious` is an example.

What the checker lacked, found on the way:
- An implementation's function did not know, while its body was checked,
  the result its trait declares, so a borrow given back inside a value
  (`Some(&mut store.dense[i])`) was taken to end with the call it was given to.
- A type a trait leaves to an implementation, said by the implementation in
  terms of its own type parameters (`type Store = (H::Store, ..)`), and a
  trait's function naming another trait's type of `Self` (`Self::Store`),
  were each one variable for every use: the first use decided it for all.
  They are now kept as written (`Syntax.projMark`) and asked anew at each use.
- A condition on a type made from an implementation's parameters,
  `(..R): Fill<S>`, could not meet a need of that trait of that type in the
  implementation's functions; now it does, where nothing else does.
- `()` as a pattern of a reference to `()`.

Core's region rules were not shown where a system with a query was given as
a callable: the callback of `for_each` is a closure whose parameter, a tuple
of borrows, is read a part at a time (`v0.[0]`), so where the closure is made
its parameter is not yet known to be a tuple of references, and certificate
inference, which decides there whether a callable binds the region of a
reference it is given, made it bind none and left its region to nothing.
That decision is now put off where what the callable is given is not yet
known, and made once it is, looking into tuples. The simulation's
`integrate` is a query. An implementation's function may write the lifetimes
its trait's function declares (`fn at<'a>(store: &'a mut ..) -> ..`): each is
the trait's of that name.

## The compiler stays in Lean, and is to be fast and incremental

**Decision (user): there is to be no self-hosted compiler.** The compiler
is the one written in Lean, and the work on it is to make it very fast and
very incremental: a change to a program costs what the change touches, not
the whole program. The specification of an incremental self-hosted
compiler (`GSC-2-…`) is not followed on this branch.

### The build directory, and the plan towards an incremental compiler

**Decision (user): restructure the compiler towards one that is incremental,
with a build directory.** The plan, in steps each shipped on its own with the
test suite passing:

1. A build directory per program, and what a compile makes kept in it (done:
   below).
2. The checker's state split into what is declared (built once from the
   items), what one group of functions needs while it is checked, and what
   a group's check gives, so that a group is a function of what it is given.
3. Uses counted from what a function's summary says of its parameters, not by
   following its body.
4. The checker hands the elaborator each body with its types and meanings on
   it, in place of facts keyed by expression numbers; names are resolved
   once.
5. Core functions known by name, not position, until they are linked; the
   certificate found a group at a time, each group's kept; whether a borrow is
   a scope of its own decided by inference, not by trying.
6. Each of those kept in the build directory by what it was made from, so
   that a change to a function's body redoes that function and, where what
   it shows others has not changed, nothing else.

What is proved stays as it is: every program is certified whole, and the
proved checker checks the whole certificate.

**Step 2, as built: the checker keeps its state after each step, and a
compile in the same process takes it where nothing the step was made from
changed.** The checker goes through a program in steps: its declarations,
then each group of functions that call each other, callees first, then each
function an implementation gives. Each step's state is kept under a key of
everything it was made from, in order: the declarations' of every item with
its functions' bodies left out, each group's of the key before it and the
group's functions whole. A compile that finds its key among those the last
one kept takes that state and does not check the step again; the functions
of later groups are then put back as this program has them, since the state
kept had the earlier program's. That is exact as long as a step looks only
at what its key covers: a group follows calls only into groups before it,
and checks nothing of a later one. Checked: compiling each example and
covey's three programs again from what the first compile kept gives the same
bytecode, and so does compiling each with a number changed in one of two
places at random (26 programs; one edit made a program the checker refuses,
and both compiles refused it alike).

The server and the watch mode keep what was kept, a program at a time; a
single compile has nothing kept. In watch mode, covey: a comment added 290 ms
to 200 ms; a system's body changed 440 ms to 390 ms. The state was not split
into the three parts the plan named: the steps' keys are what make it exact,
not the state's shape.

Tried for step 3 and not kept: what the count of uses found of the calls it
followed, kept for every count made in the same context (one check of a
function's uses), not only within one count. The test suite took the same
time with it (16.4 s, 190 s of processor time), so the memo stays per count.

**The build directory** is `GLORIOUS_TARGET` if set, and otherwise one in the
user's cache (`$XDG_CACHE_HOME/glorious/build/`, or `~/.cache`), named from
the program's path: a program's own folder holds only what was written in it.
It keeps `program`, what the last compile made as the commands use it (the
bytecode, the constructor names, what Core's typing showed, the borrows that
are not scopes of their own, and how each place was made), under the key it
was made from: the compiler's file by size and time, and every text of the
program. `run`, `certify` and `build` read it where the key is the same, and
compile and write it otherwise; `GLORIOUS_FRESH` set: compiled whatever is
kept. A program that went wrong is compiled again to say where. covey run
again unchanged: 0.55 s to 0.016 s; calculator 1.2 s to 0.026 s.

It also keeps `certificate`, the last certificate found, in a binary form of
its own. A later compile asks the proved checker whether it fits the program
now, for each set of rules it would look for one with, before it looks:
where the program's Core is what it was (a change to a comment, to a
function nothing reaches, to how something is written that comes out the
same), no certificate is looked for. covey with a comment added: 0.57 s to
0.35 s. A certificate that does not fit costs one run of the checker, which
is quick. The test suite does not keep certificates: it is there to test
inference too.

### The compile server

**Decision: `glorious serve` keeps one process for compiling, and the commands
ask it where it runs.** What every compile finds alike (the prelude read and
checked, the library's texts read and checked once) is then found once, and
what the server keeps of each program stays in memory. It listens on the
loopback address at a port the system gives, and writes the port and which
compiler it is to `~/.cache/glorious/server`. `run`, `certify` and `build`
send it the program's path and get back what was built (as the build
directory keeps it), and run or report on it as they would themselves; where
no server runs, the file names another compiler, or it cannot be reached, they
build the program themselves. `GLORIOUS_FRESH` or `GLORIOUS_TARGET` set: the
server is not asked. It is started by hand: nothing starts a process that
outlives the command. One compile at a time.

Measured with covey: a comment added 0.35 s to 0.27 s; a component's value
changed 0.34 s to 0.27 s (the kept certificate still fits: the program's types
did not change, so no certificate was looked for, with or without a server);
calculator after the server's first compile of it 1.2 s to 1.1 s.

### What a compile of a file keeps for the next

**Decision: `glorious run|check|build|certify FILE` keeps what its search
found, and the next compile of the same file starts from it.** Where a
borrow can be a scope of its own, which can be is found by asking, for each
place, whether the program can then be shown to follow Core's rules: one
certificate found for each, side by side. That search is most of a compile.
What it found is written to the program's build directory (below), a
line for each place:
the function it is in, how many places of that function come before it, and
how it was made. With it, which of Core's sets of rules and which way of
finding a certificate passed. The next compile asks that all at once, with a
place not seen before asked alone first; a certificate found then is checked
as any is, so what is kept can be out of date or wrong and cost only the
search it was to save. `GLORIOUS_FRESH` set: not read.

Measured (wall clock, one machine, the same file compiled again):

| file | before | kept |
|---|---|---|
| `examples/calculator.glorious` | 3.30 s | 1.43 s |
| `examples/json.glorious` | 0.82 s | 0.39 s |
| `covey/simulation.glorious` | 2.24 s | 0.90 s |
| `examples/orders.glorious` | 1.36 s | 1.17 s |

(`kept` also has the library pruned, below.)

**And the library's modules read for one file are checked without the
functions it cannot reach.** A function of `std` is kept if its name,
without its module, is written in the program or in what is kept of the
library, until nothing more is; implementations, traits and types are all
kept. More is kept than is called (any function of that name in any module),
never less. The library is checked whole by the tests, which is why what a
program does not reach need not be checked again with it. A program naming
four of the library's modules and nothing else: 0.70 s, now 0.40 s.

**The count of a value's uses remembers the calls it followed.** It follows
a call into the function called, as many times as the call is reached, on
every path. A call of a function given the same values (none of them a
callable, whose body would have to be compared) in the same context comes
to what it came to before and costs the same part of the budget; so what is
remembered changes no answer, and running out of budget happens where it
did. calculator 1.43 s to 1.26 s.

**The search for borrows starts from what fails.** Where every place at
once cannot be shown, what failed names a function (inference says which;
the checker, which function it turned away), and the places taken out are
the one that function was made for, or every place of the function it is
in. Again, until it passes; then each place taken out is tried back, side
by side, and those that pass together. Only where nothing is named does
the search ask each place alone, as before. The test suite: 19.6 s to
16.2 s, and two borrows fewer are scopes of their own (1198 of 1350; the
two searches keep different sets where not all can be kept).

**Implementations are found by their trait's name.** The checker kept
them in one array and, for each condition it settled, went through every
implementation comparing trait names (made each time from the written
name). Programs over lists of types have many: each `impl<..T>` is one for each length.
They are now also kept by trait, as they are declared. covey 0.88 s to
0.57 s.

A group of functions whose records of what they touch were settled went
through every record made since the group began, each by its own walk, so a
group went again over the records of every group inferred inside it. One walk
over them now, and openness carried back along the edges.

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

   What this is not. There is no outlives relation. Holding a dangling
   reference is allowed; using it is what is ruled out. References are still
   freely copied: nothing here says a writer is alone (stage 5).

   **A region may be one of several places** (`Rgn.or`): a reference of
   region `or a b` points into `a` or into `b`, and touching it needs both.
   Everything that grants or asks for regions does so place by place
   (`Rgn.parts`, `Rgn.flat`, `Grants`, `Sub`): a borrow takes away every
   place of what was lent, and "the regions a callable touches are different"
   is said of their places. A value of a reference type may be used where a
   reference of a region of more places is expected (`Widen`, in the typing
   of an operand); the checker allows that where the type wanted is known: a
   call's arguments, a result, a constructor's fields, what is stored, and a
   `let` of an operand, and a closure's captures. `Typing/Witness.lean` has
   `either`, a reference to one of two cells chosen by a function with one
   region, accepted with the rules for borrows on.

   Region inference finds them only when it has to: if regions cannot be
   found with every operand at its own type, it tries again with each operand
   used where a type is wanted (an argument, a result, a field, what is
   stored, a capture) given a region of its own that the operand's is one of
   the places of (`Infer.widen`, `lows`); such a region is then each of the
   places used as it, written in the order of the inference's regions, which
   a function's signature and the code using it share, so that the checker,
   which compares types exactly, sees the same `or` both ways. With this
   `longest(&a, &b)` and `if(c) { &mut a } else { &mut b }` get the region
   rules. They do not get borrows as scopes of their own: a reference that
   one of two borrows may be does not outlive either borrow's scope.

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

- **`effect Out<T> where T: Show { .. }`**: what is asked of an effect's
  parameter is asked where one of its operations is performed. The
  operations of an effect may follow each other with `,`, `;` or nothing
  between, as the specification writes them (10.1).
- **`*const T` and `*mut T`** are types of the prelude: an address, with what
  is said to be there. The prelude makes one from an address and gives its
  address back; a `*mut T` is made a `*const T` by a function. A reference
  is not made a pointer: on the machines here a reference is no address.
- **`struct W<T = Int>`**: a declared type written with fewer arguments than
  it has parameters has, for the rest, what its declaration says; a default
  may mention the parameters before it, and comes after every parameter that
  is always written (13.1).

Limits. A function that needs a trait of a type it is generic in is still
called where it is named. A declared type's bounds are not assumed inside a
function that is given one: the function says them again. Only traits
without arguments of their own are asked of a type's parameter.

## A block where no callable is wanted; `return` and `break_at`

From the audit of the specification (5.4, 5.5, 11).

- **A block written as an argument where the type wanted is known and is no
  callable is run there, and is its value**: `f({ let a = 2; a * 3 })` for a
  function of an `Int`. Where a callable is wanted it is one, as before, and
  is run only when called.
- **`return(value, @f)` and `break_at(value, @outer)`** are the prelude's, and
  are functions like any other: each takes a label and goes to it. A program
  may have a `return` of its own.

- **`let name` in a pattern** is a new name there, whatever constant or
  constructor is spelled so (4.3): the resolver writes the name another way
  in the pattern and wherever its clause means it.

Limits. Where the type wanted is a type parameter with nothing asked of it,
the block is still a callable; the specification has it run there.
`continue_at(@outer)` waits for loops that are named, with the library.

## A function written in a block

**Decision: `fn name(..) { .. }` among a block's statements is a function of
the module the block is in, which only that block can name** (20). The
parser gives it a name of its own and writes that name wherever the block,
and the functions written beside it, mean it; so it can call itself and
them, has type parameters like any function, and two blocks may each have
one of the same name. It uses nothing of the block's: it is not a callable
that holds what is around it, and `let f = fn(..) { .. }` is the way to
write one of those.

Limits. Only functions are written in a block: a type, a constant or an
`impl` there is not read. A message names such a function with the number
the parser gave it.

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

Since:

- a clause that tests for something the clauses before it have already taken
  every case of (6.2). A clause that takes whatever is left is not said to
  be unreached, since the compiler writes such clauses itself;
- a function with every parameter's type written that gives back a reference
  with no lifetime written and is given more than one reference: which the
  result lasts as long as has to be said (9.2). With a parameter's type
  left out it is found, as before.

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

Limits. (A function of a trait could not have type parameters of its own at
first: its evidence is one value, and Core has no value that is a function at
every type. It can now: a function is copied for each type it is used at, so
the implementation is known at each call, also through a bound; `fn
apply_to<B>(s: &Self, f: fn(Int) -> B) -> B` is used at two types in one
function generic in `M: Mapper`.) A trait's lifetime, `trait Borrowed<'a>`, is a name its functions' types
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

A type that has `Drop` is used at most once, as the specification's
`trait Drop: Use<[0, 1]>` has it (7.6). At first it was not: such a type
could be copied, and each copy that came to rest in a variable was destroyed,
so `let mut f = File(7); let g = f;` closed the file twice. Reading such a
value out of a variable, using it twice or giving it away twice is now
refused; the module that declares the type may still read one through a
reference, as its `drop` does to see what to do. A program does not call
`drop`. Later variables end first.

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
- **Since: every type has a function that destroys its values, and a
  function is given how to destroy the types it is generic in.** Being
  destroyed is a trait of the compiler's own that every type has: by doing
  nothing, by its own `Drop` and then its parts', or part by part, on
  condition that each of its type parameters can be destroyed. Where a value
  is let go, the trait's function for its type is called; where its type is
  one the function is generic in, the function needs the trait of it, and is
  given the implementation by whoever calls it, exactly as for a trait the
  program writes. So `fn sink<T>(t: T) {}` given a value with `Drop` runs
  it, and so does the prelude where it lets go of what it is given. The
  functions are found by the proved solver and written by the elaborator
  from what the checker says of each type. An implementation's functions
  are given how each of its type parameters is destroyed.
- **What a `_` takes is destroyed** when its clause is done: it is given a
  name for that, known by its place among the `_` of the clause.
- **None of this is there in a program where no type has `Drop`**: the
  prelude and the library are checked once for each kind of program.
- **What a callable holds is not destroyed with it**, since a callable does
  not say how it is destroyed. That was a silent loss; now the two ways to
  it are refused (see "Values with `Drop` and callables" below).
- **Still not destroyed**: a value whose type is found only where a callable
  written in a `let` is used; and what a coercion lets go of a type it is
  generic in.
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
- A value that has to be used cannot wait across an operation that may not
  be resumed. It can across one declared `[1, 1]` (see "Exactly once is
  resumed" below). It can wait across a call of a callable the function was given
  only if that callable's type says it performs nothing (`/ {}`, see "What a
  callable performs can be written"); it is then part of the function's
  contract that what it is given holds no label to jump to.
- References are as before: `&mut` is not a use-once value.
- All of this is the unproved checker. Core is told nothing about it.

What this does for the examples: `backtracking` and `tasks` declare their
operations `[1, 1]`; `tasks`, which keeps resumptions in a mutable queue,
swaps the queue rather than assigning it and has a cleanup that runs
whatever is left in it. `generators` stops a generator early, so its `yield`
says nothing (see "Exactly once is resumed" below).

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

## A reference can be to a part of a value

A reference in Core was to a whole cell. So `&mut p.x`, where `p` is a
reference, had to be written out as a variable of the function's that held
the field while the borrow lasted, and such a borrow could not be given back;
and nothing could refer to an element of an array at all, which the standard
library's slices and collections need.

A reference value now carries the fields to go through from what its cell
holds to the part it is to. Reading, writing and swapping go through that
path. `focus` makes, from a reference, the reference one field further in:
the same cell and the same borrow, so the rules for borrows in Core see it as
the reference it came from. Two rules type it. A field by number, of a tuple
or of a type with one shape, is always there. A place of an array, which may
be a number the program computes, is there or not when the reference is used.

- **Two more faults.** Reading or writing through a reference whose part is
  not there stops the machine: `Fault.absent`. The soundness theorem for the
  ownership and region rules now names two ways to go wrong, an intrinsic
  with no result and a part that is not there (`Absent`); both are a place of
  an array that is not there, or arithmetic. The checker on the surface keeps
  the array from changing while a reference into it is held, so a checked
  surface program does not reach the second by letting the array shrink; this
  is not proved. The prelude's `element` and `element_mut` ask whether the
  place is there before making the reference.
- **Borrows are of the cell.** In Core a borrow of a part is a borrow of the
  whole cell. That two borrows of fields apart may be held together, and that
  a `&mut` to a part excludes the reference it came from while it lasts, is
  the surface checker's doing, as it was. Nothing unsound follows if it were
  wrong: a write through a path keeps the cell's type.
- **A path goes into a variant** since "References into one of several
  constructors" below; it did not at first.
- **A field of a local variable** is still borrowed as a variable of its own
  while the borrow lasts, which is what lets two fields of one variable be
  lent at once in Core, where a borrow is of a cell.
- **A place below zero** asked of `focus` stops the machine there, a fault of
  the same kind (`Fault.below`, counted under `Absent`). A place past the end
  is found only when the reference is used.

## References into one of several constructors

A step of a reference's path now says, where the type has several
constructors, which one the value has to have been built by (`PathStep`:
that constructor or none, and the field's number). `focus` given a
constructor makes such a step, and one more rule types it (`HasTm.focusIn`,
`PartOk.variant`): the field's type is that constructor's. Reading or writing
through the reference finds the part only while the value is built by that
constructor, and is `Fault.absent` otherwise, the fault there already was for
a place past the end of an array. The soundness theorems are as they were.

On the surface a pattern that binds by reference, gone through a reference,
gives references that can be given back whatever the type:

```
fn inner(o: &mut Option<Int>) -> Option<&mut Int> {
    match(o) { &mut Some(x) => Some(x), &mut None => None }
}
```

and the same through a recursive type, to a value inside a tree. The refusal
"a borrow of a field of one of several constructors lasts only inside the
function that makes it" is gone.

- **Nothing asks, when the reference is made, whether the value is built by
  the constructor.** A pattern has asked just before. That the value is not
  rebuilt by another while the reference is held is the surface checker's
  doing, as for an array that might shrink; if it were wrong the machine
  would stop, not read something of the wrong type.
- **Through a variable that is not a reference** a field of one of several
  constructors is still taken out into a variable while the borrow lasts.
- **A declared lifetime no longer gets in the way.** With
  `fn f<'a>(p: &'a mut P) -> &'a mut Int`, what the body gave back at `'a`
  was counted as held by every value of lifetime `'a`, `p` among them, so a
  pattern through `p` or a second branch using `p` was refused with "`p` is
  used while `p`, which borrows from it, is still in use". What a body ends
  with, fitted to a declared lifetime, is now marked as given and not as
  held. A value put into a variable or a place of that lifetime is still
  held by all of them, which refuses more than it need: `let r: &'a mut Int
  = &mut p.x` cannot be followed by any use of `p`.
- In the library this gives `as_ref`, `as_mut` and `take` for options,
  `as_ref` and `as_mut` for results, `HashMap::get_mut`, and `get_ref` and
  `get_mut` for the ordered map, which goes down its tree by reference.
- The Rust VM's path steps carry the constructor too; compiled code reads
  only references to whole cells in place and leaves the rest to the runtime,
  so the ABI's layout of values is as it was.

## Rows of effects have names

A function type written without what it performs was already open: what it
performs is inferred, and a function given one performs that too. A row can
now be named, so that a signature can say so: `fn apply<A, B, e: EffectRow>(f:
fn(A) -> B / e, x: A) -> B / e`, and `{Log | e}` for a row that holds `Log`
and whatever `e` stands for. A row parameter is not a type parameter: it is
not counted among the type arguments a call may write.

- **The row is the caller's.** Once the program is checked, a row parameter
  must still be a row nobody knows: a function that performs an effect under
  a row it said was `e`, or that uses two row parameters as one, is refused.
- **One row parameter per row.** `{| e1, e2}`, the union of two, is not
  supported: a row has one unknown rest in the checker.
- **Associated rows** of traits are not supported.

## A type has a value

A type every constructor of which holds a value of the type itself, with
nothing between, is refused: no value of it can be built. A type that holds
itself in some constructors is accepted, as before; values are trees on every
machine here, so nothing needs to be said about where the nested value lives.
The native ABI will have to say it. Recursion through a generic type's
argument (`struct S { w: Wrap<S> }`) is not seen.

## Two backends, one contract

The Rust VM compiles bytecode to x86-64 in memory and to LLVM IR, under the
contract in `docs/abi.md`. The choice that shapes it: an activation's locals
and the control stack stay the runtime's, whichever engine runs the function.
A compiled body runs the instructions between calls and asks the runtime for
every call, return and effect. So the three engines are interchangeable per
function with nothing converted between them, and resumptions, label jumps
and cleanups work through any mixture, which is what was asked of the ABI.

- **What it costs.** Calls are no faster than the interpreter's, and this
  language makes control flow out of calls: `if` is a function given two
  blocks. Measured on a recursive Fibonacci, each call of `fib` is 34
  instructions as compiled, of which about eight are calls and six make a
  closure, and the compiled program takes as long as the interpreted one.
  The x86-64 backend does what it was asked for, which is to compile at
  once: a program is machine code microseconds after it is read.
- **The bytecode is rewritten when it is loaded** (`vm/src/opt.rs`), for
  every engine: known calls without closures, small functions written in
  place with what follows them, tests of what was just built decided. With
  it `fib` is a comparison, two subtractions, an addition and two calls, and
  the same program runs 6 times faster compiled to x86-64 (1.04 s to 0.17 s
  for `fib(27)`) and twice as fast interpreted.
- **Loops are functions made for their blocks.** `while` is `loop`, which
  installs a handler for `break` and `continue` around each turn and calls
  itself. Where a function is called with closures that can be read off the
  code, it is made again for those closures; in the `loop` made for a
  `while`'s condition and body, the handler is installed in place with both
  written after it, and the call of itself at the end becomes a jump back
  that leaves the handler installed. Three million turns of a `while` that
  adds to two variables take 0.46 s compiled to x86-64, against 4.5 s
  interpreted as written; appending to an array and summing it, 0.14 s
  against 0.86 s. Interpreted, the rewritten code is not much faster than it
  was: what is written in place leaves instructions that only keep the
  locals' numbers, which compiled code skips and the interpreter runs.
- The rewriting is not proved; every test program is run with and without
  it. The VM compiles to x86-64 unless told otherwise.
- **What would make it fast**, in the order of what each is worth: (1) in
  the compiler, calling a function that is known without making a closure
  of it, and writing library control flow (`if`, `match`, the loops) in
  place where it is called with blocks written out; (2) in the ABI, a
  convention for calls between compiled functions that keeps arguments in
  registers and frames on the machine stack, with the runtime's stack kept
  for what can be captured; (3) the flat layouts of specification 17.2. None
  of these is built.
- **Bytecode is the input** of both backends, not Core: the bytecode is what
  is proved to behave as the Core program does, and the VM already reads
  it. A backend sees no types, so it checks at run time that an integer is
  one before working on it in place.

## What C is given

An `extern "C"` function takes and gives whole numbers, `f32` and `f64`,
and addresses written `*const T` and `*mut T`; C's own names for its types
(`c_int`, `c_long`, `c_double`, ..) are the types they are on x86-64 Linux,
in `extern` blocks without being imported and elsewhere from `std::c`. Whole
numbers and addresses go where C keeps those and floats where it keeps
floats, at most six of the first and eight of the second. A function not in
the process is looked for in C's library of mathematics.

`c_callback(f, n)` gives an address C can call with `n` whole numbers, at
most five, which runs the callable `f` and gives back the whole number it
gives. The callable performs nothing: an effect cannot pass C, nor can a jump
to a label, and the checker holds the callable to that. The callable and the
code at the address are never let go of.

- **Records are copied in and out.** A value built by a constructor is not
  laid out in memory as C would lay it out. `#[repr(C)]` on a struct whose
  fields are whole numbers, floats and addresses gives it
  `Type::c_size()`, `Type::c_write(value, at)` and `Type::c_read(at)`, which
  put it at an address and read it back as C lays such a struct out on
  x86-64 Linux: each field at the next multiple of its size, the whole a
  multiple of the largest. A struct inside a struct, an array, or a type
  parameter is not laid out, and the attribute then does nothing.
- **Nothing is exported.** `#[export_name]` is read and does nothing: the
  program is not a library C can link against, only one that C can call back
  into while it is being called.
- **Not on the proved machines.** A foreign call has no meaning there; these
  programs run on the Rust VM and the backends alone, and are not certified.

## The host is effects

`std::host` declares what a program asks of the machine it runs on as effects,
as the library specification does (27): `Console`, `FileRead`, `FileWrite`,
`Diagnostic`, `ProcessEnvironment`, `ProcessArgs`, and `Clock` and `Entropy`
besides. `run_host` answers them all with the operating system, through C.
A program that asks for a file therefore says so in its type, and can be run
with another handler that answers from memory.

- **The types are this implementation's**, not the specification's: a path
  and a text are `Str`, bytes are `[u8]`, an error is the operating system's
  number for it. `Path`, `OsString`, `Slice` and a structured `IoError` are
  not built.
- **`args()` gives what the process was started with**, the interpreter's
  own arguments included when the program is run by it.
- **It is the operating system's `open`, `read`, `write`**: there is no
  buffering beyond a line's, no streams, and a byte goes to or from C at a
  time, which is slow for large files.
- **Not on the proved machines**, like everything that calls C.

## Collections in the specification's shape

`std::collections` has `VecDeque` and `BinaryHeap` written as the library
specification writes its collections (16): functions of the type, `&mut Self`
to change one where it is, `Option<&'a T>` to look at an element. They are
written in the language, with nothing new in the compiler, which is what the
references to parts of values were for.

- **Sizes are `Int`**, not `usize`, as everywhere else in this library.
- **A `BinaryHeap`'s elements are copied** when they are compared and moved,
  so they are of a type used any number of times.
- **`Vec<T>` and `String`** are there in the same shape (`std::vec::Vec`,
  `std::text::String`, and under `alloc::vec` and `alloc::string`): `new`,
  `len`, `get`, `get_mut`, `first`, `last`, `push`, `pop`, `insert`,
  `remove`, `append`, `reverse`, `truncate`, `clear` for the one;
  `from_str`, `to_str`, `push`, `push_str`, `len`, `clear` for the other,
  which holds its text as UTF-8 bytes. An item that cannot be put where it
  was asked to go is given back as it is, `Err(item)`, not wrapped in the
  specification's `Rejected`.
- **`HashMap<K, V>`** (`std::hash`) has `set`, `unset`, `count`, `has` and
  `get_ref`, which gives `Option<&V>` into the map, beside the functions over
  values it had. Keys are copied when they are compared.
- **Not built**: capacities and `reserve`, slices and iterators in this
  shape, `rotate`, `split_off`, `drain`, `retain` and the functions that take
  a callable, `as_slices`, `front_mut`, `replace_top`, and maps and sets,
  which are still the functions over values they were.

## The library's names

The library specification names its modules under `core`, `alloc` and `std`
(1.2). Those names exist: `core::{option, result, cmp, num, char, iter, hash}`,
`alloc::{vec, string, collections}` with `collections::{map, set}`, and
`std::{io, fs, env, time, random, ffi}`. Each is the declarations of a module
this library already had, brought in again under the name, so a declaration
has one identity whichever name it is reached by. `core` and `alloc` come
with a program whenever the library does.

- **The names are there; what the specification puts under them mostly is
  not.** `core::num` is the functions on `Int` this library has, not the
  scalar families; `alloc::string` is the functions on `Str`, not `String`.
- **No profiles.** There is one library: `core` does not stand without
  `alloc`, nor `alloc` without `std`.

`glorious native FILE OUT` builds a program of its own with the LLVM backend:
it writes the bytecode, asks the VM for the LLVM module, and has `clang`
compile and link it with the runtime.

## An implementation for some of a type

`impl T for Option<A>` and `impl T for Bool` name a type by another of its
names: `Option<A>` is `Result<A, ()>` and `Bool` is `Result<(), ()>`. Such an
implementation is one for the type the name stands for with some of its
arguments fixed, and so is `impl T for Pair<Int, B>`, where an argument is
written as a type. The proved solver still finds an implementation by the
type's head; what it is asked of is then held to the fixed arguments, and
`T` of a `Result<Int, Int>` is refused where `T` is implemented for
`Option<A>`.

- **A type has one implementation of a trait**, as before: not one for
  `Option<A>` and another for `Result<A, E>`, nor one for `Pair<Int, B>` and
  another for `Pair<Str, B>`. The solver is proved for implementations told
  apart by head, and this keeps it so.
- **A fixed argument is a type with no parameters of the implementation in
  it**, written as one name.

## An array is taken apart by its length

`[a, b, c]` in a pattern is an array of exactly three elements. An array of
`n` elements is built by a constructor of its own in Core, so this is a
constructor pattern like any other, and the certificate covers it. There is
an array of every length, so clauses of such patterns need one that takes
whatever is left, and a `let` cannot have one.

- **No `..`**: `[first, ..]`, and `(a, ..)` for a tuple, are not built. The
  first would be a test that the array is at least so long, which Core's
  patterns do not have; the second needs the tuple's length, which the
  elaborator is not told.
- **Not by reference**: a pattern that binds by reference does not go into
  an array.
- **Fixed arrays `[T; N]` and const generics** are still not built.

## A type can be said not to have a trait

`impl !Trait for Type {}` says the type does not have the trait. An
implementation of the trait for the type is then refused, wherever it is
written. That is all it does: nothing is concluded from it elsewhere, and a
trait asked of the type is refused as it would have been, for want of an
implementation.

## Slices and iteration

`core::slice::Slice<'a, T>` (`std::slice`) is a stretch of an array, borrowed:
`of`, `len`, `get`, `first`, `last`, `sub`, `split_at`, `iter`, and
`Vec::as_slice`. `core::iter::Iterator` (`std::iterator`) is the
specification's trait: `type Item` and `next(&mut Self) -> Option<Item>`, with
`Range`, `IntoIter` for an array's elements given away, and `SliceIter` for a
slice's by reference. What is done with the values is functions over anything
iterated: `fold`, `for_each`, `count`, `collect`, `map_collect`, `find_map`,
`nth`. The lazy streams this library had are still `std::iter`.

- **Adapter types** came later: see "Conditions that say what a type is"
  below.
- `find` takes a test that borrows the value, `find_map` a function that is
  given it. (`find` was left out at first: see "Regions through two calls"
  below.)
- A fault was fixed on the way: `Self::Item` in a trait's function was one
  type for every implementation in a program, so two iterated types with
  different items could not be used together.

## Formatting

`alloc::fmt` (`std::fmt`) has the specification's `Formatter` (21): `new`,
`write_str`, `write_char`, `newline`, `indent`, `dedent`, `quoted`, `display`,
`finish`, with `Display` for a type to say how it is written and `format` for
the text of a value. Indentation is four spaces, written before the first
thing on a line.

- **A trait's function that gives no reference** no longer ties together the
  unwritten lifetimes of what it takes. `fn fmt(&Self, &mut Formatter)` had
  one lifetime for both, so its body could not use the value while it wrote
  to the sink.
- A program that calls `format` was at first certified as well owned and no
  further; see "Regions through two calls" below.
- **Not built**: `Debug`, format options and output limits, the diagnostics
  types.

## Borrowing what has no name, and what is not a variable

`&x` needed `x` to be `let mut`. Now a value bound with `let`, by a pattern or
as a parameter, that is borrowed with `&` and never assigned to, borrowed
with `&mut` or bound again, is kept as a variable is, where a reference can
point; nothing can assign to it, since nothing does. And `&f(x)` or
`&mut [1, 2]`, a borrow of a value with no name, names the value where the
statement it is in starts and borrows that.

- **The value lasts to the end of the block** its statement is in, not to
  the end of the statement.
- **It is made before the rest of its statement**: in `g(a(), &b())`, `b()`
  runs before `a()`.

## Regions through two calls

The search for a program's regions failed for a generic function that lends
a variable of its own to a function of a trait: `let mut out = ..;
fmt(value, &mut out)`. What a callable touches is found by going through
what it calls, and a callable called at a region its caller chose is renamed
to that region on the way. Through two such calls, an implementation's
function called by the function the dictionary holds, the region was renamed
once: the inner one's region became the outer one's bound region and stayed
that, so the variable's scope seemed to touch a region that was no one's.
Each call on the way now renames in turn (`renamed` in `Infer.lean`).

This is in the search for a certificate, which proves nothing itself; the
checker that accepts what it finds is unchanged. Programs that call `format`,
`find`, or any generic function of that shape now get all three
certificates.

- Still not found: a callable given two references at once, one to the
  caller's variable and one the caller was itself given
  (`for<'a, 'b> fn(&'a T, &'b mut Int)` called with a parameter and a
  variable). The program is accepted and certified as well owned.

## Conditions that say what a type is

An implementation's conditions were a trait of a type parameter and nothing
more. One may now say what the trait leaves to that parameter's
implementation: `where I: Iterator<Item = A>`. In the implementation's
functions `I`'s `Item` is `A`; where the implementation is used, the type
given for `A` has to be the `Item` of the type given for `I`, or the use is
refused. Which implementation a bound is met by is found as before, by the
trait and the head of the type, so what is proved of that is untouched.

That is enough for iterators made from iterators, each a type of its own
that does nothing until asked: `Map`, `Filter`, `Take`, `Skip`, `Enumerate`,
`Zip`, `Chain` in `core::iter`, made by `map`, `filter`, `take`, `skip`,
`enumerate`, `zip`, `chain`.

- **Their types name what the inner iterator gives.** The specification has
  `Map<I, F>` with `F` any callable; here it is `Map<I, A, B>` holding a
  `fn(A) -> B`, because a condition cannot yet say that a parameter is a
  callable. The functions that make them work out `A`, so it is written
  only where the type is.
- **`Vec::iter`** gives a vector's elements by reference, one after another.

## The specification's required cases

The language specification lists forty-eight behaviours to be shown (21).
Each was tried with small programs, kept among the cases under "Conformance
L..". Where one is not met, this is how.

| | |
|---|---|
| Met as tried | L01 to L17, L19 to L22, L25, L26, L28 to L31, L33, L35 to L39, L42, L45, L48 |
| Met in part | L23, L32, L43, L44, L47 |
| Not offered | L18, L24, L34, L40 |
| Not tried | L27, L41, L46 |

- **L23, field moves from a type with `Drop`.** Refused outside the module
  that declares the type, for patterns and, since this pass, for a field
  taken out by name or number, which had been let through and skipped the
  type's `drop`. The declaring module may still take one apart; the
  specification asks for `unsafe` there.
- **L32.** An arm without a resumption resumes with what it gives. Exact
  finite counts above one are not offered, so there is nothing to refuse.
- **L33.** Not met when first tried, and now met: see "Exactly once is
  resumed" below.
- **L35.** Met, and a fault found on the way: `defer { .. }` made the block
  a callable and let it go, running nothing. It now runs the block.
- **L43, L44.** One runtime holds every value whichever engine runs a
  function, and artifacts carry the ABI's generation. Values are not laid
  out flat, and `usize` is 64 bits everywhere.
- **L47.** A fault stops the machine, and a failure a program handles is a
  value or an effect; there is no separate abort.
- **L18, L24, L34, L40.** There are no availability witnesses, no holes left
  in what a reference points to (`replace` puts something back at once), no
  resumption used more than once, and no raw memory beyond addresses given
  to and by C.

## Values with `Drop` and callables

Nothing destroys what a callable holds: `let f = { eat(n) };` with `f` never
called took `n` with it, and `if(c) { eat(n) } else { 7 }` did the same on
the path that does not run the first block, since the paths are callables.
A type's `drop` then never ran, and nothing said so.

Both are now refused, by the count of uses that was there for values that
have to be used:

- **A callable that holds a value with a `drop` to run has to be called**,
  or given to something that calls it. It is treated as a value that has to
  be used: letting it go, or giving it to a function that may not call it,
  is refused. The blocks given to `if` and the like share what they hold
  with the code around them and are not such callables.
- **A value with a `drop` to run is used on every path or on none.** Used on
  none, it stays in its variable and is destroyed when the block ends. Used
  on some, the others have to use it too: `else { discard(n); 7 }`.
  `core::value::discard` takes a value and lets it go, which runs its
  `drop`. Here "used" is "given to something": what takes a value has it.

**Borrowed, then given away.** A value that is borrowed is kept in a
variable, and what a variable holds was copied when it was read: so
`let a = peek(&n); eat(n)` could not be written for a value that is used
once, which is how every resource is used. Now a variable that is not bound
again gives its value away where the value is used: the use is counted as a
name's is, a borrow still held then is refused ("`n` is given away while `r`
holds a reference to it"), and the variable no longer destroys what it held.
(At first this was only for a variable never assigned or borrowed for
writing; see "Written, then given away" below.) A callable written in the block
may be what uses the value, a `defer` among them: `defer { release(m); }`
after `let m = ..;` is how a resource is given back however the block is
left, with `&m` used in between. Such a callable holds the value, so it is
itself used once and, for a value that has to be used or has a `drop`, has
to be called. What this needs is that no borrow of the name follows a use
of the value, in the order the block is written, with a `defer` counted
last; otherwise reading the variable is the copy it was, and refused for a
value that is used once.

**Used on some paths.** Such a variable may give its value away on some
paths and not on others: `let mut n = ..; if(c) { eat(n) } else { 7 }`. Its
cleanup asks whether it did. A flag beside the variable is set wherever the
value is used, and when the block is left the value is destroyed if the
flag is not set. The flag and the cleanup are there only where the count of
uses finds a path that does not use the value. This is the specification's place that may or may not hold
its value, with a cleanup that depends on a flag (7.4). A value bound with
`let` and never borrowed is not kept in a variable; for it both paths still
have to say, and the message says to write `let mut`. The flag is a
variable of the same block, and a callable that sets it must not outlive
the block: that is checked for callables that use a variable, and not for
ones that hold a name's value, which may be given back.

A callable that holds such a variable's value need not be called for the
`drop`'s sake: what it did not use the variable destroys. It is still used
at most once, and still has to be called where the value has to be used.

A value that holds a resumption is still not read out of a variable: the
machine's read is a copy, and Core does not copy a resumption.

`let _ = value;` now lets the value go as `value;` does, running its `drop`;
it kept it unnamed and never destroyed it.

This is in place of callables that say how they are destroyed, which the
specification has and which needs the machine to know, for each callable,
what to run. It refuses programs the specification accepts and loses
nothing silently.

- Not covered: a value with `Drop` given to a function generic in its type
  that puts it in a callable and lets that go. The function is checked with
  the type unknown.
- A program with no `Drop` is checked as before.

## Written, then given away

`let mut f = open(); write(&mut f, ..); close(f)` is how a resource is
used, and was refused: a variable that was assigned or borrowed for writing
did not give its value away, so `close(f)` was a copy. So was a `Vec` of
such values filled and then consumed. Now any variable gives its value
away, on the same condition as before, with writing counted as borrowing
is: in the order the block is written, nothing borrows the variable, writes
it, or reads a part of it after its value is used.

- **A part read where it is, `f.written`, is a look and not a use**: it
  does not give the value away, and may come before the use that does. It
  was counted as a use of the whole.
- **A callable written before the value is used may borrow the variable**,
  which is what a loop's body does: `while(.., { write(&mut f, ..) });
  close(f)`. What was refused for every such callable is now refused where
  the value is given away, for a callable that could still run after:
  "`f` is given away while `g`, which uses it, can still be called". This
  is seen from types, as held borrows are: whatever is still to be used,
  and whatever the expression has computed, must not hold a callable that
  uses the variable.
- A callable that both uses the value and borrows the variable, or one that
  borrows it written after the use, is as before: the read is then a copy.
- An arm of a handler that borrows the variable still counts as coming
  after, wherever it is written: when it runs is the handled code's to say.

Three more things this needed, found by trying to break it:

- **A callable that takes the value is where the value goes**, whenever it
  runs. So where one is written, nothing still to be used may be a callable
  that looks at the variable: `let w = { write(&mut f, 1) }; let c = {
  close(f) }; c(); w()` is refused at `c`. This refuses `w(); c()` after
  both are written, too: write `c` after the last use of `w`.
- **Callables that each take the value are not in each other's way**: both
  branches of an `if` may. Which of them runs is counted, as it is for a
  name's value.
- **A block that was not run never took the variable's value.** A block
  given to `if` beside one that ran was said to hold the value and let it
  go, so `if(c) { close(f) } else { close(f) }` was refused for a value
  that has to be used once anything had borrowed `f`. The value is the
  variable's until a block that takes it runs; whether every path uses it
  is seen where the variable's uses are counted.

## Collections of what has to be used

The library's `Vec`, `VecDeque`, `IntoIter` and the tables of `std::index`
took their array out with `replace`, changed it, and assigned it back; the
assignment let go of the empty array left meanwhile, which for a type that
has to be used is letting go of that type. So a `Vec<Ticket>` could not be
pushed to. Four things were in the way, each fixed:

- **`overwrite(reference, value)`**, an intrinsic: the value put where the
  reference points, what was there neither given back nor destroyed. It is
  `unsafe`, as that is a value lost unless nothing was there. The prelude
  has over it `push_at` and `pop_at`, which are safe (they take the array
  out, leave an empty one, and write over that), and `restore_at`, which
  is unsafe and is what the library uses to put an array back.
- **An array written out, `[a, b]`, of values that have to be used** was
  refused: each element is pushed by a call, and an element computed
  before a call is let go if the call does not return. The calls a literal
  stands for had no identity for "this one always returns" to be found
  for; now they have.
- **What is needed of a reference to a `T` is not needed of a `T`.** A
  function with `T: Use<[0, 1]>` that used a `&mut [T]` twice was told `T`
  is used more than once. A type parameter is now asked only of what holds
  values of it: not through a reference, nor as what a callable takes.
- Taking one field of a value, `v.items`, lets go of the rest; the
  library's `into_vec` functions take the value apart by pattern instead.

## `impl` with conditions for all its functions

`impl<T> Interner<T> where T: Eq + Hash { .. }` was a syntax error: only an
implementation of a trait took `where`. On a type's own functions the
conditions are now asked of each function, as though written on each.

## `std::bytes`, `std::index`, `std::error`

The specification's binary readers and buffers (23) and its tables for
building compilers (24): `ByteReader`, `ByteBuf`, hexadecimal; `Id<Tag>`,
`IndexVec`, `Arena`, `GenArena`, `Interner`, `StringInterner`, `BitSet`,
`SparseSet`, `WorkQueue`. All are ordinary source over arrays; `Tag` is a
type parameter no field uses, which is enough to keep an `Id<Function>`
from being an `Id<Block>`.

- **Places and lengths are `Int`**, as everywhere in this library; an `Id`
  holds a `u32` as specified and has `index` and `at` beside the
  specification's conversions.
- **Arrays where the specification has `Vec`**: `finish`, `into_vec`,
  `hex_decode` give `[T]`, as the stream functions do.
- **`read_str` gives a `Str` of its own**, not one borrowed from the bytes:
  a text here is not a view of bytes.
- **A mark knows how long what it was taken from was**, and no more: one
  used on another reader of the same length is not refused. A `GenId` is
  checked in full, by its generation.
- **`Interner::find` takes its key by value**, as `Hash` and `Eq` do.
- **`BitSet` keeps a flag for each place**, not bits packed in words.
- Reserving room never fails here; the functions that say `ReserveError`
  give it only for a size below nothing.
- Not built: base64; `ByteReader::read_u128_le` is, the signed widths
  other than `read_i64_le` are not in the specification.

## `std::time` and `std::random` (library 29.3, 29.4)

- **`Duration`** is seconds and nanoseconds under a second; a second or
  more of nanoseconds is refused, sums and differences that do not fit are
  `None`. **`Instant`** is a duration on a numbered clock: moments of two
  clocks are not compared or subtracted (`DifferentClock`), and one taken
  from an earlier one is `BeforeOrigin`. `Instant::at` makes one, for
  whoever answers `Clock`; `monotonic_now` and `system_now` ask the host's
  `Clock`, whose two operations give nanoseconds as numbers. The
  specification's `Clock` with `sleep` is not here: the host has no such
  operation yet.
- **`SeededRng`** is xoshiro256** (version 1), its four words read from the
  seed the least byte first, a seed of zeros standing for 1, 2, 3, 4. It
  gives the numbers a reference written outside the language gives.
  `random_below` asks again for what falls in the part of the range that
  does not divide evenly, so each number is as likely as any other.
- **`RandomSource::fill` gives the bytes as an array** or fails: there is no
  writable slice to fill. `HostEntropy` is the machine's, through
  `Entropy`.
- A shift that would lose bits goes wrong, as the rest of arithmetic does:
  the generator takes those bits off first. There are no wrapping
  operations by name yet.

## `std::diagnostic` (library 21)

`Severity`, `DiagnosticCode`, `Diagnostic` (a message with places, notes
and what would help), `DiagnosticBag` and `render_diagnostic`.

- **What is written**: `error[17]: message`, then each place as `  -->
  name:line:column: label` (`:::` for a secondary one), then `  note: ..`
  and `  help: ..`. A place in no text the map has, or not in it, is
  `<unknown>`. More notes than are allowed are counted, `(2 more)`. Longer
  than is allowed, the whole is refused: nothing is cut short.
- **A full bag gives the diagnostic back.** `into_vec` gives them by the
  text their first primary place is in, then how far in, then errors before
  warnings before notes, then by code; ones this does not tell apart stay
  in the order they were pushed.
- Texts are `Str` and `into_vec` gives an array, as elsewhere in this
  library. `SourceId::to_u32` is added to `std::source` for the ordering.

Writing it showed a message that named the wrong thing. A callable given a
reference is read first with the types of what it is given known; if that
fails it is read again without them, and what then went wrong (`&L has no
field primary`, of a field that is there) was said instead of what had
(a field of another module's type that is not `pub`). What went wrong
first is now what is said, and a field read through a reference whose type
is not known where it is read says that.

## `std::fingerprint` (library 20)

A hash of 64 bits, BLAKE3, digests and fingerprints, written in the
language. BLAKE3 gives the reference implementation's digests for inputs
of 0 to 5000 bytes (one byte, one block, one chunk, and each of those plus
one, up to five chunks); the fingerprint of a stream is the reference's
digest of the same stream built by hand.

- **`Hasher` is FNV-1a**, its 64 bits kept as two halves; numbers are
  written the least byte first. `hash64` over the `Hash` trait is not here:
  that trait gives a number from a value and has no writer.
- **A digest's bytes are an array**, always thirty-two: `from_bytes` gives
  `None` for any other count, where the specification has `[u8; 32]`.
- **`Blake3::update` keeps the pieces** and hashes them at `finish`.
- **Programs too long for the Lean machines** are a list of their own
  (`longCases`): compiled as any other, run on the Rust VM and the other
  back ends. The Lean machines took twenty seconds over fifteen digests.
- **Slow to compile.** A program that hashes once takes four seconds, two of
  them the library; one with fifteen separate calls, each given a borrowed
  value with no name, took twenty: Core's certificate is worked out again
  for each place a function is used with other regions, and tried several
  ways. The test goes over the lengths in one function.

## `Some(x)` is an `Option`

`say(Some(3))` was refused: `Some` was another name for `Ok`, and nothing
said what `Ok(3)` could have failed with, so no way to show it was found.
`Some` is now `Ok` with its type written, `fn(_) -> Result<_, ()>`, and a
name given a value with its type written may use another name for a type
there (`let Just: fn(Int) -> Option<Int> = Ok;` said `Option` was unknown).
A truth value is still shown as what it is, `Ok(())` or `Err(())`.

## How long a change takes to try

Trying a change took one to two minutes, and checking one before keeping it
six to eight. What it takes now, on the machine this is written on (24
cores), with the quick build unless said:

| | before | now |
|---|---|---|
| every test program on the three engines (`selftest`) | 160 s | 16 s; 10 s with the default build |
| everything checked before a commit (`./verify.sh`) | 6 to 8 min | 28 s |
| the compiler built from nothing | not timed; the build also ran every test program, one after another | 29 s |
| built again after an edit to the checker | 20 to 35 s | 3 to 8 s for a function that is not in a `mutual` block; 11 s for the inference itself; up to 20 s for a change to what the checker's first module declares |
| after an edit to the elaborator | 31 s | 9 s |
| after an edit to the parser | not timed at first; 18 s once the build no longer ran the tests | 10 s |
| ten small programs tried | not timed; one process for each, one after another | 0.1 s |
| one program that names the library | 2.4 s | 2.2 s; 1.5 s with the default build |

What was slow, and what was done:

- **The test programs are gone through side by side**, on every core, and
  each is compiled once: it was compiled once for the Lean machines, again
  for the Rust VM, again for the count of what Core shows, and again for the
  other back ends. `selftest` now says that count too. So do `survey`,
  `cases` and `probe` go side by side.
- **The Rust VM is started for all the programs by one small process.**
  Started from the test run's own process, each start waited a hundredth of
  a second for a gigabyte of memory to be copied, one at a time.
- **The tests the build ran are checks the executable runs**
  (`Glorious/Checks.lean`, numbered). The build ran every test program one
  after another before it was done, and to do that every module was also
  compiled into a library of its own, which each module after it waited for.
- **Every file is a Lean `module`.** What the files of the front end
  declare is public and what their functions do is not, so a change to what
  a function does rebuilds its own file and nothing that reads it. This
  does not hold for functions in a `mutual` block: Lean puts those in what
  the file shows, so a change to one still rebuilds what follows. The files
  of the kernel and its proofs show everything, as before.
- **The checker reads `Glorious/Elab/Base.lean`**, what it shares with the
  elaborator, and not the elaborator.
- **`lake build -R -Kquick=1`** compiles the C that Lean writes with the
  cheap code generator and keeps frame pointers. The largest files took ten
  to sixteen seconds each in the C compiler, nearly all of it in a few very
  large functions; they take six or seven, and the compiler built runs at a
  little over half the speed. The build without it is the one to use;
  `./verify.sh` uses the quick one unless told `QUICK=0`.
- **The parser's largest function is three.** Lean took ten seconds over
  one function of three hundred lines, and takes three over the file now.
  Its monad is one of its own and not four stacked, which made what Lean
  compiles of it a third the size.
- **The library's texts are read once in a process**: each program that
  names it lexed every text three times and parsed it once, a quarter of
  the whole test run. A program reads them the same unless one of its own
  constructors with named fields is a name the library writes, or it
  changes the operators of a library module; then they are read again.
- **Lists that were searched are sets and maps**: what the count of uses
  reads of the declarations (built again from lists at every binding
  looked at), the calls sure to come back, the names a module can write,
  the regions callables bind.
- **The search for borrows that can be scopes of their own asks side by
  side**: each place alone, and then each round of taking them one at a
  time. The answers are what one at a time would give.
- **One tree.** A commit was checked in a second worktree, built again
  there, and the first could not be built meanwhile. It is checked where it
  is made.

What still takes the time: the C compiler on the file of the inference
(seven seconds), functions in `mutual` blocks rebuilding what reads them,
checking the library once in each process (two seconds for one kind of
program, four and a half for all four), and the largest example (the
calculator, seven seconds, most of it certifying its Core again for each
borrow tried).

## Reading a part of a value with `drop`; writing over what a reference points to

- `fn eat(t: T) -> Int { say(t.name); 1 }`, where `T` has `Drop`, took `t`
  apart to read its name, in the module that declares `T`, and so `t`'s
  `drop` never ran. Reading parts that can be copied (no reference, nothing
  used once, nothing with a `drop`) now takes nothing out of a named value
  that has a `drop`: it stays whole, and is destroyed when its block is left
  as a name nothing uses is. In another module this was refused, and is now
  allowed, since nothing is skipped. A part that cannot be copied is as
  before: taken out only in the declaring module, which is then what lets go
  of the rest. In the type's own `drop` the value is let go as before.
- `h.t = new` and `*r = new` did not destroy what was there, where assigning
  to a variable did. They now do, once the new value is made and the place
  found.
- `xs[0] = new` was `xs = index_set(xs, 0, new)`, which reads `xs`: for
  elements with a `drop` that was refused, and through a reference it copied
  the array out. Where the array is a place (a variable, a field, `*r`, an
  element in turn) the element is now written where it is, as `*(&mut
  xs[0]) = new`: what was there is destroyed. The place is worked out before
  the array is borrowed, so `xs[len(xs) - 1] = v` is fine. Of the borrows
  this adds, twelve in the test programs are not scopes of their own in
  Core: what Core shows of those programs is otherwise what it was.
- The fields of a value are destroyed the last declared first, and the
  elements of an array the last first. (Rust goes the other way.)

## Computing with traits

Covey is to be written the way MalekiRe/unstable_covey is, with systems as
plain functions whose parameter types say what they touch, and what the
Rust does with specialization, type-level lists and const evaluation done
by the trait machinery here. (The effects version in `covey/` stays as a
prototype until the trait one replaces it: on effects a system that takes a
table twice gets an empty one at run time, where the Rust refuses to
compile; a system is not a value that can be ordered or inspected; and a
query's shape is a type, which is a trait's business.) What that needs, in
the order it is being built:

- **A type parameter that is only asked questions.** `fn weight<A:
  Access>() -> Int` dropped what was written of `A`, because `A` is in
  neither a parameter's type nor the result's. It is a parameter of the
  function now; a call says it, `weight<Write>()`.
- **A value a trait leaves to implementations**, `const WRITES: Bool;`. It
  is a function of the trait that takes nothing, so everything that works
  for a trait's functions works for it: a default, `where` bounds, an
  implementation for a pair in terms of its parts (which is a fold over a
  tuple of types). Named without being called it is called:
  `<A as Access>::WRITES`, and `A::WRITES` where the name is in capitals.
  Evaluated when the program runs, for now: it becomes a literal once a
  trait's function at a known type is a direct call.
- `Self::f(..)` in a trait's own body is the implementation's `f`.

- **`value.f(a)` is `f(value, a)`**, where `f` is a function or a trait's
  function that can be named where the call is written; otherwise `f` is a
  field holding a callable, as before. The specification kept calls
  explicit (decision D10: "rather than silently introduce dot methods");
  this is asked for, for `(a, b).chain()` and `app.add_systems(..)`. It is
  the names in scope that decide, not the value's type.
- **`value.name(..)` finds a type's own function by its name alone**:
  `counter.bump()` is `Counter::bump(&mut counter)` where one type that
  can be named there has a function `bump` of its own and no declared type
  has a field `bump` (which could hold a callable). The value's type is not
  known where names are given their meaning, so where two types have the
  function it is not chosen, and the message says to write
  `Type::name(value, ..)`. That leaves out the common names (`len`, `get`)
  of the library's collections used side by side; choosing by the value's
  type would mean reading the program again for each call, as the `..` of
  a tuple pattern does.
- **Generic associated types, over types.** `type Of<T>;` in a trait is a
  type for each type it is asked at; an implementation says `type Of<T> =
  [T];`. It is asked as `Of<T>` in the trait's own functions and as
  `F::Of<Int>` in a function's type. Each place it is written has an answer
  of its own, found where the implementation is known, as a plain
  associated type's is. With it, a trait's function may have type
  parameters of its own, `fn map<A, B>(Of<A>, fn(A) -> B) -> Of<B>`: a use
  has them anew, and in an implementation they are the function's. It may
  take a lifetime, `type Item<'a>; fn next<'a>(&'a mut Self) ->
  Option<Item<'a>>`, an iterator that lends: the lifetime asked is the one of
  that use, so what `next` gave keeps its borrow. Where the answer is not
  known (`L::Item<'a>` with `L` a type parameter), it is taken to hold
  whatever the lifetime borrows, both for a borrow still in use and for one
  that would outlive its variable. Not built: saying what one is in a
  bound (`F: Family<Of<Int> = A>`); type arguments written at a call for a
  trait function's own parameters; and a trait with parameters of its own
  that also leaves such a type. A function generic in `F` that calls
  `single` at two types has been run only where `F` was known and the
  function written out for it.
- **A family of types by a trait's parameter** also works: `trait
  Family<T> { type Of; }`, asked as `F: Family<Int, Of = A>, F:
  Family<Str, Of = B>`. Two things were wrong for that and are fixed: an
  equality bound was of the trait whatever its arguments, and two bounds of
  one trait on one parameter had the arguments of the first.
- **covey: a function of any parameters is a system, by one
  implementation for each number of them.** `Parameter` gives, for a
  parameter's type, what it asks for without the reference (`Changed<A>`,
  `Read<A>`, `Emitted`, `Asking`); `Fetch` is implemented for a list of
  those, one at a time, each taking its column out of the world, lending it
  on with what was gathered before, and putting it back; at the end of the
  list the function is called with what was gathered. The references are
  gathered on the way down, so no type has to be for every lifetime, which
  generic associated types would otherwise be needed for. That a system
  takes a component once is asked of the list (`AllApart`). Three things
  in the checker were needed, none about covey: a condition `where P:
  Kind<Marker = M>` decides `M` when the implementation is chosen; a
  condition on a type made from parameters, `where (M, ()): Fetch<..>`, is
  given to the implementation's functions; and a type left to an
  implementation for a reference (`impl Kind for &mut T`) is found.
- **The command line reads only the library modules a program names**, and
  those they name, checked with the program: the whole library, read and
  checked once, serves a run of many programs and costs one program 2 s.
  Measured on a program using two modules: 2.5 s to 0.5 s.
- **Where no borrow can be a scope the search stops early**: if no run of
  places passes, twelve spread among them are asked alone, and if none
  passes the rest are not asked. The count over the tests is unchanged
  (1156); covey's example went from 42 CPU-seconds to 13.
- **Tuples of any length are the pairs they are made of** (`std::tuple`).
  No parameter stands for a list of types. `Tuple` gives a tuple's nested
  form, `(A, B, C)` as `(A, (B, (C, ())))`, and back; `Callable` gives a
  function's parameters in that form and calls it with them. Both are
  implemented in the library for each length up to twelve, written out by
  the compiler's own source, so that a program writes an implementation
  for `()` and one for a pair and has every length: `Concat` and `Count`
  in the same module are written so, and covey's `chain` takes any number
  of systems. What this does not reach: a function whose parameters are
  references, taken as a list (`fn(&mut A, &B)` as `(&mut A, (&B, ()))`),
  since the list's type would have to be for every lifetime of each; that
  is what generic associated types are for, and covey still has one
  implementation of `System` for each shape of parameter list.
- **`[T; N]` and `const N: Int` are the trait machinery's.** A length is a
  type: the prelude has `Z`, `B0<N>` and `B1<N>`, a number's bits from the
  lowest, and `3` where a type is written is `B1<B1<Z>>`. What number a
  type stands for is its `Known::VALUE`, found through the three
  implementations. `const N: Int` is a type parameter asked to be `Known`,
  and `N` written as a value in the function is `N::VALUE`. `[T; N]` is the
  prelude's `Fixed<T, N>`, an array held in a type that says its length; it
  is the same value when the program runs. Nothing of this is in the
  checker by name: errors show `[Int; 3]` and `3` because types are shown
  that way.
- **A literal is what is wanted of it, by a trait with a fallback.** In a
  program that writes a length in brackets, `[a, b, c]` is
  `array_literal<3>(..)`, of any type with `Literal<T, 3>`: an array, or
  one of exactly three. `#[fallback] impl` says which implementation a
  type that nothing decides is taken to have (an array), unless another of
  the trait's has every other trait asked of that type. The fallback is a
  general rule of the checker; the prelude uses it once. A program that
  writes no length in brackets has its literals as before.
- **`let [a, b, c] = xs` takes a fixed array apart** as a tuple of its
  elements: `elements(xs)`, by an implementation the prelude has for each
  length up to eight.
- **Limits of fixed arrays**: `[x; n]` makes an array that can
  grow, and `fixed_repeat(x)` one of a fixed length; in an
  implementation, `where N: Known` is written and the number is
  `N::VALUE`; no arithmetic on lengths (`[T; N + 1]`); a length is checked
  where types meet, and an index is still checked when the program runs.
- **`[first, ..rest]` is written out where it is read.** A clause whose
  whole pattern is an array with `..` (or `..name`) takes any array, asks
  the prelude whether it has as many elements as the pattern names
  (`rest_fits`), and takes those off its ends (`rest_first`, `rest_last`);
  the clauses after it are for an array that has not. Whether every shorter
  array is some other clause's is the checker's to say, and of an array it
  cannot: so for each such length the clauses' patterns for it are written
  as patterns of a tuple of so many, in a callable nothing calls, and the
  checker refuses that where it does not cover every case. Limits: only a
  clause's whole pattern (not inside `Some(..)`, not a function's
  parameter, not `let`); taking the first element off copies the others
  (`sum` over `[x, ..rest]` is quadratic).
- **`..` in a tuple pattern is found by reading the program again.** How
  many parts `(first, ..)` leaves out is known only from the tuple's type.
  Where the checker meets such a pattern and knows the type, it says how
  many, and the program is read again with that many `_` written; where it
  does not know the type, it asks for it. Each pattern costs a reading of
  the program up to it. The tools that show a program's stages (`why`,
  `stages`) do not do this.
- **Destructors, swept.** Every way of binding two values with a `drop`
  (a name, a tuple, a struct or array pattern, in `let`, a clause, a
  callable's parameters) was run against every way of using one (not at
  all, given away, a field read, borrowed, bound again, let go), 108
  programs, each asked to run each `drop` once. Fourteen did not. Fixed:
  a clause whose pattern is a tuple was read without knowing what the tuple
  held, so a name of it whose field was read was taken to be of no type
  with a `drop` (the tuple's type is now given to the clause, and where a
  name's type is still not known when its uses are counted it is asked
  again once the function has been read). And a callable bound by `let`
  that is general in a type it lets go of ran no `drop` at any type: it is
  still general, and a use of it at a type with something to destroy is
  refused, with what to write. Left as it is, by the specification (7.4,
  an authorized deconstruction consumes the shell): `match(a) { Loud(n) =>
  n }` takes a value with a `drop` apart without running it.
- **Two more skipped destructors.** A name bound by the pattern of a `let`
  of which only fields were read, `let (a, b) = pair(); a.0`, was never
  destroyed (as a clause's name is, it now is when the block ends, and what
  is left of one a field was moved out of). And a field read of a value in
  no variable whose own type has a `drop`, `make().0` or `pair.0.0`, let
  the value go without running it: that is refused, with what to write.
  Before the pattern of a `let` is read, a type left to an implementation
  is found where it can be, so that what has a `drop` is seen to have one.
- **A destructor was skipped, the fourth time**: what the pattern of a `let`
  took under a name nothing used, or under `_` (`let (a, b) = pair();`),
  was not destroyed. It is now, as a clause's is. And `x;` and `let _ = x`
  for a value with a `drop` to run were refused as "used on one path and
  not on another"; they let the value go, and its `drop` runs there.
- **A function is written out for each implementation it is called with.**
  Once traits are values (`untrait`), a call that gives an implementation
  that is known calls a copy of the function made for it, in which the
  trait's functions are called by name (`Glorious/Elab/Specialize.lean`).
  What `main` reaches then passes no implementation about. It is done in
  the front end and proves nothing; Core checks what comes out as before.
  Measured on a loop calling a trait's function of a nested tuple 300 000
  times: 0.95 s to 0.53 s on x86-64, 1.76 s to 1.31 s on the interpreter.
  covey's example, whose regions Core could not be shown before (an
  implementation that takes implementations whose functions take
  references), has them shown. A copy is made per implementation, not per
  type, so a function without bounds is one function for all types: Core
  does not tell types apart at run time, so nothing is lost by that.
- **Lists of types as parameters, `..R`, in implementations.**
  `impl<H, ..R> Size for (H, ..R) where (..R): Size { .. }` is written out,
  before it is read, once for each length of `R` the program can need
  (with two lists, every pair of lengths whose sum is no more than that;
  lists named after one `..` together are as long as each other: see
  below for how long that is). `..R`
  stands for `R0, R1, ..` wherever it is written in brackets or in the
  conditions after `where`: in types, patterns (`let (h, ..rest) = t`) and
  what is built (`(x, ..rest)`, `[..show(r)]`). What follows `..` may be
  more than a name and is then written once for each: `(..Option<R>)`,
  `..R: Show`. A list of values is as long as the list of types its name
  is in another case, or the first. So `join` of two tuples is one
  implementation and no recursion, and a tuple of types can be mapped.
  This is a rewriting of the text, not a kind of type: a function cannot
  take a list of types (only implementations can), and a message about one
  of the copies names `R0`, `R1`.

  **(Later, by the user: a list of types has no longest length.)** It was
  written out to twelve. Now it is written out to the most things the
  program's own texts write between one pair of parentheses (a tuple, a
  function's parameters or arguments; two at least), times the most lists
  one implementation takes (one that joins two makes what is as long as
  both), and where the checker
  then finds a tuple or list of parameters with no implementation that is
  longer than that, counting the trait's tuple with the type's (as joining
  two makes), the program is read again with lists that long, up to eight
  times, each at least twice as long. So a thirty-tuple has `Count`, and
  `join((1, "x"), (3, 4, 5))` has an implementation. What is
  written out is what the program can need, which is less than twelve for
  most: a program pays for the lengths it uses. Still a rewriting: each
  length is checked as its own implementation; a list whose length nothing
  written or joined says (a recursion that makes ever longer tuples) is
  not found. Found on the way: in an implementation's function, a type
  made of the function's own parameters, `(R0,)`, was taken to have the
  trait by the one other implementation for tuples of one, and refused;
  it is now left to what the function assumes.
- **A condition may say what a type made of the implementation's type
  parameters leaves to its implementation**, or one of its parameters
  that is not the head's: `where (..A): Tuple<Nested = L>`, `F: Then<X,
  Out = Y>`. It is met where the implementation is used, deciding `L` or
  `Y` there, and wherever the implementation's own associated type is
  asked, so a type found by a chain of implementations is found; inside
  the implementation's functions it is not assumed, as nothing there
  needs it to be.
- **covey is written with lists of types**: the function a system is,
  however many parameters it has, is one implementation of `System`, of
  `CallWith` and of `Condition`, where it was one for each number of
  parameters; what has been gathered for it is flattened by `Gathered` and
  `Then` (a tuple with one more part at the end). It takes 2.6 s to run
  the simulation where it took 2.5; writing the gathering itself with
  lists took 3.1, there being then an implementation of `Fetch` for each
  length of what was gathered.
- **An associated constant at a known type is its number.** After the
  copies, a function that takes nothing and whose body is integer
  arithmetic (`int_add`, `int_sub`, `int_mul`) of numbers and of calls of
  such functions is worked out once (`Elab.foldConstants`), and every call
  of it is that number: `N::VALUE` of `[T; 5]` is `5` in Core, not a
  chain of calls down the binary digits. One whose result would not fit
  in 64 bits is left as a call, to go wrong when it runs as it would have.
- **What a dotted call is called on is borrowed** where the function is
  written to take a reference first: `counter.bump()` is `bump(&mut
  counter)`, `game.world.spawn()` is `spawn(&mut game.world)`. Decided once
  every declaration has been seen, by what is written: the function's first
  parameter type, and whether the name is known to hold a value (a `let
  mut`, a name bound to what is plainly a value, a parameter with a type
  that is no reference's). A name that may already be a reference is given
  as it is.
- **An implementation's head is a type.** `impl<T> Tag for Wrap<Option<T>>`,
  `impl<B> Tag for Pair<Int, B>`, `impl<A> Twin for (A, A)`: an argument
  that is not one of the implementation's type parameters, the first time
  it is written, is a type the argument has to be.
- **Two implementations of a trait for one type**, where one asks more of
  the type than the other: it is the one for the types it fits. The
  specification has no specialization (§13.2); this is asked for. With it
  `impl<A, B> Same for (A, B)` and `impl<A> Same for (A, A)` tell whether
  two types are one, and `impl<T, R> Get<T> for (Column<T>, R)` beside
  `impl<T, H, R> Get<T> for (Column<H>, R) where R: Get<T>` finds a column
  by its type in a tuple of columns, each function typed on its own.
  - Two that some type fits, with neither asking more, are refused where
    they are declared; so is the same one twice.
  - Where the type is not all known, or is a function's own type
    parameter, and an implementation that asks more may yet come to fit,
    which one it is is not decided there: the function has to be given it
    (`where W: Kind`), and whoever calls with a known type decides. This
    is what keeps it sound without picking by lifetimes: a choice is only
    ever made of a type that is known.
- **A condition of an implementation may be a trait at arguments, of any
  of its type parameters**: `where R: Get<T>`, `where H: Same<T>`.
- Which implementation meets a bound in a program that uses any of this is
  found by the checker fitting types, not by `Traits.solve`, which knows an
  implementation by its trait and the name its type is made with and is
  proved of that. What the checker finds is not proved; it is checked with
  the program's Core, as everything the elaborator writes is. A program
  that uses none of it is solved as before.

- **An implementation can be for functions, and for references**: `impl<W,
  A> System<W> for fn(&mut Column<A>) -> () where W: Get<A>`, `impl<T> Fetch
  for &mut T`. A function it is for performs nothing (what the
  implementation's own functions do with it is typed without effects), and
  takes references of any lifetime, as `for<'a> fn(&'a mut T)` does. With
  the two above, a plain function is a system: `run(integrate, &mut world)`
  finds each parameter's column in the world by its type, calls the
  function, and puts the columns back.
  - One implementation for each number of parameters, until a list of
    types can be a parameter.
  - Two functions of the same parameter types are the same type, so `run`
    calls the function through its value: nothing is inlined yet.

Still to come: a type of its own for each function
and closure, with `Fn<(..)>` as a bound; lists of types as parameters, with
head and rest; an implementation that is preferred over a more general one;
a copy of a function for each type it is used at; generic associated types,
const generics and fixed arrays.

## Covey

- `covey/` is an entity component system written in Glorious, after
  MalekiRe/unstable_covey: the whole app is one type, and the compiler
  works out from it which column a system touches and which systems a label
  runs. `covey/simulation.glorious` is run with the tests.
- **A system is a plain function, and its parameters say what it touches**:
  `fn integrate(positions: &mut Column<Position>, velocities:
  &Column<Velocity>)`. `System<S>` is implemented for functions by their
  parameters; each column is taken out of the world, lent to the function,
  and put back.
- **The world's storage is a tuple of columns**, `(Column<Position>,
  (Column<Velocity>, ()))`, grown by `.register<T>()`. `Get<T>` finds a
  column in it by its type: two implementations for a pair, the one whose
  first column is `T`'s being the narrower. A world without a column of
  `T` has no implementation, so a system that asks for one does not
  compile.
- **Labels are types**; `.add_systems(Update, (integrate, friction).chain())`
  puts an entry on the app's list of systems, which is a type too, and
  `emit` runs the entries under its label by `Dispatch<E, S>`, found the
  same way as `Get`.
- **A label can carry a value**: `.on<Hit>((wound, reap).chain())`, and a
  system under it may take `&Hit` first; `game.emit(Hit(1))` runs them.
- **A plugin is a function from an app to an app**: `.add_plugins(physics)`.
- **A system with two parameters of one component does not compile.** Its
  implementation asks `(A, B): Apart`, which a pair has, except `(A, A)`,
  which has it only if `A` has a trait nothing has. The message is that
  trait's name: "`Velocity` does not implement
  `ASystemTakesAComponentOnce`", where the label is emitted.
- It was first written on effects (a component's storage as an effect
  instance, a plugin as a handler layer). That version ran, and is in the
  history. It was dropped because a system that took a table twice got an
  empty one at run time where the Rust refuses to compile, a system was not
  a value that can be ordered or inspected, and a query's shape is a type.
- **Not there yet.**
  - One `System` implementation is written out for each number and kind
    of parameter (four so far), until a list of types can be a parameter.
  - A system performs no effects. It can ask for an entity to be ended
    (`&mut Commands`), and no more than that yet.
  - Every call of a system and of a trait's function goes through a value
    at run time: nothing is inlined, so it is the shape of the Rust and not
    yet its speed.

## Instances of an effect, told apart by their type arguments

- `effect Store<C> { take() -> [C], put([C]) }` is a family. `Store<Int>` and
  `Store<Str>` are two effects (§10.1: an effect is its declaration and its
  arguments), each handled by the nearest handler of exactly that one. A row
  had one instance of a family and no more.
- **In the checker**, two instances are the same effect if they are written
  the same; they are two if their arguments can never be the same (`Int` and
  `Str`, or two different type parameters of a function). One not yet known
  is taken for the instance its context names, the nearest first (§10.3);
  where it could be either of two that are themselves apart, the program has
  to say: `take<Int>()`. An operation's arguments are looked at before its
  effect is, so `put(names)` says which by what it is given.
- **Core is unchanged.** It knows an operation by a number, so before a
  program is elaborated each instance it uses becomes an effect of its own
  (`take@<Int>`), and a function about an instance of its caller's choosing
  (`fn store<C>`, `fn each_mut<C>`) is written out once for each choice. The
  checker says, for every call, which types say which instance, in terms a
  caller of the function fills in; the copies are found from `main`.
  Nothing is done to a program in which no family has two instances.
- I had this down as needing a runtime identity for instances through the
  kernel, its proofs and the three backends. Copying needs none of it.
- **Limits.** A trait's function is called through a value at runtime, so
  one cannot be copied: an implementation's function may perform `Store<Int>`
  but not `Store<C>` for a `C` of its own. A function that is copied has to
  be called where it is named, not passed as a value. A handler handles one
  instance of a family, the one its computation's type names; there is no
  way yet to write which in the arm. Two functions that call each other and
  are both copied are not supported. Generic operations (`emit<T>(T)`, with
  the parameter on the operation and not the effect) are still refused.

## An operation's own lifetimes

- `effect Files { read<'a>(Path<'a>) -> Bytes }`, as the standard library's
  specification writes them: an operation may have lifetimes of its own,
  and a reference in what it takes or gives without a written lifetime has
  one of its own too. Each performance has its own, so what an operation
  is given may borrow from the performer's variables, and what it gives
  back may borrow from what it was given (`pick<'a>(&'a Int, &'a Int) ->
  &'a Int`).
- In an arm such a payload is borrowed for as long as the arm runs: it
  may not be kept anywhere that outlasts the arm ("could be used after the
  arm"). The arm has to be one without the resumption (`read(p) =>
  value`, which resumes with the value once it is done), as the
  performer's variables are gone once it is resumed and comes back; and
  an operation that never returns cannot be given what borrows. A
  callable it is given or gives is held to what the declaration says, as
  before.
- So `effect Reader { ask() -> &Int }`, the handler lending its own
  variable, now compiles: two tests that said it was refused say what it
  gives. Type parameters of an operation's own are still refused: an
  operation has one type wherever its effect is handled.
- Core's certificate has no type for an operation of a region of each
  performance; a program with one is certified without the region rules,
  as other programs whose regions cannot be found are.

## A borrow written anywhere in a statement is a scope

- Core has a rule for a borrow that is a scope of its own: while it lasts,
  nothing else reaches what is borrowed, and that is checked by the proved
  checker. The elaborator made a borrow such a scope in four shapes: an
  argument of a function called by name, `let p = &x`, the arguments of a
  call whose result is given a name, and a borrow put straight into a tuple
  or constructor that is given a name. Anything else was the plain
  reference, about which Core's borrow rules say nothing: `swap(&mut a,
  &mut b)` (an intrinsic), `a[i] = v`, `x.f = v`, `f(&x)` with `f` a local
  callable, `*pick(&a, &b)`, `match(element(&a, 1)) { .. }`.
- Now a borrow of a variable written anywhere in a statement, outside a
  callable written there, is made before the statement and is a scope
  that lasts while the statement runs. Making a reference does nothing, so
  making it earlier changes nothing else. Each statement is one more place
  the search for a certificate tries: first with the borrows given to
  functions left to their calls, then with those too lasting the whole
  statement, and for a `let`, lasting while what is made of them is used.
  Of the tests' borrows, 1065 are scopes and 105 are not, in 59 programs;
  before, with eighteen fewer tests, 731 and 409, in 156.
- **What is assigned is computed before the place it goes**, as the
  specification says (§5.3, "Evaluate the RHS first"). It was the other
  way round for `*r = v` and `a[i] = v`: the index was worked out, and its
  bounds checked, before the value. It also means the borrow by which the
  place is reached does not last while the value is worked out, so
  `x.1 = x.0 + 1` and `xs[0] = xs[2] + xs[1]` are scopes too.
- What the statement works out before any of its borrows is used is worked
  out before they are made, so that the scope does not last while it runs:
  `a[len(a) - 1] = v` reads `a` for the index. Only what comes first is
  taken out, in the order it was written, so the order things happen in is
  what it was; once a call that is given a borrow has run, what follows
  stays where it is. Nothing is taken out of what a handler watches.
- A borrow written in what a handler watches (`handle work(&mut n) { .. }`)
  is made before the handler is there and lasts until it is gone. As a
  scope that lasts as long as the call it could not be one: the handler
  would run while it is set aside.
- What is left: two parts of one variable borrowed at once (Core's rule is
  about the whole variable); a borrow that a callable or a branch gives
  back; of two borrows given to one call, one outliving the other; two
  variables borrowed under one lifetime name; a reference an operation
  hands to the computation it is handled for.
- The search tries each place alone when all at once fails, side by side.
  It gave up on programs with more than 32 places, which with the standard
  library is soon reached, and then no borrow of the program was a scope;
  the limit is 160 now. Three things keep the cost down: a call inside a
  statement is asked only where the statement's own place fails; the second
  way is tried only where a place has one; and where there are more than
  16 places they are first asked a run of them at a time, since few fail
  and a run that passes whole needs none of its places asked alone. A
  program of 88 places takes 6.0 s and 21 s of processor time; asked one
  place at a time it took 10.1 s and 126 s. Each try still certifies the
  whole program again: a search that asks about one function at a time is
  what would remove the rest.

## What a function touches is written down once

- Working out a certificate copied, at each use of a function, the record of
  what the function touches together with the records of everything it
  calls, and of what those call: the copies multiplied with each level of
  calls. A program that called a hash of five levels fifteen times made 2.7
  million records and took 22 s to compile. When a group of functions has
  its types, each record that nothing can still be added to is now worked
  out and written flat, so a use copies that alone; the same program makes
  42 thousand and takes 7.8 s. A record a parameter's type names, or one
  that includes such a record, is left as it was: what a callable parameter
  touches is decided by each use. Every program of the tests gets the same
  certificate as before (compared one by one, 1533 programs).

## A field of a value borrowed; a parameter that is only borrowed

- `let c = C { .. }; len_at(&c.xs)` and `fn f(c: C) { len_at(&c.xs) }` said
  `c` was not a mutable variable or a reference. A name that is borrowed
  whole and never changed was already kept where a reference can point; one
  whose field is borrowed with `&` now is too, where it is plainly bound to
  a value: by a constructor, a tuple, a function named with its type, with
  a written type that is not a reference's, or as a parameter with such a
  type. A name bound to what some other call gives, or by a pattern, may be
  a reference, of which a field is borrowed through it; for those the
  message says to write the type. (Where a name kept so turns out to hold a
  reference, the field is borrowed through the reference it holds.)
- **A third `drop` that did not run.** `fn f(h: H) -> Int { size(&h) }`,
  with `H` holding a value with `drop`: the parameter is made a variable so
  that it can be borrowed, and the variable's cleanup was looked for at a
  place of the text that no statement had. It was never found, so what `f`
  was given was never destroyed. The variable is now at the clause's first
  statement, and is the one cleanup for the name.

## A borrow of a field is the variable's reference narrowed

`&mut c.n`, where `c` is a variable, was written out before elaboration as
a variable of its own: the field copied in, the borrow of that, and a
cleanup putting it back when the borrow's extent was left. How long that
was had to be read off the text, and whatever read `c` in that time read
the old field: `let x = bump(&mut c.n); x + c.n * 100` and `bump(&mut c.n)
+ c.n` gave wrong answers, on every engine, since all were given the same
program. A first repair kept the copy and narrowed its extent (the checker
said which calls give a value that can hold no borrow), sent reads and
writes of the field to the copy, and refused what was left.

The copy is gone. The machine can narrow a reference to a part of what it
points to (`focus`), which is how a field of what a reference points to was
already borrowed; a field of a variable is now borrowed the same way, as
the variable's own reference narrowed, where it is written. The field
stays where it is, so nothing can read an old one, and none of this is
needed any more: the extent of a field borrow, the narrowing and what the
checker said for it, the rewriting of reads and writes, the values kept
under names so that they were still computed first (which had the wrong
answer described below), and four refusals:

- two field borrows that overlap with neither inside the other;
- a field borrow given back by the block that makes it, or kept in a
  variable outside it (`let r = { &mut c.n }();`, `match(k) { 0 => &mut
  c.n, _ => &mut c.m }`): it lasts as long as the variable, as `&mut c`
  does;
- the whole variable used while something that might hold the borrow can
  still be used;
- `a.f = v` no longer takes the field out and puts it back: it writes it.

What Core shows. A borrow of a field can be a scope of its own, as a
borrow of the variable can: the narrowed reference is what is lent. Core's
rule is that while a cell is lent nothing else uses the cell, the whole of
it; so a field borrow is a scope where nothing in its extent uses another
part of the variable, and otherwise is kept exclusive by the check of the
source alone. In the test programs 692 borrows are scopes of their own,
where 727 were. The 727 counted borrows of the copies: what was shown of
those said nothing of the variable the field came from, whose reads and
writes the unproved rewriting redirected. The 692 are of the variables
themselves.

What is left for the kernel: a lend that says which part of the cell it
lends, so that two fields of one variable can each be lent and used
side by side with the rule still proved. `tail` directly beside a variable
whose field is borrowed is refused, as beside any variable that is
borrowed: it was let through by accident.

`&mut a[i]` borrowed a copy of the element, so writing through it changed
nothing. `&a[i]` and `&mut a[i]` are now references to the element where it
is, when `a` is a variable, a field, `*r` or an element in turn. Through a
reference it is `&mut (*r)[i]`, as reading is `(*r)[i]`.

Found by writing programs whose answers were worked out by hand; forty of
them are now cases.

## A wrong answer: what is computed before a borrow of a field

`"<" ++ pair.0 ++ ">" ++ written(&pair.1)` gave `>>>` and not `<ab>`. A
borrow of a field is taken out of the statement it is in, and what the
statement computes before it is kept under names so that it is still
computed first; the names said which borrow and which place in a call,
and not which call, so in a call inside a call inside a call three values
had one name and the last was read three times. The names now say how deep
the call is. Every engine agreed on the wrong answer, since they were
given the same program; it was found by writing a larger program
(`examples/json.glorious`) and reading what it printed.

Three such programs are now among the examples, with what they should
print: `json`, `orders` and `shapes`.

## Patterns that reach through a reference inside a value

`match(Cursor::peek(c)) { Some(&Spot { token: Token::Let, at }) => .. }`
was refused: a pattern that binds by reference had to be the whole of a
clause's parameter, and here the reference is inside an `Option`. Such a
clause is now written out as two steps: the value's own pattern with a name
where the `&` was, and then clauses of that name by reference. Clauses that
ask the same of the value and differ only past the references are one
group; where none of a group is for what the references point to, the
clauses that follow are tried.

- **The clauses that follow are given the value again**, so with
  fallthrough the value has to be one that can be looked at twice: one
  that holds what is used once is refused, with why. A match whose clauses
  with references come last, or cover every case of what is pointed to, is
  not affected.
- Whether the clauses take every case is asked once, of the clauses as
  written, each pattern reaching through the references in it; a column of
  references is covered when what they point to is.
- For some of these Core's regions are not found (a reference kept in an
  `Option` and matched), as for other references kept in values: the
  program is checked by the source rules and typed in Core.

Several definitions of one function, `fn get(Some(x)) ..` and `fn
get(None) ..`, are not clauses of one function here; `fn get { Some(x) =>
.., None => .. }` is.

## How long a program that names the library takes

A program that only named `std` took thirty seconds to compile, after the
library doubled in a day: every part of it is checked for every program
(what is checked first is then the same for all, so that it can be kept).
Four things made that grow much faster than the library:

- What a callable captures was found by going through every capture of the
  program, for each callable asked about. Each capture variable now has the
  places of its own captures (`capOut`), kept when two become one.
- Generalising a type went through every capture, and asked of each whether
  it was shared by looking through a list. It now starts from the type and
  follows what is reachable.
- Whether an edge is shared or a variable's value was a search of a list;
  both are sets now.
- What has to be used was gathered from every capture for every function;
  it is asked of each capture variable when a type is looked at.

That program now takes under three seconds, and the test programs half as
long. The regions a callable touches (`accSet`) are worked out to a fixed
point over the callables reached, and kept while nothing they depend on
changes, instead of chain by chain of calls.

A function's type carried every need the function had of any type, with
every capture variable the need mentioned, and each use of the function
asked them all again with copies of everything they mentioned; a function
that used it carried those copies in turn. A calculator of a hundred lines
took a minute, five seconds for each place its entry was called. A need is
now part of a function's contract only where it is about something a
caller decides: a type variable the function is general in, or something
its type holds. The rest were settled when the function was checked. The
calculator (`examples/calculator.glorious`) takes thirteen seconds, most of
it finding which of its borrows can be scopes of their own.

## Paths, futures, buffers, base64

- **`std::path`** (29.1) is `PathBuf` over a text, for paths written with
  `/`: `components`, `file_name`, `extension`, `parent`, `join`, `push`,
  `pop`. There is one path type, not `Path<'a>` and `PathBuf`, and no
  `OsString`: a text here is not a view of bytes, and every text is valid.
- **`std::future`** (30.3) has `Future`, `FutureStep`, `Await`, `ready`,
  `drive` and `block_on`. `Await<F: Future>` gives `<F as Future>::Output`,
  as the specification has it: an effect's operation can name a type a trait
  leaves to an implementation of one of the effect's type parameters (see
  "An effect's operation can name what a trait leaves"). `poll` takes the future alone: there is no
  `PollContext` or wake key, since nothing here wakes anything.
- **`BufferWriter` and `BufferReader`** are in `std::stream` (28.2), each
  with its inner stream's effects. `new` cannot fail and gives the buffer
  itself. `finish` writes what is kept and gives the writer back, or gives
  back the writer, the bytes not written and why; letting a buffer go
  writes nothing.
- **`base64_encode` and `base64_decode`** are in `std::bytes` (23), with
  both alphabets and the three padding rules; a text that says its last
  bytes with bits left over is refused as not the one way to write them.

`vm/check-backends.sh` now remembers each program that agreed on every
engine, by a hash of its bytecode, its input, the VM and the C compiler,
and does not run it again while those are the same. It was taking most of
each verification. `GLORIOUS_BACKENDS_CACHE=` runs everything.

## Constructors that share a name

`enum Token { Plus, Minus }` and `enum Op { Plus, Minus }` in one module,
or `struct Cycle` beside `GraphError::Cycle(Cycle)`, as the library
specification itself has: a constructor was one name of its module, so the
second took the first's place, and what came of it was a wrong message
about a type holding itself. A constructor of an `enum` whose name another
constructor of the module has is now named only with its type,
`Token::Plus`, in expressions and in patterns; written alone, the message
gives the ways to write it. A `struct` keeps its own name, and a
constructor that shares its name with nothing is written as before.

## Tasks

`std::task` has the specification's task interface (30.4) as far as it
goes without what is not built: `Task<T>`, a handle that has to be given
to `join` or `cancel_task`; `Spawn<T>` and `TaskControl<T>`; `run_inline`,
a provider that runs work where it is spawned; and `round_robin`, which
runs coroutines a step at a time in turn (`yield_now` gives way).

- **`Spawn<T>` has its type on the effect**, where the specification has it
  on the operation, `spawn<T, ..>(F) -> Task<T>`: so the tasks spawned
  under one provider make one type. **An operation cannot have type
  parameters of its own.** The proved type system gives an operation one
  type in each row of effects (`ε.lookup op = some targs`), and a handler's
  arm is typed against that one. This was built in the checker, with the
  arm checked for every type and its values kept from outliving it, and
  taken out again when no certificate could be made for a program that
  performed such an operation at two types. It is refused with what to
  write instead.
- **Spawned work performs nothing** (`fn() -> T / {}`): that is what lets
  a provider call it and still be sure to answer, which its operations
  promise (`[1, 1]`).
- No futures, `await`, wake keys or `LinearTask`: `Await<F> where F:
  Future` needs a condition on an effect's parameter that an arm can use.

## Functions that call each other, and their type parameters

`fn size<T>(t: &Tree<T>)` and `fn sizes<T>(kids: &[Tree<T>], i: Int)`,
each calling the other, were refused: "expected `&Tree<T>`, found
`&Tree<T>`". Functions that call each other are checked together, each at
one type inside the group, and each one's `T` was a type of its own. A type
parameter that functions of one group write with the same name is now one
type to all of them, which is what calling each other with what they were
given needs. Each is still for every `T` to whoever calls it from outside.

- **By name.** `ping<A>` and `pong<B>` calling each other are still
  refused, and the message says why. Nothing else relates the two.
- A function of the group used at another type than it is checked at
  (recursion at a different type) is refused, as before.

## Parts of a value taken separately

`let x = t.a; let y = t.b;` was "`t` is used more than once" for a value
whose parts are used once, and `redeem(f.fd) * 100 + f.written` likewise;
the way round was a pattern. Where a name is used only by reading parts of
its value, each part is now a value of its own: it is used as often as
that part is read, it has to be used on every path if its type does, and
the parts never read are what is let go.

- **A part never read is destroyed when the name's block is left**, by the
  cleanup a name nothing uses has. Before, taking one field of a value
  left the others undestroyed: a `drop` among them did not run.
- **Where there is no name with a place to clean up**, a field of a value
  just computed (`make().a`), of a part of a name (`o.inner.a`), or of a
  name a pattern bound, the others are still let go there, and a `drop`
  among them would not run: that is refused, with what to write instead.
  It was accepted and did not run.
- **A name used as a whole too** is as before: each part read is a use of
  the name.
- **Not for a value that holds a resumption.** The machine counts every
  read of such a value as a use of all of it, so two parts read is two
  uses, as before.

## Budgets, cursors, graphs and source maps

`std::budget` (25.2, 25.3), `std::parse` (26.1), `std::graph` (26.2) and
`std::source` (25.1), as ordinary source.

- **A memory charge and a depth permit have to be used**, and only their
  module can take one apart: the one thing to do with one is give it back.
  A budget made with `named(limit, id)` tells its tickets from another's
  by the number; `new` gives every budget the number 0, since nothing here
  hands out fresh identities.
- **`many` stops with `Limit` when it has found as many as it may and input
  is left**, without trying the parser again: what one more try found
  would have nowhere to go.
- **A parser is a callable given by value**, `fn(&mut Cursor<'a, T>) ->
  ParseStep<U, E> / e`; the specification's `&mut F` with `Fn` and `RunsIn`
  conditions says the same of a callable kept in a variable.
- **`Graph::successors` gives an array**, not a slice borrowed from the
  graph, and the functions over a graph are written `N: Eq + Hash, G:
  Graph<Node = N>`: a condition cannot be put on `G::Node` itself.
- `GraphError::Cycle` holds a `Cycle`, as specified: see "Constructors
  that share a name".
- The groups of `strongly_connected_components` come sinks first.
- A source's text is kept as its bytes; `text` and `slice` give a `Str`
  made from them, and `line_range` a pair.

Writing these found that **a type parameter that is in a function's type
only as what a trait's type is said to be** (`N` in `fn f<N: Hash, G:
Graph<Node = N>>(g: &G)`) lost the traits written of it: "`N` is not known
to implement `Hash`". Such a parameter is now one of the function's like
any other.

Each traversal is one function. When they were written, two generic
functions that called each other could not be; they can now (see
"Functions that call each other, and their type parameters").

## C strings, addresses and `Box`

From the specification's memory and C support (22.2 to 22.4), added to
`std::ffi`: `CString`, a text for C in memory of its own, which has to be
given back (`release`, or `into_bytes`); `CStr<'a>`, bytes that end in
their one zero, looked at where they are; `NulError`, `CStrError`;
`c_bool`; `null`, `ptr_is_null`, `ptr_add`, `ptr_write_bytes`, `ptr_copy`,
`ptr_copy_nonoverlapping`. `std::boxed::Box<T>` is in `alloc::boxed` too.

- **An address is a `usize`**, as in the rest of this module: there is no
  `*const T`, since a value here is not bytes at an address. So the
  specification's pointer functions that read and write a `T`
  (`ptr_read<T>`, `ptr_as_ref`, `slice_from_raw`, `Box::into_raw`) are not
  built; bytes and whole numbers are read and written by width.
- **`CStr::from_ptr` is `bytes_at`**, which copies the bytes out: a slice
  cannot point into memory that is C's.
- **`Box<T>` is the value under another name.** Every value here is kept
  somewhere of its own already; `Box` is there so that a type written
  `Node(Box<Tree>, Box<Tree>)` reads as it does elsewhere.
- `CString` has no `drop`: the library has none (see "Generators"), so it
  is given back by name.

Taking a field out of a value, `f.fd`, was said to let go of the whole
value, the field taken included: `redeem(f.fd)` was refused for a ticket
that has to be used, in a value whose other fields are numbers. It lets go
of the other fields, and is refused only when one of those has to be used.

## A row with several unknown parts

`copy_stream` performs what reading its one stream does and what writing
its other does: `/ { | <R as Read>::Effects, <W as Write>::Effects }`. A
row had one unknown part, so the two were taken to be one row, and a copy
from memory to the host's output was refused. A row may now be written with
several after `|`, and need not be written at all.

A row that is someone else's to say (a row parameter, or what a trait
leaves to the implementation for a type parameter) is no longer made equal
to the row of where it is performed. That it is *among* what the function
performs is kept with the function's type, and seen to at each use, where
the rows are known: the function's row is then at least each of them. So
`both(one, two)` for two functions that perform different effects performs
both, and handling only one of them is refused.

- **A row written for a function has to have what the function performs.**
  `/ { | <R as Read>::Effects }` on a function that also writes `W` is
  refused where it is declared, as is a row parameter called under a row
  that does not name it.
- **A row written closed is the exception**: `fn quiet<R: Read>(..) / {}`
  that reads `R` is accepted, and is for types whose implementation
  performs nothing; using it at another is refused there. An
  implementation has no other way yet to say that of a type parameter, and
  `impl Iterator` for what wraps a generator needs to.
- A row in a trait's function with several unknown parts is not kept
  apart: the parts are one row there, as before.

## Trait arguments of an implementation's own

`impl<T> From<T> for Wrap<T>` was refused: the arguments an implementation
gives its trait had to be types written out, since an implementation is
known by its trait at those arguments and the head of its type. One whose
arguments are made of its own type parameters is now the trait's one
implementation for that type, at whatever the type's own arguments make
them: where the trait is asked of `Wrap<Int>` at some argument, the
argument is made `Int`, and the implementation is found under its own name.
The solver still finds it by a name and a head, so what is proved of it
holds.

- **No other implementation of the trait for that type**: `impl From<Int>
  for Wrap<Str>` beside it is refused, since which applies would depend on
  more than the head.

## `..` in a pattern

`Rect(w, ..)`, `P(.., z)` and `P(a, .., d)` stand for the fields of a
constructor that are not written, each let go as `_` lets one go. It is
written out where names are given their meaning, from how many fields the
constructor was declared with; a name given to a constructor (`Some(..)`)
is that constructor, and a pattern that binds by reference may use it.

- **Not of a tuple.** How many parts a tuple has is known only once types
  are, and a pattern is read by everything that counts uses and borrows
  before that. `(a, ..)` is refused, with the reason.
- **Not of an array.** An array's pattern is for one length; `[first, ..]`
  would be for every length from one up, which the machine's patterns do
  not have.

## Generators

`std::generator` has the specification's generators (30.2): the effects
`Yield<Y, R>` and `YieldOnce<Y, R>`, `GeneratorStep`, the `Generator` trait,
and `Coroutine<Y, R, T>`, which is a computation that yields, stopped where
it last did. `generator(body)` makes one, `resume` uses it up and gives what
it yielded with the generator that goes on, or what it finished with.
`iterate` makes one that is resumed with nothing into an iterator, so an
endless generator can be taken from: `take(iterate(generator(..)), 4)`.
None of it is known to the compiler: a generator is a resumption in a
struct.

- **What a generator is resumed with is left to the implementation**
  (`type Resume`), where the specification has `Generator<R>`. The language
  takes the specification's form since "Trait arguments of an
  implementation's own" below; the library keeps `type Resume` because
  `iterate` needs a condition that names the trait, and a condition of an
  implementation names a trait without arguments.
- **A coroutine's body performs `Yield` and nothing else.** The row of its
  other effects would be a parameter of `Coroutine`, and a declared type
  has no row parameters.
- **A generator let go is forgotten where it stopped**; `close_generator`
  gives it up and runs its cleanups. Making letting go do that was tried,
  with `Drop` for `Coroutine`, and works; it is not kept because a `Drop`
  in the library makes every program that uses the library one that counts
  uses and destroys values, which costs each of them.

That attempt found two faults in programs that have a `Drop` of their own
and use the library, both fixed:

- An implementation for a type with a lifetime parameter was given a
  condition that the lifetime can be destroyed, which nothing can meet:
  "`'_` does not implement `%Destroy`" for any such program that iterated
  a slice.
- **What a clause does not use is destroyed when the clause is done**, by a
  cleanup, and a `tail` call cannot have a cleanup after it: so a function
  generic in a type that ignored a value and then called itself with `tail`
  was refused once any type had `Drop`. Where a clause or the rest of a
  block has a `tail` call in it, what it does not use is now destroyed
  first, before the body: the specification has the cleanup of a `tail`
  call before the transfer (12.2).

## What a trait's function performs

A trait's function performed nothing: an implementation that performed an
effect was refused, whatever the trait said, and the trait could say nothing.
Now it can, in two ways.

- **A row written on the function.** `fn emit(Self) / {Out};`. Every
  implementation may perform those effects and no others, and a use of the
  function performs them.
- **A row left to the implementation** (the specification's associated
  effect rows, 13.1 and the library's stream traits). The trait declares
  `type Effects: EffectRow;` and its functions write
  `/ { | Self::Effects }`; an implementation says `type Effects = {};` or
  `type Effects = {Console};`. A generic function writes
  `/ { | <W as Write>::Effects }`, or `W::Effects` where one trait only
  has that name, and performs whatever the type it is used at says: nothing
  for a stream in memory, the host's effect for standard output.

How it is done: such a row is held as a type the trait leaves to the
implementation, the type of a callable that takes nothing, gives nothing and
performs the row. So everything that was there for those types, the
question asked once per type and answered by the implementation, carries the
row. `<T as Trait>::Name` is new syntax for both kinds.

- A name is taken to be a row if one of the trait's functions writes it
  after `|`; what is written after `type Effects:` is read and not kept.
- **One row after `|`.** A function over a reader and a writer would perform
  both their rows, and a row has one unknown part: the specification's
  `copy_stream` cannot be given its type.
- A callable among a trait function's parameters still performs nothing.

`std::stream` has the specification's `Read` and `Write` (28) in this shape,
with `MemoryCursor`, `Stdout`, `Stderr`, `Stdin`, `write_all`, `write_str`
and `read_to_end`. Reading gives the bytes read instead of filling a buffer
it is lent, since there is no slice for writing.

## Exactly once is resumed

**Changed.** A resumption of an operation declared `[1, 1]` had to be used,
and `cancel(k)` counted as a use: resumed or cancelled, each written out. So
performing such an operation might not come back, and a value that has to be
used could not wait across it. The specification means something else by
exact one-shot (10.6): the resumption is invoked, a computation suspended on
it can carry what a cancellable one cannot, and its required cases L33 and
S90 ask for exactly that.

Now `[1, 1]` means resumed. `cancel` given such a resumption is refused, as
letting it go already was. Performing an operation declared `[1, 1]` comes
back, so a value that has to be used may wait across it, and across a call
of a callable that performs only such operations.

- An operation that says nothing is as before: its resumption may be
  resumed, cancelled with `cancel`, or let go by an arm, which cancels it.
  A generator that can be stopped early is this kind; `examples/generators`
  now is.
- What makes this hold is the rule for any value that has to be used: a
  resumption of a `[1, 1]` operation cannot be dropped, ignored by a
  pattern, left in a variable, kept by a callable that may not run, or held
  while something runs that may not come back. That is the unproved
  checker's rule, as before; Core is told nothing of it.
- A resumption that is let go somewhere other than its arm is given up there
  (see "Callables say how they are destroyed"), so its cleanups run, in a
  program that has a `drop` or a `defer` to run; in any other there is
  nothing for them to do.

## The library specification's required cases

The library specification lists ninety-six (33). Most are about modules this
library does not have. Those that could be tried against what there is are
kept among the cases under "Library conformance S..": S01 to S03, S07, S09,
S12, S20, S31, S33, S36 and S53 are met as tried.

With the modules added since, more of them have cases: S06 and S44 (a
`Vec`, an arena and an undo log of values that have to be used, pushed,
popped and taken back), S08 and S09 (both branches giving a borrowed
variable away; one branch not), S14 (two callables with different rows
given to one function), S42 (`Vec::insert` gives the item back), S67
(`CStr` checks its zero, `to_str` its UTF-8), S70 and S71 (`ByteReader`),
S72 to S74 (`Arena`, `GenArena`, `Interner`), S75 (`SourceMap`), S76
(charges and permits), S77 and S78 (`attempt`, `many`), S79 (graphs under
a step budget), S83 (`write_all`, `copy_stream`), S89 and S90 (`Yield`,
`YieldOnce`), S93 (`cancel_task` gives what was made).

Not tried, for want of the module: S60 to S62 (streaming hashes, BLAKE3,
fingerprints), S64 (bounded diagnostics), S84 to S87 (buffered writers,
files and children, paths, clocks by domain), S91, S92, S94, S95 (futures,
`await`, linear tasks, poll contexts).

- **S02** was not: `true` and `false` were names for `Ok(())` and `Err(())`
  at any error type, so `true` could be given where a `Result<(), Str>` was
  wanted. They are now written with their type, `Result<(), ()>`, as the
  specification's constants are. `Some` stays a name for `Ok` itself, as
  the specification has it.
- A name given to a constructor can be written with a type,
  `let Just: fn(_) -> Result<_, ()> = Ok;`: it builds at that type, and in a
  pattern it is still the constructor.
- **S44.** `pop` used its array twice, once to ask its length, so an array
  of values that have to be used could not be emptied. It now takes the
  array apart by pattern, and asking an array's length is no longer counted
  as a use of it, since nothing is taken. (A `Vec` of such values in a
  mutable variable could then still not be given away once it had been
  pushed to; see "Written, then given away" and "Collections of what has
  to be used".)
- **S06.** `replace` asks nothing of the type, and neither does `swap`,
  which the compiler knows as it knows `replace`: it is a read of the second
  place, an exchange with the first, and a write to the second. Core's rule
  for a read wants a type that can be copied, which in Core is any type
  with no resumption or callable inside; a program that swaps one of those
  is accepted and not certified as well owned.
- `std::ffi` has the specification's `Layout` and `Allocation` (22.1):
  `Layout::from_size_align`, `extend`, `padded`; `allocate`; and
  `Allocation::as_ptr`, `layout` and `release`. An `Allocation` has to be
  used: it cannot be let go, only released. Sizes are whole numbers, and
  there is no `Layout::of<T>`, since values are not laid out flat.
- `core::value` has the specification's `Either`, `Rejected`, `identity`,
  `Default` and `take` (3). `Default` is given for `Int`, `Str` and
  `Option<A>`, which covers `Bool`.

## Callables say how they are destroyed

A callable that captured a value with a `drop` to run used to be refused unless
it was certainly called, since nothing destroyed what a callable held. Now a
closure may say how it is destroyed, and one let go without being called is
given up, which destroys what it captured.

- **Core.** `Program.drops` names, for some functions, the function that
  destroys a closure of it: `cancel` of such a closure calls it with the
  captures as arguments. Any other closure is still given up with nothing done.
  The bytecode machine and the Rust VM do the same (format version 6). The
  cancel rule now takes a callable of any arity. Proved: the bytecode
  simulation, the cleanup account, type safety and cell ownership.
  `ProgramOk.drops` asks that a destructor has `dropSig` of every signature of
  its function: no captures, the captures as parameters, the closure's regions,
  unit, nothing performed and no region touched. The proved checker checks it.
- **Front end.** The checker asks how each value a callable captures is
  destroyed, keyed by the callable as written (its hash) and the name, since a
  statement's position is not restored after a nested block. `untrait` wraps such
  a callable as `%destroyed(callable, { destroy each capture })`. The elaborator
  makes the destructor from that block, with the closure's captures as its
  parameters, and records the pair in `drops`. Callables are destroyed (the
  `(callable)` destroyer) by `cancel`, written in place where the type is known.
- **Inference.** A destructor gets an entry at `dropSig` of each of its
  closure's entries: inferred at the regions the captures mention, then given
  all the closure's. A `cancel` of a callable whose type is not yet known is
  settled when the function's body has been read. Still unknown, it is a
  resumption's (one argument), except in the generic destroyer, in destructors,
  or where it is a capture: then the arity is the one every closure made of the
  function gives there (`captureArities`), or it is left to each use.
- **Ownership.** A callable kept by `let` that captures a value has it: the
  count of paths that use the value treats the capture as a use, and the
  callable is then counted as any value is (used on every path, or given up
  with `cancel`). Callables passed straight to a function are not changed:
  that function might let one go without destroying it, so a value one
  captures is still counted on the paths that call it.
- **Limits.** A cleanup and a destructor perform nothing, and giving up a
  callable requires that what it performs could be performed. A callable that
  performs operations is therefore refused where it would be let go at the end
  of its block; `cancel` before then works. A value of a type the function is
  generic in that a callable captures is destroyed by the callable in the
  program's own functions (the function is given how, and the callable
  captures that; one used on some paths only is refused, with `cancel` as the
  way out); in the library's, it is not. A callable in a field of a value is not given up when the value is destroyed
  unless the field's type is known to need it.

## A value used on one path only is kept in a variable

The specification allows a value to be moved on one path and not on another
(path-sensitive initialization). A `let mut` variable already did this: a flag
set where its value is given away, and its cleanup destroying the value where
it was not. A plain `let` whose value has a `drop` to run and is used on some
paths only was refused with the advice to write `let mut`.

Now the compiler takes that advice itself. The refusal carries a marker naming
the function, the place of the `let` and the name; the driver rewrites that one
`let x = e` as `let mut x = e` and checks the program again (within the same
bound as the re-reading for `..` in a pattern). If the program is still refused,
what is said is the first refusal, not what the rewritten program got wrong.
A parameter is kept in a variable at the start of its clause (`let mut n = n`),
and a name a pattern binds straight after the pattern's `let`.

So is a value of a type the function is generic in (not a reference or a
callable), used on one path and not on another, in the program's own
functions: `fn choose<T>(c, a: T, b: T) -> T { if(c) { a } else { b } }`
destroyed the one not chosen only where `T` was known to have a `drop`, that
is never. Kept in a variable, it is destroyed where it was not used, by how
`T` is destroyed, which the function is then given. The library's generic
functions are not rewritten so; they are written to use what they are given
on every path. A field taken out of such a value on one path is refused, as it is of a
`let mut` (`replace` takes it out).

## A tuple variable whose fields are borrowed apart is a variable per field

Core lends a whole cell, so two fields of one variable lent at once
(`swap(&mut x.0, &mut x.1)`, a handler reading `x.1` while `x.0` is lent) were
kept apart only by the unproved check of the source. Rather than give Core
lends of parts of a cell (a region per field, `allowed` and the grants told
apart by path; the proofs of borrows all touched), the program's own
`let mut x = (a, b, ..)` whose fields are borrowed is now, before checking,
one variable per field: `x.0`, `x.1`, .. (`Elab.splitFieldVars`). `x.i` is the
variable, `&mut x.i.rest` borrows it, reading `x` reads every field into a
tuple, and assigning `x` takes the value apart and assigns each. A variable
used any other way (borrowed whole, say) is left as it is. So each field is a
cell of its own, and the borrows are lends of different cells, which Core's
rules show apart. In the test programs 12 more borrows are scopes of their own
(1330; 89 are not, in 53 programs, from 99 in 59).

A struct variable made by its constructor, `let mut c = C { n: 1, m: 2 }`,
is split the same way, its variables named by the fields (`c.n`), where the
struct has no `Drop` (whose value only its own `drop` may take apart).

Limits: only a variable made by writing out its tuple or its struct; the
library is not split: it is checked once for every program.

(Found while testing what is destroyed: one field taken of a value that is in
no variable, `f(x).0`, lets the other fields go. Where their types are known
and one has a `drop`, that is refused; in a function generic in their types it
is not seen, and nothing destroys them. `Vec::truncate` did this, and now
takes the pair apart with a pattern, whose `_` destroys. The general case is
not built: the elaborator would have to destroy the other fields there, which
asks the function for how to destroy its type parameter where it may not be
asked anything yet.) What the checker says names the field's variable
(`x.0` is read while ..), which is what is meant.

## A resumption let go is given up

A resumption that is let go other than by its arm (kept in a variable that is
then let go, handed to a function that ignores it, left in a value that is
destroyed) was forgotten: the cleanups and `drop`s of the computation it
suspended never ran. A callable type that holds a resumption now needs
destroying as one that holds a value with a `drop` does, and is destroyed the
same way, by `cancel`. The destroying machinery is written for a program that
has a `Drop` or, now, a `defer`; in any other, giving up a resumption has
nothing to run.

An arm that does not use its resumption still gives it up as it starts, before
its body: the checker leaves out of what the arm's end destroys a resumption
the arm does not name or names `_`, and the elaborator does not count what it
wrote to destroy one as a use. Giving one up where nothing may be performed (a
cleanup) needs what it performs to be nothing, as for any callable; where it
performs something, it is refused, with `cancel` before as the way out.

## An effect's operation can name what a trait leaves

`effect Fetch<S: Source> { fetch(S) -> S::Out }`: what an operation gives or
takes may be a type a trait leaves to an implementation of the effect's type
parameter. Two things were missing. The traits were declared after the
effects, so `S::Out` found no trait leaving `Out`; the shapes of traits (their
arity and what they leave) are now known before anything else is declared.
And the type was asked once, at the declaration, so every use shared one
answer; it is now kept as written (`projMark`, as an implementation's own
projections are) and asked at each use, of the type that use gives
(`unproject` where an operation is performed or handled).

Where several traits leave an `Out` (the library's `Future` and others leave
`Output`), the one written of the parameter, `effect Await<F: Future>`, is
the one asked; `<F as Future>::Output` says it too.

## An implementation is given how to destroy its nested type parameters

`impl<H, R> Columns for (Column<H>, R)` was given how each argument of its
head is destroyed (`Column<H>`, `R`), but not `H`, which is inside one: a value
of `H` its functions let go (covey's `despawn`, which removes an entity's
component from each column) found no way to destroy it, and was let go with
nothing run. Where values are destroyed, such an implementation now asks how
each of its type parameters that is no argument of its head is destroyed, as a
condition of its own (`extra`), answered where it is used: every type has
that answer.

## Cleanups left undone are counted in every test program

`Core.cleanup_accounting` says that when a program finishes, the cleanups it
installed are those it started and those left in resumptions never taken.
What is not proved is that the last are none. The test programs now say it of
themselves: each that runs on the Core machine is run again counting
(`Driver.cleanupsOf`, `glorious cleanups FILE`), and the test summary says how
many install cleanups and how many leave one in a resumption never taken.
With resumptions let go now given up (see "A resumption let go is given
up"), 203 install cleanups and none leaves one. This is measured, not proved.

## How a value is destroyed is not a condition left to explain

A system registered under a label is kept in an `On<Tick, fn(..)>`, and
`Dispatch` of the systems, a tuple, has a condition in a program with a
`drop`: how each is destroyed. That is found by the type's shape alone, and
was; but where the implementation was chosen by fitting, what a call needs
was gone through by `leavesFitting`, which looked for an implementation of
`%Destroy` for a function's type as for any trait, found none, and refused the
program (covey with a component with a `drop` and a system). It now asks
`solveFitting` first, as `leaves` does in effect, and nothing is left of how a
value is destroyed. A missing implementation says now what needed it:
`` `()` does not implement `Get<Health>`, which `Get` of `(Column<Position>,
())` needs ``.

## Giving up a callable needs only what it touches outside its own regions

`cancel k` was typed only where the function doing it may touch every region
`k`'s type says a call touches. A callable that takes references,
`fn(&mut Column<Life>, &mut Commands)`, binds the regions of those, and its
type says a call touches them: regions chosen at each call, which no function
may be granted. So the function that destroys any callable (`%destroy` at
`(callable)`) failed the region rules whenever it was used at such a type, and
the program with it (covey with a component with a `drop` and a system).
The rule (`HasTm.cancel`) now asks `SubFree n acc ϕ`: what a call touches that
is none of the type's own `n` regions. A resumption and a label bind none, so
for them it is `Sub` as before, which is what giving up a resumption, whose
cleanups run, needs (`Safety`); a closure's destructor touches nothing
(`dropSig`). Proofs updated: `SubFree.inst`, `Rgn.freeOf_of_mem_parts_inst`,
`subFreeB_sound`.

## A destructor may touch what its closure's calls touch

A closure's destructor gives up what the closure captured; giving up a
resumption runs its cleanups, which touch what the resumption touches. The
destructor was required to touch nothing (`acc = []`), so a closure holding a
resumption that touches a variable could not be destroyed under the region
rules. `ProgramOk.drops` now asks `sigd.acc = sig.acc.filter Rgn.free`: what a
call of the closure touches of the regions it was made with, none chosen at
a call. `cancel` asks in turn that what its callable's type touches has no
repeats where loans are checked, as a call does, and `Safety` grants the
destructor's call from `cancel`'s `SubFree` (`Rgn.flat_map_filter_sublist`,
`InjOn.nodup_free`, `Rgn.freeOf_of_free`).

Inference had to follow. A destructor was instantiated at the closure's
signature with no regions given for those fixed when the closure was made, so
each was a fresh one, not one of the signature's (`freshAtom` now, one each).
And a function that gives up a callable whose type it does not fix
(`fn drop_it(c: fn() -> Int) { cancel(c); .. }`, the destroyer of any
callable) touched nothing of it: the type was still unknown when the group was
settled. Such a cancel is now kept with the group's scheme (`givenUpOpen`),
its records left open, and taken on by each user (`refSig`) and each
instantiation, where the type is known; except where that type binds regions
of its own, whose touches are not told apart from the rest here. Check 94: a
closure holding a resumption whose cleanup writes a variable, given up by
`drop_it`, is shown to keep the region rules. `examples/tasks.glorious` is
still not: a closure kept in a data type's field is given a type that touches
nothing, and its regions fall back to `cell0`; a data type with regions of its
own would be needed.

## Indexing through references, and a `Vec`

`a[i]` was of arrays held in variables (and fields through references): a
function given `a: &mut [T]` could not write `a[i] = v`, read `a[i]`, or
write `a[i].f = v` (`(*a)[i]` it could), and a `Vec` could not be indexed at
all. Now:

- `&a[i]` and `a[i] = v` borrow the element with `element_at` and
  `place_at`, which are the functions of two prelude traits, `Indexed` and
  `IndexedMut: Indexed` (with `size_at`), implemented for arrays, `[T; N]`,
  `Vec`, and `&A` / `&mut A` of any of them, through the reference. (As a
  generic function over the trait, `place_at` lost covey's `spawning` its
  region certificate: the call went through the trait's evidence. As the
  trait's own function it is chosen by the type, as `index` is.)
- `a[i]` reads by `Index`, now also of `Vec` and of `&A` / `&mut A` for any
  `A: Indexed`; `len` of `&A` / `&mut A` likewise.
- `a[i].f = v` writes the field through a borrow of the element.
- `&mut a`, where `a` is no mutable variable but holds a `&mut` reference, is
  a reborrow of what it is to (`&mut *a`), as the element borrow of `a[i] = v`
  needs; Rust refuses it.

Dot calls stay as they were: `v.push(x)` is the prelude's `push` of arrays,
and `Vec::push(&mut v, x)` is how a `Vec` grows (the specification makes it
the canonical call and leaves method sugar out).

## A braced block a clause ends with: the refusal says what it is

`Err(e) => { say(e); 0 - 1 }` is a clause whose result is a callable: braces
make one wherever a block is not a call's argument or an operand (5.4), and a
clause's result is neither. Written by habit from Rust, it was refused with
`expected Int, found fn() -> Int`, or a mismatch of the whole `match`. Both
refusals now add that such a block is a callable and that its statements are
written without the braces to be run there. The rule itself is unchanged.

## `**r`, `&**r`, `&&T`, and matching a reference

The lexer reads a run of operator characters as one symbol, so `**r`, `&**r`
and `&&T` were refused as unknown symbols. In an expression's prefix place,
a symbol of one `&` or none followed by `*`s is now read as that many
dereferences, borrowed through if it starts with `&`; in a type, `&&` is a
reference to a reference (`&&'a mut T` gives the lifetime and `mut` to the
inner one). A prefix fixity a program declares for such a symbol still wins.

Matching a reference with patterns of a value (`match(s) { Dot => .. }` for
`s: &Shape`) was refused; see the next section.

## Matching a reference with patterns of a value

`match(s) { Dot => 0, Line(n) => *n }` for `s: &Shape` now looks at what `s`
points to and binds `n: &Int`, as Rust's binding modes have it (and
`&mut Shape` binds `&mut` references). Where a callable's clauses are checked
against a first parameter that is a reference, and some of their first
patterns are of a value (a constructor, a tuple, a constructor without fields
written as a name), the checker says which (`Syntax.refPatsMark`), and the
program is read again with those patterns written `&Pattern`
(`Elab.refPatsItems`, in `compileSourceAt`), which the language had: so the
rest is as if they were written so. A name pattern is left as it is, binding
the reference. The second reading costs only programs that need it.

`&Dot`, a constructor without fields borrowed, was taken for a variable and
refused as an unknown name; a name written with a capital is now borrowed as
a value is.

## A dot call of a type's own function, where the one in scope does not fit

`v.push(3)` for a `Vec` called the prelude's `push` of arrays: a dot call
`value.f(a)` was `f(value, a)` with whatever `f` is in scope, and a type's
own `T::f` only where no `f` is. (The specification has no dot calls; the
canonical spelling is `Vec::push(&mut v, 3)`, which stays.) The resolver,
which does not know types, now notes such calls with the types' own
functions of the name that it can see (`ModuleInfo.dotAlts`). Where the
checker finds the value's type has one of them and the function in scope does
not fit (its first parameter, its number of arguments, or the trait it is of
is not implemented for the type), it says so (`Syntax.dotOwnMark`) and the
program is read again with that call of the type's own function
(`Elab.dotOwnItems`, `%own:` in the resolver), whose receiver is then
borrowed as its first parameter says. Nothing changes where the function in
scope fits. `v.push(3); v.len()` and `p.get()` of `impl P { fn get(p: &P) }`
work; compile times of the examples are as they were.

## The specification's §6 functions, and its default prelude's library names

The prelude now has `try(r, @f)` (what `Ok` holds, or leaving for the label
with `Err`), `try_map_error`, `ensure(condition, @f, { error })`,
`some_or_leave(option, @f, { fallback })`, `abort` and `unreachable`
(the message written, then the program stops, going wrong, with no cleanup
run), `assert`, `assert_message`, `assert_eq` and `assert_ne` (of `Eq` and
`Show`; the values are read through the references, so copied). They are in
the part of the prelude that programs compiled without checking do not read.
`Fail<E>` (`fail(E) -> !`), `Report<D>` (`report(D)`) and `catch_fail(body)`
are in `std::value`, brought in by need as below (not where the text
declares the effect, or an operation of the name in an effect of its own).
`loop_at` is not built.

The specification's default prelude also has `identity`, `discard`, `Either`
(`Left`, `Right`), `Rejected`, `Ordering` (`Less`, `Equal`, `Greater`) and
`Range`, which this library keeps in `std::value`, `std::cmp` and
`std::iterator`. A program that names one of them as a word of its own, does
not declare it and does not bring it in by a path, has a `use` of it written
after its text (`Driver.stdPreludeUses`; no position in the text moves), and
the library is then read. Not where the text brings in a whole module (`::*`)
or has no library. `take` is left out: the library has five. `Range` is now
the specification's `Range<T> { pub start: T, pub end: T }`; the iterator of
whole numbers is `Range<Int>`.

A program that goes wrong reading past an array's end is said to ask a place
of an array of so many, not to apply an arithmetic intrinsic.

Compiling a program afresh, prelude included, takes 16 ms more for `hello`
(0.133 s against 0.117 s, quick build); a program whose compiled form is kept
is as fast as it was.

## `Clone`

The specification's `trait Clone { fn clone(value: &Self) -> Self; }` is in
the prelude, with implementations for `Int`, `Str`, `char`, `()` (the copy),
pairs and triples, `Result` (so `Option` and `Bool`) and arrays (each part's
clone), and `Vec` in the library. There is no derive: a program's own type
says its own. The specification's other fundamental traits stay as this
prelude has them (`Eq` with `==` of values, `Show`), not `PartialEq` with
`eq` of references or `Display`/`Debug` with a `Formatter`.

## A task board, and what it took

A program of a type with its own functions (`impl Board { fn add(b: &mut
Board, ..) }`), a `Vec` of records in a field, an effect for logging, and
early returns, written as a Rust programmer would, needed:

- `b.tasks.push(t)` where `b` is a parameter written with a reference's type:
  the field of what `b` points to is borrowed for the call (`&mut (*b).tasks`)
  where the function takes a reference first. Before, only fields of
  variables and of names known to hold values were.
- `return(Err(..), @finish)` in `Board::finish`, and `@f` in a module's
  `m::f`: a function's label answers to its name as written as well as its
  full one (the checker binds both; the elaborator opens the scope under the
  one the body uses).
- `&b.tasks[i].status`: a field of an array's element, borrowed through a
  borrow of the element (as `a[i].f = v` writes through one).

The program is a case; it is shown well owned with regions and loans, with 6
borrows that are not scopes of their own.

## A value with a `drop` is not copied out of an array or through a reference

Two ways to copy a value whose type has a `drop` were open, and each copy's
`drop` ran: `let x = a[i]` (of an array, a `Vec` through `Index`), which
also let the rest of the array go without destroying it; and `*r` in the
module that declares the type, which was allowed so that the type's `drop`
could read what it is given. Now `Index::index`'s result must be one that is
copied (`a[i]` of a `drop` type is refused, with `pop`, `remove` and `&a[i]`
said instead), and only the `drop` function itself, and the copy a clause
that binds by reference is chosen by (`*%given..`, of `byReference`, which
nothing destroys), read such a value through a reference. Two cases.

## Smaller additions of the same days

- `Vec::sort` (by `<`, stable) and `Vec::sort_by(v, { (a, b) => .. })`, in
  place, by the library's merge sort of arrays.
- `T::f(..)` for a type parameter `T` and a trait's function `f`, checked as
  `<T as Trait>::f(..)` is (the trait is the one that has `f`).
- A name bound to a whole number or a capitalized name (a constructor without
  fields, a constant) is a value for a dot call's receiver, which is then
  borrowed if the function takes a reference first.
- A dot call that is read again with a type's own function costs a fresh
  compile of the program each time (about 75 ms for a small one): the
  receiver is borrowed as the resolver decides, before checking, so the
  reading starts over from the text. Two such calls in one program cost two.

## `HashMap` changed in place, as the specification has it

`std::hash::HashMap` had, besides its functions that give a new map, an
in-place set of its own naming (`set`, `unset`, `get_ref`, `has`, `count`,
`get_mut` by key value) that copied what keys stood for. It now has the
specification's (17) instead: `HashMap::new`, `len`, `is_empty`,
`contains_key(&k)`, `get(&k) -> Option<&V>`, `get_mut(&k)`,
`insert(k, v) -> Option<V>` (what the key stood for before), `remove(&k) ->
Option<V>`, `clear`, `keys` and `into_entries`. Keys are hashed and compared
as values, so they are copied (numbers, texts); what a key stands for is
never copied, so it may have a `drop` (a replaced or removed value is given
back; the rest are destroyed with the map). Lookups look at each pair where
it is (`&(k, _)` patterns), not through `a[i].0`, which copies the element.
`entry(k)` gives `Occupied(&mut V)` or `Vacant(map, key)` (not the
specification's entry structs), with `or_insert`, `or_insert_with` and
`or_insert_default`. Iterators over references are not built. The three
cases that used the old names use these.

A dot call whose name is a function of several types' own (`a.size()` with
`A::size` and `B::size`) was refused as ambiguous; the resolver now takes the
first and tells the checker of the rest, which chooses by the value's type as
for a function in scope that does not fit (the case that expected the
refusal now gives what both calls give).

## A dot call's own function chosen without reading the program again

A dot call whose function in scope did not fit was read again from the text
with the type's own function, each such call once: a program with a dozen
map calls took a fresh compile for several of them. Now the checker, where
the resolver noted alternatives, finds the receiver's type first and checks
the call as of the type's own function where it takes its first argument as
the one in scope does (`receiverKinds`, of functions and of trait
functions), or where the one in scope takes it whole, the own one by
reference, and the receiver is a mutable variable, which is then borrowed.
What it chose (`Blocks.dotChosen`) is written into the program for what
follows (`Elab.chosenItems`). Other cases are read again as before. A
function of a type that cannot be named where it is called (`Entry`, given
by `HashMap::entry`) is found through the value too, where nothing in scope
has the name.

## More of `Vec`

`capacity`, `reserve` and `shrink_to_fit` (a `Vec` holds room for what it
holds, so the last two do nothing), `index`, `index_mut`, `first_mut`,
`last_mut`, `swap_remove`, `replace`, `swap`, `rotate_left`, `rotate_right`,
`split_off`, `resize`, `retain` (with `for<'a> fn(&'a T) -> Bool`),
`into_iter`, `finish_empty`, and, not in the specification, `contains` and
`extend` of an array. Places are `Int` and bounds errors are `()` (the
library has no `BoundsError`); `insert` keeps giving back the item where the
place is not there. Not built: the `try_` forms, slices (`as_mut_slice`,
`extend_from_slice`), `drain`, `iter_mut`, `partition`, `extract_if`,
`resize_with`.

## Truths are shown as `true` and `false`

`say(1 < 2)` wrote `Ok(())`: `Bool` is `Result<(), ()>`, and `Show` had one
implementation for every `Result`. The specification shows `Bool` as
`true`/`false` and other results with `Ok`/`Err`. The prelude now has `impl
Show for Result<(), ()>` besides the general one, and the more particular
implementation is preferred (specialization, which the checker had). An
`Option<()>` is a `Bool`, and is shown so; `Option<Int>`'s `None` is still
`Err(())`. Where the error type of an `Ok(())` is not known, which of the
two is meant is not known either, and the program says so. The expected
output of 35 test programs changed accordingly (only those lines).

## Running does not look for each borrow's scope

Most of a fresh compile of a mid-sized program went to looking, place by
place, for which borrows can be scopes of their own in Core: each try
elaborates and certifies the whole program again (`wc3` 2.08 s of which
0.53 s without it, `bank` 1.93/0.74, a map program 5.62/0.75, `calculator`
3.36/1.67, quick build). What it finds changes only the certificate, which
`run` does not use. Now `run`, `check`, `watch`, `build`, `native` and `exe`
compile without that search (`compileSource ... (search := false)`): what an
earlier compile found is asked all at once, and else no borrow is a scope of
its own (one certificate, of the plain program). `certify`, `sigs`, the server and the test suite search as
before. The kept build records whether it was searched (format version 2),
and `certify` compiles again where it was not; a compile that did not search
keeps neither its places nor its certificate for later ones.

## `impl Trait` in a function's parameters

`fn f(x: impl Show)` is `fn f<Impl0: Show>(x: Impl0)`: a type parameter of
its own per such parameter, a trait feature. Elsewhere, a result's
included, `impl Trait` is refused. `impl<T: Show> ..` asks of its
parameters what `where T: Show` does, for implementations of traits and of
a type's own functions.

## No syntax for library names, no Rust surface forms

The specification makes `if`, `match`, `loop`, `break`, `return`, `and`,
`or`, `not` and `for` ordinary library names that the compiler never reads
specially (1.1, 3.1, 8.4, 19); it has no `else if` rule (5.4), no `return`
keyword (5.5), no format macros (3.3), no macros or derive (20; library
1.4 and 2.2), and no conversion of an expression into a callable or of an
owner into a borrow because of an expected type (1.3, 5.3). Rust's forms
for these (`for x in it`, `if c {}`, `match x {}`, `else if`, `&&`, `||`,
`!`, `+=`, `return e`, `e?`, bare `break`, `|x|` callables, `if let`,
`a..b`, `P { ..base }`, `&self` receivers, `mut x` parameters,
`Fn(A) -> R`, `#[derive]`, `println!` and the like, Rust's trait names) are
refused, the common ones saying what is written instead. Dot calls stay:
they are the accepted extension, and their receiver adjustments (an
element, a field or a value made where it is called on, borrowed) apply
only to the receiver of a dot call.

## `where I::Item: Ord`

A function's `where` may ask a trait of what a trait of a type parameter
leaves to its implementation: `I::Item: Ord` is read as a type parameter of
its own, `ItemOfI: Ord`, with `I: Iterator<Item = ItemOfI>`. Only where `I`
is asked exactly one trait, which is then taken to be the one leaving `Item`.

## Modules are units, checked in order

Modules may not use each other in a circle (an earlier decision), so each
module is a unit of compilation of its own. The resolver writes a mark
before each module's items but the prelude's, and what each module uses;
the driver puts the modules in an order that has each after those it uses,
the library's before the program's (`Driver.unitsOf`). The checker checks
unit after unit (`Check.checkUnitsKept`): each unit's declarations, then its
groups, keyed by the key before it, its items, and what it reads of the
program's modules besides them (the coercions that apply in it, the dot calls
among its calls with more than one candidate, which fields of the
constructors it can see are `pub`: `Driver.unitInfoKey`). So a change to
one module leaves every unit before it, the library's above all, to be taken
from what was kept, and what was kept is kept between runs (`Glorious/Store.lean`,
the checker's states written as Lean writes `.olean` files).

This is the first part of separate compilation: what is kept is a prefix of
units in that order, not each unit apart from the others; and elaboration,
certificates and Core are still made for the whole program. A program that
declares a name the prelude has is checked the same way, the prelude its
first unit (it was checked whole, every time).

Which way of finding a certificate passed is kept too, so the next compile
tries it first (it was kept only by `certify`). Kept, it is not taken as
places a borrow was made a scope at: those start a search a `run` has no
use for.

**Kept schemes of certificate inference: tried, and not kept.** Each group's
scheme was frozen (its own unknowns renumbered from the declarations' end,
with its regions and records) and taken back by a key of the group's Core
bodies and what they call. To be sound it could be taken only for a group
whose inference left the declarations' unknowns and the waiting closures as
they were; about two thirds of the groups were. On the 14 programs measured
it made an edited run no faster (despawn 0.39 s with it, 0.40 s without;
calculator 0.65 s and 0.67 s): what is left of certificate inference after
an edit is mostly not inferring schemes. It was 400 lines; they are out.

## Executables built ahead of time; wild links

`glorious exe` (`glorious-vm --bundle`) puts at the end of the VM the program
already loaded and rewritten, and its x86-64 code with what must be filled in
when it starts: each call of a runtime entry point (by number) and each table
of instruction offsets. At start it maps the code and writes those addresses;
nothing is rewritten or compiled. This is the `aot_own` choice: our own code
section and our own loader, no linker per program; the stub is the VM.

Measured (calculator example, release VM, median of 9): `glorious-vm` on the
bytecode, rewriting and compiling at start, 0.061 s; the executable built
ahead of time 0.013 s. Before this, the rewrite itself took 0.26 s of a 0.26 s
run: liveness was a hash set per instruction rebuilt every pass, and `sweep`
ran it once per layer of dead code. It is now bit sets, and one sweep with
"faint" liveness (an instruction that gives what nothing needs reads nothing).

Cost: the executable holds the rewritten program and its code, not the
bytecode: 4.5 MB for the calculator (0.9 MB VM, 0.27 MB rewritten program,
3.0 MB code, 0.28 MB relocations and tables) against 0.9 MB before. The
rewriting inlines heavily (15 KB of bytecode becomes 271 KB); the JIT made the
same code at every start.

The LLVM path links with wild where it is installed (`glorious native`,
`vm/check-backends.sh`). Measured linking the calculator's object with the
runtime library (median of 5): system `ld` 0.124 s, wild 0.029 s, lld 0.042 s,
mold 0.048 s. The VM, which is the stub, is linked with wild through clang
(`vm/.cargo/config.toml`; both must be on the PATH to build it).

## Implementations for callables: `impl<F: Fn<..>> Trait for F`

A type parameter of an implementation that is said to be a callable,
`impl<F: Fn<(A, B), Output = R, Effects = {E}>>` or `where F: Fn<..>` (also
`RunsIn`), is that callable's type, `fn(A, B) -> R / {E}`, wherever the
implementation's head and conditions write it. This happens in the parser,
before anything else reads the implementation. Where `Output` is not said, the
result is a type parameter of the implementation's own; where `Effects` is
not said, the callable performs nothing, as `fn(..) -> R` in a head always
meant. `(..P)` works, so covey's `System` and `CallWith` are now
`impl<.., F> System<E, S> for F where F: Fn<(..P), Output = ()>`. `F` is not
named inside the functions; `Self` is. `Self` in an implementation's
function is now the type the implementation is for (before, it was unknown).

This is the first step. Callables still have one structural type each, so
`F` is a signature, not a single item's identity. The agreed next step gives
each item and closure a type of its own, which converts implicitly to the
structural type, as Rust's items do to function pointers.

Found while doing this: what the checker kept from an earlier compile
(`checked`) carried that compile's implementation functions. Declarations
are keyed without bodies, and a state taken from a group is the whole state,
so an implementation function that was checked again was checked with the old
text. Call identities are token positions, so after an edit above it the
elaborator found no record for the new call (`unknown name ecs::dispatch`
after a body edit in covey). Every state taken from what was kept now has
this program's implementation functions put in, matched by order and trait
(`withImplBodies`); where they do not line up, nothing is taken. Checks 95
and 96 compile a program with what was kept of a version that differs in one
body, both ways, and fail without the fix.

## Certificate inference keeps its instantiations

Inferring a certificate instantiates each function's group at each signature
it is used at (`Infer.instantiate`): the group's scheme is copied, solved at
that signature, and its entries and the uses of other functions it asks for
come out. That depends on the group's Core, what is known of its functions
(handler arms, capture counts, destructors), the functions it refers to, and
the program's declarations and rules, and on nothing else. Each function now
has a key made of those (`fnKeys`: per group, with the keys of the groups it
refers to). What each instantiation gave is kept by key and signature in the
build directory (`infer`). A later compile that instantiates a function
with the same key at the same signature gives the same entries again, and
asks for the same uses, with fresh regions for each one the use had.

The proved checker checks the result like any other certificate. Where it
turns it away, or inference fails with what was kept, the certificate is
looked for afresh, so what is kept can make a compile faster but never
different. Keys use Core's function numbers, so adding a function before
others makes those others miss: a miss is only slower.

Measured (edit of `main`, quick build, median of 3, without the kept
instantiations → with them): calculator 0.79 → 0.66 s, orders 0.93 → 0.65 s,
simulation 0.92 → 0.65 s, query 0.70 → 0.54 s, despawn 0.49 → 0.42 s,
spawning 0.50 → 0.43 s, json 0.45 → 0.43 s, shapes 0.27 → 0.25 s. What is
left of certificate inference after an edit is mostly the schemes of the
functions `main` calls (30% of the simulation's run). Checking the prelude
in every process is 12%, and reading the library 8%.

## The prelude as checked is kept for every program

Each process checked the prelude (and, where a program has the whole
library, the library) before the program: 12% of an edited simulation's
compile. The state after that check is now kept in the user's cache
(`~/.cache/glorious/library/first-{std}-{drop}`, written as the other kept
states are and read only by the compiler that wrote it), and a compile takes
it from there. It is shared by every program, so a program's first compile
gains too.

Measured (edit of `main`, quick build, median of 3, before → after):
simulation 0.65 → 0.55 s, calculator 0.66 → 0.50 s, shapes 0.25 → 0.15 s.

## Implementations for every type: `impl<T: Num> Double for T`

An implementation whose head is one of its type parameters is written out,
after parsing and before checking (`Syntax.expandBlankets`), as one
implementation for each type that has an implementation of every trait it
asks of `T`. Every type is a candidate when it asks none: Int, the scalars,
each declared type, tuples of up to 8 parts, callables of up to 6 parameters,
and both references. The copy for `Option` is
`impl<A> Double for Option<A> where Option<A>: Num`. A copy is not made for
a type that already has an implementation of the trait at the same trait
arguments for its head, nor for one with `impl !Double for H {}`. Chains of
these (`impl<T: B> C for T` over `impl<T: A> B for T`) are written out
round by round. In each copy, `T` in the functions is the type it is for
(`%blanket:T`, put in the function's type scope with `Self`), and its call
identities are moved so that copies are told apart.

**Specialization.** A type with its own implementation keeps it. One with an
implementation for some of its arguments (`impl Double for Option<Int>`) has
both, and the existing rule chooses the one that asks more of the type. A
function generic in `T` that says `T: Num` may use `Double` of `T`: the
blanket mark (`St.blanketTraits`) lets the need go to its callers, where it
is met by the implementation for the type the function is used at. So
`fn via<T: Num>(t: &T) { describe(t) }` used at `Int` runs `Int`'s own
`describe`, as Rust's specialization does with monomorphization. This keeps
dictionary passing coherent: no generic site chooses the blanket copy for a
type that has a narrower one.

Limits:
- A blanket implementation in the prelude or library is not written out for
  a program's own types. There is none.
- Two blanket implementations of one trait at the same arguments that are
  both written out for a type are two implementations of it for that type,
  which the checker refuses (`Show` is implemented twice for `Int`).
- The copies come after everything else, in the last unit.

## Certificate attempts after the first run in parallel

`certifyProgram` tries ways of finding a certificate in order: rules from
strictest to weakest, each with up to four ways of reading callables and
references. Once one passes, its number is kept, so the next compile tries
it first. On a fresh build of a program that passes only with a later way,
every earlier way ran one after another (despawn: 9 attempts). Now the
first (kept or 0) runs alone, and if it fails, all the others start at once,
each as a `Task`; the first of them in order that passes is taken, so the
result is the same as before. Attempts that are not needed keep running in
the background until they finish or the process ends.

Measured (fresh build, quick build, median of 3, before → after): despawn
1.35 → 0.76 s; json 0.44 → 0.48 s (two attempts: the second waits while
the others use the machine); simulation 0.90 → 0.90 s (one attempt).

## The library's modules, checked once for every program

What the checker keeps of each unit is keyed by the unit and every unit
before it. The library's modules come first, so their states depend only on
the library and the seed (whether the library and `Drop` are in), and not on
the program. The states of the leading `std` units
(`Check.checkUnitsKept (library := n)`) are now also kept in the user's
cache (`~/.cache/glorious/library/units`, newest first, at most 32), and
every compile adds them to what its own build directory kept. A program's
first build then takes the library modules another program checked.

This is separate compilation where it pays off now. Checking the program's
own modules side by side would mean merging checker states that grew from
one start: every id counter given a range of its own, the chunked id stores
made sparse, and a merge rule for each of about 150 fields. The programs
here have chains of modules (covey: prelude → `std::tuple` → `ecs` → main),
so there is nothing to check side by side yet. That is left for when there
is.

Measured (fresh build directory, quick build; first ever → with another
program's library modules kept): calculator 1.22 → 1.02 s, orders 1.01 →
0.89 s; simulation 0.90 → 0.89 s and json 0.46 → 0.47 s (their library
modules are small). The file is 1.3 MB after four programs.

## Certificate inference keeps groups' schemes

A group's scheme (`Infer.schemeOf`) is now kept by the group's key
alongside the instantiations, in the build directory's `infer`. It is kept
only where inferring it changed none of the declarations' variables and
decided none of the closures other groups left waiting. Freezing renumbers
the scheme's own variables from `frozenBase` and keeps the declarations' as
they are. With them go the records of what its callables touch, which of
its regions are cells or bound by callables, what its regions stand for, the
records others may add to, and the closures it leaves waiting itself. A
scheme naming any other variable is not kept. A later compile that meets
the key thaws it (fresh variables for its own) and infers nothing, not even
the groups the scheme was inferred from. The proved checker checks the
result as before, and a certificate it turns away is looked for afresh.

On the first build of the simulation, 98 groups could be kept and 179 not,
because they left closures waiting. Keeping what a group leaves waiting
made the rest keepable.

One traversal (`Ren`: what to do with each kind of variable) now renames
schemes for copies at uses (`copyRen`), for freezing and for thawing.
Before, the copy functions were written out one per kind of term. The two
certify entry points are one (`certifyKept`; `certify` takes the
certificate from it), and the driver's three certificate helpers are one
(`certifyWith`), which says whether the checker accepted, so nothing is
checked twice.

Measured (quick build, median of 3; edit of `main`, kept instantiations
only → with kept schemes): simulation 0.55 → 0.37 s, orders 0.65 → 0.39 s,
calculator 0.50 → 0.40 s, query 0.54 → 0.32 s, despawn 0.42 → 0.30 s, json
0.43 → 0.28 s, shapes 0.15 → 0.15 s. Fresh builds pay for freezing (4% of
the simulation's) and a larger file: simulation 0.90 → 1.01 s, calculator
1.02 → 1.07 s, json 0.47 → 0.51 s.

## Notes: what makes Jai's compiler fast, and what applies here

Sources:
- The Way to Jai, ch. 4: https://github.com/Ivo-Balbaert/The_Way_to_Jai/blob/main/book/04A_More_info_about_the_compiler.md
- An independent Jai compiler's measured compile-speed notes (jacket):
  https://github.com/matteopolak/jacket/blob/main/docs/compiler/compile-speed.md

What they report:
- Front end for ~10k lines: about 0.025–0.08 s. Typical debug builds up to
  250k lines under 1 s. Link is often the largest part (0.25–0.33 s of 0.32–0.43 s).
- No processing in source order: declarations are worked on as jobs, which
  wait on what they need (no forward declarations) and run on a job
  system across threads.
- One internal bytecode, then either a naive x64 backend written for speed
  (no optimization) or LLVM for release.
- A hand-written recursive-descent parser.
- jacket, measured:
  - lexing and parsing on worker threads ahead of semantic analysis;
  - one interner that hashes a spelling once;
  - 40-byte tokens;
  - word compares for punctuation;
  - code that only compile-time execution runs is not lowered;
  - failure paths compiled without optimization;
  - codegen split into units per core;
  - memory leaked at exit (no teardown);
  - mimalloc (about 8% overall).
  Rejected after measuring: a bump arena (+2–3%) and early import discovery.

What carries over to Glorious, by what it costs us now (an edit
recompile of the simulation: about 0.37 s):
- Our time is in checking and certificate inference, which Jai does not
  have: those are where the job idea applies. Groups of functions (and
  modules) as jobs that wait on their callees' schemes, run on `Task`s.
  It needs per-group state that does not thread one checker state; see
  "The library's modules, checked once" for what that takes.
- Already done:
  - our own naive x86 backend with no external linker (`glorious exe`);
  - wild where we do link;
  - only what `main` reaches is elaborated into Core;
  - kept work keyed by content.
- Cheap and worth doing:
  - per-phase timings (`--timings`), as Jai and jacket print;
  - leaving the process without freeing what the compile built: tried
    (the result held in a global until exit) and measured no change (the
    frees in profiles happen during the compile, not at its end);
  - lex each text once and keep the parsed library;
  - lex and parse modules on `Task`s.
- Parser micro-tuning (interning, token size): jacket found lexing and
  parsing a quarter of a check of 600k generated lines and got 9% from
  the lexer work. For us they are about 9% of an edit recompile, so the
  repeated work (each text lexed about four times) comes first.

## Start-up: 22 of 26 ms is Lean setting itself up (parked)

A `glorious` process takes 26 ms before `main` does anything (optimized
build). Nearly all of it is `lean_initialize`: the C that Lean writes calls
it, in place of initializing only the runtime, whenever any module imported is
`Lean`'s. Our only such import is `Lean.CompactedRegion` (the kept states'
file format). That sets up all of Lean, its parser tables included
(`Lean.Parser.addBuiltinParser` in the profile).

Declaring the two entry points (`lean_compacted_region_save`/`_read`) in
`Store.lean` without the import brought start-up to 4 ms, but the save then
crashed: it needs what `lean_initialize` sets up. A compile then kept
nothing, and each was as slow as a first build. Reverted.

Ways left:
- Our own format for kept states, which is a large serializer.
- Calling the full initializer only before the first save or load, which
  needs a C shim and running Lean's initializers after start, which they
  may refuse.

Parked: 22 ms is about 8% of an edit recompile of the simulation (0.27 s).

## A unit that is the same is kept whole, and only whole

`Check.checkItems` keys the unit's final state by every item whole
(`mixHash seed (hash items)`); `checkUnitsKept` chains the next unit from
that key. Where the key is kept, the unit is set to that state at once and
nothing else of it is looked up or kept. Only a unit that changed keeps a
state per step (declarations, each group, each implementation function).
Kept states fell from 229 to 14 for the simulation after one edit, and
`checked` from 6.3 MB to 1.4 MB.

Saving the checker's states had become the largest single cost of an edit
recompile: 64 of 277 ms for the simulation (optimized build). The compactor
walks every object of every state.

Cost: the first compile after editing a unit that had been kept whole checks
that unit from its start, not from the edited group. From then on its steps
are kept again.

Measured (optimized build, edit of `main`, median of 5, before → after):
simulation 0.27 → 0.20 s, calculator 0.31 → 0.17 s, orders 0.22 → 0.20 s,
despawn 0.21 → 0.15 s, json 0.20 → 0.11 s, shapes 0.10 → 0.09 s.

## Modules that do not use each other are checked side by side

`Check.checkUnitsKept` takes for each unit the units before it that it uses
(`deps`, from the resolver's `unitUses`), and groups the units into levels:
each one more than the highest level of what it uses. A level of one unit is
checked as before. A level of several is checked side by side, a `Task`
each, every one from the state before the level. The `j`-th numbers its
new ids from `j` gaps (`unitGap`, 2^20) above:
- the type, row, capture and edge stores;
- loans;
- rigid keys;
- brands.

Then what each added is put together (`mergeStates`), with a rule for each
of the checker state's 144 fields:
- stores by segment and piece;
- lists and arrays grown at the front or the end;
- maps and sets by entry;
- flags by or;
- the last function's leftovers from the last unit;
- implementations' places shifted.

Each rule asks of what was there before only whether it is the same object
(`samePtr`). Where a field was changed by more than one unit, a unit's ids
ran into the next one's, or a unit was refused, the level is checked one
unit after another instead, so the result never differs from that.

The stores (`Store`) are now segments: a `jumpTo` starts one, so a gap
costs nothing. The first version padded one array of pieces across the gap,
and every later write copied it: a fresh build of the simulation went from
1 s to 7 s. Loans and rigid keys became stores, to be numbered the same way.

Kept states:
- A level put together is kept under a key of its own.
- A unit kept whole is not what this level's start grew into, so what it
  added could not be told.
- What follows a level is keyed by what its units are made of, whichever way
  they were checked.

Measured (quick build, fresh build of four sibling modules of 80 functions
each, median of 5): 0.57 s one after another, 0.40 s side by side, the check
from 231 to 93 ms. The examples have no sibling modules of their own; the
simulation's two library modules are checked side by side at no measurable
cost.

## Where a compile spends its time: `GLORIOUS_TRACE`

`Glorious.Trace.timed` times a stage, pure or not: the compiler is strict,
so the stage is computed between the two readings of the clock.
`GLORIOUS_TRACE=1` prints each stage under the one it was part of (four deep)
and the totals by name.

Stages timed:
- in Main: loading what was kept, the compile, saving what is kept;
- the driver's stages: lex, parse, resolve, aliases, defaults, check,
  lowering traits, elaborate, certify;
- each certificate way and each borrow-scope attempt;
- each unit's check.

Unset, a stage is only its computation.

## Covey toward MalekiRe/unstable_covey: what it has, and the order

The upstream is the `static-ecs` crate (about 12,000 lines of library; 19,000
with devtools), beside a window system, a UI, and demos. Covey is 672 lines.
To be one to one with `static-ecs`, in this order (each a step that compiles
and runs, with the upstream's tests for it ported as covey programs):

1. **The core API as upstream names it.**
   - `App::new().add_systems(label, systems).build()` and `app.emit(&label)`.
   - Labels with an input (`Schedule` with `In`).
   - `world.spawn_bundle`, `get`, `get_mut`, `insert`, `remove`,
     `despawn`, `query`.
   - **`Commands` deferred, applied when the emit finishes**: spawn, insert,
     remove, despawn and queue, as closures over the world.
   - `Res`/`ResMut`, `Local`.
   - `Query<D, F>` items `&T`, `&mut T`, `Entity`, `Option<D>`, `Has<T>`, with
     `iter_mut`, `for_each` and `get`; `Single`.
2. **The world inferred from the systems**: `build` gives a world storing
   exactly what the systems mention, and `register` for the rest. Then tables
   (archetypes) and `Sparse` storage, and change detection: `Mut<T>`, `Added`,
   `Changed`.
3. **Component behavior and lifecycle**:
   - `Requires`, `OneOf`, `Immutable`;
   - hooks `OnAdd`/`OnInsert`/`OnReplace`/`OnRemove` as labels;
   - `Disabled`/`Disabling`/`MayHave`;
   - states: `OnEnter`/`OnExit`/`OnTransition` and `in_state`.
4. **Plugins as types**, with their components named.
5. **Relations**: `OneToOne`/`OneToMany`/`ManyToMany`, `To`/`From` joins,
   `cascade`, and relation hooks.
6. **Composing systems**:
   - `chain`, `run_if`, `parallel`;
   - dependency graphs (`ready`, `node`, `after`) checked when compiled;
   - the executor. The VM runs one thread, so `parallel` is checked for
     disjoint access and run in order until it has workers.
7. **Async tasks and bridges, and behaviors**: on effect handlers, which is
   where Glorious differs most.

Out of scope unless asked: devtools and the MCP server, remote bridges (they
need sockets), and the window and UI crates.

## Holes covey found, and what was done

Covey is the toolbox for finding what the language lacks. Rewriting it after
`unstable_covey` found these:

- **A function that needs a trait of a type it is used at could not be a
  value.** "`age` needs a trait of a type it is used at, so it is called where
  it is named: write a block that calls it." The checker now throws a mark
  (`Syntax.etaMark`) instead. The program is read again with each naming of
  the function in that function, other than a call of it, written as a block
  that calls it with as many parameters (`Elab.etaItems`). Rust's generic
  functions as values are the same. Fixed.
- **Which implementation fits a type not all known** was decided position by
  position (`mayFit`), so `(On<E, P>, T)` was thought to perhaps fit
  `(On<Hit, ..>, ..)` asked at `E = Update`. That made the dispatch on a
  label ambiguous whenever a system's type had an unknown in it. Now an
  implementation may fit only if its variables can each be one type
  throughout (`Ty.meetAll`, the function's own type parameters left open).
  Fixed.
- **A bound of a type not yet decided** was refused where met, though meeting
  the group's other bounds could decide it. Bounds now go in rounds:
  - one of an undecided type waits;
  - what the others said of associated types is settled between rounds;
  - the fourth round refuses what is left.

  This was not enough for covey's `Commands<_>`. The world's type reached a
  system's `Commands<S>` only through the associated types `Gathered::Flat`
  and `Then::Out` of `CallWith`, which did not decide the variable. Covey now
  gathers a system's arguments flat (`Fetch<E, S, (..G), F, O>`, the next
  `(..G, X)`), which the implementations' own arguments decide. Deciding a
  variable through a chain of associated types is still open.
- **A tuple of one written out from a list** (`(..G, &mut Query<Q, N,
  St>)` with `G` empty) was counted as having parts at the commas of the type
  arguments, so it was written `(&mut Query<..>)`, a type in brackets. The
  commas inside `<..>` are now inside. Fixed.
- **A bound whose type was not known when bounds were keyed**, of a trait
  with several implementations for one head, kept the trait's plain name and
  so found the first implementation. ("No implementation of `Columns` was
  found; this is a compiler defect" for `(Resource<Ended>, ..)`.) Each bound
  now chooses among the implementations when it is met. Fixed.
- **A type's own function's own type parameters** were after the type's, so
  `app.on<E, P>(..)` gave `E, P` to `App<S, L>`. They now come first, as
  `.on::<E, P>()` gives them in Rust; a function with none of its own still
  takes the type's. Fixed.
- **A state kept from an earlier compile** brought that program's module
  facts with it, among them the alternatives of dot calls: `commands.insert`
  then stayed `World::insert`. A kept state now takes this program's
  (`adopt`). Fixed.
- **A bound a function's needs come down to, at arguments** (`S: Get<Value>`
  from `(Value,): Bundle<S>`), went into its type by name alone, and its
  arguments were lost where it was used. It is now said with them. Fixed.

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
