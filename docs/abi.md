# The ABI between compiled code and the runtime

Generation 1. This is what the x86-64 backend (`vm/src/x86.rs`), the LLVM
backend (`vm/src/llvm.rs`) and the interpreter (`vm/src/lib.rs`) agree on, so
that a function run by any of them can call, be called by, be captured in a
resumption of, and unwind through a function run by any other. A program
built for another generation is refused before any of it runs (`glo_main`).

It is the shared runtime control convention of specification 17.4: every
engine keeps a function's locals and the control stack where the runtime
keeps them. It is not the concrete layout contract of 17.2: values are the
runtime's objects, not flat records with declared offsets. See "What this is
not" at the end.

## Values

A value is 32 bytes, aligned to 16. Byte 0 is its tag.

| tag | value | bytes 8..16 | bytes 16..32 |
|---|---|---|---|
| 0 | integer | unused | the integer, 128 bits, little-endian |
| 1 | built by a constructor | pointer to the runtime's object | unused |
| 2 | closure | pointer to the runtime's object | unused |
| 3 | resumption | its number | unused |
| 4 | label | its identity | unused |
| 5 | reference | the cell's number | the path to the part, or nothing |

Compiled code may read and write integers in place: check the tag, read
bytes 16..32. An integer of type `Int` fits in 64 bits, so the high half is
the sign of the low; compiled code checks that before working in 64 bits and
falls back to the runtime if it is not so (the wide scalars use all 128).

Compiled code may move any value by copying its 32 bytes, if the place it
was copied from is then never read as that value again: it writes tag 0 over
the source. To copy a value that is not an integer it calls `glo_copy`,
which counts the new holder. Everything else about a value that is not an
integer is the runtime's: its fields, its constructor, what a reference
points to.

There is one representation. A value made by interpreted code and used by
compiled code is the same object at the same address; nothing is converted
where one kind of code calls another.

## Activations

An activation of a function is its locals: the arguments, then what the
closure captured, then one more for each instruction that gives a value, in
the order the instructions run. They are an array of values owned by the
runtime. Local `i` is at `locals + 32 * i`.

The control stack belongs to the runtime: where to return to, handlers,
label scopes, cleanups, cells. Compiled code never sees it. A call, a return,
an effect performed, a jump to a label, a resumption taken up: each is asked
of the runtime, which leaves the activation, and control comes back, if it
does, as a fresh entry into the function's body.

## A function's body

```
u64 body(Vm *vm, Value *locals, u64 pc, u64 len)
```

System V calling convention. `locals` is the activation's array with `len`
values in it and room for one more for each instruction of the function, so
it does not move while the body runs. `pc` is the instruction to start from;
a body can be entered at any instruction of its function. The result is not
looked at.

The body runs instructions from `pc`. After one that gives a value there is
one more local. It must return as soon as control has left the activation or
the machine has stopped; `glo_step` says when. Before it returns, and before
any call to `glo_step`, the runtime must be told how many locals there are:
`glo_step` takes the count, and a body only ever returns after `glo_step`
said to.

A body may do an instruction itself only if what it does is what the
interpreter does. Both backends do these themselves: an integer written out;
a local moved or copied; `+ - * < ==` on two integers that fit in 64 bits
when the result does; a test of a local against an integer; a test of a
local's constructor; a field of a local. Everything else is `glo_step`.

## The runtime's entry points

| | |
|---|---|
| `StepOut glo_step(Vm*, u64 pc, u64 len)` | Run the instruction at `pc` as the interpreter does. `StepOut` is two `u64`: a status and the number of locals. Status 0: go on with the next instruction. 2: go on with the instruction the failed test names. 1: return. |
| `void glo_copy(Value *locals, u64 i, u64 len)` | A copy of local `i` as local `len`. |
| `u64 glo_is_ctor(const Value*, u64 tag, u64 arity)` | 1 if the value was built by that constructor with that many fields. |
| `u64 glo_field(Value *locals, u64 i, u64 field, u64 len)` | A copy of a field of local `i` as local `len`; 0 if it is not there. |
| `i32 glo_main(u64 abi, const u8 *bytes, u64 size, Body *bodies, u64 count, i32 argc, char **argv)` | Run a program built ahead of time: its bytecode, and for each function its body or null. The result is the process's exit code. |

## Which engine runs a function

It is decided per function, when the program starts. `glorious-vm
--backend=interp|x86|mix FILE` interprets every function, compiles every
function to x86-64 in memory, or does the one for two functions in three and
the other for the rest.

`glorious-vm --emit-llvm FILE` writes an LLVM module with a body for every
function, the bytecode, and a `main`:

```
glorious build prog.glorious prog.gbc
glorious-vm --emit-llvm prog.gbc > prog.ll
clang -O2 prog.ll vm/target/release/libglorious_vm.a -o prog -lpthread -ldl -lm
```

The program built this way reads `GLORIOUS_BACKEND` when it starts: unset,
every function runs its LLVM body; `interp`, none does; `x86`, every function
is compiled again in memory; `mix`, a third of the functions run the LLVM
body, a third the x86-64 body, a third the interpreter.

## What is tested

Every test program that compiles (638 when this was written) is run
interpreted, compiled to x86-64, mixed, built with LLVM, and built with LLVM
and mixed three ways, and gives the same output and exit code each time.
Those programs handle effects, resume and cancel resumptions, jump to
labels, run cleanups, lend cells and call C, so the mixed runs take
resumptions and unwinding through functions of all three engines.

## What this is not

- **Not fast calls.** A call goes through the runtime, which is what makes
  the three engines interchangeable and also what a program made of small
  functions spends its time in. Compiled code is faster than interpreted
  code on the instructions between calls and no faster on calls. Compiling
  is fast: the x86-64 backend is one pass with no tool, and a program is
  compiled when it starts.
- **Not the layout contract of specification 17.2.** A value built by a
  constructor is the runtime's object. There are no declared sizes, offsets
  or tag widths for a program's types, no `repr(C)` records, and so nothing
  for C to read but integers and addresses.
- **Not proved.** The backends are compared with the interpreter by running
  the programs, as the interpreter is compared with the proved machines.
