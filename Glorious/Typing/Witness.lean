import Glorious.Typing.Certify
import Glorious.Proof.Witness

/-!
# Programs the checker accepts, and programs it turns away

The safety theorems would say nothing if the checker accepted no program. Here
it accepts the `effects` program of `Glorious.Witness`, with the ownership
rules on: the program installs three handlers, performs a resumptive operation
under a handler that does not serve it, resumes each resumption once, and ends
with a terminal operation. The kernel runs the checker to confirm it.

Further down are programs with cells: ones that use a cell within its scope,
which the region rules accept, and ones that let a reference or a closure
holding one out of the scope and use it afterwards, which go wrong and which
the region rules turn away.

Last are programs that lend a cell: one that uses it only through the borrow
while it is lent, which the rules for borrows accept, and one that writes it
behind the borrow's back, which they turn away.
-/

namespace Glorious.Typing.Witness

open Core

/-- `Ask`, operation 0. -/
def askRow : Row := [(0, [])]

/-- `Fail`, operation 1. -/
def failRow : Row := [(1, [])]

/-- A computation that may ask; it can be run any number of times. -/
def asker : Ty := .fn 0 [] .int askRow false none []

/-- The resumption the `Ask` arm receives: it runs where `Fail` is served, and
can be resumed once. -/
def resumption : Ty := .fn 0 [.int] .int failRow true none []

def cert : Cert where
  sigs := [
    ⟨0, ⟨[], [], .int, askRow, 0, 0, []⟩, [[.ty .int]]⟩,
    ⟨1, ⟨[], [.int, resumption], .int, failRow, 0, 0, []⟩, [[.ty .int]]⟩,
    ⟨2, ⟨[], [.int], .int, [], 0, 0, []⟩, [[.ty .int]]⟩,
    ⟨3, ⟨[], [.int], .int, [], 0, 0, []⟩, [[]]⟩,
    ⟨4, ⟨[], [.int], .int, [], 0, 0, []⟩, [[.ty .int]]⟩,
    ⟨5, ⟨[asker], [], .int, askRow, 0, 0, []⟩, [[.handler .int failRow [] [[], []]]]⟩,
    ⟨6, ⟨[asker], [], .int, failRow, 0, 0, []⟩, [[.handler .int askRow [] [[], []]]]⟩]
  datas := []
  -- `Ask` takes an integer and is resumed with one; `Fail` takes an integer
  -- and is not resumed.
  ops := [⟨0, [], [.int], some .int⟩, ⟨1, [], [.int], none⟩]
  mainTy := .int
  mainHints := [.ty asker, .ty asker, .ty (.fn 0 [] .int failRow false none []),
    .handler .int failRow [] [[], []]]
  strict := true
  regions := true
  loans := false

theorem effects_checked : checkProgram cert Glorious.Witness.effects = true := by decide

/-- So `effects` is well typed and well owned. -/
theorem effects_ok : ProgramOk cert.ctx Glorious.Witness.effects :=
  checkProgram_sound effects_checked

/-- Given any input, `effects` cannot go wrong except by overflow, a freed cell
or a dead label; and it does not: it halts (`Glorious.Witness.effects_core`). -/
theorem effects_safe (input : List Int) (h : GoesWrong Glorious.Witness.effects input) :
    ∃ c, Machine.Reaches (stepIO Glorious.Witness.effects)
        (initIO Glorious.Witness.effects input) c
      ∧ stepIO Glorious.Witness.effects c = .stuck ∧ Fault c.state ∧ ¬ Resumed c.state :=
  checked_owned_safety effects_checked rfl input h

/-! `resumeTwice` of `Glorious.Witness` resumes one resumption twice. It is well
typed, and goes wrong by exactly the fault the ownership rules are for; with
those rules on, the checker turns it away. -/

def twiceCert (strict : Bool) : Cert where
  sigs := [
    ⟨0, ⟨[], [], .int, askRow, 0, 0, []⟩, [[]]⟩,
    ⟨1, ⟨[], [.int, .fn 0 [.int] .int [] true none []], .int, [], 0, 0, []⟩, [[]]⟩,
    ⟨2, ⟨[], [.int], .int, [], 0, 0, []⟩, [[]]⟩]
  datas := []
  ops := [⟨0, [], [.int], some .int⟩]
  mainTy := .int
  mainHints := [.ty asker, .handler .int askRow [] [[], []]]
  strict := strict
  regions := false
  loans := false

example : checkProgram (twiceCert false) Glorious.Witness.resumeTwice = true := by decide

example : checkProgram (twiceCert true) Glorious.Witness.resumeTwice = false := by decide

/-! What the checker turns away, and a use of the coverage check on a data type. -/

/-- Reading a local that does not exist. -/
example : checkProgram ⟨[], [], [], .int, [], true, true, false⟩ ⟨[], .ret (.var 0)⟩ = false := by decide

/-- Performing an operation nothing handles. -/
example : checkProgram ⟨[], [], [], .int, [], true, true, false⟩ ⟨[], .raise 0 []⟩ = false := by decide

/-- Calling something that is not callable. -/
example : checkProgram ⟨[], [], [], .int, [.ty .int], true, true, false⟩
    ⟨[], .let_ (.atom (.int 1)) (.tail (.var 0) [])⟩ = false := by decide

/-- A function with a clause for `0` only does not cover its integer parameter;
with a second clause that binds the argument, it does. -/
example : checkProgram
    ⟨[⟨0, ⟨[], [.int], .int, [], 0, 0, []⟩, [[]]⟩], [], [], .int,
      [.ty (.fn 0 [.int] .int [] false none [])], true, true, false⟩
    ⟨[⟨[⟨[.int 0], .ret (.int 1)⟩]⟩], .let_ (.closure 0 []) (.tail (.var 0) [.int 5])⟩
    = false := by decide

example : checkProgram
    ⟨[⟨0, ⟨[], [.int], .int, [], 0, 0, []⟩, [[], []]⟩], [], [], .int,
      [.ty (.fn 0 [.int] .int [] false none [])], true, true, false⟩
    ⟨[⟨[⟨[.int 0], .ret (.int 1)⟩, ⟨[.bind], .ret (.var 1)⟩]⟩],
      .let_ (.closure 0 []) (.tail (.var 0) [.int 5])⟩
    = true := by decide

/-- An option of an integer: `None` is constructor 1, `Some` is constructor 2. -/
def option : Ty := .data 0 []

def optionDecl : DataInst := ⟨0, [], [(1, []), (2, [.int])], true⟩

/-- `get(None) = 0; get(Some(x)) = x`, applied to `Some(7)`: both constructors
have a clause, so the function covers its parameter. -/
example : checkProgram
    ⟨[⟨0, ⟨[], [option], .int, [], 0, 0, []⟩, [[], []]⟩], [optionDecl], [], .int,
      [.ty option, .ty (.fn 0 [option] .int [] false none [])], true, true, false⟩
    ⟨[⟨[⟨[.ctor 1 []], .ret (.int 0)⟩, ⟨[.ctor 2 [.bind]], .ret (.var 1)⟩]⟩],
      .let_ (.construct 2 [.int 7]) (.let_ (.closure 0 []) (.tail (.var 1) [.var 0]))⟩
    = true := by decide

/-- Without the clause for `None` it does not. -/
example : checkProgram
    ⟨[⟨0, ⟨[], [option], .int, [], 0, 0, []⟩, [[]]⟩], [optionDecl], [], .int,
      [.ty option, .ty (.fn 0 [option] .int [] false none [])], true, true, false⟩
    ⟨[⟨[⟨[.ctor 2 [.bind]], .ret (.var 1)⟩]⟩],
      .let_ (.construct 2 [.int 7]) (.let_ (.closure 0 []) (.tail (.var 1) [.var 0]))⟩
    = false := by decide

/-! Two bodies over one environment. A callable that may be called once is
captured by a first function; a second function is then given what the first
captured, in its place. Whichever is run, the callable is owned once, so the
ownership rules accept the program. Capturing it a second time instead owns it
twice, and they do not. -/

/-- A callable that may be called once, and a function that captured it. -/
def onceFn : Ty := .fn 0 [] .int [] true none []

def shared (env : Option (List Ty)) : Ty := .fn 0 [] .int [] true env []

/-- Function 0 gives an integer; functions 1 and 2 each call what they captured. -/
def bodies : List Fn :=
  [⟨[⟨[], .ret (.int 1)⟩]⟩, ⟨[⟨[], .tail (.var 0) []⟩]⟩, ⟨[⟨[], .tail (.var 0) []⟩]⟩]

def bodySigs : List SigEntry :=
  [⟨0, ⟨[], [], .int, [], 0, 0, []⟩, [[]]⟩, ⟨1, ⟨[onceFn], [], .int, [], 0, 0, []⟩, [[]]⟩,
    ⟨2, ⟨[onceFn], [], .int, [], 0, 0, []⟩, [[]]⟩]

/-- The second body takes over the environment of the first. -/
def takeOver : Program :=
  ⟨bodies,
    .let_ (.closure 0 []) <| .let_ (.closure 1 [.var 0]) <| .let_ (.rebind (.var 1) 2) <|
      .tail (.var 2) []⟩

/-- The second body captures the callable again. -/
def captureTwice : Program :=
  ⟨bodies,
    .let_ (.closure 0 []) <| .let_ (.closure 1 [.var 0]) <| .let_ (.closure 2 [.var 0]) <|
      .tail (.var 2) []⟩

def sharedCert (first : Ty) (strict : Bool) : Cert :=
  ⟨bodySigs, [], [], .int, [.ty onceFn, .ty first, .ty (shared none)], strict, true, false⟩

example : checkProgram (sharedCert (shared (some [onceFn])) true) takeOver = true := by decide

/-- The first function's type has to state its environment for it to be taken over. -/
example : checkProgram (sharedCert (shared none) true) takeOver = false := by decide

example : checkProgram (sharedCert (shared none) false) captureTwice = true := by decide

example : checkProgram (sharedCert (shared none) true) captureTwice = false := by decide

/-! ## Cells and regions

A cell is used by the callable its scope runs. That callable is polymorphic in
the cell's region, and what it gives back cannot mention the region. -/

/-- The type of a callable a cell scope of an integer can run, giving a `ρ`. -/
def scopeFn (ρ : Ty) (acc : List Rgn) : Ty :=
  .fn 1 [.ref (.bound 0) .int] ρ [] false none acc

/--
```
bump(r) = let x = *r in r := x + 1; *r
main    = cell 5 in bump
```
-/
def counter : Program where
  fns := [
    ⟨[ ⟨[.wild],
          .mem .load [.var 0] <|
          .let_ (.prim .intAdd [.var 1, .int 1]) <|
          .mem .store [.var 0, .var 2] <|
          .mem .load [.var 0] <|
          .ret (.var 4)⟩ ]⟩ ]
  main := .let_ (.closure 0 []) <| .cellTail (.int 5) (.var 0)

def counterCert : Cert where
  sigs := [⟨0, ⟨[], [.ref (.bound 0) .int], .int, [], 0, 1, [.bound 0]⟩, [[.ty .int]]⟩]
  datas := []
  ops := []
  mainTy := .int
  mainHints := [.ty (scopeFn .int [.bound 0])]
  strict := true
  regions := true
  loans := false

theorem counter_checked : checkProgram counterCert counter = true := by decide

/-- So `counter` never reads or writes a released cell. -/
theorem counter_borrows (input : List Int) {c : Config}
    (h : Machine.Reaches (stepIO counter) (initIO counter input) c) : ¬ Freed c.state :=
  checked_borrow_safety counter_checked rfl input h

/--
A function that reads through any reference it is given, called with the region
of the cell at hand; and a closure that captured the reference, made and called
inside the scope.
```
get(r)       = *r
peek[r]()    = *r
body[get](r) = let p = peek[r] in get(r) + p()
main         = cell 21 in body[get]
```
-/
def readers : Program where
  fns := [
    ⟨[ ⟨[.wild], .mem .load [.var 0] <| .ret (.var 1)⟩ ]⟩,
    ⟨[ ⟨[], .mem .load [.var 0] <| .ret (.var 1)⟩ ]⟩,
    ⟨[ ⟨[.wild],
          .let_ (.closure 1 [.var 0]) <|
          .call (.var 1) [.var 0] <|
          .call (.var 2) [] <|
          .let_ (.prim .intAdd [.var 3, .var 4]) <|
          .ret (.var 5)⟩ ]⟩ ]
  main := .let_ (.closure 0 []) <| .let_ (.closure 2 [.var 0]) <| .cellTail (.int 21) (.var 1)

/-- A closure that reads a cell of region `r` when called. -/
def peekTy (r : Rgn) : Ty := .fn 0 [] .int [] false none [r]

def readersCert : Cert where
  sigs := [
    ⟨0, ⟨[], [.ref (.bound 0) .int], .int, [], 0, 1, [.bound 0]⟩, [[]]⟩,
    -- `peek` is closed over a reference whose region is fixed when it is made.
    ⟨1, ⟨[.ref (.var 0) .int], [], .int, [], 1, 0, [.var 0]⟩, [[]]⟩,
    ⟨2, ⟨[scopeFn .int [.bound 0]], [.ref (.bound 0) .int], .int, [], 0, 1, [.bound 0]⟩,
      [[.clo (peekTy (.var 0)) [.var 0], .rgns [.var 0], .ty .int]]⟩]
  datas := []
  ops := []
  mainTy := .int
  mainHints := [.ty (scopeFn .int [.bound 0]), .ty (scopeFn .int [.bound 0])]
  strict := true
  regions := true
  loans := false

theorem readers_checked : checkProgram readersCert readers = true := by decide

theorem readers_borrows (input : List Int) {c : Config}
    (h : Machine.Reaches (stepIO readers) (initIO readers input) c) : ¬ Freed c.state :=
  checked_borrow_safety readers_checked rfl input h

/--
The reference leaves the scope, and is read after the cell is released.
```
keep(r) = r
main    = let r = cell 5 in keep in *r
```
-/
def escape : Program where
  fns := [ ⟨[ ⟨[.wild], .ret (.var 0)⟩ ]⟩ ]
  main :=
    .let_ (.closure 0 []) <| .cell (.int 5) (.var 0) <| .mem .load [.var 1] <| .ret (.var 2)

theorem escape_goesWrong : GoesWrong escape [] := ⟨10, rfl⟩

/-- Without regions the reference is only a reference to an integer. -/
def looseRef : Ty := .ref (.cell 0) .int

def escapeCert (regions : Bool) : Cert where
  sigs := [⟨0, ⟨[], [looseRef], looseRef, [], 0, 0, []⟩, [[]]⟩]
  datas := []
  ops := []
  mainTy := .int
  mainHints := [.ty (.fn 0 [looseRef] looseRef [] false none [])]
  strict := true
  regions := regions
  loans := false

/-- `escape` is well typed, and well owned; -/
example : checkProgram (escapeCert false) escape = true := by decide

/-- but not under the region rules, -/
example : checkProgram (escapeCert true) escape = false := by decide

/-- whether or not `keep` is made polymorphic in the region: what the scope
gives back would mention the cell's region. -/
example : checkProgram
    ⟨[⟨0, ⟨[], [.ref (.bound 0) .int], .ref (.bound 0) .int, [], 0, 1, []⟩, [[]]⟩], [], [], .int,
      [.ty (scopeFn (.ref (.bound 0) .int) [])], true, true, false⟩ escape = false := by decide

/--
A closure that captured the reference leaves the scope, and is called after the
cell is released.
```
peek[r]() = *r
hide(r)   = peek[r]
main      = let p = cell 5 in hide in p()
```
-/
def leak : Program where
  fns := [
    ⟨[ ⟨[], .mem .load [.var 0] <| .ret (.var 1)⟩ ]⟩,
    ⟨[ ⟨[.wild], .let_ (.closure 0 [.var 0]) <| .ret (.var 1)⟩ ]⟩ ]
  main := .let_ (.closure 1 []) <| .cell (.int 5) (.var 0) <| .tail (.var 1) []

theorem leak_goesWrong : GoesWrong leak [] := ⟨10, rfl⟩

def leakCert (regions : Bool) : Cert where
  sigs := [
    ⟨0, ⟨[looseRef], [], .int, [], 0, 0, []⟩, [[]]⟩,
    ⟨1, ⟨[], [looseRef], .fn 0 [] .int [] false none [], [], 0, 0, []⟩,
      [[.ty (.fn 0 [] .int [] false none [])]]⟩]
  datas := []
  ops := []
  mainTy := .int
  mainHints := [.ty (.fn 0 [looseRef] (.fn 0 [] .int [] false none []) [] false none [])]
  strict := true
  regions := regions
  loans := false

example : checkProgram (leakCert false) leak = true := by decide

example : checkProgram (leakCert true) leak = false := by decide

/-- With regions, the closure's type says it reads the cell: so the scope
cannot give it back. -/
example : checkProgram
    ⟨[⟨0, ⟨[.ref (.var 0) .int], [], .int, [], 1, 0, [.var 0]⟩, [[]]⟩,
      ⟨1, ⟨[], [.ref (.bound 0) .int], peekTy (.bound 0), [], 0, 1, []⟩,
        [[.clo (peekTy (.var 0)) [.var 0]]]⟩], [], [], .int,
      [.ty (scopeFn (peekTy (.bound 0)) [])], true, true, false⟩ leak = false := by decide

/-- And a closure whose type hides that it reads the cell is not well typed. -/
example : checkProgram
    ⟨[⟨0, ⟨[.ref (.var 0) .int], [], .int, [], 1, 0, []⟩, [[]]⟩,
      ⟨1, ⟨[], [.ref (.bound 0) .int], .fn 0 [] .int [] false none [], [], 0, 1, []⟩,
        [[.clo (.fn 0 [] .int [] false none []) [.var 0]]]⟩], [], [], .int,
      [.ty (scopeFn (.fn 0 [] .int [] false none []) [])], true, true, false⟩ leak = false := by decide

/-! ## Labels and regions

A label is a region too: the callable its scope runs is polymorphic in it, the
label's type says that applying the label touches it, and what the scope gives
back cannot mention it. -/

/-- A label that takes an integer, in the scope whose region is `r`. -/
def labelTy (r : Rgn) : Ty := .fn 0 [.int] .never [] false none [r]

/--
A scope left early from inside a nested call, through a closure that captured
the label, and one that ends normally.
```
check[l](x) = tail l(x * 100)
body(l)     = let c = check[l] in c(3) + 1
seven(l)    = 7
main        = (label body) + (label seven)
```
-/
def jumps : Program where
  fns := [
    ⟨[ ⟨[.wild], .let_ (.prim .intMul [.var 0, .int 100]) <| .tail (.var 1) [.var 2]⟩ ]⟩,
    ⟨[ ⟨[.wild],
          .let_ (.closure 0 [.var 0]) <|
          .call (.var 1) [.int 3] <|
          .let_ (.prim .intAdd [.var 2, .int 1]) <|
          .ret (.var 3)⟩ ]⟩,
    ⟨[ ⟨[.wild], .ret (.int 7)⟩ ]⟩ ]
  main :=
    .let_ (.closure 1 []) <|
    .label (.var 0) <|
    .let_ (.closure 2 []) <|
    .label (.var 2) <|
    .let_ (.prim .intAdd [.var 1, .var 3]) <|
    .ret (.var 4)

theorem jumps_core : Halts jumps [] ⟨.int 307, ⟨[], []⟩⟩ := ⟨40, rfl⟩

def jumpsCert : Cert where
  sigs := [
    -- `check` is closed over a label whose region is fixed when it is made.
    ⟨0, ⟨[labelTy (.var 0)], [.int], .int, [], 1, 0, [.var 0]⟩, [[.ty .int]]⟩,
    ⟨1, ⟨[], [labelTy (.bound 0)], .int, [], 0, 1, [.bound 0]⟩,
      [[.clo (.fn 0 [.int] .int [] false none [.var 0]) [.var 0], .ty .int]]⟩,
    ⟨2, ⟨[], [labelTy (.bound 0)], .int, [], 0, 1, []⟩, [[]]⟩]
  datas := []
  ops := []
  mainTy := .int
  mainHints := [.ty (.fn 1 [labelTy (.bound 0)] .int [] false none [.bound 0]),
    .ty (.fn 1 [labelTy (.bound 0)] .int [] false none []), .ty .int]
  strict := true
  regions := true
  loans := false

theorem jumps_checked : checkProgram jumpsCert jumps = true := by decide

/-- So `jumps` goes wrong in no way but the two a checked program can. -/
theorem jumps_sound (input : List Int) (h : GoesWrong jumps input) :
    ∃ c, Machine.Reaches (stepIO jumps) (initIO jumps input) c
      ∧ stepIO jumps c = .stuck ∧ (Overflow c.state ∨ Absent c.state) :=
  checked_full_safety jumps_checked rfl rfl input h

/--
A closure that captured the label leaves the scope, and is called after the
scope has ended.
```
one()      = 1
jump[l, h]() = tail l(h)
hide(l)    = let h = one in jump[l, h]
main       = let g = label hide in g()
```
-/
def lateJump : Program where
  fns := [
    ⟨[ ⟨[], .ret (.int 1)⟩ ]⟩,
    ⟨[ ⟨[], .tail (.var 0) [.var 1]⟩ ]⟩,
    ⟨[ ⟨[.wild], .let_ (.closure 0 []) <| .let_ (.closure 1 [.var 0, .var 1]) <| .ret (.var 2)⟩ ]⟩ ]
  main := .let_ (.closure 2 []) <| .label (.var 0) <| .tail (.var 1) []

theorem lateJump_goesWrong : GoesWrong lateJump [] := ⟨10, rfl⟩

/-- A callable that gives an integer and, without regions, touches nothing. -/
def thunkTy : Ty := .fn 0 [] .int [] false none []

def lateJumpCert (regions : Bool) : Cert where
  sigs := [
    ⟨0, ⟨[], [], .int, [], 0, 0, []⟩, [[]]⟩,
    ⟨1, ⟨[.fn 0 [thunkTy] .never [] false none [], thunkTy], [], .int, [], 0, 0, []⟩, [[]]⟩,
    ⟨2, ⟨[], [.fn 0 [thunkTy] .never [] false none []], thunkTy, [], 0, 0, []⟩,
      [[.ty thunkTy, .ty thunkTy]]⟩]
  datas := []
  ops := []
  mainTy := .int
  mainHints := [.ty (.fn 0 [.fn 0 [thunkTy] .never [] false none []] thunkTy [] false none [])]
  strict := true
  regions := regions
  loans := false

/-- `lateJump` is well typed, and well owned; -/
example : checkProgram (lateJumpCert false) lateJump = true := by decide

/-- but not under the region rules. -/
example : checkProgram (lateJumpCert true) lateJump = false := by decide

/-! ## Borrows

A borrow is used by the callable its scope runs. That callable is polymorphic
in the borrow's region, and of the regions around it may touch none that was
lent. -/

/-- The type of a callable a borrow's scope of an integer can run. -/
def borrowFn (acc : List Rgn) : Ty := .fn 1 [.ref (.bound 0) .int] .int [] false none acc

/--
A cell lent for writing, then for reading, and read again when both borrows
have ended.
```
bump(p) = let x = *p in p := x + 1; 0
peek(p) = *p
body(r) = let _ = lend mut r in bump in let v = lend r in peek in v + *r
main    = cell 5 in body
```
-/
def lender : Program where
  fns := [
    ⟨[ ⟨[.wild],
          .mem .load [.var 0] <|
          .let_ (.prim .intAdd [.var 1, .int 1]) <|
          .mem .store [.var 0, .var 2] <|
          .ret (.int 0)⟩ ]⟩,
    ⟨[ ⟨[.wild], .mem .load [.var 0] <| .ret (.var 1)⟩ ]⟩,
    ⟨[ ⟨[.wild],
          .let_ (.closure 0 []) <|
          .lend true (.var 0) (.var 1) [] [] <|
          .let_ (.closure 1 []) <|
          .lend false (.var 0) (.var 3) [] [] <|
          .mem .load [.var 0] <|
          .let_ (.prim .intAdd [.var 4, .var 5]) <|
          .ret (.var 6)⟩ ]⟩ ]
  main := .let_ (.closure 2 []) <| .cellTail (.int 5) (.var 0)

theorem lender_core : Halts lender [] ⟨.int 12, ⟨[], []⟩⟩ := ⟨40, rfl⟩

/-- A callable that reads and writes what it is given, and one that reads it. -/
def writer : Ty := borrowFn [.bound 0, .wr (.bound 0)]

def reader : Ty := borrowFn [.bound 0]

def lenderCert : Cert where
  sigs := [
    ⟨0, ⟨[], [.ref (.bound 0) .int], .int, [], 0, 1, [.bound 0, .wr (.bound 0)]⟩, [[.ty .int]]⟩,
    ⟨1, ⟨[], [.ref (.bound 0) .int], .int, [], 0, 1, [.bound 0]⟩, [[]]⟩,
    ⟨2, ⟨[], [.ref (.bound 0) .int], .int, [], 0, 1, [.bound 0, .wr (.bound 0)]⟩,
      [[.ty writer, .ty reader, .ty .int]]⟩]
  datas := []
  ops := []
  mainTy := .int
  mainHints := [.ty writer]
  strict := true
  regions := true
  loans := true

theorem lender_checked : checkProgram lenderCert lender = true := by decide

/-- So whenever `lender` uses a reference, no newer borrow in scope excludes it. -/
theorem lender_exclusive (input : List Int) {c : Config}
    (h : Machine.Reaches (stepIO lender) (initIO lender input) c) :
    ¬ Aliased c.state ∧ ¬ Suspended c.state :=
  checked_exclusive_safety lender_checked rfl rfl input h

/--
A cell written through its own reference while it is lent for writing: the
callable the borrow's scope runs captured the reference lent.
```
poke[r](p) = r := 9; *p
body(r)    = let f = poke[r] in lend mut r in f
main       = cell 5 in body
```
-/
def alias : Program where
  fns := [
    ⟨[ ⟨[.wild], .mem .store [.var 1, .int 9] <| .mem .load [.var 0] <| .ret (.var 3)⟩ ]⟩,
    ⟨[ ⟨[.wild], .let_ (.closure 0 [.var 0]) <| .lend true (.var 0) (.var 1) [] [] <| .ret (.var 2)⟩ ]⟩ ]
  main := .let_ (.closure 1 []) <| .cellTail (.int 5) (.var 0)

/-- It runs: nothing in the machine stops it. -/
theorem alias_core : Halts alias [] ⟨.int 9, ⟨[], []⟩⟩ := ⟨40, rfl⟩

/-- But on the way it writes the cell behind the borrow's back. -/
theorem alias_aliased : ∃ c, Machine.Reaches (stepIO alias) (initIO alias []) c
    ∧ Aliased c.state :=
  ⟨_, ⟨4, rfl⟩, .inl ⟨_, _, _, _, _, _, _, rfl, rfl, rfl⟩⟩

/-- Without the rules for borrows the borrow is the reference it was lent from. -/
def aliasCert (loans : Bool) : Cert where
  sigs := [
    ⟨0, ⟨[.ref (.var 0) .int], [.ref (.var 0) .int], .int, [], 1, 0, [.var 0]⟩, [[]]⟩,
    ⟨1, ⟨[], [.ref (.bound 0) .int], .int, [], 0, 1, [.bound 0]⟩,
      [[.clo (.fn 0 [.ref (.var 0) .int] .int [] false none [.var 0]) [.var 0]]]⟩]
  datas := []
  ops := []
  mainTy := .int
  mainHints := [.ty (borrowFn [.bound 0])]
  strict := true
  regions := true
  loans := loans

/-- `alias` is well typed, well owned, and uses its cell within its scope; -/
example : checkProgram (aliasCert false) alias = true := by decide

/-- but not under the rules for borrows, -/
example : checkProgram (aliasCert true) alias = false := by decide

/-- whether or not `poke` is made polymorphic in the borrow: its type says it
writes what was lent. -/
example : checkProgram
    ⟨[⟨0, ⟨[.ref (.var 0) .int], [.ref (.bound 0) .int], .int, [], 1, 1,
          [.var 0, .wr (.var 0), .bound 0]⟩, [[]]⟩,
      ⟨1, ⟨[], [.ref (.bound 0) .int], .int, [], 0, 1, [.bound 0, .wr (.bound 0)]⟩,
        [[.clo (borrowFn [.var 0, .wr (.var 0), .bound 0]) [.var 0]]]⟩], [], [], .int,
      [.ty writer], true, true, true⟩ alias = false := by decide

/-- And a `poke` whose type hides that it writes the cell is not well typed. -/
example : checkProgram
    ⟨[⟨0, ⟨[.ref (.var 0) .int], [.ref (.bound 0) .int], .int, [], 1, 1, [.bound 0]⟩, [[]]⟩,
      ⟨1, ⟨[], [.ref (.bound 0) .int], .int, [], 0, 1, [.bound 0, .wr (.bound 0)]⟩,
        [[.clo (borrowFn [.bound 0]) [.var 0]]]⟩], [], [], .int,
      [.ty writer], true, true, true⟩ alias = false := by decide

end Glorious.Typing.Witness
