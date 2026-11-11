import Glorious.Driver
import Glorious.Cases

/-!
# Front-end tests

The front-end is not proved, so these run at build time. Every case is compiled
and run on both the Core machine and the bytecode machine; the two results must
agree with each other and with the expected output.
-/

namespace Glorious.Tests

#eval show IO Unit from do
  let mut failures : Array String := #[]
  for c in cases do
    let got := evalSource c.src c.input
    if got != c.expect then
      failures := failures.push s!"program:\n{c.src}\nexpected:\n{c.expect}\ngot:\n{got}\n"
  unless failures.isEmpty do
    throw (IO.userError ("\n".intercalate failures.toList))

/-! Stack depth. An explicit tail call keeps no frame, and a library loop runs
in constant stack because its handler is re-installed by a tail call and keeps
no caller frame. Peak depth must not depend on the number of iterations. -/

def counting (n : Nat) : String :=
  "fn count(i, n) { tail match(i == n) { Ok(_) => i, Err(_) => tail count(i + 1, n) } }
   fn main() { count(0, " ++ toString n ++ ") }"

#guard evalSource (counting 50) == "50"
#guard (peakStack (counting 10)).isSome
#guard peakStack (counting 10) == peakStack (counting 300)

def echoLoop : String :=
  "fn main() { loop { match(read()) { Some(x) => print(x), None => break(0) } } }"

#guard evalSource echoLoop [4, 5] == "4\n5\n0"
#guard (peakStack echoLoop [1, 2, 3]).isSome
#guard peakStack echoLoop (List.replicate 5 1) == peakStack echoLoop (List.replicate 300 1)

/-! Without `tail`, a recursive call keeps its frame: the discipline is explicit. -/

def notTail (n : Nat) : String :=
  "fn count(i, n) { match(i == n) { Ok(_) => i, Err(_) => count(i + 1, n) } }
   fn main() { count(0, " ++ toString n ++ ") }"

#guard peakStack (notTail 10) != peakStack (notTail 300)

/-! When a program goes wrong, the diagnosis names the cause in the program's terms. -/

#guard diagnose "effect Ask { ask(x) }  fn main() { ask(1) }"
  == "operation `ask` is performed, but no handler for it is installed"
#guard diagnose "fn f { 0 => 1 }  fn main() { f(5) }"
  == "no clause of `f` matches the arguments (5)"
#guard diagnose "fn main() { match(Some(1)) { None => 0 } }"
  == "no clause of a callable in `main` matches the arguments (Ok(1))"
#guard diagnose "effect Ask { ask() }  fn main() { handle ask() { ask(k) => k(1) + k(2) } }"
  == "a resumption is used a second time: it was already resumed or cancelled"
#guard diagnose "fn main() { let l = @out { @out }; l(1) }"
  == "a label is applied after its scope has ended"
#guard diagnose "fn main() { let x = 5; x(1) }" == "`5` is called, but it is not callable"
#guard diagnose "fn main() { 9223372036854775807 + 1 }"
  == "integer overflow: the result of an operation on (9223372036854775807, 1) does not fit in 64 bits"
#guard diagnose "fn main() { (1, 2).5 }" == "`(1, 2)` does not have the field being read"
#guard diagnose "fn f(a, b) { a }  fn main() { f(1) }" == "no clause of `f` matches the arguments (1)"
#guard diagnose "fn main() { 1 + 2 }" == "did not go wrong"
-- A program the checker rejects is elaborated without types; its blocks still
-- take the arguments the functions they are passed to give them.
#guard diagnose "effect Ask { ask() -> Int }
  fn main() { handle ask() + 1 { ask(k) => (if(2 < 1) { k(1) } else { 0 }) + k(2) + k(3) } }"
  == "a resumption is used a second time: it was already resumed or cancelled"

-- A mutable variable's cell is released however its block is left: by
-- finishing, by a label, by a terminal operation, or by cancellation.
#guard liveCells "fn bump(n) { let mut x = n; x = x + 1; x }
  fn main() { let mut i = 0; while({ i < 20 }) { i = i + bump(0) }; i }" == some 0
#guard liveCells "fn main() { @out { let mut x = 1; @out(x); 0 } }" == some 0
#guard liveCells "effect Fail { fail(Int) -> ! }  fn work() { let mut x = 7; fail(x); 0 }
  fn main() { handle work() { fail(e) => e } }" == some 0
#guard liveCells "effect Ask { ask() -> Int }  fn work() { let mut x = 7; x + ask() }
  fn main() { handle work() { ask(k) => cancel(k); 3 } }" == some 0
-- A resumption that is dropped keeps what it captured: a known leak.
#guard liveCells "effect Ask { ask() -> Int }  fn work() { let mut x = 7; x + ask() }
  fn main() { handle work() { ask(k) => 3 } }" == some 1
-- Without the checker, a callable that outlives its variable finds the cell gone.
#guard diagnose "fn mk() { let mut n = 0; { n = n + 1; n } }  fn main() { mk()() }"
  == "a reference is used after the cell it points to was freed"

-- The checker does not let a cleanup perform effects. The machines still give
-- such a program a meaning: the cleanup runs in place, inside the handlers it
-- was registered inside, and an arm that resumes it never sees its result.
#guard diagnose "effect Tick { tick() }  effect Stop { stop(Int) -> ! }
  fn work() { defer tick(); stop(1) }
  fn main() { handle (handle work() { tick(k) => k(()) + 1 }) { stop(v) => v } }"
  == "did not go wrong"
#guard diagnose "effect Stop { stop(Int) -> ! }
  fn work() { defer stop(2); stop(1) }
  fn main() { handle work() { stop(v) => v } }" == "did not go wrong"

-- Ownership. A program whose Core follows the ownership rules is certified with
-- them, and the proof then says it never uses a resumption twice. That covers a
-- resumption used on one path, passed on, kept in a mutable variable and taken
-- out again, or captured by a callable that is called once.
#guard owned "effect Ask { ask() -> Int }  fn main() { handle ask() + 1 { ask(k) => k(1) } }"
  == some true
#guard owned "effect Ask { ask() -> Int }
  fn main() { handle ask() + 1 { ask(k) => let f = { k(1) }; f() } }" == some true
#guard owned "effect Ask { ask() -> Int }
  fn main() { handle ask() + 1 { ask(k) => if(1 < 2) { k(10) }; 0 } }" == some true
#guard owned "effect Ask { ask() -> Int }
  fn main() { handle ask() + 1 { ask(k) => match(1 < 2) { Ok(_) => k(1), Err(_) => k(2) } } }"
  == some true
#guard owned "effect Ask { ask() -> Int }
  fn main() { let mut slot = None; handle ask() + 1 { ask(k) => replace(&mut slot, Some(k)); 0 };
    match(replace(&mut slot, None)) { Some(k) => k(5), None => 0 } }" == some true
-- The two blocks of `if ... else` may both use a resumption. `if` gives back a
-- body it did not run, and the block after `else`, given that body, runs in its
-- environment: the resumption is captured once and used by whichever runs. No
-- rule names `if` or `else`; a function a program defines does the same.
#guard owned "effect Ask { ask() -> Int }
  fn main() { handle ask() + 1 { ask(k) => if(1 < 2) { k(10) } else { k(20) } } }" == some true
#guard owned "effect Ask { ask() -> Int }
  fn main() { handle ask() + 1 { ask(k) =>
    if(1 < 2) { if(2 < 1) { k(1) } else { k(2) } } else { k(3) } } }" == some true
#guard owned "effect Ask { ask() -> Int }
  fn decide(c, k) { if(c) { k(1) } else { k(2) } }
  fn main() { handle ask() + 1 { ask(k) => decide(1 < 2, k) } }" == some true
#guard owned "effect Ask { ask() -> Int }
  fn pick(c, a, b) { match(c) { Ok(_) => a(), Err(_) => b(a) } }
  fn main() { handle ask() + 1 { ask(k) => pick(2 < 1, { k(1) }, { k(2) }) } }" == some true
-- Two callables that each took the resumption for themselves own it twice,
-- whichever of them is later run. Such a program compiles, typed but not shown
-- well owned.
#guard owned "effect Ask { ask() -> Int }
  fn pick(c, a, b) { match(c) { Ok(_) => a(), Err(_) => b() } }
  fn main() { handle ask() + 1 { ask(k) => pick(1 < 2, { k(1) }, { k(2) }) } }" == some false
#guard owned "effect Ask { ask() -> Int }
  fn main() { handle ask() + 1 { ask(k) =>
    let a = { k(1) }; let b = { k(2) }; if(1 < 2) { a() } else { b() } } }" == some false

end Glorious.Tests
