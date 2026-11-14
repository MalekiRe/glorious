module

public import Glorious.Driver

/-!
# What is asked of the front end besides what programs give

The front end is not proved. `glorious selftest` runs every test program, and
then asks each of these: how deep the stack gets, what is said when a program
goes wrong, which cells are still live at the end, how many cleanups ran, and
what the typing of a program's Core shows. Each is numbered, to be named when
it does not hold.
-/

public section

namespace Glorious.Checks

def counting (n : Nat) : String :=
  "fn count(i, n) { tail match(i == n) { Ok(_) => i, Err(_) => tail count(i + 1, n) } }
   fn main() { count(0, " ++ toString n ++ ") }"

def echoLoop : String :=
  "fn main() { loop { match(read()) { Some(x) => print(x), None => break(0) } } }"

def notTail (n : Nat) : String :=
  "fn count(i, n) { match(i == n) { Ok(_) => i, Err(_) => count(i + 1, n) } }
   fn main() { count(0, " ++ toString n ++ ") }"

/-- Each thing asked, with its number. -/
def all : List (Nat × (Unit → Bool)) := [
  -- Stack depth. An explicit tail call keeps no frame, and a library loop runs
  -- in constant stack because its handler is re-installed by a tail call and keeps
  -- no caller frame. Peak depth must not depend on the number of iterations.
  (1, fun _ => evalSource (counting 50) == "50"),
  (2, fun _ => (peakStack (counting 10)).isSome),
  (3, fun _ => peakStack (counting 10) == peakStack (counting 300)),
  (4, fun _ => evalSource echoLoop [4, 5] == "4\n5\n0"),
  (5, fun _ => (peakStack echoLoop [1, 2, 3]).isSome),
  (6, fun _ => peakStack echoLoop (List.replicate 5 1) == peakStack echoLoop (List.replicate 300 1)),
  -- Without `tail`, a recursive call keeps its frame: the discipline is explicit.
  (7, fun _ => peakStack (notTail 10) != peakStack (notTail 300)),
  -- When a program goes wrong, the diagnosis names the cause in the program's terms.
  (8, fun _ => diagnose "effect Ask { ask(x) }  fn main() { ask(1) }"
    == "operation `ask` is performed, but no handler for it is installed"),
  (9, fun _ => diagnose "fn f { 0 => 1 }  fn main() { f(5) }"
    == "no clause of `f` matches the arguments (5)"),
  (10, fun _ => diagnose "fn main() { match(Some(1)) { None => 0 } }"
    == "no clause of a callable in `main` matches the arguments (Ok(1))"),
  (11, fun _ => diagnose "effect Ask { ask() }  fn main() { handle ask() { ask(k) => k(1) + k(2) } }"
    == "a resumption is used a second time: it was already resumed or cancelled"),
  (12, fun _ => diagnose "fn main() { let l = @out { @out }; l(1) }"
    == "a label is applied after its scope has ended"),
  (13, fun _ => diagnose "fn main() { let x = 5; x(1) }" == "`5` is called, but it is not callable"),
  (14, fun _ => diagnose "fn main() { 9223372036854775807 + 1 }"
    == "integer overflow: the result of an operation on (9223372036854775807, 1) does not fit in 64 bits"),
  (15, fun _ => diagnose "fn main() { (1, 2).5 }" == "`(1, 2)` does not have the field being read"),
  (16, fun _ => diagnose "fn f(a, b) { a }  fn main() { f(1) }" == "no clause of `f` matches the arguments (1)"),
  (17, fun _ => diagnose "fn main() { 1 + 2 }" == "did not go wrong"),
  -- A program the checker rejects is elaborated without types; its blocks still
  -- take the arguments the functions they are passed to give them.
  (18, fun _ => diagnose "effect Ask { ask() -> Int }
    fn main() { handle ask() + 1 { ask(k) => (if(2 < 1) { k(1) } else { 0 }) + k(2) + k(3) } }"
    == "a resumption is used a second time: it was already resumed or cancelled"),
  -- A mutable variable's cell is released however its block is left: by
  -- finishing, by a label, by a terminal operation, or by cancellation.
  (19, fun _ => liveCells "fn bump(n) { let mut x = n; x = x + 1; x }
    fn main() { let mut i = 0; while({ i < 20 }) { i = i + bump(0) }; i }" == some 0),
  (20, fun _ => liveCells "fn main() { @out { let mut x = 1; @out(x); 0 } }" == some 0),
  (21, fun _ => liveCells "effect Fail { fail(Int) -> ! }  fn work() { let mut x = 7; fail(x); 0 }
    fn main() { handle work() { fail(e) => e } }" == some 0),
  (22, fun _ => liveCells "effect Ask { ask() -> Int }  fn work() { let mut x = 7; x + ask() }
    fn main() { handle work() { ask(k) => cancel(k); 3 } }" == some 0),
  -- An arm that does not use its resumption cancels it, which releases what the
  -- suspended computation held.
  (23, fun _ => liveCells "effect Ask { ask() -> Int }  fn work() { let mut x = 7; x + ask() }
    fn main() { handle work() { ask(k) => 3 } }" == some 0),
  -- A resumption passed to something that forgets it keeps what it captured: a
  -- known leak.
  (24, fun _ => liveCells "effect Ask { ask() -> Int }  fn work() { let mut x = 7; x + ask() }
    fn forget(k) { 3 }
    fn main() { handle work() { ask(k) => forget(k) } }" == some 1),
  -- Cleanups: installed, started, and left in a resumption that was never taken.
  -- The first is always the sum of the other two (`Core.cleanup_accounting`).
  (25, fun _ => cleanups "effect Ask { ask() }  fn work() { defer print(1); ask(); 0 }
    fn main() { handle work() { ask(k) => k(()) } }" == some (1, 1, 0)),
  (26, fun _ => cleanups "effect Ask { ask() }  fn work() { defer print(1); ask(); 0 }
    fn main() { handle work() { ask(k) => 7 } }" == some (1, 1, 0)),
  (27, fun _ => cleanups "effect Ask { ask() }  fn work() { defer print(1); defer print(2); ask(); 0 }
    fn forget(k) { 7 }
    fn main() { handle work() { ask(k) => forget(k) } }" == some (2, 0, 2)),
  (28, fun _ => cleanups "effect Fail { fail() -> ! }  fn work() { defer print(1); fail(); 0 }
    fn main() { handle work() { fail() => 7 } }" == some (1, 1, 0)),
  -- Without the checker, a callable that outlives its variable finds the cell gone.
  (29, fun _ => diagnose "fn mk() { let mut n = 0; { n = n + 1; n } }  fn main() { mk()() }"
    == "a reference is used after the cell it points to was freed"),
  -- The checker does not let a cleanup perform effects. The machines still give
  -- such a program a meaning: the cleanup runs in place, inside the handlers it
  -- was registered inside, and an arm that resumes it never sees its result.
  (30, fun _ => diagnose "effect Tick { tick() }  effect Stop { stop(Int) -> ! }
    fn work() { defer tick(); stop(1) }
    fn main() { handle (handle work() { tick(k) => k(()) + 1 }) { stop(v) => v } }"
    == "did not go wrong"),
  (31, fun _ => diagnose "effect Stop { stop(Int) -> ! }
    fn work() { defer stop(2); stop(1) }
    fn main() { handle work() { stop(v) => v } }" == "did not go wrong"),
  -- Ownership. A program whose Core follows the ownership rules is certified with
  -- them, and the proof then says it never uses a resumption twice. That covers a
  -- resumption used on one path, passed on, kept in a mutable variable and taken
  -- out again, or captured by a callable that is called once.
  (32, fun _ => owned "effect Ask { ask() -> Int }  fn main() { handle ask() + 1 { ask(k) => k(1) } }"
    == some true),
  (33, fun _ => owned "effect Ask { ask() -> Int }
    fn main() { handle ask() + 1 { ask(k) => let f = { k(1) }; f() } }" == some true),
  (34, fun _ => owned "effect Ask { ask() -> Int }
    fn main() { handle ask() + 1 { ask(k) => if(1 < 2) { k(10) }; 0 } }" == some true),
  (35, fun _ => owned "effect Ask { ask() -> Int }
    fn main() { handle ask() + 1 { ask(k) => match(1 < 2) { Ok(_) => k(1), Err(_) => k(2) } } }"
    == some true),
  (36, fun _ => owned "effect Ask { ask() -> Int }
    fn main() { let mut slot = None; handle ask() + 1 { ask(k) => replace(&mut slot, Some(k)); 0 };
      match(replace(&mut slot, None)) { Some(k) => k(5), None => 0 } }" == some true),
  -- The two blocks of `if ... else` may both use a resumption. `if` gives back a
  -- body it did not run, and the block after `else`, given that body, runs in its
  -- environment: the resumption is captured once and used by whichever runs. No
  -- rule names `if` or `else`; a function a program defines does the same.
  (37, fun _ => owned "effect Ask { ask() -> Int }
    fn main() { handle ask() + 1 { ask(k) => if(1 < 2) { k(10) } else { k(20) } } }" == some true),
  (38, fun _ => owned "effect Ask { ask() -> Int }
    fn main() { handle ask() + 1 { ask(k) =>
      if(1 < 2) { if(2 < 1) { k(1) } else { k(2) } } else { k(3) } } }" == some true),
  (39, fun _ => owned "effect Ask { ask() -> Int }
    fn decide(c, k) { if(c) { k(1) } else { k(2) } }
    fn main() { handle ask() + 1 { ask(k) => decide(1 < 2, k) } }" == some true),
  -- A chain of alternatives: `or` gives the body that was not run to its right
  -- operand, which runs in its place and gives back, if it fails too, a body
  -- made from what it took over. The block after `else` takes over from that
  -- one, though it was made in another activation.
  (40, fun _ => owned "effect Ask { ask() -> Int }
    fn main() { handle ask() + 1 { ask(k) =>
      if(2 < 1) { k(1) } or { if(1 < 2) { k(2) } } else { k(3) } } }" == some true),
  (41, fun _ => owned "effect Ask { ask() -> Int }
    fn main() { handle ask() + 1 { ask(k) =>
      if(2 < 1) { k(1) } or { if(2 < 1) { k(2) } } or { if(1 < 2) { k(3) } } else { k(4) } } }"
    == some true),
  -- A function that selects among three and hands the first on does the same.
  (42, fun _ => owned "effect Ask { ask() -> Int }
    fn pick3(n, a, b, c) { match(n) { 0 => a(), 1 => b(a), _ => c(a) } }
    fn main() { handle ask() + 1 { ask(k) => pick3(1, { k(1) }, { k(2) }, { k(3) }) } }" == some true),
  (43, fun _ => owned "effect Ask { ask() -> Int }
    fn pick(c, a, b) { match(c) { Ok(_) => a(), Err(_) => b(a) } }
    fn main() { handle ask() + 1 { ask(k) => pick(2 < 1, { k(1) }, { k(2) }) } }" == some true),
  -- Two callables that each took the resumption for themselves own it twice,
  -- whichever of them is later run. Such a program compiles, typed but not shown
  -- well owned.
  (44, fun _ => owned "effect Ask { ask() -> Int }
    fn pick(c, a, b) { match(c) { Ok(_) => a(), Err(_) => b() } }
    fn main() { handle ask() + 1 { ask(k) => pick(1 < 2, { k(1) }, { k(2) }) } }" == some false),
  (45, fun _ => owned "effect Ask { ask() -> Int }
    fn main() { handle ask() + 1 { ask(k) =>
      let a = { k(1) }; let b = { k(2) }; if(1 < 2) { a() } else { b() } } }" == some false),
  -- Regions. A program whose Core follows the region rules is certified with
  -- them, and the proof then says it never reads or writes a mutable variable
  -- whose block has ended. That covers a variable used by the blocks and
  -- functions it is passed to, by reference or captured, however many variables
  -- a function is used with, through loops, handlers and data.
  (46, fun _ => borrowChecked "fn incr(p) { *p = *p + 1 }
    fn main() { let mut a = 1; let mut b = 2; incr(&mut a); incr(&mut b); incr(&mut a); a + b }"
    == some true),
  (47, fun _ => borrowChecked "fn swap(a, b) { let t = *a; *a = *b; *b = t; }
    fn main() { let mut x = 1; let mut y = 2; swap(&mut x, &mut y); x * 10 + y }" == some true),
  (48, fun _ => borrowChecked "fn main() { let mut n = 0; let bump = { n = n + 1; }; bump(); bump(); n }"
    == some true),
  (49, fun _ => borrowChecked "fn apply(f) { f() }
    fn main() { let mut x = 1; apply({ x = x + 1; }); apply({ x = x * 10; }); x }" == some true),
  (50, fun _ => borrowChecked "fn fact(n) { let mut acc = 1; let mut i = n;
      while({ 0 < i }) { acc = acc * i; i = i - 1; }; acc }
    fn main() { fact(5) }" == some true),
  (51, fun _ => borrowChecked "fn go(r, n) { if(0 < n) { *r = *r + n; go(r, n - 1) } else { *r } }
    fn main() { let mut t = 0; go(&mut t, 4) }" == some true),
  (52, fun _ => borrowChecked "fn main() { let mut x = 1; let s = Some(&mut x);
      match(s) { Some(p) => *p = 5, None => () }; x }" == some true),
  (53, fun _ => borrowChecked "effect Tick { tick() }
    fn work() { tick(); tick(); 3 }
    fn main() { let mut count = 0; let r = handle work() { tick(k) => count = count + 1; k(()) };
      r + count }" == some true),
  -- What the region rules have no type for compiles as before, without that
  -- proof: a reference that may be to one variable or to another, and a variable
  -- that holds something that uses the variable.
  (54, fun _ => borrowChecked "fn main() { let mut a = 1; let mut b = 2;
      let p = if(a < b) { &mut a } else { &mut b }; *p = 9; a + b }" == some false),
  -- A function that passes a reference to its own variable to itself has a type
  -- that binds the region; so has a callable a function is passed and gives a
  -- reference to its own variable, or two.
  (55, fun _ => borrowChecked "fn go(r, n) { let mut y = n; if(0 < n) { go(&mut y, n - 1) + *r } else { *r } }
    fn main() { let mut t = 5; go(&mut t, 3) }" == some true),
  (56, fun _ => borrowChecked "fn go(r: &Int, n: Int) -> Int { if(0 < n) { let mut y = n; go(&y, n - 1) } else { *r } }
    fn main() { let mut t = 5; go(&t, 3) }" == some true),
  (57, fun _ => borrowChecked "fn apply(f: for<'a> fn(&'a Int) -> Int) -> Int { let mut x = 1; let mut y = 2; f(&x) + f(&y) }
    fn main() { apply({ r => *r + 1 }) }" == some true),
  (58, fun _ => borrowChecked "fn both(f: for<'a, 'b> fn(&'a Int, &'b Int) -> Int) -> Int { let mut x = 3; let mut y = 4; f(&x, &y) }
    fn main() { both(fn(a, b) { *a * 10 + *b }) }" == some true),
  -- A callable for every lifetime kept in a declared type binds its regions
  -- there too.
  (59, fun _ => borrowChecked "struct V(for<'a> fn(&'a Int) -> Int)
    fn run(v: V) -> Int { match(v) { V(f) => let mut x = 4; let mut y = 6; f(&x) + f(&y) } }
    fn main() { run(V({ r => *r + 1 })) }" == some true),
  -- A reference kept in a declared type, or given by an effect, is of the
  -- region its lifetime says.
  (60, fun _ => borrowChecked "struct Holder<'a>(&'a Int)
    fn get<'a>(h: Holder<'a>) -> &'a Int { match(h) { Holder(r) => r } }
    fn main() { let mut x = 7; *get(Holder(&x)) }" == some true),
  (61, fun _ => borrowChecked "effect Reader<'a> { ask() -> &'a Int }
    fn use_it() -> Int { *ask() + 1 }
    fn main() { let mut x = 41; handle use_it() { ask(k) => k(&x) } }" == some true),
  (62, fun _ => borrowChecked "effect Yield { yield(Int) }
    fn main() { let mut saved = None; handle (yield(1) + 1) { yield(v, k) => saved = Some(k); 0 };
      match(replace(&mut saved, None)) { Some(k) => k(41), None => 0 } }" == some false),
  -- A label is a region as a mutable variable is: a program certified with the
  -- region rules never jumps to a label whose block has ended. With the ownership
  -- rules too, the only way left for it to go wrong is arithmetic overflow.
  (63, fun _ => borrowChecked "fn find(want) { @out { let mut i = 0;
      while({ i < 5 }) { if(i == want) { @out(i) }; i = i + 1; }; 0 - 1 } }
    fn main() { find(3) }" == some true),
  (64, fun _ => borrowChecked "fn first_big(a, b) { @done { if(10 < a) { @done(a) }; if(10 < b) { @done(b) }; 0 } }
    fn main() { first_big(3, 12) }" == some true),
  -- A callable made before a block, and given inside it one that jumps out of
  -- the block, has in its type a region that did not exist when it was made.
  (65, fun _ => borrowChecked "fn main() { let apply = { f => f() }; @out { apply({ @out(5) }); 0 } }"
    == some false),
  -- A callable given the type of another that uses a later variable is one more.
  (66, fun _ => borrowChecked "fn main() { let mut x = 1; let get = { x }; let mut y = 2;
      let both = { x + y }; let pick = if(x < y) { get } else { both }; pick() }" == some false),
  -- A borrow is a scope of its own in Core where the program's Core can then be
  -- shown to follow the rules for borrows. `checked_exclusive_safety` is about
  -- those: while one lasts, what it borrows is used only through it. Written as
  -- an argument of a call of a function, the scope is the call.
  (67, fun _ => lentBorrows "fn incr(p) { *p = *p + 1 }
    fn main() { let mut x = 5; incr(&mut x); incr(&mut x); x }" == some 2),
  (68, fun _ => lentBorrows "fn swap(a, b) { let t = *a; *a = *b; *b = t; }
    fn main() { let mut x = 1; let mut y = 2; swap(&mut x, &mut y); (x, y) }" == some 2),
  -- Two borrows for reading of one variable are two scopes, one inside the other.
  (69, fun _ => lentBorrows "fn add(a: &Int, b: &Int) { *a + *b }
    fn main() { let mut x = 4; add(&x, &x) }" == some 2),
  (70, fun _ => lentBorrows "fn bump(p: &mut Int, by: &Int) { *p = *p + *by }
    fn main() { let mut a = 1; let mut b = 10; bump(&mut a, &b); bump(&mut b, &a); (a, b) }"
    == some 4),
  -- The function may pass the borrow on, and may handle operations itself.
  (71, fun _ => lentBorrows "fn incr(p) { *p = *p + 1 }
    fn twice(p) { incr(p); incr(p) }
    fn main() { let mut x = 1; twice(&mut x); x }" == some 1),
  (72, fun _ => lentBorrows "effect Tick { tick() }
    fn work(p) { *p = *p + 1; handle { tick(); *p } () { tick(k) => k(()) } }
    fn main() { let mut n = 0; work(&mut n) }" == some 1),
  -- Given a name, the scope is the statements up to the last that mentions the
  -- name; the variable can be used again after them.
  (73, fun _ => unprovedBorrows "fn main() { let mut x = 1; let p = &mut x; *p = 2; x }" == some []),
  (74, fun _ => unprovedBorrows "fn main() { let mut x = 1; let r = &x; let s = &x; *r + *s + x }"
    == some []),
  -- What the statements bind and the rest of the block uses, the scope gives back.
  (75, fun _ => unprovedBorrows "fn main() { let mut x = 1; let p = &mut x; let v = *p + 1; *p = v;
      let w = v * 2; x = w; x + v }" == some []),
  -- Where something made from the borrow is used later, the scope takes that in.
  (76, fun _ => unprovedBorrows "fn main() { let mut x = 1; let p = &mut x; let q = p; *q = 2; *p = 3; x }"
    == some []),
  -- So it does where a call gives the borrow back, or the borrow is put in a value.
  (77, fun _ => unprovedBorrows "fn id(p: &mut Int) -> &mut Int { p }
    fn main() { let mut x = 1; let q = id(&mut x); *q = 5; x }" == some []),
  (78, fun _ => unprovedBorrows "fn main() { let mut x = 1; let s = Some(&mut x);
      match(s) { Some(p) => *p = 4, None => () }; x }" == some []),
  -- A callable that reads the variable can run while it is lent for reading.
  (79, fun _ => unprovedBorrows "fn main() { let mut x = 3; let r = &x; let get = { x }; get() + *r }"
    == some []),
  -- A borrow is not made a scope where the program would not then pass. Where
  -- the function performs an operation handled outside the call, the handler
  -- would run while the borrow is set aside;
  (80, fun _ => lentBorrows "effect Tick { tick() }
    fn work(p) { tick(); *p = *p + 1; tick(); *p }
    fn main() { let mut n = 0; handle work(&mut n) { tick(k) => k(()) } }" == some 0),
  -- A callable made before the call can be given the borrow: its type binds
  -- the region of the reference it takes.
  (81, fun _ => lentBorrows "fn apply(f, p) { f(p) }
    fn main() { let mut n = 0; apply({ q => *q = 7; }, &mut n); n }" == some 1),
  -- So can a function that lends to itself.
  (82, fun _ => lentBorrows "fn go(r, n) { if(0 < n) { let mut y = n; go(&mut y, n - 1) } else { *r } }
    fn main() { let mut t = 5; go(&mut t, 3) }" == some 2),
  -- A scope need not be whole statements at its end: where the variable is
  -- borrowed again in the statement that last uses `p`, the arguments that use
  -- `p` are computed first, and the scope ends with them.
  (83, fun _ => (unprovedBorrows "fn get(r: &Int) { *r }
    fn main() { let mut x = 7; let p = &mut x; get(p) + get(&x) }").map (·.length) == some 0),
  -- A borrow is made where it is first used, so two borrows written one after
  -- the other and used one after the other do not overlap;
  (84, fun _ => (unprovedBorrows "fn main() { let mut a = 1; let mut b = 2; let p = &mut a; let q = &mut b;
      *p = 10; a = a + 1; *q = 20; a + b }").map (·.length) == some 0),
  -- nor does a `defer` or an operation that comes before the first use fall
  -- inside the scope.
  (85, fun _ => (unprovedBorrows "fn main() { let mut x = 1; let p = &mut x; defer host_write(9); *p = 2; x }").map
    (·.length) == some 0),
  (86, fun _ => (unprovedBorrows "effect Ask { ask() }
    fn main() { let mut x = 0; handle { let p = &mut x; ask(); *p = 1; 0 }() { ask(k) => k(()) } }").map
    (·.length) == some 0),
  -- Each place is decided alone.
  (87, fun _ => lentBorrows "effect Tick { tick() }
    fn incr(p) { *p = *p + 1 }
    fn work(p) { tick(); *p = *p + 1; tick(); *p }
    fn main() { let mut x = 1; let mut n = 0; incr(&mut x);
      let r = handle work(&mut n) { tick(k) => k(()) }; r + x }" == some 1),
  -- A program that does not pass the region rules does not pass these.
  (88, fun _ => lentBorrows "fn main() { let mut a = 1; let mut b = 2;
      let p = if(a < b) { &mut a } else { &mut b }; *p = 9; a + b }" == none),
  -- A call with one borrow among its arguments is, in Core, a call with a scope
  -- around it: nothing is made for it. A second borrow costs a callable, and so
  -- does one given a name, whose scope is some statements and not a call.
  (89, fun _ => borrowFns "fn f(a, p, b) { *p = *p + a + b }
    fn main() { let mut x = 5; f(1, &mut x, 2); x }" == some 0),
  (90, fun _ => borrowFns "fn swap(a, b) { let t = *a; *a = *b; *b = t; }
    fn main() { let mut x = 1; let mut y = 2; swap(&mut x, &mut y); (x, y) }" == some 1),
  (91, fun _ => borrowFns "fn main() { let mut x = 1; let p = &mut x; *p = 2; x }" == some 1),
  -- Putting a new value in a variable and taking the old one is not a borrow.
  (92, fun _ => unprovedBorrows "fn main() { let mut x = 1; let old = replace(&mut x, 5); (old, x) }"
    == some [])
]

end Glorious.Checks
