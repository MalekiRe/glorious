/-!
# Test programs

Each case is a program, its input, and what it must print followed by its
value. The same cases are run on the Core machine, the Lean bytecode machine
and the Rust VM.
-/

namespace Glorious

structure Case where
  src : String
  input : List Int
  expect : String

def cases : List Case := [
  -- Arithmetic and operator fixity, all defined in the prelude.
  ⟨"fn main() { 1 + 2 * 3 }",
    [], "7"⟩,
  ⟨"fn main() { (1 + 2) * 3 - 4 }",
    [], "5"⟩,
  ⟨"fn main() { 10 - 3 - 2 }",
    [], "5"⟩,
  ⟨"fn main() { -7 + 2 }",
    [], "-5"⟩,

  -- Data, tuples and projection.
  ⟨"fn main() { (1, (2, 3)) }",
    [], "(1, (2, 3))"⟩,
  ⟨"fn main() { let p = (1, (2, 3)); p.1.0 + p.0 }",
    [], "3"⟩,
  ⟨"fn main() { let (a, (b, c)) = (1, (2, 3)); a + b * c }",
    [], "7"⟩,
  ⟨"struct Point(x, y)  fn main() { let Point(x, y) = Point(3, 4); x * x + y * y }",
    [], "25"⟩,
  ⟨"fn main() { Some(None) }",
    [], "Ok(Err(()))"⟩,

  -- Conditionals are library functions; only the selected branch runs.
  ⟨"fn main() { if(1 < 2) { 10 } else { 20 } }",
    [], "10"⟩,
  ⟨"fn main() { if(2 < 1) { 10 } else { 20 } }",
    [], "20"⟩,
  ⟨"fn main() { if(1 == 1) { 10 } }",
    [], "Ok(10)"⟩,
  -- The block after `else` runs in place of the body that was not run, and
  -- sees the same variables.
  ⟨"fn main() { let mut x = 0; if(2 < 1) { x = 1 } else { x = x + 2 }; x }",
    [], "2"⟩,
  ⟨"fn main() { let a = 1; let r = if(2 < 1) { a }; let a = 5; r else { a } }",
    [], "5"⟩,
  ⟨"fn main() { let n = 1; let r = if(2 < 1) { n }; let g = { r else { n + 10 } }; g() }",
    [], "11"⟩,
  -- `else` gives what failed to its fallback, which may name it or not.
  ⟨"fn main() { (Err(3) else { e => e + 1 }) + (None else { 7 }) + (Some(4) else { 0 }) }",
    [], "15"⟩,
  -- A block without parameters fits wherever a callable of one argument is
  -- expected, through a function of the program's own as well.
  ⟨"fn wrap(v, f) { v else f }  fn main() { wrap(None) { 3 } + wrap(Some(1)) { 9 } }",
    [], "4"⟩,
  ⟨"struct Box(run: fn(Int) -> Int)
    fn main() { let b = Box({ 5 }); match(b) { Box(f) => f(1) } }",
    [], "5"⟩,
  -- What a block is given need not be the body of an `if`.
  ⟨"fn zero(_) { 0 }
    fn main() {
      let n = 3;
      let r = if(2 < 1) { n };
      let r2 = match(2 < 1) { Ok(_) => r, Err(_) => Err(zero) };
      r2 else { n + 1 }
    }",
    [], "4"⟩,
  -- A function a program defines can choose between two blocks the same way.
  ⟨"effect Ask { ask() -> Int }
    fn pick(c, a, b) { match(c) { Ok(_) => a(), Err(_) => b(a) } }
    fn main() { handle ask() + 1 { ask(k) => pick(2 < 1, { k(1) }, { k(2) }) } }",
    [], "3"⟩,
  -- Coercions. The prelude declares that any failure can be forgotten, so a
  -- `Result` fits where an `Option` is expected: here the subject of a `match`,
  -- an argument, a declared result, and the result of a clause.
  ⟨"fn main() { match(if(2 < 1) { 10 }) { Some(n) => n, None => 0 } }",
    [], "0"⟩,
  ⟨"enum E { Bad(Int) }
    fn parse(n) { match(n) { 0 => Err(Bad(n)), _ => Ok(n) } }
    fn get(o) { match(o) { Some(n) => n, None => 7 } }
    fn main() { get(parse(0)) + get(parse(3)) + get(if(1 < 2) { 1 }) }",
    [], "11"⟩,
  ⟨"fn bump(flag) -> Result<(), ()> { let mut n = 0; if(flag) { n = n + 1 } }
    fn main() { bump(1 < 2); 0 }",
    [], "0"⟩,
  ⟨"fn main() {
      let r = match(2 < 1) { Ok(_) => if(2 < 1) { 2 }, Err(_) => None };
      match(r) { Some(n) => n, None => 5 }
    }",
    [], "5"⟩,
  -- A program declares its own the same way. One is applied only where
  -- exactly one fits, in one step, and where its name still means it.
  ⟨"struct Meters(Int)
    coerce meters
    fn meters(n: Int) -> Meters { Meters(n) }
    fn show(m) { match(m) { Meters(n) => n + 1 } }
    fn main() { show(5) + show(Meters(1)) }",
    [], "8"⟩,
  ⟨"struct Meters(Int)  struct Feet(Int)
    coerce meters  fn meters(n: Int) -> Meters { Meters(n) }
    coerce feet  fn feet(m: Meters) -> Feet { match(m) { Meters(n) => Feet(n * 3) } }
    fn show(f) { match(f) { Feet(n) => n } }
    fn main() { show(2) }",
    [], "error: 5:17: in `main`: argument 1 of `show`: expected `Feet`, found `Int`"⟩,
  ⟨"struct Meters(Int)
    coerce a  fn a(n: Int) -> Meters { Meters(n) }
    coerce b  fn b(n: Int) -> Meters { Meters(n + 1) }
    fn show(m) { match(m) { Meters(n) => n } }
    fn main() { show(5) }",
    [], "error: 5:17: in `main`: argument 1 of `show`: expected `Meters`, found `Int` (the coercions `a`, `b` all apply here, so none is chosen)"⟩,
  ⟨"fn main() { let option = 5; match(if(1 < 2) { 10 }) { Some(n) => n, None => 0 } }",
    [], "error: 1:29: in `main`: argument 2 of `match`: expected `fn(Result<Int, fn(()) -> Int>) -> _`, found `fn(Result<Int, ()>) -> Int`"⟩,
  ⟨"coerce nope  fn main() { 1 }",
    [], "error: `coerce nope`: there is no function `nope`"⟩,
  -- A failed `if` gives back its body, which was not run and still can be.
  ⟨"fn main() { match(if(1 != 1) { 10 }) { Ok(n) => n, Err(body) => body(()) + 1 } }",
    [], "11"⟩,
  ⟨"effect Boom { boom() -> ! }
  fn main() { handle (if(1 < 2) { 1 } else { boom() }) { boom() => 0 } }",
    [], "1"⟩,
  ⟨"effect Boom { boom() -> ! }
  fn main() { handle ((1 < 2) or { boom() }) { boom() => false } }",
    [], "Ok(())"⟩,
  ⟨"effect Boom { boom() -> ! }
  fn main() { handle ((2 < 1) and { boom() }) { boom() => true } }",
    [], "Err(())"⟩,
  ⟨"fn main() { not (1 < 2) }",
    [], "Err(())"⟩,
  ⟨"fn main() { (3 >= 3, 3 <= 2, 4 > 1) }",
    [], "(Ok(()), Err(()), Ok(()))"⟩,

  -- Matching is applying a pattern callable.
  ⟨"fn main() { match(Some(41)) { Some(x) => x + 1, None => 0 } }",
    [], "42"⟩,
  ⟨"fn main() { match(None) { Some(x) => x + 1, None => 0 } }",
    [], "0"⟩,
  ⟨"fn main() { match((Ok(1), Err(2))) { (Ok(a), Ok(b)) => a + b, (Ok(a), Err(b)) => a - b, _ => 0 } }",
    [], "-1"⟩,
  ⟨"fn classify { 0 => 100, 1 => 200, n => n }  fn main() { (classify(0), classify(1), classify(7)) }",
    [], "(100, 200, 7)"⟩,

  -- Functions, closures and captures.
  ⟨"fn twice(f, x) { f(f(x)) }  fn main() { twice({ n => n * 3 }, 2) }",
    [], "18"⟩,
  ⟨"fn adder(n) { { x => x + n } }  fn main() { let add5 = adder(5); add5(add5(1)) }",
    [], "11"⟩,
  ⟨"fn main() { let a = 2; let f = fn(x, y) { x * a + y }; f(10, 1) }",
    [], "21"⟩,
  ⟨"fn fact(n) { if(n < 2) { 1 } else { n * fact(n - 1) } }  fn main() { fact(10) }",
    [], "3628800"⟩,
  ⟨"fn sum(n, acc) { match(n) { 0 => acc, _ => tail sum(n - 1, acc + n) } }
  fn main() { sum(100, 0) }",
    [], "5050"⟩,
  ⟨"fn even(n) { match(n) { 0 => true, _ => tail odd(n - 1) } }
  fn odd(n) { match(n) { 0 => false, _ => tail even(n - 1) } }
  fn main() { even(10) }",
    [], "Ok(())"⟩,

  -- Effects: terminal operations, resumptions, completion clauses, forwarding.
  ⟨"effect Fail { fail(error) -> ! }
  fn main() { handle 1 + fail(7) { fail(e) => e * 2 } }",
    [], "14"⟩,
  ⟨"effect Ask { ask(x) }
  fn main() { handle ask(1) + ask(2) { ask(x) => x * 10 } }",
    [], "30"⟩,
  ⟨"effect Ask { ask(x) }
  fn main() { handle ask(1) + ask(2) { r => r + 1000, ask(x, k) => k(x * 10) } }",
    [], "1030"⟩,
  ⟨"effect Ask { ask(x) }
  fn main() { handle ask(1) + 5 { ask(x, k) => 99 } }",
    [], "99"⟩,
  ⟨"effect Ask { ask(x) }
  fn main() { handle (handle ask(1) + ask(2) { ask(1) => 100 }) { ask(x) => x * 10 } }",
    [], "120"⟩,
  ⟨"effect Ask { ask(x) }  effect Fail { fail(e) -> ! }
  fn main() { handle (handle ask(3) { fail(e) => 0 }) { ask(x) => x + 1 } }",
    [], "4"⟩,
  ⟨"effect Ask { ask(x) }
  fn main() { handle ask(1) { ask(x, k) => k(x) + k(x) } }",
    [], "error: 2:15: in `main`: `k` is used more than once, but a value that holds a resumption can be used only once"⟩,
  ⟨"effect Ask { ask(x) }  fn main() { ask(1) }",
    [], "error: `main` performs effects that nothing handles: {Ask}"⟩,

  -- State threaded through resumptions: a counter written with a handler.
  ⟨"effect Counter { next() }
  fn counting(body, start) {
      let run = handle body() {
          result => { n => (result, n) },
          next(k) => { n => (k(n))(n + 1) }
      };
      run(start)
  }
  fn main() { counting({ next() * 100 + next() * 10 + next() }, 1) }",
    [], "(123, 4)"⟩,

  -- Labels: early exit, the implicit function label, and escape.
  ⟨"fn main() { @out { 1 + @out(10) } + 5 }",
    [], "15"⟩,
  ⟨"fn main() { @out { 7 } }",
    [], "7"⟩,
  ⟨"fn find(target, a, b, c) {
      let check = { x => if(x == target) { @find(Some(x)) } };
      check(a); check(b); check(c);
      None
  }
  fn main() { (find(2, 1, 2, 3), find(9, 1, 2, 3)) }",
    [], "(Ok(2), Err(()))"⟩,
  ⟨"fn main() { let l = @out { @out }; l(1) }",
    [], "error: 1:13: in `main`: the result of the scope `@out`: expected `_`, found `fn(_) -> _` (this would need a type that contains itself)"⟩,

  -- Loops are a handler, a tail call and two terminal operations.
  ⟨"effect State { get(), put(value) }
  fn with_state(initial, body) {
      let run = handle body() {
          result => { s => result },
          get(k) => { s => (k(s))(s) },
          put(value, k) => { s => (k(()))(value) }
      };
      run(initial)
  }
  fn main() {
      with_state((0, 0)) {
          loop {
              let (i, total) = get();
              if(i == 5) { break(total) };
              put((i + 1, total + i))
          }
      }
  }",
    [], "10"⟩,

  -- The host: output is written in order, input is consumed, and both survive
  -- effects and early exits.
  ⟨"fn main() { print(1); print((2, 3)); 4 }",
    [], "1\n(2, 3)\n4"⟩,
  ⟨"fn main() { (read(), read(), read()) }",
    [7, 8], "(Ok(7), Ok(8), Err(()))"⟩,
  ⟨"fn sum_input(total) { match(read()) { Some(n) => tail sum_input(total + n), None => total } }
  fn main() { let total = sum_input(0); print(total); total * 2 }",
    [1, 2, 3, 4], "10\n20"⟩,
  ⟨"effect Fail { fail(e) -> ! }
  fn work() { print(1); fail(2); print(3); 0 }
  fn main() { handle work() { fail(e) => print(e * 10); 0 } }",
    [], "1\n20\n0"⟩,
  ⟨"fn countdown(n) { match(n) { 0 => (), _ => print(n); tail countdown(n - 1) } }
  fn main() { countdown(3) }",
    [], "3\n2\n1\n()"⟩,
  ⟨"fn main() { loop { let x = read() else { break(0) }; print(x * x) } }",
    [2, 3], "4\n9\n0"⟩,

  -- Cleanup. `defer` runs when the rest of its block is left by any path:
  -- a normal return, a label exit, a terminal operation, or cancellation. Inner
  -- cleanups run first, and before control continues at its destination.
  ⟨"fn main() { defer print(1); print(2); 3 }",
    [], "2\n1\n3"⟩,
  ⟨"fn main() { defer print(1); defer print(2); print(3); 0 }",
    [], "3\n2\n1\n0"⟩,
  ⟨"fn main() { let r = @out { defer print(1); @out(5); print(99); 0 }; print(r); 0 }",
    [], "1\n5\n0"⟩,
  ⟨"effect Fail { fail(e) -> ! }
  fn inner() { defer print(1); fail(7); print(99) }
  fn outer() { defer print(2); inner(); print(98); 0 }
  fn main() { handle outer() { fail(e) => print(e); 0 } }",
    [], "1\n2\n7\n0"⟩,
  ⟨"fn f(x) { defer print(0); if(x == 1) { @f(10) }; 20 }
  fn main() { (f(1), f(2)) }",
    [], "0\n0\n(10, 20)"⟩,
  -- Applying a label does not return, so one label can be applied where
  -- results of different types are expected, and also passed as a callable.
  ⟨"fn main() { @out { let a = if(true) { @out(1) } else { 5 }; let b = if(true) { @out(2) } else { (1, 2) }; 0 } }",
    [], "1"⟩,
  ⟨"fn apply(f, x) { f(x) }\n  fn main() { @out { apply(@out, 3) + 1 } }",
    [], "3"⟩,

  -- A resumptive operation does not run the cleanups it captures: they run when
  -- the resumed computation finally leaves, exactly once.
  ⟨"effect Ask { ask() }
  fn work() { defer print(1); let x = ask(); print(x); x }
  fn main() { handle work() { ask(k) => print(0); k(42) } }",
    [], "0\n42\n1\n42"⟩,

  -- Cancelling a resumption runs the cleanups of the continuation it captured.
  -- An arm that does not use its resumption cancels it before anything else.
  -- A resumption that is given a name and then forgotten some other way is
  -- still simply dropped.
  ⟨"effect Ask { ask() }
  fn work() { defer print(1); defer print(2); ask(); print(99); 0 }
  fn main() { handle work() { ask(k) => cancel(k); 7 } }",
    [], "2\n1\n7"⟩,
  ⟨"effect Ask { ask() }
  fn work() { defer print(1); ask(); print(99); 0 }
  fn main() { handle work() { ask(k) => 7 } }",
    [], "1\n7"⟩,
  ⟨"effect Ask { ask() }
  fn work() { defer print(1); ask(); print(99); 0 }
  fn main() { handle work() { ask(_) => print(5); 7 } }",
    [], "1\n5\n7"⟩,
  ⟨"effect Ask { ask() }
  fn work() { defer print(1); ask(); print(99); 0 }
  fn keep(k) { 7 }
  fn main() { handle work() { ask(k) => keep(k) } }",
    [], "7"⟩,
  ⟨"effect Ask { ask() }
  fn work() { defer print(1); ask() }
  fn main() { handle work() { ask(k) => cancel(k); k(1) } }",
    [], "error: 3:15: in `main`: `k` is used more than once, but a value that holds a resumption can be used only once"⟩,

  -- A resource bracket, written in the language.
  ⟨"effect Fail { fail(e) -> ! }
  fn with_resource(id, use) { print(id); defer print(0 - id); use(id) }
  fn main() {
      handle (with_resource(1) { a => with_resource(2) { b => fail(a + b) } }) {
          fail(e) => e * 100
      }
  }",
    [], "1\n2\n-2\n-1\n300"⟩,

  -- Mutable variables are cells: assignment persists across loop iterations,
  -- closures and handler arms, and a reference can be passed and written through.
  ⟨"fn main() { let mut total = 0; let mut i = 0;
     loop { if(i == 5) { break(()) }; total = total + i; i = i + 1 }; total }",
    [], "10"⟩,
  ⟨"fn main() { let mut i = 0; let mut acc = 1; while({ i < 5 }) { acc = acc * 2; i = i + 1 }; acc }",
    [], "32"⟩,
  ⟨"fn main() { let mut n = 0; let bump = { n = n + 1; n }; bump(); bump(); (bump(), n) }",
    [], "(3, 3)"⟩,
  ⟨"fn incr(p) { *p = *p + 1 }  fn main() { let mut x = 5; incr(&mut x); incr(&mut x); x }",
    [], "7"⟩,
  ⟨"fn swap(a, b) { let t = *a; *a = *b; *b = t }
  fn main() { let mut x = 1; let mut y = 2; swap(&mut x, &mut y); (x, y) }",
    [], "(2, 1)"⟩,
  ⟨"effect Tick { tick() }
  fn work() { tick(); tick(); tick(); 0 }
  fn main() { let mut count = 0; handle work() { tick() => count = count + 1 }; count }",
    [], "3"⟩,
  ⟨"fn main() { let mut x = 1; let x = x + 10; x }",
    [], "11"⟩,
  ⟨"fn main() { let x = 1; x = 2; x }",
    [], "error: 1:24: in `main`: `x` is not a mutable variable"⟩,
  ⟨"fn main() { let x = 1; &mut x }",
    [], "error: 1:24: in `main`: `x` is not a mutable variable, so it cannot be borrowed"⟩,

  -- A resumption is one-shot: it is resumed once or cancelled once, and the
  -- checker rejects a second use.
  ⟨"effect Choice { choose() }
  fn main() { handle (if(choose()) { 1 } else { 2 }) * 10 { choose(k) => k(true) } }",
    [], "10"⟩,
  ⟨"effect Choice { choose() }
  fn main() { handle choose() { choose(k) => k(true); k(false) } }",
    [], "error: 2:15: in `main`: `k` is used more than once, but a value that holds a resumption can be used only once"⟩,
  ⟨"effect Choice { choose() }
  fn main() { handle choose() { choose(k) => cancel(k); k(true) } }",
    [], "error: 2:15: in `main`: `k` is used more than once, but a value that holds a resumption can be used only once"⟩,
  ⟨"effect Choice { [2, 2] choose() }  fn main() { 0 }",
    [], "error: operation `choose`: a resumption is used at most once, so write `[0, 1]` or `[1, 1]`"⟩,

  -- Types and effects are inferred. Mistakes that used to surface when a program
  -- ran are now reported before it does.
  ⟨"fn main() { 1 + (2, 3) }",
    [], "error: 1:13: in `main`: argument 2 of `+`: expected `Int`, found `(Int, Int)`"⟩,
  ⟨"fn f(a, b) { a }  fn main() { f(1) }",
    [], "error: 1:31: in `main`: `f` takes 2 arguments, but is given 1"⟩,
  ⟨"fn main() { let x = 5; x(1) }",
    [], "error: 1:24: in `main`: `x` is called with 1 argument: expected `fn(Int) -> _`, found `Int`"⟩,
  ⟨"fn main() { (1, 2).5 }",
    [], "error: 1:13: in `main`: a tuple of 2 values has no field 5"⟩,
  ⟨"fn main() { match(Some(1)) { None => 0 } }",
    [], "error: 1:13: in `main`: the clauses of this callable do not cover every case"⟩,
  ⟨"fn f { 0 => 1 }  fn main() { f(5) }",
    [], "error: in `f`: the clauses of `f` do not cover every case"⟩,
  ⟨"fn main() { let (a, b) = (1, 2, 3); a }",
    [], "error: 1:13: in `main`: a tuple pattern: expected `(_, _)`, found `(Int, Int, Int)`"⟩,
  ⟨"fn main() { if(1) { 2 } }",
    [], "error: 1:13: in `main`: argument 1 of `if`: expected `Result<_, _>`, found `Int`"⟩,
  ⟨"effect Fail { fail(e) -> ! }  fn risky() { fail(1) }  fn main() { risky() }",
    [], "error: `main` performs effects that nothing handles: {Fail}"⟩,
  ⟨"effect Ask { ask(x) }  fn main() { handle ask(1) { ask(1) => 2 } }",
    [], "error: `main` performs effects that nothing handles: {Ask}"⟩,
  ⟨"fn main() { let mut x = 1; x = (1, 2); x }",
    [], "error: 1:28: in `main`: the assigned value: expected `Int`, found `(Int, Int)`"⟩,
  ⟨"fn incr(p) { *p = *p + 1 }  fn main() { incr(5) }",
    [], "error: 1:41: in `main`: argument 1 of `incr`: expected `&mut Int`, found `Int`"⟩,

  -- A declaration with inferred fields has one type throughout the program; one
  -- with type parameters is polymorphic.
  ⟨"enum Wrap { Wrap(v) }  fn main() { (Wrap(1), Wrap((1, 2))) }",
    [], "error: 1:36: in `main`: argument 1 of constructor `Wrap`: expected `Int`, found `(Int, Int)`"⟩,
  ⟨"enum Wrap<T> { Wrap(T) }  fn main() { (Wrap(1), Wrap((1, 2))) }",
    [], "(Wrap(1), Wrap((1, 2)))"⟩,
  ⟨"enum List<T> { Nil, Cons(T, List<T>) }
  fn length(list) { match(list) { Nil => 0, Cons(_, rest) => 1 + length(rest) } }
  fn main() { (length(Cons(1, Cons(2, Nil))), length(Cons((), Nil))) }",
    [], "(2, 1)"⟩,
  ⟨"effect Emit<T> { emit(T) }
  fn work() { emit(1); emit(2); 0 }
  fn main() { handle work() { emit(x) => print(x) } }",
    [], "1\n2\n0"⟩,

  -- Functions are generalised: one definition is used at several types.
  ⟨"fn id(x) { x }  fn main() { (id(1), id((1, 2)), id(id)(3)) }",
    [], "(1, (1, 2), 3)"⟩,
  ⟨"fn apply(f, x) { f(x) }  fn main() { (apply({ x => x + 1 }, 1), apply({ p => p.0 }, (7, 8))) }",
    [], "(2, 7)"⟩,
  ⟨"fn first(p) { p.0 }  fn main() { first((1, 2)) }",
    [], "error: 1:15: in `first`: `.0` reads a field of a value whose type is not known here; annotate the value it is read from"⟩,
  ⟨"fn first<A, B>(p: (A, B)) -> A { p.0 }  fn main() { (first((1, 2)), first(((3, 4), 5))) }",
    [], "(1, (3, 4))"⟩,

  -- Annotations are optional and checked when written. A function's own type
  -- parameters stand for any type, so its body cannot assume one.
  ⟨"fn double(x: Int) -> Int { x * 2 }  fn main() { double(21) }",
    [], "42"⟩,
  ⟨"fn double(x: Int) -> Int { x * 2 }  fn main() { double((1, 2)) }",
    [], "error: 1:49: in `main`: argument 1 of `double`: expected `Int`, found `(Int, Int)`"⟩,
  ⟨"fn double(x: Int) -> (Int, Int) { x * 2 }  fn main() { double(1) }",
    [], "error: 1:35: in `double`: the result of a clause: expected `(Int, Int)`, found `Int`"⟩,
  ⟨"fn id<T>(x: T) -> T { x }  fn main() { (id(1), id((1, 2))) }",
    [], "(1, (1, 2))"⟩,
  ⟨"fn bad<T>(x: T) -> T { 1 }  fn main() { bad(2) }",
    [], "error: 1:24: in `bad`: the result of a clause: expected `T`, found `Int`"⟩,
  ⟨"fn swap<A, B>(pair: (A, B)) -> (B, A) { (pair.1, pair.0) }  fn main() { swap((1, (2, 3))) }",
    [], "((2, 3), 1)"⟩,
  ⟨"fn incr(p: &mut Int) { *p = *p + 1 }  fn main() { let mut x = 1; incr(&mut x); x }",
    [], "2"⟩,
  ⟨"fn twice(f: fn(Int) -> Int, x: Int) -> Int { f(f(x)) }  fn main() { twice({ n => n + 3 }, 1) }",
    [], "7"⟩,
  ⟨"fn main() -> Int { (1, 2) }",
    [], "error: 1:20: in `main`: the result of a clause: expected `Int`, found `(Int, Int)`"⟩,
  ⟨"fn f(x: Nope) { x }  fn main() { f(1) }",
    [], "error: in `f`: unknown type `Nope`"⟩,


  -- Effects are part of a function's type: they are inferred, they follow a
  -- closure to wherever it is finally called, and a handler removes only what
  -- it handles completely.
  ⟨"fn even(n) { if(n == 0) { true } else { odd(n - 1) } }\n  fn odd(n) { if(n == 0) { false } else { even(n - 1) } }\n  fn main() { (even(10), odd(7)) }",
    [], "(Ok(()), Ok(()))"⟩,
  ⟨"effect State<S> { get() -> S, put(S) }\n  fn run(init, body) { let mut s = init; handle body() { get() => s, put(v) => s = v } }\n  fn main() { (run(1, { put(get() + 1); get() }), run((1, 2), { put((get().1, get().0)); get() })) }",
    [], "(2, (2, 1))"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle { handle ask() + ask() { ask() => 1 } }() + ask() { ask() => 10 } }",
    [], "12"⟩,
  ⟨"effect Ask { ask(Int) -> Int }\n  fn main() { handle { handle ask(1) + ask(2) { ask(1) => 100 } }() { ask(n) => n } }",
    [], "102"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn mk() { { ask() } }\n  fn main() { let f = handle mk() { ask() => 1 }; f() }",
    [], "error: `main` performs effects that nothing handles: {Ask}"⟩,

  -- Coverage is checked through tuples and nested constructors, and for `let`.
  ⟨"fn both { (Ok(_), Ok(_)) => 1, (Err(_), _) => 2, (_, Err(_)) => 3 }\n  fn main() { both((true, false)) }",
    [], "3"⟩,
  ⟨"fn both { (Ok(_), Ok(_)) => 1, (Err(_), Err(_)) => 2 }\n  fn main() { both((true, false)) }",
    [], "error: in `both`: the clauses of `both` do not cover every case"⟩,
  ⟨"fn main() { let Some(x) = Some(1); x }",
    [], "error: 1:13: in `main`: the pattern of this `let` does not cover every case"⟩,
  ⟨"struct Pair<A, B>(first: A, second: B)\n  fn swap(p) { let Pair(a, b) = p; Pair(b, a) }\n  fn main() { swap(Pair(1, (2, 3))) }",
    [], "Pair((2, 3), 1)"⟩,


  -- A callable bound by `let` can be used at several types, unless it shares
  -- state that fixes one.
  ⟨"fn main() { let id = { x => x }; (id(1), id((1, 2))) }",
    [], "(1, (1, 2))"⟩,
  ⟨"fn main() { let first = { p => p.0 }; first((1, 2)) }",
    [], "1"⟩,
  ⟨"fn main() { let mut slot = None; let put = { v => slot = Some(v) }; put(1); put((1, 2)); 0 }",
    [], "error: 1:77: in `main`: argument 1 of `put`: expected `Int`, found `(Int, Int)`"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { let call = { f => f() }; call({ 1 }) + handle call({ ask() }) { ask() => 2 } }",
    [], "3"⟩,
  ⟨"fn konst<T>(x: T) -> T { let g = { y => x }; g(1); g((1, 2)) }\n  fn main() { konst(5) }",
    [], "5"⟩,

  -- A label ends with its scope. A callable that can jump to it may be passed
  -- down, but not kept anywhere that outlives the scope.
  ⟨"fn find(n) { if(n > 3) { @find(1) }; 0 }\n  fn main() { (find(1), find(9)) }",
    [], "(0, 1)"⟩,
  ⟨"fn apply(f) { f() }\n  fn main() { @out { apply({ @out(5) }); 0 } }",
    [], "5"⟩,
  ⟨"fn main() { let apply = { f => f() }; @out { apply({ @out(5) }); 0 } }",
    [], "5"⟩,
  ⟨"fn compose(f, g) { { x => f(g(x)) } }\n  fn main() { @out { let h = compose({ v => @out(v + 1) }, { v => v * 2 }); h(5); 0 } }",
    [], "11"⟩,
  ⟨"enum Box<T> { Box(T) }\n  fn main() { @out { let b = Box({ @out(1) }); match(b) { Box(f) => f() }; 0 } }",
    [], "1"⟩,
  ⟨"fn main() { @a { @b { if(1 < 2) { @a(1) }; @b(2) } + 10 } }",
    [], "1"⟩,
  ⟨"fn main() { let mut f = { x => 0 }; @out { f = { x => @out(x) }; 1 }; f(2) }",
    [], "error: 1:37: in `main`: a callable that jumps to `@out` could be called after `@out` has ended: `f`, which outlives the scope, could hold it"⟩,
  ⟨"fn main() { let got = @out { Some({ @out(None) }) }; match(got) { Some(f) => f(); 0, None => 1 } }",
    [], "error: 1:13: in `main`: a callable that jumps to `@out` could be called after `@out` has ended: it is the result of the scope"⟩,
  ⟨"effect Emit<T> { emit(T) }\n  fn work() { @out { emit({ @out(1) }); 2 } }\n  fn main() { handle work() { emit(f, k) => f() } }",
    [], "error: 2:15: in `work`: a callable that jumps to `@out` could be called after `@out` has ended: it is passed to a handler of `Emit` outside"⟩,
  ⟨"fn compose(f, g) { { x => f(g(x)) } }\n  fn main() { let mut cell = { x => x }; @out { cell = compose({ v => @out(0) }, { v => v }); 0 }; cell(1) }",
    [], "error: 2:42: in `main`: a callable that jumps to `@out` could be called after `@out` has ended: `cell`, which outlives the scope, could hold it"⟩,
  ⟨"fn main() { let mut cell = { v => 0 }; @out { let g = { v => @out(v) }; cell = g; 1 }; cell(2) }",
    [], "error: 1:40: in `main`: a callable that jumps to `@out` could be called after `@out` has ended: `cell`, which outlives the scope, could hold it"⟩,
  ⟨"enum Box { Box(inner) }\n  fn main() { @out { let b = Box({ @out(1) }); 0 } }",
    [], "error: 2:15: in `main`: a callable that jumps to `@out` could be called after `@out` has ended: it is stored in a declaration whose field types are inferred; give that declaration a type parameter"⟩,
  ⟨"struct Callback(run: fn() -> Int)\n  fn main() { @out { let c = Callback({ @out(1) }); 0 } }",
    [], "error: 2:15: in `main`: a callable that jumps to `@out` could be called after `@out` has ended: it is stored in a declaration's `fn` field; give that declaration a type parameter for the field"⟩,
  ⟨"fn f(cell) { *cell = { @f(1) }; 0 }\n  fn main() { let mut c = { 0 }; f(&mut c); c() }",
    [], "error: in `f`: a callable that jumps to `@f` could be called after `@f` has ended: the caller could hold it through a parameter"⟩,
  ⟨"fn f() { { @f({ 0 }) } }\n  fn main() { f()() }",
    [], "error: in `f`: a callable that jumps to `@f` could be called after `@f` has ended: it is returned from the function"⟩,
  ⟨"fn find(each, target) { each({ x => if(x == target) { @find(x) } }); 0 }\n  fn main() { find({ f => f(1); f(2); f(3) }, 2) }",
    [], "error: in `find`: a callable that jumps to `@find` could be called after `@find` has ended: the caller could hold it through a parameter"⟩,

  -- A resumption is not tied to a scope: it may be kept and called later.
  ⟨"effect Yield { yield(Int) }\n  fn main() { let mut saved = None; handle (yield(1) + 1) { yield(v, k) => saved = Some(k); 0 }; match(replace(&mut saved, None)) { Some(k) => k(41), None => 0 } }",
    [], "42"⟩,

  -- A trailing `;` discards the value of the last expression, so the block
  -- yields unit. Without it, the value of an `if` with no `else` is an option.
  ⟨"fn each(f, n) { if(n > 0) { f(n); each(f, n - 1) }; }  fn main() { each(print, 3) }",
    [], "3\n2\n1\n()"⟩,
  ⟨"fn each(f, n) { if(n > 0) { f(n); each(f, n - 1) } }  fn main() { each(print, 3) }",
    [], "error: in `each`: `each` is used recursively at a different type: expected `fn(fn(Int) -> _, Int) -> _`, found `fn(fn(Int) -> _, Int) -> Result<_, fn(()) -> _>` (this would need a type that contains itself); if the last expression of the body is not meant as the result, end it with `;`"⟩,
  ⟨"fn log(x) { if(x > 0) { print(x) } }  fn main() { log(1) }",
    [], "1\nOk(())"⟩,
  ⟨"fn log(x) { if(x > 0) { print(x) }; }  fn main() { log(1) }",
    [], "1\n()"⟩,
  ⟨"fn main() { let f = { x => x + 1; }; f(1) }",
    [], "()"⟩,


  -- A mutable variable lasts until the end of its block, and its storage is
  -- released there. A reference to it, or a callable that uses it, may be passed
  -- down but not kept anywhere that outlives the block.
  ⟨"fn incr(p) { *p = *p + 1; }\n  fn main() { let mut x = 1; incr(&mut x); x }",
    [], "2"⟩,
  ⟨"fn twice(f) { f(); f() }\n  fn main() { let mut n = 0; twice({ n = n + 1; }); n }",
    [], "2"⟩,
  ⟨"fn mk() { let mut n = 0; { n = n + 1; n } }\n  fn main() { mk()() }",
    [], "error: 1:11: in `mk`: `n` could be used after its block has ended: something that uses it is the block's result"⟩,
  ⟨"fn mk() { let mut n = 0; &mut n }\n  fn main() { *mk() }",
    [], "error: 1:11: in `mk`: `n` could be used after its block has ended: something that uses it is the block's result"⟩,
  ⟨"fn main() { let mut a = 1; let mut p = &mut a; { let mut b = 2; p = &mut b; }(); *p }",
    [], "error: 1:50: in `main`: `b` could be used after its block has ended: `p`, which outlives the scope, could hold it"⟩,
  ⟨"fn with(body) { let mut n = 0; body(&mut n); n }\n  fn main() { with({ p => *p = 5; }) }",
    [], "error: 1:17: in `with`: `n` could be used after its block has ended: `body`, which outlives the scope, could hold it"⟩,

  -- A resumption holds the computation it captured and the handler around it.
  -- It may be kept, but not beyond a variable or label either of them uses.
  ⟨"effect Yield { yield() }\n  fn main() { let mut saved = None; let r = handle { yield(); 5 }() { yield(k) => saved = Some(k); 0 }; match(replace(&mut saved, None)) { Some(k) => r + k(()), None => r } }",
    [], "5"⟩,
  ⟨"effect Tick { tick() }\n  fn work() { tick(); tick(); 3 }\n  fn main() { let mut count = 0; let r = handle work() { tick(k) => count = count + 1; k(()) }; (r, count) }",
    [], "(3, 2)"⟩,
  ⟨"effect Tick { tick() }\n  fn work() { tick(); tick(); 0 }\n  fn main() { let mut saved = None; { let mut count = 0; handle work() { tick(k) => count = count + 1; saved = Some(k); 0 } }(); match(saved) { Some(k) => k(()), None => 0 } }",
    [], "error: 3:39: in `main`: `count` could be used after its block has ended: `saved`, which outlives the scope, could hold it"⟩,
  ⟨"effect Tick { tick() }\n  fn main() { let mut saved = None; @out { handle { tick(); @out(1) }() { tick(k) => saved = Some(k); 0 } }; match(saved) { Some(k) => k(()), None => 0 } }",
    [], "error: 2:37: in `main`: a callable that jumps to `@out` could be called after `@out` has ended: `saved`, which outlives the scope, could hold it"⟩,

  -- A `tail` call leaves nothing behind in the caller, so it cannot be written
  -- where a variable is still to be released or a `defer` is still to run.
  ⟨"fn count(n, acc) { let mut x = n; x = x - 1; tail count2(x, acc) }\n  fn count2(n, acc) { acc }\n  fn main() { count(3, 0) }",
    [], "error: 1:46: `tail` cannot be used here: `x` is released after the call returns"⟩,
  ⟨"fn f(n) { defer print(n); tail g(n) }\n  fn g(n) { n }\n  fn main() { f(1) }",
    [], "error: 1:27: `tail` cannot be used here: a `defer` runs after the call returns"⟩,
  ⟨"fn count(n) { let mut x = n; if(x == 0) { 0 } else { tail count(x - 1) } }\n  fn main() { count(3) }",
    [], "0"⟩,


  -- Anything that holds a resumption can be used only once: a callable that
  -- captured it, data it is stored in. A function says, by how it uses its
  -- parameters, whether it can be given such a value.
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => let f = { k(1) }; f() } }",
    [], "2"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => let f = { k(1) }; f(); f() } }",
    [], "error: 2:44: in `main`: `f` is used more than once, but a value that holds a resumption can be used only once"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => let pair = (k, 5); let (again, n) = pair; again(n) } }",
    [], "6"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => let pair = (k, 5); pair.0(pair.1) } }",
    [], "error: 2:44: in `main`: `pair` is used more than once, but a value that holds a resumption can be used only once"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn once(f) { f() }\n  fn main() { handle ask() + 1 { ask(k) => once({ k(1) }) } }",
    [], "2"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn twice(f) { f(); f() }\n  fn main() { handle ask() + 1 { ask(k) => twice({ k(1) }) } }",
    [], "error: 3:44: in `main`: `twice` may use what it is given more than once, but a value that holds a resumption can be used only once"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn both(x) { (x, x) }\n  fn main() { handle ask() + 1 { ask(k) => both(k); 0 } }",
    [], "error: 3:44: in `main`: `both` may use what it is given more than once, but a value that holds a resumption can be used only once"⟩,

  -- Clauses of one callable are alternatives, so each may use the resumption.
  -- So may two separate callables of which a function runs only one: uses are
  -- counted along the paths the program can take, following calls into the
  -- functions that make the choice.
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => match(1 < 2) { Ok(_) => k(10), Err(_) => k(20) } } }",
    [], "11"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => if(1 < 2) { k(10) } else { 0 } } }",
    [], "11"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => k(if(1 < 2) { 10 } else { 20 }) } }",
    [], "11"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => if(1 < 2) { k(10) } else { k(20) } } }",
    [], "11"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => if(1 < 2) { if(2 < 1) { k(1) } else { k(2) } } else { k(3) } } }",
    [], "3"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => match((1 < 2) and { 2 < 3 }) { Ok(_) => k(1), Err(_) => k(2) } } }",
    [], "2"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn pick(c, a, b) { match(c) { Ok(_) => a(), Err(_) => b() } }\n  fn main() { handle ask() + 1 { ask(k) => pick(1 < 2, { k(1) }, { k(2) }) } }",
    [], "2"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn decide(c, k) { if(c) { k(1) } else { k(2) } }\n  fn main() { handle ask() + 1 { ask(k) => decide(1 < 2, k) } }",
    [], "2"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => let a = { k(1) }; let b = { k(2) }; if(1 < 2) { a() } else { b() } } }",
    [], "2"⟩,

  -- Naming a resumption, or putting it in a value, is not yet a use: calling it
  -- is, and so is letting it go where the count cannot follow.
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => if(1 < 2) { let j = k; j(1) } else { k(2) } } }",
    [], "2"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => match(if(1 < 2) { Some(k) } else { None }) { Some(j) => j(1), None => k(2) } } }",
    [], "2"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => k; k(5) } }",
    [], "6"⟩,

  -- More than one use along some path is still rejected, and so is anything the
  -- count cannot follow: a callable handed to a function value, or a path cut
  -- short by leaving through a label.
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => if(1 < 2) { k(10) } else { k(20) }; k(30) } }",
    [], "error: 2:15: in `main`: `k` is used more than once, but a value that holds a resumption can be used only once"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => if(1 < 2) { k(10); k(11) } else { k(20) } } }",
    [], "error: 2:15: in `main`: `k` is used more than once, but a value that holds a resumption can be used only once"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn both(a, b) { a(); b() }\n  fn main() { handle ask() + 1 { ask(k) => both({ k(1) }, { k(2) }) } }",
    [], "error: 3:15: in `main`: `k` is used more than once, but a value that holds a resumption can be used only once"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => let a = { k(1) }; let b = { k(2) }; a() + b() } }",
    [], "error: 2:15: in `main`: `k` is used more than once, but a value that holds a resumption can be used only once"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => let j = k; j(1) + k(2) } }",
    [], "error: 2:15: in `main`: `k` is used more than once, but a value that holds a resumption can be used only once"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn wrap(k) { { k(1) } }\n  fn main() { handle ask() + 1 { ask(k) => let f = wrap(k); f() + f() } }",
    [], "error: 3:44: in `main`: `f` is used more than once, but a value that holds a resumption can be used only once"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => let box = Some(k); match(box) { Some(j) => j(1) + k(2), None => 0 } } }",
    [], "error: 2:15: in `main`: `k` is used more than once, but a value that holds a resumption can be used only once"⟩,
  ⟨"effect Ask { ask() -> Int }\n  effect Stop { stop() -> ! }\n  fn main() { handle ask() + 1 { ask(k) => handle k(1) { stop() => k(2) } } }",
    [], "error: 3:15: in `main`: `k` is used more than once, but a value that holds a resumption can be used only once"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn go(run) { handle ask() + 1 { ask(k) => run({ k(1) }, { k(2) }) } }\n  fn main() { go(fn(f, g) { f() }) }",
    [], "error: 2:16: in `go`: `k` is used more than once, but a value that holds a resumption can be used only once"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => @out { if(1 < 2) { @out(k(1)) }; k(2) } } }",
    [], "error: 2:15: in `main`: `k` is used more than once, but a value that holds a resumption can be used only once"⟩,

  -- A mutable variable can hold a resumption, but reading it would copy it:
  -- `replace` takes the value out and leaves another in its place.
  ⟨"effect Yield { yield(Int) }\n  fn main() { let mut saved = None; handle (yield(1) + 1) { yield(v, k) => saved = Some(k); 0 }; match(saved) { Some(k) => k(41), None => 0 } }",
    [], "error: 2:98: in `main`: reading the mutable variable `saved` copies its value (`replace` takes it out instead), but a value that holds a resumption can be used only once"⟩,
  ⟨"fn main() { let mut x = 1; let old = replace(&mut x, 5); (old, x) }",
    [], "(1, 5)"⟩,

  -- The arm of an operation that can be resumed may run many times, so it
  -- cannot use up something from outside.
  ⟨"effect Ask { ask() -> Int }\n  effect Tick { tick() }\n  fn work() { tick(); tick(); 0 }\n  fn main() { handle ask() { ask(outer) => handle work() { tick() => outer(1); } } }",
    [], "error: 4:15: in `main`: `outer` is used more than once, but a value that holds a resumption can be used only once"⟩,


  -- A callee may perform fewer effects than are permitted where it is called,
  -- so one function value can be called both inside and outside a handler. It
  -- is then held to what every such place permits.
  ⟨"fn g(f) { f(0); let mut i = 0; while({ i < 2 }) { f(i); i = i + 1 }; 0 }\n  fn main() { g(print) }",
    [], "0\n0\n1\n0"⟩,
  ⟨"fn mk() { { x => print(x) } }\n  fn main() { let show = mk(); show(0); let mut i = 0; while({ i < 2 }) { show(i); i = i + 1 }; 0 }",
    [], "0\n0\n1\n0"⟩,
  ⟨"effect Ask { ask() -> Int }\n  effect Log { log(Int) }\n  fn main() { handle ask() + 1 { ask(k) => handle { log(1); k(5) }() { log(x) => print(x) } } }",
    [], "1\n6"⟩,
  ⟨"effect A { a() -> Int }\n  effect B { b() -> Int }\n  fn both(f) { (handle f() { a() => 1 }) + (handle f() { b() => 2 }) }\n  fn main() { both({ 5 }) }",
    [], "10"⟩,
  ⟨"effect A { a() -> Int }\n  effect B { b() -> Int }\n  fn both(f) { (handle f() { a() => 1 }) + (handle f() { b() => 2 }) }\n  fn main() { both({ a() }) }",
    [], "error: `main` performs effects that nothing handles: {A}"⟩,
  ⟨"effect Log { log(Int) }\n  fn g(f) { f(0); handle f(1) { log(x) => print(x) } }\n  fn main() { g({ x => log(x); }) }",
    [], "error: `main` performs effects that nothing handles: {Log}"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { let mut n = 0; handle ask() + 1 { ask(k) => while({ n < 2 }) { n = n + 1; k(n); }; 0 } }",
    [], "error: 2:59: in `main`: `while` may use what it is given more than once, but a value that holds a resumption can be used only once"⟩,

  -- A cleanup runs in place, with everything below it still there, so it can
  -- jump to an enclosing label even while that label is being left. A cleanup
  -- that starts an exit of its own replaces the one in progress, and no cleanup
  -- is skipped. A cleanup cannot perform effects.
  ⟨"fn main() { @out { defer @out(2); @out(1) } }",
    [], "2"⟩,
  ⟨"fn main() { @out { defer @out(2); 5 } }",
    [], "2"⟩,
  ⟨"effect Tick { tick() }\n  effect Stop { stop(Int) -> ! }\n  fn work() { defer tick(); stop(1) }\n  fn main() { let mut n = 0; let r = handle (handle work() { tick() => n = n + 1 }) { stop(v) => v }; (r, n) }",
    [], "error: 3:15: in `work`: a `defer` cannot perform effects: operation `tick` cannot be performed here: effect `Tick` is not handled here"⟩,
  ⟨"fn main() { @outer { @inner { defer print(1); defer @outer(9); @inner(0) }; 5 } }",
    [], "1\n9"⟩,
  ⟨"effect Tick { tick() }\n  effect Stop { stop(Int) -> ! }\n  fn work() { defer stop(2); stop(1) }\n  fn main() { handle work() { stop(v) => print(v); v } }",
    [], "error: 3:15: in `work`: a `defer` cannot perform effects: operation `stop` cannot be performed here: effect `Stop` is not handled here"⟩,
  ⟨"effect Tick { tick() }\n  effect Stop { stop(Int) -> ! }\n  effect Ask { ask() -> Int }\n  fn work() { defer tick(); ask() }\n  fn main() { let mut n = 0; handle (handle work() { tick() => n = n + 1 }) { ask(k) => cancel(k); n } }",
    [], "error: 4:15: in `work`: a `defer` cannot perform effects: operation `tick` cannot be performed here: effect `Tick` is not handled here"⟩,

  ⟨"effect Tick { tick() }\n  effect Stop { stop(Int) -> ! }\n  fn work() { defer tick(); stop(1) }\n  fn main() { handle (handle work() { tick(k) => k(()) + 1 }) { stop(v) => v } }",
    [], "error: 3:15: in `work`: a `defer` cannot perform effects: operation `tick` cannot be performed here: effect `Tick` is not handled here"⟩,


  -- `cancel` gives up a callable without calling it. Only a resumption has
  -- anything to clean up.
  ⟨"fn main() { cancel(5); 0 }",
    [], "error: 1:13: in `main`: argument 1 of `cancel`: expected `fn(_) -> _`, found `Int`"⟩,
  ⟨"fn main() { cancel(fn() { 1 }); 0 }",
    [], "error: 1:13: in `main`: argument 1 of `cancel`: expected `fn(_) -> _`, found `fn() -> Int`"⟩,
  ⟨"fn main() { cancel({ x => x + 1 }); 0 }",
    [], "0"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn work() { @inner { defer @inner(5); ask() } }\n  fn main() { handle work() { r => (r, r), ask(k) => match(cancel(k)) { () => (0, 0) } } }",
    [], "(0, 0)"⟩,
  -- A cleanup of a cancelled computation can jump to a label inside it, and the
  -- computation then runs on where it is being cancelled. So `cancel` needs
  -- what the callable may perform to be handled there, as a call would.
  ⟨"effect A { a() -> Int }\n  effect H { h() -> Int }\n  fn work() { let r = @out { defer @out(1); h() }; r + a() }\n  fn main() { handle (handle work() { h(k) => cancel(k); 7 }) { a(k2) => k2(100) } }",
    [], "7"⟩,
  ⟨"effect A { a() -> Int }\n  effect H { h() -> Int }\n  effect G { give(k) -> Int }\n  fn work() { let r = @out { defer @out(1); h() }; r + a() }\n  fn main() { handle (handle (handle work() { h(k) => give(k) }) { a(k2) => k2(100) }) { give(k, kg) => cancel(k); 7 } }",
    [], "error: `main` performs effects that nothing handles: {A, G}"⟩,

  -- Borrows. `&x` borrows a mutable variable for reading and `&mut x` for
  -- writing too, for as long as what holds the reference may still be used.
  -- A `&mut` reference used as a value is lent, not copied. A callable that
  -- mentions a variable does not borrow it: it uses the variable when it runs.
  ⟨"fn main() { let mut x = 1; let p = &mut x; *p = 2; x }",
    [], "2"⟩,
  ⟨"fn main() { let mut x = 1; let r = &x; let s = &x; *r + *s + x }",
    [], "3"⟩,
  ⟨"fn incr(p) { *p = *p + 1 }\n  fn twice(p) { incr(p); incr(p) }\n  fn main() { let mut x = 1; twice(&mut x); x }",
    [], "3"⟩,
  ⟨"fn main() { let mut x = 1; let p = &mut x; let q = p; *q = 2; *p = 3; x }",
    [], "3"⟩,
  ⟨"fn id(p: &mut Int) -> &mut Int { p }\n  fn main() { let mut x = 1; let q = id(&mut x); *q = 5; x }",
    [], "5"⟩,
  ⟨"fn get(r: &Int) { *r }\n  fn main() { let mut x = 7; let p = &mut x; get(p) + get(&x) }",
    [], "14"⟩,
  ⟨"fn main() { let mut a = 1; let mut b = 2; let p = if(a < b) { &mut a } else { &mut b }; *p = 9; a + b }",
    [], "11"⟩,
  ⟨"fn main() { let mut n = 0; let bump = { n = n + 1; }; let get = { n }; bump(); get(); bump(); get() }",
    [], "2"⟩,
  ⟨"fn main() { let mut x = 3; let r = &x; let get = { x }; get() + *r }",
    [], "6"⟩,
  ⟨"fn go(r, n) { let mut y = n; if(0 < n) { go(&mut y, n - 1) + *r } else { *r } }\n  fn main() { let mut t = 5; go(&mut t, 3) }",
    [], "11"⟩,
  -- A borrow that is given a name is, in Core, a callable run with the borrow:
  -- the statements up to the last that uses it. These run as they did before.
  ⟨"fn main() { let mut x = 1; let p = &mut x; let v = *p + 1; *p = v; let w = v * 2; x = w; x + v }",
    [], "6"⟩,
  ⟨"fn main() { let mut a = 1; let mut b = 2; let p = &mut a; let q = &mut b; *p = 10; a = a + 1; *q = 20; a + b }",
    [], "31"⟩,
  ⟨"fn main() { let mut x = 1; let p = &mut x; let mut y = *p; y = y + 1; *p = y; x + 0 }",
    [], "2"⟩,
  ⟨"fn main() { let mut x = 1; let s = Some(&mut x); match(s) { Some(p) => *p = 4, None => () }; x }",
    [], "4"⟩,
  ⟨"fn main() { let mut x = 0; let p = &mut x; let mut i = 0; while({ i < 3 }) { *p = *p + i; i = i + 1; }; x }",
    [], "3"⟩,
  ⟨"fn main() { let mut x = 1; let r = @out { let p = &mut x; *p = 5; if(*p == 5) { @out(7) }; 0 }; r + x }",
    [], "12"⟩,
  ⟨"fn main() { let mut x = 1; let p = &mut x; defer host_write(9); *p = 2; x }",
    [], "9\n2"⟩,
  ⟨"fn main() { let mut x = 1; let p = &mut x; let f = { *p = *p + 10; }; f(); f(); x }",
    [], "21"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { let mut x = 1; handle { let p = &mut x; *p = ask() + *p; *p } () { ask(k) => k(41) } }",
    [], "42"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { let mut x = 1; let p = &mut x; let v = handle { ask() + *p } () { ask(k) => k(41) }; *p = v; x }",
    [], "42"⟩,
  ⟨"fn first(a: &mut Int, b: &mut Int) -> &mut Int { a }\n  fn main() { let mut x = 1; let mut y = 2; let q = first(&mut x, &mut y); *q = 9; x + y }",
    [], "11"⟩,
  ⟨"fn main() { let mut x = 1; let t = (&x, 5); let (r, n) = t; *r + n + x }",
    [], "7"⟩,
  -- While a `&mut` borrow lasts the variable is used only through it, and
  -- while a `&` borrow lasts the variable is not assigned. A call counts as a
  -- use of every variable that a callable it is given may use.
  ⟨"fn main() { let mut x = 1; let p = &mut x; x = 5; *p }",
    [], "error: 1:44: in `main`: `x` is assigned while `p` holds a `&mut` reference to it"⟩,
  ⟨"fn main() { let mut x = 1; let p = &mut x; let y = x; *p = 2; y }",
    [], "error: 1:44: in `main`: `x` is read while `p` holds a `&mut` reference to it"⟩,
  ⟨"fn main() { let mut x = 1; let p = &mut x; let q = &mut x; *p = 1; *q = 2; x }",
    [], "error: 1:44: in `main`: `x` is borrowed with `&mut` while `p` holds a `&mut` reference to it"⟩,
  ⟨"fn main() { let mut x = 1; let r = &x; x = 2; *r }",
    [], "error: 1:40: in `main`: `x` is assigned while `r` holds a reference to it"⟩,
  ⟨"fn main() { let mut x = 1; let r = &x; let p = &mut x; *p = 3; *r }",
    [], "error: 1:40: in `main`: `x` is borrowed with `&mut` while `r` holds a reference to it"⟩,
  ⟨"fn swap(a, b) { let t = *a; *a = *b; *b = t; }\n  fn main() { let mut x = 1; swap(&mut x, &mut x); x }",
    [], "error: 2:30: in `main`: `x` is borrowed with `&mut` while a value this expression is still using holds a `&mut` reference to it"⟩,
  ⟨"fn f(p, v) { *p = v }\n  fn main() { let mut x = 1; f(&mut x, x); x }",
    [], "error: 2:30: in `main`: `x` is read while a value this expression is still using holds a `&mut` reference to it"⟩,
  ⟨"fn main() { let mut x = 1; let p = &mut x; let bump = { x = x + 1; }; bump(); *p }",
    [], "error: 1:71: in `main`: calling `bump` may assign or borrow `x` while `p` holds a `&mut` reference to it"⟩,
  ⟨"fn apply(f, p) { f(); *p }\n  fn main() { let mut n = 0; let bump = { n = n + 1; }; apply(bump, &mut n) }",
    [], "error: 2:57: in `main`: calling `apply` may assign or borrow `n` while a value this expression is still using holds a `&mut` reference to it"⟩,
  ⟨"fn main() { let mut x = 1; let p = &mut x; let q = p; *p = 2; *q = 3; x }",
    [], "error: 1:55: in `main`: `p` is used while `q`, which borrows from it, is still in use"⟩,
  ⟨"fn main() { let mut x = 1; let r = &x; *r = 5; x }",
    [], "error: 1:40: in `main`: `*` assigns through a reference: expected `&mut _`, found `&Int`"⟩,
  ⟨"fn id(p: &mut Int) -> &mut Int { p }\n  fn main() { let mut x = 1; let q = id(&mut x); x = 2; *q }",
    [], "error: 2:50: in `main`: `x` is assigned while `q` holds a `&mut` reference to it"⟩,
  ⟨"fn main() { let mut x = 1; let r = &x; let set = { x = 2; }; set(); *r }",
    [], "error: 1:62: in `main`: calling `set` may assign or borrow `x` while `r` holds a reference to it"⟩,
  ⟨"fn main() { let mut x = 1; let p = &mut x; let get = { x }; let v = get(); *p = v; x }",
    [], "error: 1:61: in `main`: calling `get` may read `x` while `p` holds a `&mut` reference to it"⟩,
  ⟨"fn incr(p: &mut Int) { *p = *p + 1 }\n  fn main() { let mut x = 1; let r = &x; incr(r); x }",
    [], "error: 2:42: in `main`: argument 1 of `incr`: expected `&mut Int`, found `&Int`"⟩,

  -- Errors are reported, not guessed around.
  ⟨"fn main() { nope }",
    [], "error: 1:13: in `main`: unknown name `nope`"⟩,
  ⟨"fn f(x) { tail f(x) + 1 }  fn main() { f(1) }",
    [], "error: 1:11: `tail` call is not in tail position"⟩,
  ⟨"fn main() { 1 +",
    [], "error: 1:16: expected an expression, found end of input"⟩,
  ⟨"fn main() { 1 $ 2 }",
    [], "error: 1:15: unexpected character `$`"⟩,
  -- Traits. A trait is some functions a type may have, and an `impl` gives them
  -- for a type. A function that uses one at a type it is generic in is given
  -- the implementation by whoever calls it; which is found from the types.
  ⟨"trait Show { fn show(Self) -> Int }\nimpl Show for Int { fn show(x) { x } }\nfn main() { show(41) + 1 }",
    [], "42"⟩,
  ⟨"enum Maybe<T> { Nothing, Just(T) }\ntrait Show { fn show(Self) -> Int }\nimpl Show for Int { fn show(x) { x } }\nimpl<T> Show for Maybe<T> where T: Show { fn show(o) { match(o) { Just(v) => show(v) + 100, Nothing => 0 } } }\nfn twice(x) { show(x) + show(x) }\nfn main() { twice(1) + twice(Just(2)) + twice(Just(Just(3))) }",
    [], "612"⟩,
  ⟨"enum List<T> { Nil, Cons(T, List<T>) }\ntrait Sum { fn sum(Self) -> Int }\nimpl Sum for Int { fn sum(x) { x } }\nimpl<T> Sum for List<T> where T: Sum { fn sum(l) { match(l) { Nil => 0, Cons(h, t) => sum(h) + sum(t) } } }\nfn main() { sum(Cons(Cons(1, Cons(2, Nil)), Cons(Cons(3, Nil), Nil))) }",
    [], "6"⟩,
  -- A trait's function need not take the type: what it gives decides.
  ⟨"trait Num { fn zero() -> Self; fn add(Self, Self) -> Self }\nimpl Num for Int { fn zero() { 0 } fn add(a, b) { a + b } }\nenum Pair<T> { P(T, T) }\nimpl<T> Num for Pair<T> where T: Num { fn zero() { P(zero(), zero()) } fn add(a, b) { match(a) { P(x, y) => match(b) { P(u, v) => P(add(x, u), add(y, v)) } } } }\nfn double(x) { add(x, x) }\nfn main() { match(double(add(P(1, 2), zero()))) { P(a, b) => a * 10 + b } }",
    [], "24"⟩,
  -- Functions that call each other pass on what they were given.
  ⟨"trait Show { fn show(Self) -> Int }\nimpl Show for Int { fn show(x) { x } }\nfn even(n, x) { if(n == 0) { show(x) } else { odd(n - 1, x) } }\nfn odd(n, x) { if(n == 0) { 0 - show(x) } else { even(n - 1, x) } }\nfn main() { even(3, 5) + even(2, 7) }",
    [], "2"⟩,
  ⟨"enum Maybe<T> { Nothing, Just(T) }\ntrait Show { fn show(Self) -> Int }\nimpl Show for Int { fn show(x) { x } }\nfn show_both<A, B>(a: A, b: B) -> Int { show(a) * 10 + show(b) }\nimpl<T> Show for Maybe<T> where T: Show { fn show(o) { match(o) { Just(v) => show(v) + 1, Nothing => 0 } } }\nfn main() { show_both(4, Just(1)) }",
    [], "42"⟩,
  ⟨"trait Show { fn show(Self) -> Int }\nimpl Show for Int { fn show(x) { x * 2 } }\nfn main() { Show::show(4) }",
    [], "8"⟩,
  ⟨"struct Point(Int, Int)\ntrait Norm { fn norm(Self) -> Int }\nimpl Norm for Point { fn norm(p) { match(p) { Point(x, y) => x * x + y * y } } }\nfn main() { norm(Point(3, 4)) }",
    [], "25"⟩,
  ⟨"trait Show { fn show(Self) -> Int }\nimpl Show for Int { fn show(x) { x } }\nfn each(x, y) { let f = { v => show(v) + 1 }; f(x) + f(y) }\nfn main() { each(1, 2) }",
    [], "5"⟩,
  ⟨"effect Ask { ask() -> Int }\ntrait Show { fn show(Self) -> Int }\nimpl Show for Int { fn show(x) { x + 1 } }\nfn main() { handle show(ask()) + show(ask()) { ask(k) => k(20) } }",
    [], "42"⟩,
  ⟨"trait Reset { fn reset(&mut Self) }\nimpl Reset for Int { fn reset(p) { *p = 0; } }\nfn main() { let mut n = 5; reset(&mut n); n }",
    [], "0"⟩,
  -- A type has a trait only if an implementation says so, on its conditions.
  ⟨"enum Maybe<T> { Nothing, Just(T) }\ntrait Show { fn show(Self) -> Int }\nimpl Show for Int { fn show(x) { x } }\nfn main() { show(Just(1)) }",
    [], "error: 4:13: in `main`: `Maybe<Int>` does not implement `Show`"⟩,
  ⟨"enum Maybe<T> { Nothing, Just(T) }\ntrait Show { fn show(Self) -> Int }\nimpl Show for Int { fn show(x) { x } }\nimpl<T> Show for Maybe<T> where T: Show { fn show(o) { match(o) { Just(v) => show(v) + 100, Nothing => 0 } } }\nfn main() { show(Just(Just({ 1 }))) }",
    [], "error: 5:13: in `main`: `fn() -> Int` does not implement `Show`"⟩,
  ⟨"enum Maybe<T> { Nothing, Just(T) }\ntrait Show { fn show(Self) -> Int }\nimpl Show for Int { fn show(x) { x } }\nimpl<T> Show for Maybe<T> { fn show(o) { match(o) { Just(v) => show(v), Nothing => 0 } } }\nfn main() { 0 }",
    [], "error: 4:64: in `Show::show@Maybe`: `T` is not known to implement `Show`: add `where T: Show` to the implementation"⟩,
  -- No two implementations are for the same trait and type: which one a use
  -- gets never depends on how it was looked for.
  ⟨"trait Show { fn show(Self) -> Int }\nimpl Show for Int { fn show(x) { x } }\nimpl Show for Int { fn show(x) { x + 1 } }\nfn main() { show(1) }",
    [], "error: `Show` is implemented twice for `Int`"⟩,
  ⟨"trait Default { fn default() -> Self }\ntrait Show { fn show(Self) -> Int }\nimpl Show for Int { fn show(x) { x } }\nimpl Default for Int { fn default() { 7 } }\nfn main() { show(default()) }",
    [], "error: 5:13: in `main`: `Default` is needed of a type that nothing here decides"⟩,
  ⟨"trait Show { fn show(Self) -> Int }\nimpl Show for Int { }\nfn main() { 0 }",
    [], "error: `impl Show for Int` lacks the function `show`"⟩,
  ⟨"trait Show { fn show(Self) -> Int }\nimpl Show for Int { fn show(x) { Some(x) } }\nfn main() { 0 }",
    [], "error: in `Show::show@Int`: this is not the function `Show` declares, which takes its arguments, gives its result and performs nothing: `Result<Int, _>` is not `Int`"⟩,
  -- A trait's function performs nothing its caller would have to handle, and
  -- is called where it is named.
  ⟨"effect Ask { ask() -> Int }\ntrait Show { fn show(Self) -> Int }\nimpl Show for Int { fn show(x) { x + ask() } }\nfn main() { handle show(1) { ask(k) => k(1) } }",
    [], "error: in `Show::show@Int`: this is not the function `Show` declares, which takes its arguments, gives its result and performs nothing: effect `Ask` is not handled here"⟩,
  ⟨"trait Show { fn show(Self) -> Int }\nimpl Show for Int { fn show(x) { x } }\nfn apply(f, x) { f(x) }\nfn main() { apply(show, 1) }",
    [], "error: 4:13: in `main`: `show` is a function of the trait `Show`, so it is called where it is named: write a block that calls it"⟩,
  ⟨"trait Show { fn show(Self) -> Int }\nimpl Show for Int { fn show(x) { x } }\nfn apply(f, x) { f(x) }\nfn main() { apply({ v => show(v) }, 1) }",
    [], "1"⟩,
  -- `Drop`. A type may say what is done when a value of it is destroyed. That
  -- happens when a variable holding the value ends, however its block is left,
  -- and before the variable is assigned again. Later variables end first.
  ⟨"struct File(Int)\nimpl Drop for File { fn drop(p) { match(replace(p, File(0))) { File(fd) => host_write(fd) } } }\nfn main() { let mut f = File(7); host_write(1); 2 }",
    [], "1\n7\n2"⟩,
  ⟨"struct File(Int)\nimpl Drop for File { fn drop(p) { match(replace(p, File(0))) { File(fd) => host_write(fd) } } }\nfn main() { let a = File(1); let b = File(2); host_write(3); 0 }",
    [], "3\n2\n1\n0"⟩,
  ⟨"struct File(Int)\nimpl Drop for File { fn drop(p) { match(replace(p, File(0))) { File(fd) => host_write(fd) } } }\nfn main() { let mut f = File(1); f = File(2); host_write(9); 0 }",
    [], "1\n9\n2\n0"⟩,
  ⟨"struct File(Int)\nimpl Drop for File { fn drop(p) { match(replace(p, File(0))) { File(fd) => host_write(fd) } } }\nfn main() { @out { let f = File(4); @out(1); 2 } }",
    [], "4\n1"⟩,
  ⟨"effect Fail { fail() -> ! }\nstruct File(Int)\nimpl Drop for File { fn drop(p) { match(replace(p, File(0))) { File(fd) => host_write(fd) } } }\nfn work() { let f = File(4); fail(); 2 }\nfn main() { handle work() { fail() => 8 } }",
    [], "4\n8"⟩,
  -- A value given away is destroyed where it comes to rest.
  ⟨"struct File(Int)\nimpl Drop for File { fn drop(p) { match(replace(p, File(0))) { File(fd) => host_write(fd) } } }\nfn keep(f: File) { let mut mine = f; host_write(5); }\nfn main() { let f = File(7); keep(f); host_write(1); 2 }",
    [], "5\n7\n1\n2"⟩,
  ⟨"struct File(Int)\nimpl Drop for File { fn drop(p) { match(replace(p, File(0))) { File(fd) => host_write(fd) } } }\nfn main() { let mut f = File(1); let old = replace(&mut f, File(2)); host_write(9); 0 }",
    [], "9\n1\n2\n0"⟩,
  -- A guard that runs a callable when its block ends, written in the language.
  ⟨"struct Deferred(fn() -> ())\nimpl Drop for Deferred { fn drop(d) { match(replace(d, Deferred({ () }))) { Deferred(f) => f() } } }\nfn deferred(f) { Deferred(f) }\nfn main() { let g = deferred({ host_write(9); }); host_write(1); 2 }",
    [], "1\n9\n2"⟩,
  -- How often a value is used. A declared type may say: `impl Use<[fewest, most]>`.
  -- `Drop` says nothing about it: a type that has `Drop` and says no more can be
  -- copied, and each copy is destroyed.
  ⟨"struct File(Int)\nimpl Drop for File { fn drop(p) { match(replace(p, File(0))) { File(fd) => host_write(fd) } } }\nfn main() { let mut f = File(7); let g = f; 0 }",
    [], "7\n7\n0"⟩,
  -- At most once.
  ⟨"struct File(Int)\nimpl Drop for File { fn drop(p) { match(replace(p, File(0))) { File(fd) => host_write(fd) } } }\nimpl Use<[0, 1]> for File {}\nfn keep2(a: File, b: File) { let mut x = a; let mut y = b; 0 }\nfn main() { let f = File(7); keep2(f, f) }",
    [], "error: 5:13: in `main`: `f` is used more than once, but a `File` can be used only once"⟩,
  ⟨"struct File(Int)\nimpl Drop for File { fn drop(p) { match(replace(p, File(0))) { File(fd) => host_write(fd) } } }\nimpl Use<[0, 1]> for File {}\nfn main() { let mut f = File(7); let g = f; 0 }",
    [], "error: 4:34: in `main`: reading the mutable variable `f` copies its value (`replace` takes it out instead), but a `File` can be used only once"⟩,
  -- At least once: a value that is let go without being used is an error,
  -- wherever it happens. Taking it apart with a pattern is a use.
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn main() { let f = File(7); 0 }",
    [], "error: 4:13: in `main`: `f` is not used on every path, but a `File` has to be used"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn main() { let f = File(7); host_write(1); close(f); 0 }",
    [], "1\n7\n0"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn main() { File(7); 0 }",
    [], "error: 4:13: in `main`: the value of a statement is let go, but a `File` has to be used"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn main() { let _ = File(7); 0 }",
    [], "error: 4:13: in `main`: `_` lets go of a value, but a `File` has to be used"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn main() { let mut f = File(7); 0 }",
    [], "error: 4:13: in `main`: the mutable variable `f` lets go of what it holds when its block ends (a `defer` straight after it can take that out with `replace`), but a `File` has to be used"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn main() { let p = (File(3), 4); p.1 }",
    [], "error: 4:35: in `main`: taking one field of a value lets go of the rest, but a `File` has to be used"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn main() { let p = (File(3), 4); let (f, n) = p; close(f); n }",
    [], "3\n4"⟩,
  -- It is part of a function's contract that it may leave an argument unused.
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn ignore(x) { 0 }\nfn main() { ignore(File(7)) }",
    [], "error: 5:13: in `main`: `ignore` may leave what it is given unused, but a `File` has to be used"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn id(x) { x }\nfn main() { close(id(File(7))); 0 }",
    [], "7\n0"⟩,
  -- Every path counts: both branches, and a way out before the use.
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn main() { let f = File(7); if(1 < 2) { close(f); 1 } else { close(f); 2 } }",
    [], "7\n1"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn main() { let f = File(7); if(1 < 2) { close(f); 1 } else { 2 } }",
    [], "error: 4:13: in `main`: `f` is not used on every path, but a `File` has to be used"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\neffect Fail { fail() -> ! }\nfn work() { let f = File(7); fail(); close(f); 0 }\nfn main() { handle work() { fail() => 1 } }",
    [], "error: 5:13: in `work`: `f` is not used on every path, but a `File` has to be used"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\neffect Fail { fail() -> ! }\nfn work() { let f = File(7); close(f); fail(); 0 }\nfn main() { handle work() { fail() => 1 } }",
    [], "7\n1"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn main() { @out { let f = File(7); @out(1); close(f); 2 } }",
    [], "error: 4:20: in `main`: `f` is not used on every path, but a `File` has to be used"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn main() { let f = File(7); defer close(f); host_write(1); 0 }",
    [], "1\n7\n0"⟩,
  -- A call that performs nothing and can jump nowhere comes back, so a value
  -- may wait across it; one that may not come back lets the value go.
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn main() { let f = File(7); let mut i = 0; while({ i < 3 }) { i = i + 1; }; close(f); i }",
    [], "7\n3"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn each(f, n) { if(n < 1) { 0 } else { f(n); each(f, n - 1) } }\nfn main() { @out { let t = File(7); each({ x => @out(x) }, 3); close(t); 0 } }",
    [], "error: 5:20: in `main`: `t` is not used on every path, but a `File` has to be used"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\neffect Log { log(Int) }\nfn work() { let f = File(7); log(1); close(f); 0 }\nfn main() { handle work() { log(x) => print(x) } }",
    [], "error: 5:13: in `work`: `f` is not used on every path, but a `File` has to be used"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn run(h, f: File) { h(); close(f); 0 }\nfn main() { run({ 1 }, File(7)) }",
    [], "error: in `run`: `f` is not used on every path, but a `File` has to be used"⟩,
  -- A value that holds one has to be used too.
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nenum L { N, C(File, L) }\nfn free { N => 0, C(f, rest) => close(f); free(rest) }\nfn main() { free(C(File(1), C(File(2), N))) }",
    [], "1\n2\n0"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nenum L { N, C(File, L) }\nfn main() { let l = C(File(1), N); 0 }",
    [], "error: 5:13: in `main`: `l` is not used on every path, but a `File` has to be used"⟩,
  -- Any number of times, but at least once.
  ⟨"struct Ticket(Int)\nimpl Use<[1, infinity]> for Ticket {}\nfn show(t: Ticket) { match(t) { Ticket(n) => n } }\nfn main() { let t = Ticket(4); show(t) + show(t) }",
    [], "8"⟩,
  ⟨"struct Ticket(Int)\nimpl Use<[1, infinity]> for Ticket {}\nfn main() { let t = Ticket(4); 0 }",
    [], "error: 3:13: in `main`: `t` is not used on every path, but a `Ticket` has to be used"⟩,
  -- What a type says may only narrow what its fields allow, and counting stops at one.
  ⟨"struct Ticket(Int)\nimpl Use<[1, 1]> for Ticket {}\nstruct Box(Ticket)\nimpl Use<[0, 1]> for Box {}\nfn main() { 0 }",
    [], "error: `impl Use` for `Box`: it holds a `Ticket`, which has to be used, so the fewest uses of a `Box` cannot be 0"⟩,
  ⟨"struct Ticket(Int)\nimpl Use<[0, 1]> for Ticket {}\nstruct Box(Ticket)\nimpl Use<[0, infinity]> for Box {}\nfn main() { 0 }",
    [], "error: `impl Use` for `Box`: it holds a value that can be used only once, so the most uses of a `Box` cannot be `infinity`"⟩,
  ⟨"struct Ticket(Int)\nimpl Use<[2, 3]> for Ticket {}\nfn main() { 5 }",
    [], "error: `impl Use` for `Ticket`: a type is used any number of times (`[0, infinity]`), at most once (`[0, 1]`) or exactly once (`[1, 1]`); the language has no other count"⟩,
  -- An operation says how often its resumption is used: `[1, 1]` has to be
  -- resumed or cancelled, on every path. Unsaid, it may be let go, and is then
  -- cancelled.
  ⟨"effect Ask { [1, 1] ask() -> Int }\nfn main() { handle ask() + 1 { ask(k) => k(41) } }",
    [], "42"⟩,
  ⟨"effect Ask { [1, 1] ask() -> Int }\nfn main() { handle ask() + 1 { ask(k) => 7 } }",
    [], "error: 2:13: in `main`: `k` is not used on every path, but a resumption of an operation declared `[1, 1]` has to be used"⟩,
  ⟨"effect Ask { [1, 1] ask() -> Int }\nfn main() { handle ask() + 1 { ask(_) => 7 } }",
    [], "error: 2:13: in `main`: `_` lets go of a value, but a resumption of an operation declared `[1, 1]` has to be used"⟩,
  ⟨"effect Ask { [0, 1] ask() -> Int }\nfn main() { handle ask() + 1 { ask(k) => 7 } }",
    [], "7"⟩,
  ⟨"effect Ask { [1, 1] ask() -> Int }\nfn main() { handle ask() + 1 { ask(k) => cancel(k); 7 } }",
    [], "7"⟩,
  ⟨"effect Ask { [1, 1] ask() -> Int }\nfn main() { handle ask() + 1 { ask(k) => if(1 < 2) { k(10) } else { k(20) } } }",
    [], "11"⟩,
  ⟨"effect Ask { [1, 1] ask() -> Int }\nfn main() { handle ask() + 1 { ask(k) => if(1 < 2) { k(10) } else { 0 } } }",
    [], "error: 2:13: in `main`: `k` is not used on every path, but a resumption of an operation declared `[1, 1]` has to be used"⟩,
  ⟨"effect Ask { [1, 1] ask() -> Int }\nfn main() { handle ask() + 1 { ask(k) => print(0); k(2 * 21) } }",
    [], "0\n43"⟩,
  ⟨"effect Ask { [1, 1] ask() -> Int }\nfn keep(k) { 7 }\nfn main() { handle ask() + 1 { ask(k) => keep(k) } }",
    [], "error: 3:42: in `main`: `keep` may leave what it is given unused, but a resumption of an operation declared `[1, 1]` has to be used"⟩,
  ⟨"effect Ask { [1, 1] ask() -> Int }\neffect Log { log(Int) }\nfn main() { handle (handle ask() + 1 { ask(k) => log(1); k(1) }) { log(x) => print(x) } }",
    [], "error: 3:13: in `main`: `k` is not used on every path, but a resumption of an operation declared `[1, 1]` has to be used"⟩,
  ⟨"effect Ask { [1, 1] ask() -> Int }\nfn main() { let mut saved = None; handle (ask() + 1) { ask(k) => saved = Some(k); 0 }; match(replace(&mut saved, None)) { Some(k) => k(41), None => 0 } }",
    [], "error: 2:13: in `main`: the mutable variable `saved` lets go of what it holds when its block ends (a `defer` straight after it can take that out with `replace`), but a resumption of an operation declared `[1, 1]` has to be used"⟩,
  ⟨"effect Ask { [1, 1] ask() -> ! }\nfn main() { 0 }",
    [], "error: operation `ask` does not return, so it has no resumption to say this of"⟩,
  -- A callable that holds such a value has to be called, wherever it goes.
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn mk(f: File) { { close(f); 1 } }\nfn main() { mk(File(7))() }",
    [], "7\n1"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn mk(f: File) { { close(f); 1 } }\nfn main() { let g = mk(File(7)); 0 }",
    [], "error: 5:13: in `main`: `g` is not used on every path, but a callable that holds a `File` has to be used"⟩,
  ⟨"effect Ask { [1, 1] ask() -> Int }\nfn main() { let run = handle { ask() + 1 }() { r => { n => r + n }, ask(k) => { n => (k(n))(n + 1) } }; run(5) }",
    [], "12"⟩,
  ⟨"effect Ask { [1, 1] ask() -> Int }\nfn main() { let run = handle { ask() + 1 }() { r => { n => r + n }, ask(k) => { n => (k(n))(n + 1) } }; 5 }",
    [], "error: 2:13: in `main`: `run` is not used on every path, but a callable that holds a resumption of an operation declared `[1, 1]` has to be used"⟩,
  -- Of two blocks of which one runs, the second runs in the first's place:
  -- what both mention is held once, and what only the first mentions is let go
  -- when the second runs.
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn main() { let f = File(1); let g = File(2); if(1 < 2) { close(f); close(g); 1 } else { close(f); 2 } }",
    [], "error: 4:30: in `main`: `g` is not used on every path, but a `File` has to be used"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn main() { let f = File(1); let r = if(1 < 2) { close(f); 1 }; let f = File(2); r else { close(f); 2 } }",
    [], "error: 4:65: in `main`: `f` is not used on every path, but a `File` has to be used"⟩,
  -- What `main` gives is let go.
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn main() { File(1) }",
    [], "error: the result of `main` is let go when the program ends, but a `File` has to be used"⟩,
  -- What a callable performs can be written after its result: these effects and
  -- no others. `/ {}` is a callable that performs nothing. Unwritten, it is inferred.
  ⟨"effect Log { log(Int) }\nfn f(x) -> Int / {Log} { log(x); x }\nfn main() { handle f(3) { log(v) => print(v) } }",
    [], "3\n3"⟩,
  ⟨"effect Log { log(Int) }\nfn f(x) -> Int / {} { log(x); x }\nfn main() { handle f(3) { log(v) => print(v) } }",
    [], "error: in `f`: `f` says it performs nothing, and that is not what it performs: effect `Log` is not handled here"⟩,
  ⟨"effect Log { log(Int) }\neffect Ask { ask() -> Int }\nfn f(x) -> Int / {Log} { log(x); ask() }\nfn main() { 0 }",
    [], "error: in `f`: `f` says it performs {Log}, and that is not what it performs: effect `Ask` is not handled here"⟩,
  ⟨"effect Log { log(Int) }\nfn f(x) -> / {Log} { log(x) }\nfn main() { handle f(3) { log(v) => print(v) } }",
    [], "3\n()"⟩,
  ⟨"fn f(x) -> { print(x) }\nfn main() { f(3) }",
    [], "3\n()"⟩,
  ⟨"effect Log { log(Int) }\nfn run(g: fn() -> Int / {}) { g() }\nfn main() { run({ 5 }) }",
    [], "5"⟩,
  ⟨"effect Log { log(Int) }\nfn run(g: fn() -> Int / {}) { g() }\nfn main() { handle run({ log(1); 5 }) { log(v) => print(v) } }",
    [], "error: 3:13: in `main`: argument 1 of `run`: expected `fn() -> Int`, found `fn() -> Int / {Log}` (effect `Log` is not handled here)"⟩,
  ⟨"effect Log { log(Int) }\nfn run(g: fn() -> Int / {Log}) { g() }\nfn main() { handle run({ log(1); 5 }) { log(v) => print(v) } }",
    [], "1\n5"⟩,
  ⟨"effect St<T> { get() -> T }\nfn run(g: fn() -> Int / {St<Int>}) { g() }\nfn main() { handle run({ get() + 1 }) { get(k) => k(4) } }",
    [], "5"⟩,
  ⟨"effect St<T> { get() -> T }\nfn run(g: fn() -> Int / {St}) { g() }\nfn main() { handle run({ get() + 1 }) { get(k) => k(4) } }",
    [], "5"⟩,
  ⟨"fn run(g: fn() -> Int / {Nope}) { g() }\nfn main() { 0 }",
    [], "error: in `run`: unknown effect `Nope`"⟩,
  ⟨"struct Job(fn(Int) -> Int / {})\nfn main() { match(Job({ x => x + 1 })) { Job(f) => f(2) } }",
    [], "3"⟩,
  -- A value that has to be used may wait across a call of a callable the
  -- function was given if that callable performs nothing; and then whoever
  -- gives one may not give one that jumps to a label.
  ⟨"effect Yield { [1, 1] yield(Int) }\nfn gen() { yield(1); yield(2); () }\nfn find(generator, wanted: fn(Int) -> Result<(), ()> / {}) { handle generator() { _ => None, yield(value, k) => if(wanted(value)) { cancel(k); Some(value) } else { k(()) } } }\nfn main() { find({ gen() }, { x => x > 1 }) }",
    [], "Ok(2)"⟩,
  ⟨"effect Yield { [1, 1] yield(Int) }\nfn gen() { yield(1); yield(2); () }\nfn find(generator, wanted) { handle generator() { _ => None, yield(value, k) => if(wanted(value)) { cancel(k); Some(value) } else { k(()) } } }\nfn main() { find({ gen() }, { x => x > 1 }) }",
    [], "error: 3:30: in `find`: `k` is not used on every path, but a resumption of an operation declared `[1, 1]` has to be used"⟩,
  ⟨"effect Yield { [1, 1] yield(Int) }\nfn gen() { yield(1); yield(2); () }\nfn find(generator, wanted: fn(Int) -> Result<(), ()> / {}) { handle generator() { _ => None, yield(value, k) => if(wanted(value)) { cancel(k); Some(value) } else { k(()) } } }\nfn main() { @out { find({ gen() }, { x => @out(None) }) } }",
    [], "error: 4:20: in `main`: `find` holds a value that has to be used while it calls what it is given, but what it is given here can jump to a label and not come back"⟩,
  -- While a handled computation is suspended in an arm, it still holds the
  -- borrows it made: the arm may not use what they exclude, nor may a callable
  -- the operation was given. Once it has been resumed and is done, they are over.
  ⟨"effect Ask { ask() }\nfn main() { let mut x = 0; handle { let p = &mut x; ask(); *p = 1; 0 }() { ask(k) => x = 5; k(()) }; x }",
    [], "error: 2:86: in `main`: `x` is assigned while `k` holds a `&mut` reference to it"⟩,
  ⟨"effect Ask { ask() }\nfn main() { let mut x = 0; handle { let p = &mut x; ask(); *p = 1; 0 }() { ask() => x = 5 }; x }",
    [], "error: 2:85: in `main`: `x` is assigned while the computation this arm resumes holds a `&mut` reference to it"⟩,
  ⟨"effect Ask { ask() }\nfn main() { let mut x = 0; handle { let p = &mut x; ask(); *p = 1; 0 }() { ask(k) => k(()); x = 5; 0 }; x }",
    [], "5"⟩,
  ⟨"effect Ask { ask() }\nfn main() { let mut x = 0; handle { let p = &mut x; ask(); *p = 1; 0 }() { ask(k) => print(x); k(()) }; x }",
    [], "error: 2:86: in `main`: `x` is read while `k` holds a `&mut` reference to it"⟩,
  ⟨"effect Ask { ask() }\nfn main() { let mut x = 0; handle { let p = &x; ask(); *p }() { ask(k) => print(x); k(()) } }",
    [], "0\n0"⟩,
  ⟨"effect Ask { ask() }\nfn main() { let mut x = 0; handle { let p = &x; ask(); *p }() { ask(k) => x = 2; k(()) } }",
    [], "error: 2:75: in `main`: `x` is assigned while `k` holds a reference to it"⟩,
  ⟨"effect Ask { ask() }\nfn main() { let mut x = 0; let work = { let p = &mut x; ask(); *p = 1; 0 }; handle work() { ask(k) => x = 5; k(()) }; x }",
    [], "error: 2:103: in `main`: `x` is assigned while `k` holds a `&mut` reference to it"⟩,
  ⟨"effect Ask { ask() }\nfn bump(p) { ask(); *p = *p + 1 }\nfn main() { let mut x = 0; handle bump(&mut x) { ask(k) => x = 5; k(()) }; x }",
    [], "error: 3:60: in `main`: `x` is assigned while `k` holds a `&mut` reference to it"⟩,
  ⟨"effect Ask { ask() }\nfn bump(p) { ask(); *p = *p + 1 }\nfn main() { let mut x = 0; let mut y = 0; handle bump(&mut x) { ask(k) => y = 5; k(()) }; x + y }",
    [], "6"⟩,
  ⟨"effect Give<F> { give(F) }\nfn main() { let mut x = 0; handle { let p = &mut x; give({ x = 5; }); *p = 1; 0 }() { give(f, k) => f(); k(()) }; x }",
    [], "error: 2:53: in `main`: calling operation `give` may assign or borrow `x` while `p` holds a `&mut` reference to it"⟩,
  ⟨"effect Give<F> { give(F) }\nfn main() { let mut x = 0; handle { give({ x = 5; }); 0 }() { give(f, k) => f(); k(()) }; x }",
    [], "5"⟩,
  -- A reference can be borrowed from: `&mut *p` for writing, `&*p` for reading.
  -- Using `p` as a value already lends it; this says so.
  ⟨"fn incr(p) { *p = *p + 1 }\nfn main() { let mut x = 0; let p = &mut x; incr(&mut *p); incr(&mut *p); *p }",
    [], "2"⟩,
  ⟨"fn get(p) { *p }\nfn main() { let mut x = 4; let p = &mut x; let a = get(&*p); *p = a + 1; x }",
    [], "5"⟩,
  ⟨"fn main() { let mut x = 0; let p = &mut x; let q = &mut *p; *p = 1; *q = 2; x }",
    [], "error: 1:61: in `main`: `p` is used while `q`, which borrows from it, is still in use"⟩,
  ⟨"fn main() { let mut x = 0; let p = &mut x; let q = &mut *p; *q = 2; *p = 1; x }",
    [], "1"⟩,
  ⟨"fn main() { let mut x = 0; let p = &x; let q = &mut *p; 0 }",
    [], "error: 1:40: in `main`: `&mut *` borrows from a `&mut` reference: expected `&mut Int`, found `&Int`"⟩,
  ⟨"fn main() { let mut x = 0; let p = &mut x; let a = &*p; let b = &*p; *a + *b }",
    [], "0"⟩,
  ⟨"fn main() { let mut x = 0; let p = &mut x; let a = &*p; *p = 3; *a }",
    [], "error: 1:57: in `main`: `p` is used while `a`, which borrows from it, is still in use"⟩,
  ⟨"fn main() { let y = 5; let q = &*y; 0 }",
    [], "error: 1:24: in `main`: `&*` borrows from a reference: expected `&_`, found `Int`"⟩,
  -- Alternatives chain: `or` gives what failed to its right operand, as `else`
  -- does, and both group to the left.
  ⟨"effect Ask { ask() -> Int }\nfn main() { handle ask() + 1 { ask(k) => if(2 < 1) { k(1) } or { if(2 < 1) { k(2) } } or { if(1 < 2) { k(3) } } else { k(4) } } }",
    [], "4"⟩,
  ⟨"effect Ask { [1, 1] ask() -> Int }\nfn main() { handle ask() + 1 { ask(k) => if(2 < 1) { k(1) } or { if(1 < 2) { k(2) } } else { k(3) } } }",
    [], "3"⟩,
  ⟨"effect Ask { [1, 1] ask() -> Int }\nfn main() { handle ask() + 1 { ask(k) => if(2 < 1) { k(1) } or { if(2 < 1) { k(2) } } else { 0 } } }",
    [], "error: 2:13: in `main`: `k` is not used on every path, but a resumption of an operation declared `[1, 1]` has to be used"⟩,
  ⟨"fn main() { match((2 < 1) or { 2 < 1 } or { 1 < 2 }) { Ok(_) => 1, Err(_) => 0 } }",
    [], "1"⟩,
  ⟨"fn main() { match((1 < 2) and { 2 < 3 } and { 4 < 3 }) { Ok(_) => 1, Err(_) => 0 } }",
    [], "0"⟩,
  ⟨"fn main() { let x = Err(7) or { e => Ok(e + 1) }; x else { 0 } }",
    [], "8"⟩,
  -- A name both blocks mention is the same thing only if it is the same binding.
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn main() { let f = File(1); let r = { let f = File(2); if(2 < 1) { close(f); 1 } }(); r else { close(f); 3 } }",
    [], "error: 4:13: in `main`: `f` is not used on every path, but a `File` has to be used"⟩,
  -- A value that has to be used can be kept in a mutable variable if a cleanup
  -- written straight after the variable takes it out again, leaving something
  -- that holds nothing. It is never assigned over: `replace` gives back what
  -- was there.
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn drain { Ok(f) => close(f), Err(_) => () }\nfn main() { let mut slot = None; defer drain(replace(&mut slot, None)); let old = replace(&mut slot, Some(File(3))); drain(old); host_write(1); 0 }",
    [], "1\n3\n0"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn drain { Ok(f) => close(f), Err(_) => () }\nfn main() { let mut slot = None; let old = replace(&mut slot, Some(File(3))); drain(old); 0 }",
    [], "error: 5:13: in `main`: the mutable variable `slot` lets go of what it holds when its block ends (a `defer` straight after it can take that out with `replace`), but a `File` has to be used"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn drain { Ok(f) => close(f), Err(_) => () }\nfn main() { let mut slot = None; defer drain(replace(&mut slot, None)); slot = Some(File(3)); 0 }",
    [], "error: 5:73: in `main`: assigning to `slot` lets go of what it holds (`replace` takes it out instead), but a `File` has to be used"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn drain { Ok(f) => close(f), Err(_) => () }\nfn main() { let mut slot = Some(File(2)); defer drain(replace(&mut slot, Some(File(9)))); 0 }",
    [], "error: 5:13: in `main`: the mutable variable `slot` lets go of what it holds when its block ends (a `defer` straight after it can take that out with `replace`), but a `File` has to be used"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn drain { Ok(f) => close(f), Err(_) => () }\nfn main() { @out { let mut slot = Some(File(2)); defer drain(replace(&mut slot, None)); @out(1); 0 } }",
    [], "2\n1"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn drain { Ok(f) => close(f), Err(_) => () }\nfn put(p, f) { drain(replace(p, Some(f))) }\nfn main() { let mut slot = None; defer drain(replace(&mut slot, None)); put(&mut slot, File(5)); put(&mut slot, File(6)); 0 }",
    [], "5\n6\n0"⟩,
  -- A field of what a mutable variable holds can be borrowed: `&x.0`, `&mut x.1.0`.
  -- Two fields can be borrowed at once; a borrow of a field is in the way only
  -- of that field, of what is inside it, and of the variable as a whole. What is
  -- written through the borrow is in the variable when the borrow ends, however
  -- it ends.
  ⟨"fn incr(p) { *p = *p + 1 }\nfn main() { let mut x = (1, 10); incr(&mut x.0); incr(&mut x.1); x }",
    [], "(2, 11)"⟩,
  ⟨"fn swap(a, b) { let t = *a; *a = *b; *b = t }\nfn main() { let mut x = (1, 2); swap(&mut x.0, &mut x.1); x }",
    [], "(2, 1)"⟩,
  ⟨"fn main() { let mut x = (1, 2); let p = &mut x.0; *p = 5; let q = &x.1; *p + *q + x.1 }",
    [], "9"⟩,
  ⟨"fn main() { let mut x = (1, 2); let p = &mut x.0; let y = x.0; *p = 5; y }",
    [], "error: 1:51: in `main`: `x` is read while `p` holds a `&mut` reference to it"⟩,
  ⟨"fn main() { let mut x = (1, 2); let p = &mut x.0; let q = &mut x.0; *p = 5; *q }",
    [], "error: 1:51: in `main`: `x` is borrowed with `&mut` while `p` holds a `&mut` reference to it"⟩,
  ⟨"fn main() { let mut x = (1, 2); let p = &mut x.0; x = (7, 8); *p }",
    [], "error: 1:51: in `main`: `x` is assigned while `p` holds a `&mut` reference to it"⟩,
  ⟨"fn main() { let mut x = (1, 2); let p = &mut x.0; *p = 5; x.0 }",
    [], "5"⟩,
  ⟨"struct Point(Int, Int)\nfn incr(p) { *p = *p + 1 }\nfn main() { let mut pt = Point(3, 4); incr(&mut pt.1); match(pt) { Point(a, b) => a * 10 + b } }",
    [], "35"⟩,
  ⟨"fn incr(p) { *p = *p + 1 }\nfn main() { let mut x = ((1, 2), 3); incr(&mut x.0.1); let r = &x.0; (*r).1 + x.1 }",
    [], "6"⟩,
  ⟨"fn main() { let mut x = (1, 2); @out { let p = &mut x.0; *p = 9; @out(0); *p = 100; 0 }; x }",
    [], "(9, 2)"⟩,
  ⟨"fn get(p) { *p }\nfn main() { let mut x = (4, 5); get(&x.0) + get(&x.1) }",
    [], "9"⟩,
  ⟨"fn main() { let mut x = (1, 2); let p = &mut x.0; let w = &x; *p = 3; 0 }",
    [], "error: 1:51: in `main`: `x` is borrowed while `p` holds a `&mut` reference to it"⟩,
  ⟨"enum E { A(Int), B(Int) }\nfn main() { let mut e = A(1); let p = &mut e.0; *p }",
    [], "error: 2:31: in `main`: `E` has no fields to read with `.0`"⟩,
  ⟨"fn incr(p) { *p = *p + 1 }\nfn main() { let mut x = (1, 2); let mut i = 0; while({ i < 3 }) { incr(&mut x.0); i = i + 1; }; x }",
    [], "(4, 2)"⟩,
  ⟨"fn main() { let y = (1, 2); let p = &y.0; *p }",
    [], "error: 1:29: in `main`: `y` is not a mutable variable or a reference, so no field of it can be borrowed"⟩,
  ⟨"effect Ask { ask() }\nfn bump(p) { *p = *p + 1; ask(); *p = *p + 1 }\nfn main() { let mut x = (1, 2); handle bump(&mut x.0) { ask(k) => k(()) }; x }",
    [], "(3, 2)"⟩,
  ⟨"effect Ask { ask() }\nfn bump(p) { *p = *p + 1; ask(); *p = *p + 1 }\nfn main() { let mut x = (1, 2); handle bump(&mut x.0) { ask(k) => print(x.0); k(()) }; x }",
    [], "error: 3:67: in `main`: `x` is read while `k` holds a `&mut` reference to it"⟩,
  ⟨"effect Ask { ask() }\nfn bump(p) { *p = *p + 1; ask(); *p = *p + 1 }\nfn main() { let mut x = (1, 2); handle bump(&mut x.0) { ask(k) => print(x.1); k(()) }; x }",
    [], "2\n(3, 2)"⟩,
  ⟨"effect Fail { fail() -> ! }\nfn bump(p) { *p = *p + 1; fail() }\nfn main() { let mut x = (1, 2); handle bump(&mut x.0) { fail() => 0 }; x }",
    [], "(2, 2)"⟩,
  -- Lifetimes can be written: `'a` on a reference, declared with the type
  -- parameters. A function is held to what it writes: the result here may
  -- borrow from `x` and not from `y`, and its callers rely on that.
  ⟨"fn first<'a, 'b>(x: &'a Int, y: &'b Int) -> &'a Int { x }\nfn main() { let mut a = 1; let mut b = 2; *first(&a, &b) }",
    [], "1"⟩,
  ⟨"fn first<'a, 'b>(x: &'a Int, y: &'b Int) -> &'a Int { y }\nfn main() { 0 }",
    [], "error: 1:55: in `first`: the result of a clause: lifetime `'b` is not known to last as long as `'a`: say `'b: 'a`"⟩,
  ⟨"fn first<'a, 'b>(x: &'a Int, y: &'b Int) -> &'a Int { x }\nfn main() { let mut a = 1; let mut b = 2; let r = first(&a, &b); b = 5; *r + b }",
    [], "6"⟩,
  ⟨"fn first<'a, 'b>(x: &'a Int, y: &'b Int) -> &'a Int { x }\nfn main() { let mut a = 1; let mut b = 2; let r = first(&a, &b); a = 5; *r }",
    [], "error: 2:66: in `main`: `a` is assigned while `r` holds a reference to it"⟩,
  -- A bound says one lifetime lasts at least as long as another, in the
  -- parameters or after `where`.
  ⟨"fn first<'a, 'b: 'a>(x: &'a Int, y: &'b Int) -> &'a Int { y }\nfn main() { let mut a = 1; let mut b = 2; *first(&a, &b) }",
    [], "2"⟩,
  ⟨"fn first<'a, 'b>(x: &'a Int, y: &'b Int) -> &'a Int where 'b: 'a { y }\nfn main() { let mut a = 1; let mut b = 2; *first(&a, &b) }",
    [], "2"⟩,
  ⟨"fn longest<'a>(x: &'a Int, y: &'a Int) -> &'a Int { if(*x < *y) { y } else { x } }\nfn main() { let mut a = 1; let mut b = 2; *longest(&a, &b) }",
    [], "2"⟩,
  ⟨"fn pick<'a, 'b>(x: &'a mut Int, y: &'b mut Int) -> &'a mut Int { y }\nfn main() { 0 }",
    [], "error: in `pick`: what lasts for `'a` is made to depend on what lasts for `'b`: say `'b: 'a` if `'b` lasts at least as long"⟩,
  ⟨"fn f<'a>(x: &'a Int) -> &'a Int where 'b: 'a { x }\nfn main() { 0 }",
    [], "error: in `f`: unknown lifetime `'b`: a lifetime is declared with the type parameters, `<'b>`"⟩,
  -- A lifetime is not a way out of a block, and has to be declared.
  ⟨"fn bad<'a>(x: &'a Int) -> &'a Int { let mut local = 5; &local }\nfn main() { 0 }",
    [], "error: 1:37: in `bad`: `local` could be used after its block has ended: something that uses it is the block's result"⟩,
  ⟨"fn f(x: &'a Int) { *x }\nfn main() { 0 }",
    [], "error: in `f`: unknown lifetime `'a`: a lifetime is declared with the type parameters, `<'a>`"⟩,
  ⟨"fn f(x: &'static Int) { *x }\nfn main() { let mut a = 1; f(&a) }",
    [], "error: 2:13: in `main`: `a` could be used after its block has ended: it is borrowed for `'static`, and no variable lasts that long"⟩,
  ⟨"fn f<'a>(x: &'_ Int, y: &'a Int) -> &'a Int { y }\nfn main() { let mut a = 1; let mut b = 2; *f(&a, &b) }",
    [], "2"⟩,
  -- A declared type can take lifetimes, and holds what they say.
  ⟨"struct Holder<'a>(&'a Int)\nfn get<'a>(h: Holder<'a>) -> &'a Int { match(h) { Holder(r) => r } }\nfn main() { let mut x = 7; *get(Holder(&x)) }",
    [], "7"⟩,
  ⟨"struct Holder<'a>(&'a Int)\nfn main() { let mut x = 7; let h = Holder(&x); x = 8; match(h) { Holder(r) => *r } }",
    [], "error: 2:48: in `main`: `x` is assigned while `h` holds a reference to it"⟩,
  ⟨"struct Holder<'a>(&'a Int)\nfn mk() { let mut x = 7; Holder(&x) }\nfn main() { 0 }",
    [], "error: 2:11: in `mk`: `x` could be used after its block has ended: something that uses it is the block's result"⟩,
  ⟨"trait Show { fn show(Self) -> Int }\nstruct Holder<'a>(&'a Int)\nimpl<'a> Show for Holder<'a> { fn show(h) { match(h) { Holder(r) => *r } } }\nfn main() { let mut x = 4; show(Holder(&x)) }",
    [], "4"⟩,
  ⟨"enum Maybe<'a, T> { Nothing, Just(&'a T) }\nfn get<'a, T>(m: Maybe<'a, T>, d: &'a T) -> &'a T { match(m) { Nothing => d, Just(r) => r } }\nfn main() { let mut x = 4; let mut d = 0; *get(Just(&x), &d) }",
    [], "4"⟩,
  ⟨"struct Slot<'a, T>(&'a mut T)\nfn put<'a, T>(s: Slot<'a, T>, v: T) { match(s) { Slot(p) => *p = v } }\nfn main() { let mut x = 4; put(Slot(&mut x), 9); x }",
    [], "9"⟩,
  ⟨"struct Two<'a, 'b>(&'a Int, &'b Int)\nfn fst<'a, 'b>(t: Two<'a, 'b>) -> &'a Int { match(t) { Two(x, y) => x } }\nfn main() { let mut a = 1; let mut b = 2; let r = fst(Two(&a, &b)); b = 9; *r + b }",
    [], "10"⟩,
  ⟨"struct Two<'a, 'b>(&'a Int, &'b Int)\nfn snd<'a, 'b>(t: Two<'a, 'b>) -> &'a Int { match(t) { Two(x, y) => y } }\nfn main() { 0 }",
    [], "error: 2:45: in `snd`: the result of a clause: lifetime `'b` is not known to last as long as `'a`: say `'b: 'a`"⟩,
  ⟨"struct Holder<'a>(&'a Int)\nfn f(h: Holder<Int>) { 0 }\nfn main() { 0 }",
    [], "error: in `f`: type `Holder` takes a lifetime where a type is written"⟩,
  ⟨"effect E<'a> { op() }\nfn main() { 0 }",
    [], "0"⟩,
  -- A longer lifetime will do for a shorter where the type depends on it the
  -- same way round: in a reference, in what a shared reference points to, in
  -- what a callable gives, and in a declared type whose fields make it so.
  ⟨"struct Holder<'a>(&'a Int)\nfn shrink<'a, 'b: 'a>(h: Holder<'b>) -> Holder<'a> { h }\nfn main() { 0 }",
    [], "0"⟩,
  ⟨"struct Holder<'a>(&'a Int)\nfn grow<'a, 'b: 'a>(h: Holder<'a>) -> Holder<'b> { h }\nfn main() { 0 }",
    [], "error: 2:52: in `grow`: the result of a clause: lifetime `'a` is not known to last as long as `'b`: say `'a: 'b`"⟩,
  ⟨"fn cov<'a, 'b, 'c: 'b>(p: &'a &'c Int) -> &'a &'b Int { p }\nfn main() { 0 }",
    [], "0"⟩,
  -- Not in what a `&mut` reference points to, where the lifetimes must be the same;
  ⟨"fn inv<'a, 'b, 'c: 'b>(p: &'a mut &'c Int) -> &'a mut &'b Int { p }\nfn main() { 0 }",
    [], "error: 1:65: in `inv`: the result of a clause: lifetime `'b` is not `'c`: a reference that lasts for one is used where one that lasts for the other is wanted"⟩,
  ⟨"struct Cell<'a, 'b>(&'a mut &'b Int)\nfn shrink<'a, 'b, 'c: 'b>(c: Cell<'a, 'c>) -> Cell<'a, 'b> { c }\nfn main() { 0 }",
    [], "error: 2:62: in `shrink`: the result of a clause: lifetime `'b` is not `'c`: a reference that lasts for one is used where one that lasts for the other is wanted"⟩,
  -- and the other way round in what a callable takes.
  ⟨"fn contra<'a, 'b: 'a>(f: fn(&'a Int) -> Int) -> fn(&'b Int) -> Int { f }\nfn main() { 0 }",
    [], "0"⟩,
  ⟨"fn contra<'a, 'b: 'a>(f: fn(&'b Int) -> Int) -> fn(&'a Int) -> Int { f }\nfn main() { 0 }",
    [], "error: 1:70: in `contra`: the result of a clause: lifetime `'a` is not known to last as long as `'b`: say `'a: 'b`"⟩,
  ⟨"struct Sink<'a>(fn(&'a Int) -> Int)\nfn widen<'a, 'b: 'a>(s: Sink<'a>) -> Sink<'b> { s }\nfn main() { 0 }",
    [], "0"⟩,
  ⟨"struct Sink<'a>(fn(&'a Int) -> Int)\nfn narrow<'a, 'b: 'a>(s: Sink<'b>) -> Sink<'a> { s }\nfn main() { 0 }",
    [], "error: 2:50: in `narrow`: the result of a clause: lifetime `'a` is not known to last as long as `'b`: say `'a: 'b`"⟩,
  -- A field of what a reference points to can be borrowed too, written
  -- `&mut (*p).0` or `&mut p.0`, and read without copying the rest. A field can
  -- be assigned: `x.0 = v`, `(*p).1 = v`.
  ⟨"fn incr(p) { *p = *p + 1 }\nfn both(pair: &mut (Int, Int)) { incr(&mut (*pair).0); incr(&mut pair.1) }\nfn main() { let mut x = (1, 10); both(&mut x); x }",
    [], "(2, 11)"⟩,
  ⟨"fn swap(a, b) { let t = *a; *a = *b; *b = t }\nfn flip(pair: &mut (Int, Int)) { swap(&mut pair.0, &mut pair.1) }\nfn main() { let mut x = (1, 2); flip(&mut x); x }",
    [], "(2, 1)"⟩,
  ⟨"fn sum(pair: &(Int, Int)) { (*pair).0 + (*pair).1 }\nfn main() { let mut x = (3, 4); sum(&x) }",
    [], "7"⟩,
  ⟨"fn main() { let mut x = (1, 2); x.0 = 5; x.1 = x.0 + 1; x }",
    [], "(5, 6)"⟩,
  ⟨"fn set(pair: &mut (Int, Int)) { (*pair).0 = 7; (*pair).1 = (*pair).0 + 1 }\nfn main() { let mut x = (1, 2); set(&mut x); x }",
    [], "(7, 8)"⟩,
  ⟨"fn main() { let mut x = ((1, 2), 3); x.0.1 = 9; x }",
    [], "((1, 9), 3)"⟩,
  ⟨"struct Point(Int, Int)\nfn main() { let mut p = Point(1, 2); p.1 = 8; match(p) { Point(a, b) => a + b } }",
    [], "9"⟩,
  ⟨"fn clash(pair: &mut (Int, Int)) { let a = &mut pair.0; let b = &mut pair.0; *a = 1; *b = 2 }\nfn main() { 0 }",
    [], "error: 1:56: in `clash`: `pair` is used while `a`, which borrows from it, is still in use"⟩,
  ⟨"fn clash(pair: &mut (Int, Int)) { let a = &mut pair.0; (*pair).0 = 3; *a = 1 }\nfn main() { 0 }",
    [], "error: 1:56: in `clash`: `pair` is used while `a`, which borrows from it, is still in use"⟩,
  ⟨"fn ok(pair: &mut (Int, Int)) { let a = &mut pair.0; (*pair).1 = 3; *a = 1 }\nfn main() { let mut x = (0, 0); ok(&mut x); x }",
    [], "(1, 3)"⟩,
  ⟨"fn ro(pair: &(Int, Int)) { let a = &mut pair.0; *a = 1 }\nfn main() { 0 }",
    [], "error: 1:28: in `ro`: a field is borrowed for writing through a `&mut` reference: expected `&mut _`, found `&(Int, Int)`"⟩,
  ⟨"fn main() { let mut x = (1, 2); let a = &mut (*x).0; 0 }",
    [], "error: 1:33: in `main`: `x` is a mutable variable, not a reference: its field is `x.0`"⟩,
  ⟨"fn main() { let mut x = (1, 2); let p = &mut x.0; x.0 = 5; *p }",
    [], "error: 1:51: in `main`: `x` is borrowed with `&mut` while `p` holds a `&mut` reference to it"⟩,
  ⟨"fn main() { let mut x = (1, 2); let p = &mut x.0; x.1 = 5; *p = 3; x }",
    [], "(3, 5)"⟩,
  ⟨"fn nested(p: &mut ((Int, Int), Int)) { let q = &mut p.0; (*q).1 = 4; }\nfn main() { let mut x = ((1, 2), 3); nested(&mut x); x }",
    [], "((1, 4), 3)"⟩,
  -- A struct, or a constructor of an enum, can name its fields. A value is
  -- built by name, in any order, a field is read, borrowed and assigned by
  -- name, and a pattern takes fields by name, `..` for the rest.
  ⟨"struct Point { x: Int, y: Int }\nfn main() { let p = Point { x: 1, y: 2 }; p.x + p.y * 10 }",
    [], "21"⟩,
  ⟨"struct Point { x: Int, y: Int }\nfn main() { let p = Point { y: 2, x: 1 }; p.x + p.y * 10 }",
    [], "21"⟩,
  ⟨"struct Point { x: Int, y: Int }\nfn sum(Point { x, y }) { x + y }\nfn main() { sum(Point { x: 3, y: 4 }) }",
    [], "7"⟩,
  ⟨"struct Point { x: Int, y: Int }\nfn main() { match(Point { x: 3, y: 4 }) { Point { x: a, .. } => a } }",
    [], "3"⟩,
  ⟨"struct Point { x: Int, y: Int }\nfn main() { let mut p = Point { x: 1, y: 2 }; p.x = 5; p.y = p.x + 1; p.x * 10 + p.y }",
    [], "56"⟩,
  ⟨"struct Point { x: Int, y: Int }\nfn incr(r) { *r = *r + 1 }\nfn main() { let mut p = Point { x: 1, y: 2 }; incr(&mut p.x); incr(&mut p.y); p.x + p.y }",
    [], "5"⟩,
  ⟨"struct Point { x: Int, y: Int }\nfn shift(p: &mut Point) { (*p).x = (*p).x + 10; p.y = 0 }\nfn main() { let mut p = Point { x: 1, y: 2 }; shift(&mut p); p.x + p.y }",
    [], "11"⟩,
  ⟨"struct Point { x: Int, y: Int }\nfn main() { let p = Point { x: 1 }; 0 }",
    [], "error: 2:13: in `main`: field `y` of `Point` is missing"⟩,
  ⟨"struct Point { x: Int, y: Int }\nfn main() { let p = Point { x: 1, y: 2, z: 3 }; 0 }",
    [], "error: 2:13: in `main`: `Point` has no field `z`"⟩,
  ⟨"struct Point { x: Int, y: Int }\nfn main() { let p = Point { x: 1, y: 2 }; p.z }",
    [], "error: 2:43: in `main`: `Point` has no field `z`"⟩,
  ⟨"enum Node { Leaf(Int), Branch { left: Int, right: Int } }\nfn total { Leaf(n) => n, Branch { left, right } => left + right }\nfn main() { total(Branch { left: 3, right: 4 }) + total(Leaf(1)) }",
    [], "8"⟩,
  ⟨"struct Line { a: Point, b: Point }\nstruct Point { x: Int, y: Int }\nfn main() { let mut l = Line { a: Point { x: 1, y: 2 }, b: Point { x: 3, y: 4 } }; l.b.x = 9; l.a.x + l.b.x }",
    [], "10"⟩,
  ⟨"struct Point { x: Int, y: Int }\nfn main() { let x = 7; let y = 8; let p = Point { x, y }; p.x + p.y }",
    [], "15"⟩,
  ⟨"struct Point { x: Int, y: Int }\nfn run(f) { f() }\nfn main() { run { let p = Point { x: 1, y: 2 }; p.x } }",
    [], "1"⟩,
  -- `type` gives a type another name; it is the same type. `Bool` and
  -- `Option<T>` are such names.
  ⟨"type Pair = (Int, Int)\ntype Maybe<T> = Result<T, ()>\nfn first(p: Pair) -> Int { p.0 }\nfn get(m: Maybe<Int>) -> Int { m else { 0 } }\nfn main() { first((3, 4)) + get(Some(5)) }",
    [], "8"⟩,
  ⟨"type A = B\ntype B = A\nfn f(x: A) { x }\nfn main() { 0 }",
    [], "error: type alias `B` stands for itself"⟩,
  ⟨"type Pair<T> = (T, T)\nfn f(x: Pair<Int, Int>) { x }\nfn main() { 0 }",
    [], "error: type alias `Pair` takes 1 arguments, but is given 2"⟩,
  ⟨"fn even(n: Int) -> Bool { n == 0 }\nfn pick(c: Bool, x: Option<Int>) -> Int { if(c) { x else { 0 } } else { 1 } }\nfn main() { pick(even(0), Some(4)) }",
    [], "4"⟩,
  -- A module is a unit: what it does not say is `pub` is its own, and its
  -- `pub` names are written with its path or brought in by `use`.
  ⟨"mod geometry {\n  pub struct Point { pub x: Int, pub y: Int }\n  pub fn origin() { Point { x: 0, y: 0 } }\n  pub fn shift(p: Point, dx: Int) -> Point { Point { x: p.x + dx, y: p.y } }\n  fn secret() { 42 }\n  pub fn reveal() { secret() }\n}\nfn main() { let p = geometry::shift(geometry::origin(), 3); p.x + geometry::reveal() }",
    [], "45"⟩,
  ⟨"mod geometry {\n  pub struct Point { pub x: Int, pub y: Int }\n  pub fn origin() { Point { x: 0, y: 0 } }\n  pub fn shift(p: Point, dx: Int) -> Point { Point { x: p.x + dx, y: p.y } }\n  fn secret() { 42 }\n  pub fn reveal() { secret() }\n}\nuse geometry::{Point, shift, origin as zero};\nfn main() { let p = shift(zero(), 3); let q = Point { x: 1, y: p.x }; q.y + q.x }",
    [], "4"⟩,
  ⟨"mod geometry {\n  pub struct Point { pub x: Int, pub y: Int }\n  pub fn origin() { Point { x: 0, y: 0 } }\n  pub fn shift(p: Point, dx: Int) -> Point { Point { x: p.x + dx, y: p.y } }\n  fn secret() { 42 }\n  pub fn reveal() { secret() }\n}\nuse geometry::*;\nfn main() { match(shift(origin(), 5)) { Point { x, .. } => x } }",
    [], "5"⟩,
  ⟨"mod geometry {\n  pub struct Point { pub x: Int, pub y: Int }\n  pub fn origin() { Point { x: 0, y: 0 } }\n  pub fn shift(p: Point, dx: Int) -> Point { Point { x: p.x + dx, y: p.y } }\n  fn secret() { 42 }\n  pub fn reveal() { secret() }\n}\nfn main() { geometry::secret() }",
    [], "error: 8:13: in `main`: `secret` is private to module `geometry`: only what is `pub` can be named from outside"⟩,
  ⟨"mod geometry {\n  pub struct Point { pub x: Int, pub y: Int }\n  pub fn origin() { Point { x: 0, y: 0 } }\n  pub fn shift(p: Point, dx: Int) -> Point { Point { x: p.x + dx, y: p.y } }\n  fn secret() { 42 }\n  pub fn reveal() { secret() }\n}\nuse geometry::secret;\nfn main() { secret() }",
    [], "error: `secret` is private to module `geometry`: only what is `pub` can be named from outside"⟩,
  -- A field that is not `pub` is its module's, so only that module can
  -- build or take apart a value: a type that has to be used cannot be
  -- let go of anywhere else.
  ⟨"mod files {\n  pub struct File(Int)\n  impl Use<[1, 1]> for File {}\n  pub fn open(n: Int) -> File { File(n) }\n  pub fn close(File(fd)) { host_write(fd) }\n}\nuse files::{File, open, close};\nfn main() { let f = open(3); close(f); 0 }",
    [], "3\n0"⟩,
  ⟨"mod files {\n  pub struct File(Int)\n  impl Use<[1, 1]> for File {}\n  pub fn open(n: Int) -> File { File(n) }\n  pub fn close(File(fd)) { host_write(fd) }\n}\nuse files::{File, open, close};\nfn main() { let File(fd) = open(3); fd }",
    [], "error: 8:13: in `main`: `File` has private fields: only module `files` can build one or take one apart"⟩,
  ⟨"mod files {\n  pub struct File(Int)\n  pub fn open(n: Int) -> File { File(n) }\n}\nfn main() { files::File(3); 0 }",
    [], "error: 5:13: in `main`: `File` has private fields: only module `files` can build one or take one apart"⟩,
  ⟨"mod files {\n  pub struct File(Int)\n  pub fn open(n: Int) -> File { File(n) }\n}\nfn main() { files::open(3).0 }",
    [], "error: 5:13: in `main`: this field of `File` is not `pub`: only the module that declares `File` can read or borrow it"⟩,
  ⟨"mod files {\n  pub struct File(Int)\n  impl Use<[1, 1]> for File {}\n  pub fn open(n: Int) -> File { File(n) }\n}\nfn main() { let f = files::open(3); 0 }",
    [], "error: 6:13: in `main`: `f` is not used on every path, but a `files::File` has to be used"⟩,
  ⟨"mod files {\n  pub struct File(Int)\n  pub fn open(n: Int) -> File { File(n) }\n}\nimpl Use<[0, 1]> for files::File {}\nfn main() { 0 }",
    [], "error: `impl Use for files::File` is written in the first module: how often a type is used is said in its module, module `files`"⟩,
  -- Which module uses which has no cycle, the first module among them.
  ⟨"pub mod a { pub fn f(n) { crate::b::g(n) } }\npub mod b { pub fn g(n) { crate::a::f(n) } }\nfn main() { a::f(1) }",
    [], "error: modules use each other in a circle (b -> a -> b); which module uses which must have no cycle"⟩,
  ⟨"pub mod a { pub fn f(n) { n + 1 } }\nmod b { pub fn g(n) { crate::a::f(n) * 2 } }\nfn main() { b::g(1) }",
    [], "4"⟩,
  ⟨"mod a { pub fn f(n) { crate::helper(n) } }\nfn helper(n) { n }\nfn main() { a::f(1) }",
    [], "error: 1:23: in `f`: `helper` is private to the first module: only what is `pub` can be named from outside"⟩,
  ⟨"mod a { pub fn f(n) { crate::helper(n) } }\npub fn helper(n) { n }\nfn main() { a::f(1) }",
    [], "error: modules use each other in a circle (a -> the first module -> a); which module uses which must have no cycle"⟩,
  -- Modules in modules; enums, effects, traits and aliases of a module;
  -- `pub use`; `pub(super)`.
  ⟨"mod outer {\n  pub mod inner { pub fn f() { 7 } }\n  pub fn g() { inner::f() + 1 }\n}\nfn main() { outer::g() + outer::inner::f() }",
    [], "15"⟩,
  ⟨"mod list {\n  pub enum List { Nil, Cons(Int, List) }\n  pub fn sum { Nil => 0, Cons(x, rest) => x + sum(rest) }\n}\nuse list::{List, Nil, Cons, sum};\nfn main() { sum(Cons(1, Cons(2, Nil))) }",
    [], "3"⟩,
  ⟨"mod list {\n  pub enum List { Nil, Cons(Int, List) }\n}\nfn main() { list::List::Cons(1, list::Nil) }",
    [], "Cons(1, Nil)"⟩,
  ⟨"mod state {\n  pub effect State { get() -> Int, put(Int) }\n  pub fn run(init: Int, body) { let mut s = init; handle body() { get(k) => k(s), put(v, k) => s = v; k(()) } }\n}\nuse state::{State, get, put, run};\nfn main() { run(1) { put(get() + 41); get() } }",
    [], "42"⟩,
  ⟨"pub mod show {\n  pub trait Show { fn show(Self) -> Int }\n  impl Show for Int { fn show(n) { n + 100 } }\n}\nmod pt {\n  pub struct P(pub Int)\n  impl crate::show::Show for P { fn show(P(n)) { n } }\n}\nuse show::show;\nfn main() { show(1) + show(pt::P(2)) }",
    [], "103"⟩,
  ⟨"mod show {\n  pub trait Show { fn show(Self) -> Int }\n}\nmod pt {\n  pub struct P(pub Int)\n}\nimpl show::Show for pt::P { fn show(pt::P(n)) { n } }\nfn main() { show::show(pt::P(2)) }",
    [], "error: `impl show::Show for pt::P` is written in the first module: an implementation is written in the module of its trait or of its type"⟩,
  ⟨"pub mod a { pub fn f() { 1 } }\nmod b { pub use crate::a::f; }\nfn main() { b::f() }",
    [], "1"⟩,
  ⟨"mod a { pub type Pair = (Int, Int); pub fn fst(p: Pair) -> Int { p.0 } }\nfn g(p: a::Pair) -> Int { a::fst(p) }\nfn main() { g((4, 5)) }",
    [], "4"⟩,
  ⟨"mod a { pub(super) fn f() { 1 } pub mod deep { pub(super) fn g() { 2 } } pub fn h() { deep::g() } }\nfn main() { a::f() + a::h() }",
    [], "3"⟩,
  ⟨"mod a { pub mod deep { pub(super) fn g() { 2 } } }\nfn main() { a::deep::g() }",
    [], "error: 2:13: in `main`: `g` is private to module `a::deep`: only what is `pub` can be named from outside"⟩,
  ⟨"mod shapes { pub struct Sq { pub side: Int } pub enum Shape { Circle { r: Int }, Rect { w: Int, h: Int } } }\nuse shapes::{Sq, Shape, Circle, Rect};\nfn area { Circle { r } => 3 * r * r, Rect { w, h } => w * h }\nfn main() { area(Rect { h: 2, w: 5 }) + area(shapes::Circle { r: 1 }) + Sq { side: 4 }.side }",
    [], "17"⟩,
  ⟨"mod ops { infixl 6 +++; pub fn +++(a, b) { a * 10 + b } }\nuse ops::+++;\nfn main() { 1 +++ 2 +++ 3 }",
    [], "123"⟩,
  ⟨"mod a { pub struct S { pub open: Int, shut: Int } pub fn make() { S { open: 1, shut: 2 } } pub fn shut(s: S) -> Int { s.shut } }\nfn main() { let s = a::make(); s.open + a::shut(s) }",
    [], "3"⟩,
  ⟨"mod a { pub struct S { pub open: Int, shut: Int } pub fn make() { S { open: 1, shut: 2 } } }\nfn main() { let s = a::make(); s.shut }",
    [], "error: 2:32: in `main`: this field of `S` is not `pub`: only the module that declares `S` can read or borrow it"⟩,
  ⟨"mod a { pub struct S { pub open: Int, shut: Int } pub fn make() { S { open: 1, shut: 2 } } }\nfn main() { let mut s = a::make(); s.shut = 5; 0 }",
    [], "error: 2:36: in `main`: this field of `S` is not `pub`: only the module that declares `S` can read or borrow it"⟩,
  ⟨"mod a { pub fn f() { 1 } }\nmod a { pub fn g() { 2 } }\nfn main() { 0 }",
    [], "error: module `a` is written twice"⟩,
  ⟨"mod a { pub fn f() { 1 } }\nuse a::nothing;\nfn main() { 0 }",
    [], "error: `use a::nothing`: module `a` has no `nothing`"⟩,
  ⟨"use nowhere::f;\nfn main() { 0 }",
    [], "error: `use nowhere::f`: there is no module `nowhere`"⟩,
  ⟨"mod a { pub fn print(n) { n + 1 } pub fn g() { print(1) } }\nfn main() { a::g() }",
    [], "2"⟩,
  -- Whole numbers of other widths, written `5u8`. Each type has the
  -- operators; a result that does not fit has no meaning.
  ⟨"fn main() { say(100u8 + 27u8); say(int(300i16 * 100i16)); say(7 / 2); say(-7 % 3); say(5u32 / 2u32); say(0xFFu8); say(1_000_000 + 0b101 + 0o17); int(u8(255)) + int(-128i8) }",
    [], "127\n30000\n3\n-1\n2\n255\n1000020\n127"⟩,
  ⟨"fn main() { 200u8 + 100u8 }",
    [], "went wrong"⟩,
  ⟨"fn main() { 300u8 }",
    [], "error: 1:13: `300` does not fit in `u8`, found `300u8`"⟩,
  ⟨"fn main() { u8(256) }",
    [], "went wrong"⟩,
  ⟨"fn main() { 1 / 0 }",
    [], "went wrong"⟩,
  ⟨"fn f(a: i8, b: u8) -> i8 { a + b }\nfn main() { 0 }",
    [], "error: 1:28: in `f`: argument 2 of `+`: expected `i8`, found `u8`"⟩,
  ⟨"fn twice(x) { x + x }\nfn main() { say(twice(3)); say(twice(3u8)); say(twice(1.5)); 0 }",
    [], "6\n6\n3.0\n0"⟩,
  ⟨"fn g { 5u8 => 1, _ => 0 }\nfn main() { g(5u8) + g(6u8) }",
    [], "1"⟩,
  -- Floating point: 64 bits and 32, the nearest number to the true result,
  -- on every machine alike; shown with the fewest digits that give the
  -- number back.
  ⟨"fn main() { say(1.5 + 2.25); say(0.1 + 0.2); say(1.0 / 3.0); say(1e21); say(1.5e-7); say(-0.0); say(0.0 / 0.0); say(1.0 / 0.0); say(100.0); say(123456.789); say(0.1f32 + 0.2f32); say(f64(7) / 2.0); int(2.75) }",
    [], "3.75\n0.30000000000000004\n0.3333333333333333\n1e21\n1.5e-7\n-0.0\nNaN\ninf\n100.0\n123456.789\n0.3\n3.5\n2"⟩,
  ⟨"fn sqrt(x: f64) -> f64 { improve(x, x / 2.0, 0) }\nfn improve(x: f64, guess: f64, n: Int) -> f64 {\n    if(n == 30) { guess } else { improve(x, (guess + x / guess) / 2.0, n + 1) }\n}\nfn harmonic(n: Int, sum: f64) -> f64 { if(n == 0) { sum } else { harmonic(n - 1, sum + 1.0 / f64(n)) } }\nfn powers(x: f64, n: Int) { if(n == 0) { () } else { say(x); powers(x * 10.5, n - 1) } }\nfn shrink(x: f32, n: Int) { if(n == 0) { () } else { say(x); shrink(x / 3.0f32, n - 1) } }\nfn main() {\n    say(sqrt(2.0)); say(sqrt(1e-300)); say(harmonic(200, 0.0));\n    powers(1.25e-12, 30);\n    shrink(1.0f32, 12);\n    say(narrow(0.1)); say(widen(0.1f32)); say(4.9e-324); say(1.7976931348623157e308);\n    say(int(1e15 + 0.5)); say(f64(9007199254740993)); say(2.5e-5); say(1e16); say(1e17); say(123456789012345680.0);\n    int(sqrt(1e10))\n}",
    [], "1.414213562373095\n1.862645149230957e-9\n5.878030948121443\n1.25e-12\n1.3125e-11\n1.378125e-10\n1.4470312500000001e-9\n1.5193828125000002e-8\n1.5953519531250002e-7\n1.6751195507812503e-6\n0.00001758875528320313\n0.00018468193047363284\n0.0019391602699731449\n0.020361182834718022\n0.21379241976453922\n2.2448204075276617\n23.57061427904045\n247.4914499299247\n2598.6602242642093\n27285.9323547742\n286502.2897251291\n3008274.0421138555\n31586877.442195483\n331662213.1430526\n3482453238.0020523\n36565758999.021545\n383940469489.7262\n4031374929642.125\n42329436761242.31\n444459085993044.25\n4666820402926965.0\n49001614230733140.0\n5.145169494226979e17\n1.0\n0.33333334\n0.11111111\n0.037037037\n0.012345679\n0.004115226\n0.0013717421\n0.00045724737\n0.00015241579\n0.00005080526\n0.000016935088\n5.6450294e-6\n0.1\n0.10000000149011612\n5e-324\n1.7976931348623157e308\n1000000000000000\n9007199254740992.0\n0.000025\n10000000000000000.0\n1e17\n1.2345678901234568e17\n100000"⟩,
  ⟨"fn area(r: f64) -> f64 { 3.14159 * r * r }\nfn main() { say(area(2.0)); if(1.0 < 2.0 and { 2.5 >= 2.5 } and { not (0.0 / 0.0 == 0.0 / 0.0) }) { 1 } else { 0 } }",
    [], "12.56636\n1"⟩,
  ⟨"fn main() { 1e400 }",
    [], "error: 1:13: this number is too large for its type, found a number"⟩,
  ⟨"fn main() { int(1.0 / 0.0) }",
    [], "went wrong"⟩,
  -- Characters and text. A text is its characters one after another; `say`
  -- writes a value as text.
  ⟨"fn main() { say(42); say(-7); say(\"hi\" ++ \" there\"); say('x'); say(100u8 + 27u8); print((\"a\\\"b\", 1)); \"done\\n\" }",
    [], "42\n-7\nhi there\nx\n127\n(\"a\\\"b\", 1)\ndone\n"⟩,
  ⟨"fn f { 'a' => 1, 'b' => 2, _ => 0 }\nfn main() { say(f('b') + f('\\n')); say(int('\\u{1F600}')); say(char(955) else { '?' }); say(char(55296) else { '?' }); if('a' < 'b') { 1 } else { 0 } }",
    [], "2\n128512\nλ\n?\n1"⟩,
  ⟨"fn shout(text) { match(text) { StrEnd => \"!\", StrChar(c, rest) => StrChar(c, shout(rest)) } }\nfn greet { \"hi\" => 1, \"\" => 2, _ => 0 }\nfn main() { say(shout(\"hey\")); say(length(\"h\\u{e9}llo\")); say(\"caf\\u{e9} \\\"x\\\"\"); if(\"ab\" ++ \"c\" == \"abc\") { greet(\"hi\") + greet(\"\") } else { 0 } }",
    [], "hey!\n5\ncafé \"x\"\n3"⟩,
  ⟨"fn main() { \"open }",
    [], "error: 1:13: this text is not closed"⟩,
  -- The first module may declare a name the prelude has; the prelude keeps
  -- its own.
  ⟨"fn zeros() { 5 }\nfn show(x) { x + 1 }\nfn main() { say(1.5); show(zeros()) }",
    [], "1.5\n6"⟩,
  ⟨"trait Show { fn show(Self) -> Int }\nimpl Show for Int { fn show(n) { n + 1 } }\nfn main() { say(2.5); show(1) }",
    [], "2.5\n2"⟩,
  ⟨"enum Str { A, B }\nfn main() { say(\"text\"); match(A) { A => 1, B => 2 } }",
    [], "text\n1"⟩,
  -- `value is Pattern` is a test: it gives what the pattern's names stand
  -- for, or fails. `if` gives its body what the test found, and a block
  -- given that has those names. No rule names `if`: a function a program
  -- defines does the same.
  ⟨"fn main() { let v = Some(4); if(v is Some(n)) { n + 1 } else { 0 } }",
    [], "5"⟩,
  ⟨"fn main() { let v = None; if(v is Some(n)) { n + 1 } else { 0 } }",
    [], "0"⟩,
  ⟨"enum Shape { Circle(Int), Rect(Int, Int) }\nfn area(s) { if(s is Rect(w, h)) { w * h } or { if(s is Circle(r)) { 3 * r * r } } else { 0 } }\nfn main() { area(Rect(2, 5)) + area(Circle(1)) }",
    [], "13"⟩,
  ⟨"fn main() { let p = (1, 2); if(p is (a, 2)) { a } else { 9 } }",
    [], "1"⟩,
  ⟨"fn main() { let v = Some(4); if(v is Some(n)) { 1 } else { n } }",
    [], "error: 1:60: in `main`: unknown name `n`"⟩,
  ⟨"fn main() { let v = Some(4); let t = v is Some(n); match(t) { Ok(_) => 1, Err(_) => 0 } }",
    [], "1"⟩,
  ⟨"fn main() { let n = 100; let v = Some(4); if(v is Some(n)) { n } else { n } }",
    [], "4"⟩,
  ⟨"fn main() { let v = Some(3); if(v is None) { 0 } else { 1 } }",
    [], "1"⟩,
  ⟨"fn count(xs, n) { if(xs is Some(rest)) { n + rest } else { n } }\nfn main() { count(Some(5), 1) + count(None, 1) }",
    [], "7"⟩,
  ⟨"fn main() { let c = 'x'; if(c is 'x') { 1 } else { 0 } }",
    [], "1"⟩,
  ⟨"fn main() { let v = Some(4); if(v is Some(n) and { n > 3 }) { 1 } else { 0 } }",
    [], "1"⟩,
  ⟨"fn next(i) { if(i < 3) { i + 1 } }\nfn main() { let mut i = 0; let mut sum = 0; while({ next(i) is Ok(j) }) { i = j; sum = sum + j; }; sum }",
    [], "6"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn main() { let f = Some(File(3)); if(f is Some(g)) { close(g); 1 } else { 0 } }",
    [], "error: 4:36: in `main`: `_` lets go of a value, but a `File` has to be used"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd) }\nfn main() { let f = Some(File(3)); if(f is Some(g)) { 1 } else { 0 } }",
    [], "error: 4:36: in `main`: `g` is not used on every path, but a `File` has to be used"⟩,
  ⟨"effect Ask { ask() -> Int }\nfn main() { handle ask() + 1 { ask(k) => let v = Some(2); if(v is Some(n)) { k(n) } else { k(0) } } }",
    [], "3"⟩,
  ⟨"fn main() { let v = Some((1, 2)); if(v is Some((a, b))) { a + b } else { 0 } }",
    [], "3"⟩,
  ⟨"fn pick(t, f) { match(t) { Ok(found) => f(found), Err(_) => 0 } }\nfn main() { pick(Some(7) is Some(n)) { n * 2 } }",
    [], "14"⟩,
  -- A type parameter can be said to be a callable: `F: Fn<(A, B), Output =
  -- R, Effects = {E}>` is `fn(A, B) -> R / {E}`.
  ⟨"fn apply<F, A, R>(f: F, x: A) -> R where F: Fn<(A,), Output = R> { f(x) }\nfn main() { apply({ n => n + 1 }, 4) }",
    [], "5"⟩,
  ⟨"fn twice<F: Fn<(Int,), Output = Int>>(f: F, x: Int) -> Int { f(f(x)) }\nfn main() { twice({ n => n * 3 }, 2) }",
    [], "18"⟩,
  ⟨"fn run<F>(f: F) -> Int where F: Fn<(), Output = Int, Effects = {}> { f() }\neffect Ask { ask() -> Int }\nfn main() { handle run({ ask() }) { ask(k) => k(1) } }",
    [], "error: 3:13: in `main`: argument 1 of `run`: expected `fn() -> Int`, found `fn() -> Int / {Ask}` (effect `Ask` is not handled here)"⟩,
  ⟨"fn run<F>(f: F) -> Int where F: Fn<(), Output = Int, Effects = {}> { f() }\nfn main() { run({ 7 }) }",
    [], "7"⟩,
  ⟨"fn apply<F, A, R>(f: F, x: A) -> R where F: Fn<(A), Output = R> { f(x) }\nfn main() { 0 }",
    [], "error: 1:50: a callable of one argument is written `Fn<(T,)>`: without the comma `(T)` is `T` in brackets, found `)`"⟩,
  ⟨"fn apply<F, A, R>(f: F, x: A) -> R where F: Fn<(A,), Output = R> { f(x, x) }\nfn main() { 0 }",
    [], "error: 1:68: in `apply`: `f` takes 1 argument, but is given 2"⟩,
  ⟨"fn apply<F, A, R>(f: F, x: A) -> R where F: Fn<(A,), Output = R> { f(x) }\nfn main() { apply(3, 4) }",
    [], "error: 2:13: in `main`: argument 1 of `apply`: expected `fn(_) -> _`, found `Int`"⟩,
  -- Callables that run in one environment, given whole, use it up: at
  -- most one is called, and if the environment has to be used, one. Blocks
  -- given for them are built over one environment, which Core shows is
  -- owned once.
  ⟨"fn pick<'e, E, A, B>(c: Bool, a: A, b: B) -> Int where E: Environment<'e>, A: RunsIn<E, (), Output = Int>, B: RunsIn<E, (), Output = Int> { match(c) { Ok(_) => a(), Err(_) => b() } }\neffect Ask { ask() -> Int }\nfn main() { handle ask() + 1 { ask(k) => pick(1 < 2, { k(1) }, { k(2) }) } }",
    [], "2"⟩,
  ⟨"fn both<'e, E, A, B>(a: A, b: B) -> Int where E: Environment<'e>, A: RunsIn<E, (), Output = Int>, B: RunsIn<E, (), Output = Int> { a() + b() }\nfn main() { both({ 1 }, { 2 }) }",
    [], "error: in `both`: `a`, `b` run in the environment `E`, which is used up by the first that is called: on some path more than one call is made"⟩,
  ⟨"fn maybe<'e, E, A, B>(c: Bool, a: A, b: B) -> Int where E: Environment<'e> + Use<[1, 1]>, A: RunsIn<E, (), Output = Int>, B: RunsIn<E, (), Output = Int> { match(c) { Ok(_) => a(), Err(_) => 0 } }\nfn main() { maybe(1 < 2, { 1 }, { 2 }) }",
    [], "error: in `maybe`: the environment `E` has to be used: on some path none of `a`, `b` is called"⟩,
  ⟨"fn maybe<'e, E, A, B>(c: Bool, a: A, b: B) -> Int where E: Environment<'e>, A: RunsIn<E, (), Output = Int>, B: RunsIn<E, (), Output = Int> { match(c) { Ok(_) => a(), Err(_) => 0 } }\nfn main() { maybe(1 < 2, { 1 }, { 2 }) }",
    [], "1"⟩,
  ⟨"fn again<'e, E, A>(a: A) -> Int where E: Environment<'e>, A: RunsIn<&mut E, (), Output = Int> { a() + a() }\nfn main() { again({ 4 }) }",
    [], "8"⟩,
  ⟨"fn again<'e, E, A>(a: A) -> Int where E: Environment<'e>, A: RunsIn<E, (), Output = Int> { a() + a() }\nfn main() { again({ 4 }) }",
    [], "error: in `again`: `a` run in the environment `E`, which is used up by the first that is called: on some path more than one call is made"⟩,
  ⟨"fn pick<'e, E, A, B>(c: Bool, a: A, b: B) -> Int where E: Environment<'e>, A: RunsIn<E, (), Output = Int>, B: RunsIn<E, (), Output = Int> { match(c) { Ok(_) => a(), Err(_) => b() } }\nfn one() { 1 }\nfn two() { 2 }\nfn main() { pick(1 < 2, one, two) + pick(2 < 1, { 10 }, two) }",
    [], "3"⟩,
  ⟨"fn pick<'e, E, A, B>(c: Bool, a: A, b: B) -> Int where E: Environment<'e>, A: RunsIn<E, (), Output = Int>, B: RunsIn<E, (), Output = Int> { match(c) { Ok(_) => a(), Err(_) => b() } }\nfn main() { let p = pick; 0 }",
    [], "error: 2:13: in `main`: `pick` gives callables one environment to share, so it is called where it is named: write a block that calls it"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd); fd }\nfn pick<'e, E, A, B>(c: Bool, a: A, b: B) -> Int where E: Environment<'e> + Use<[1, 1]>, A: RunsIn<E, (), Output = Int>, B: RunsIn<E, (), Output = Int> { match(c) { Ok(_) => a(), Err(_) => b() } }\nfn main() { let f = File(3); pick(2 < 1, { close(f) }, { close(f) + 1 }) }",
    [], "3\n4"⟩,
  ⟨"fn three<'e, E, A, B, C>(n: Int, a: A, b: B, c: C) -> Int where E: Environment<'e>, A: RunsIn<E, (), Output = Int>, B: RunsIn<E, (), Output = Int>, C: RunsIn<E, (), Output = Int> { match(n) { 0 => a(), 1 => b(), _ => c() } }\neffect Ask { ask() -> Int }\nfn main() { handle ask() + 1 { ask(k) => let m = 5; three(1, { k(m) }, { k(m + 1) }, { k(m + 2) }) } }",
    [], "7"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd); fd }\nfn pick<'e, E, A, B>(c: Bool, a: A, b: B) -> Int where E: Environment<'e> + Use<[1, 1]>, A: RunsIn<E, (), Output = Int>, B: RunsIn<E, (), Output = Int> { match(c) { Ok(_) => a(), Err(_) => b() } }\nfn main() { let f = File(3); let g = File(4); let r = pick(2 < 1, { close(f) }, { close(f) + close(g) }); r }",
    [], "error: 5:47: in `main`: `g` has to be used, and one of the blocks given to `pick` holds it but not every one: only one of them runs"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd); fd }\nfn pick<'e, E, A, B>(c: Bool, a: A, b: B) -> Int where E: Environment<'e>, A: RunsIn<E, (), Output = Int>, B: RunsIn<E, (), Output = Int> { match(c) { Ok(_) => a(), Err(_) => b() } }\nfn main() { let f = File(3); pick(2 < 1, { close(f) }, { close(f) + 1 }) }",
    [], "error: 5:30: in `main`: `pick` may leave what it is given unused, but a callable that holds a `File` has to be used"⟩,
  ⟨"struct File(Int)\nimpl Use<[1, 1]> for File {}\nfn close(File(fd)) { host_write(fd); fd }\nfn pick<'e, E, A, B>(c: Bool, a: A, b: B) -> Int where E: Environment<'e> + Use<[1, 1]>, A: RunsIn<E, (), Output = Int>, B: RunsIn<E, (), Output = Int> { match(c) { Ok(_) => a(), Err(_) => b() } }\nfn main() { let f = File(3); let h = { close(f) }; pick(2 < 1, { 1 }, h) }",
    [], "error: 5:30: in `main`: `h` is not used on every path, but a callable that holds a `File` has to be used"⟩,
  ⟨"fn bad<A>(a: A) -> Int where A: RunsIn<E, (), Output = Int> { a() }\nfn main() { 0 }",
    [], "error: in `bad`: `A: RunsIn<E, ..>`: `E` is not said to be an environment (`E: Environment<'e>`)"⟩,
  ⟨"trait Show { fn show(Self) -> Int }\nimpl Show for Int { fn show(n) { n } }\nfn f<T>(x: T) -> Int where T: Show { show(x) }\nfn main() { f(3) }",
    [], "3"⟩,
  ⟨"fn f<T>(x: T) -> Int where T: Nope { 0 }\nfn main() { f(3) }",
    [], "error: in `f`: `T: Nope`: unknown trait `Nope`"⟩,
  -- Where references meet at a call their lifetimes are related, not made
  -- one: `r` is not taken to borrow `b` for having been given beside it.
  ⟨"fn same<'a>(x: &'a Int, y: &'a Int) -> Int { *x + *y }\nfn main() { let mut a = 1; let mut b = 2; let r = &a; let n = same(r, &b); b = 5; *r + n }",
    [], "4"⟩,
  ⟨"fn pick<'a>(x: &'a Int, y: &'a Int) -> &'a Int { x }\nfn main() { let mut a = 1; let mut b = 2; let r = &a; let q = pick(r, &b); b = 5; *r }",
    [], "1"⟩,
  ⟨"fn pick<'a>(x: &'a Int, y: &'a Int) -> &'a Int { x }\nfn main() { let mut a = 1; let mut b = 2; let r = &a; let q = pick(r, &b); b = 5; *q }",
    [], "error: 2:76: in `main`: `b` is assigned while `q` holds a reference to it"⟩,
  -- A trait's function has no body to find its lifetimes from: the
  -- unwritten ones are one, and an implementation is held to what is
  -- written.
  ⟨"trait Same { fn same(&Self) -> &Self }\nimpl Same for Int { fn same(r) { r } }\nfn main() { let mut x = 1; let r = same(&x); x = 2; *r }",
    [], "error: 3:46: in `main`: `x` is assigned while `r` holds a reference to it"⟩,
  ⟨"trait Same { fn same(&Self) -> &Self }\nimpl Same for Int { fn same(r) { r } }\nfn main() { let mut x = 1; let r = same(&x); *r }",
    [], "1"⟩,
  ⟨"trait Pick { fn first(&'a Self, &'b Self) -> &'a Self }\nimpl Pick for Int { fn first(x, y) { x } }\nfn main() { let mut a = 1; let mut b = 2; let r = first(&a, &b); b = 5; *r }",
    [], "1"⟩,
  ⟨"trait Pick { fn first(&'a Self, &'b Self) -> &'a Self }\nimpl Pick for Int { fn first(x, y) { y } }\nfn main() { 0 }",
    [], "error: in `Pick::first@Int`: this is not the function `Pick` declares, which takes its arguments, gives its result and performs nothing: lifetime `the trait's 'b` is not `the trait's 'a`: a reference that lasts for one is used where one that lasts for the other is wanted"⟩,
  ⟨"trait Pick { fn any(&Self, &Self) -> &Self }\nimpl Pick for Int { fn any(x, y) { y } }\nfn main() { let mut a = 1; let mut b = 2; let r = any(&a, &b); b = 5; *r }",
    [], "error: 3:64: in `main`: `b` is assigned while `r` holds a reference to it"⟩,
  -- `T: 'a`: what lasts for `'a` may hold a `T`.
  ⟨"fn keep<'a, T: 'a>(r: &'a Int, v: T) -> &'a Int { r }\nfn main() { let mut x = 1; let mut y = 2; let q = keep(&x, &y); y = 5; *q }",
    [], "error: 2:65: in `main`: `y` is assigned while `q` holds a reference to it"⟩,
  ⟨"fn keep<'a, T>(r: &'a Int, v: T) -> &'a Int { r }\nfn main() { let mut x = 1; let mut y = 2; let q = keep(&x, &y); y = 5; *q }",
    [], "1"⟩,
  ⟨"fn keep<'a, T>(r: &'a Int, v: T) -> &'a Int where T: 'a { r }\nfn main() { let mut x = 1; let q = keep(&x, 7); *q }",
    [], "1"⟩,
  -- `for<'a>`: a callable for references of every lifetime can be given a
  -- reference to a variable of the function it is given to, and cannot
  -- keep it.
  ⟨"fn apply(f: for<'a> fn(&'a Int) -> Int) -> Int { let mut x = 1; let mut y = 2; f(&x) + f(&y) }\nfn main() { apply({ r => *r + 1 }) }",
    [], "5"⟩,
  ⟨"fn apply<F>(f: F) -> Int where F: for<'a> Fn<(&'a Int,), Output = Int> { let mut x = 5; f(&x) }\nfn main() { apply({ r => *r * 2 }) }",
    [], "10"⟩,
  ⟨"fn apply(f: for<'a> fn(&'a Int) -> &'a Int) -> Int { let mut x = 1; let r = f(&x); *r }\nfn main() { apply({ r => r }) }",
    [], "1"⟩,
  ⟨"fn apply(f: for<'a> fn(&'a Int) -> Int) -> Int { let mut x = 1; f(&x) }\nfn main() { let mut keep = None; let mut z = 0; let n = apply({ r => keep = Some(r); 0 }); n }",
    [], "error: 2:49: in `main`: argument 1 of `apply`: a reference this callable is given is kept in `keep`, and the callable is wanted for references of any lifetime"⟩,
  ⟨"fn apply(f: for<'a, 'b> fn(&'a Int, &'b Int) -> &'a Int) -> Int { let mut x = 1; let mut y = 2; *f(&x, &y) }\nfn main() { apply(fn(a, b) { b }) }",
    [], "error: 2:13: in `main`: argument 1 of `apply`: lifetime `'b` is not known to last as long as `'a`: say `'b: 'a`"⟩,
  ⟨"fn apply(f: for<'a, 'b> fn(&'a Int, &'b Int) -> &'a Int) -> Int { let mut x = 1; let mut y = 2; let r = f(&x, &y); y = 7; *r + y }\nfn main() { apply(fn(a, b) { a }) }",
    [], "8"⟩,
  ⟨"fn apply(f: for<'a> fn(&'a mut Int)) { let mut x = 1; f(&mut x); print(x) }\nfn main() { apply({ r => *r = *r + 41 }); 0 }",
    [], "42\n0"⟩,
  ⟨"fn inner(f: for<'a> fn(&'a Int) -> Int) -> Int { let mut x = 3; f(&x) }\nfn outer(g: for<'a> fn(&'a Int) -> Int) -> Int { inner(g) + 1 }\nfn main() { outer({ r => *r }) }",
    [], "4"⟩,
  ⟨"fn apply(f: for<'a> fn(&'a Int) -> &'a Int) -> Int { let mut x = 1; let mut y = 2; let r = f(&x); x = 5; *r }\nfn main() { apply({ r => r }) }",
    [], "error: 1:99: in `apply`: `x` is assigned while `r` holds a reference to it"⟩,
  ⟨"fn bad(f: Option<for<'a> fn(&'a Int) -> Int>) -> Int { 0 }\nfn main() { 0 }",
    [], "error: in `bad`: `for<..>` is written of the type of a parameter, not inside another type"⟩,
  ⟨"fn f() -> for<'a> fn(&'a Int) -> Int { { r => *r } }\nfn main() { let mut x = 6; f()(&x) }",
    [], "6"⟩,
  -- An effect can take a lifetime: what its operations give may borrow
  -- from where the effect is handled.
  ⟨"effect Reader<'a> { ask() -> &'a Int }\nfn use_it() -> Int { *ask() + 1 }\nfn main() { let mut x = 41; handle use_it() { ask(k) => k(&x) } }",
    [], "42"⟩,
  ⟨"effect Reader { ask() -> &Int }\nfn use_it() -> Int { *ask() + 1 }\nfn main() { let mut x = 41; handle use_it() { ask(k) => k(&x) } }",
    [], "error: 3:13: in `main`: `x` could be used after its block has ended: it is stored in a declaration's `fn` field; give that declaration a type parameter for the field"⟩,
  ⟨"effect Reader { ask() -> &Int }\nfn main() { let mut x = 41; let mut y = 1; let a = handle *ask() { ask(k) => k(&x) }; let b = handle *ask() { ask(k) => k(&y) }; x = 2; a + b }",
    [], "error: 2:29: in `main`: `y` could be used after its block has ended: it is stored in a declaration's `fn` field; give that declaration a type parameter for the field"⟩,
  ⟨"effect Reader<'a> { ask() -> &'a Int }\nfn main() { let mut x = 41; let mut y = 1; let a = handle *ask() { ask(k) => k(&x) }; let b = handle *ask() { ask(k) => k(&y) }; x = 2; a + b }",
    [], "42"⟩,
  ⟨"effect Reader<'a> { ask() -> &'a Int }\nfn both() -> Int { let r = ask(); let s = ask(); *r + *s }\nfn main() { let mut x = 20; handle both() { ask(k) => k(&x) } }",
    [], "40"⟩,
  ⟨"effect Reader<'a> { ask() -> &'a Int }\nfn leak() -> &Int { ask() }\nfn main() { let mut x = 20; let r = handle leak() { ask(k) => k(&x) }; x = 5; *r }",
    [], "error: 3:72: in `main`: `x` is assigned while `r` holds a reference to it"⟩,
  ⟨"effect Slot<'a> { slot() -> &'a mut Int }\nfn bump() { let p = slot(); *p = *p + 1 }\nfn main() { let mut x = 1; handle bump() { slot(k) => k(&mut x) }; x }",
    [], "error: 3:55: in `main`: calling `k` may assign or borrow `x` while a value this expression is still using holds a `&mut` reference to it"⟩,
  ⟨"effect Reader<'a, T> { ask() -> &'a T }\nfn get() -> Int / {Reader<'_, Int>} { *ask() }\nfn main() { let mut x = 9; handle get() { ask(k) => k(&x) } }",
    [], "9"⟩,
  -- A field of what any expression that gives a reference points to can be
  -- borrowed or assigned: the reference is given a name first.
  ⟨"struct P(Int, Int)\nfn pick(r: &mut P) -> &mut P { r }\nfn main() { let mut x = P(1, 2); let q = &mut pick(&mut x).0; *q = 9; x.0 + x.1 }",
    [], "11"⟩,
  ⟨"struct P(Int, Int)\nfn pick(r: &mut P) -> &mut P { r }\nfn main() { let mut x = P(1, 2); pick(&mut x).1 = 7; x.0 + x.1 }",
    [], "8"⟩,
  ⟨"struct P(Int, Int)\nfn pick(r: &mut P) -> &mut P { r }\nfn bump(r) { *r = *r + 1 }\nfn main() { let mut x = P(1, 2); bump(&mut pick(&mut x).0); x.0 }",
    [], "2"⟩,
  ⟨"struct P(Int, Int)\nfn pick(r: &mut P) -> &mut P { r }\nfn two(a, r) { *r = *r + a }\nfn main() { let mut x = P(1, 2); let mut n = 3; two(n, &mut pick(&mut x).0); x.0 }",
    [], "error: 4:49: a field is borrowed of what an expression points to, after something else in the statement is computed: give the reference a `let` of its own first"⟩,
  ⟨"struct P(Int, Int)\nfn make() -> P { P(1, 2) }\nfn main() { let q = &mut make().0; *q }",
    [], "error: 3:13: in `main`: what a field is borrowed of here is a value that nothing holds, not a reference: give it a `let mut` first"⟩,
  -- `&mut Pattern` as a clause's parameter matches what a reference points
  -- to, and its names are references to the parts: so a part of one of a
  -- type's several constructors can be borrowed.
  ⟨"enum Shape { Circle(Int), Rect(Int, Int) }\nfn grow(s: &mut Shape) { match(s) { &mut Circle(r) => *r = *r + 1, &mut Rect(w, h) => *w = *w * 2; *h = *h + 100 } }\nfn main() { let mut a = Circle(1); let mut b = Rect(2, 3); grow(&mut a); grow(&mut b); (a, b) }",
    [], "(Circle(2), Rect(4, 103))"⟩,
  ⟨"enum Shape { Circle(Int), Rect(Int, Int) }\nfn area(s: &Shape) -> Int { match(s) { &Circle(r) => 3 * *r * *r, &Rect(w, h) => *w * *h } }\nfn main() { let mut b = Rect(2, 3); let n = area(&b); n + area(&b) }",
    [], "12"⟩,
  ⟨"fn bump { &mut Some(n) => *n = *n + 1, &mut None => () }\nfn main() { let mut x = Some(4); bump(&mut x); bump(&mut x); x }",
    [], "Ok(6)"⟩,
  ⟨"enum Tree { Leaf(Int), Node(Tree, Tree) }\nfn left(t: &mut Tree) { match(t) { &mut Node(Leaf(n), _) => *n = 0, &mut _ => () } }\nfn main() { let mut t = Node(Leaf(5), Leaf(6)); left(&mut t); t }",
    [], "Node(Leaf(0), Leaf(6))"⟩,
  ⟨"fn swap(p: &mut (Int, Int)) { match(p) { &mut (a, b) => let t = *a; *a = *b; *b = t } }\nfn main() { let mut p = (1, 2); swap(&mut p); p }",
    [], "(2, 1)"⟩,
  ⟨"enum Shape { Circle(Int), Rect(Int, Int) }\nfn bad(s: &mut Shape) { match(s) { &mut Circle(r) => *r = 1, Rect(w, h) => () } }\nfn main() { 0 }",
    [], "error: 2:25: in `bad`: where one clause binds a parameter by reference, `&mut Pattern`, every clause does, or takes the reference whole"⟩,
  ⟨"fn main() { let &mut (a, b) = (1, 2); 0 }",
    [], "error: 1:13: in `main`: what a field is borrowed of here is a value that nothing holds, not a reference: give it a `let mut` first"⟩,
  ⟨"fn whole(s: &mut Int) { match(s) { &mut n => *n = *n + 1 } }\nfn main() { let mut x = 1; whole(&mut x); x }",
    [], "2"⟩,
  ⟨"enum Shape { Circle(Int), Rect(Int, Int) }\nfn f(s: &mut Shape) -> Int { match(s) { &mut Circle(r) => *r, &mut Rect(w, h) => let big = if(*w < *h) { h } else { w }; *big = 0; 1 } }\nfn main() { let mut b = Rect(2, 3); f(&mut b); b }",
    [], "Rect(2, 0)"⟩,
  ⟨"struct Acc { total: Int, count: Int }\nenum Cmd { Add(Int), Reset }\nfn run(a: &mut Acc, c: &Cmd) { match(c) { &Add(n) => a.total = a.total + *n; a.count = a.count + 1, &Reset => a.total = 0 } }\nfn main() { let mut a = Acc { total: 0, count: 0 }; let mut c = Add(5); run(&mut a, &c); run(&mut a, &c); c = Reset; run(&mut a, &c); (a.total, a.count) }",
    [], "(0, 2)"⟩,
  -- Borrows of fields made one after another may be done with in any order.
  ⟨"fn main() { let mut x = (1, 2, 3); let a = &mut x.0; let b = &mut x.1; let c = &mut x.2; *b = 5; *a = 4; *c = 6; x }",
    [], "(4, 5, 6)"⟩,
    -- Comments in `/* */`, which may hold others; `-` before any value; a
  -- byte; a field by number of what a reference points to.
  ⟨"/* a comment /* inside another */ still */ fn main() { let x = 5; /* here */ -x + - (2 * 3) - -1 }",
    [], "-10"⟩,
  ⟨"fn main() { say(-1.5); say(- (0.0)); say(-(3i8)); say(b'a'); say(b'\\n'); let n = 4; -n * 2 }",
    [], "-1.5\n-0.0\n-3\n97\n10\n-8"⟩,
  ⟨"fn first(p: &(Int, Int)) -> Int { p.0 + p.1 }\nfn main() { let mut x = (3, 4); first(&x) }",
    [], "7"⟩,
  ⟨"struct P(Int, (Int, Int))\nfn f(p: &mut P) -> Int { p.1.0 = 9; p.0 + p.1.0 + p.1.1 }\nfn main() { let mut x = P(1, (2, 3)); f(&mut x) }",
    [], "13"⟩,
  ⟨"fn main() { let t = ((1, 2), 3); t.0.1 + t.1 }",
    [], "5"⟩,
  ⟨"fn main() { -5u8 }",
    [], "error: 1:14: `-5` does not fit in `u8`, found `5u8`"⟩,
  ⟨"fn main() { /* open",
    [], "error: 1:13: this comment is not closed"⟩,
  -- Integers of 64 bits without a sign and of 128 bits, with and without.
  ⟨"fn main() { say(18446744073709551615u64); say(18446744073709551615u64 - 1u64); say(170141183460469231731687303715884105727i128); say(-170141183460469231731687303715884105728i128); say(340282366920938463463374607431768211455u128); say(340282366920938463463374607431768211455u128 / 3u128); say(u64(5) * 1000000000000u64); 0 }",
    [], "18446744073709551615\n18446744073709551614\n170141183460469231731687303715884105727\n-170141183460469231731687303715884105728\n340282366920938463463374607431768211455\n113427455640312821154458202477256070485\n5000000000000\n0"⟩,
  ⟨"fn main() { 18446744073709551615u64 + 1u64 }",
    [], "went wrong"⟩,
  ⟨"fn main() { 340282366920938463463374607431768211455u128 + 1u128 }",
    [], "went wrong"⟩,
  ⟨"fn main() { say(0u128 < 340282366920938463463374607431768211455u128); 0 }",
    [], "Ok(())\n0"⟩,
  -- The bits of whole numbers; square root and rounding.
  ⟨"fn main() { say(bit_and(12, 10)); say(bit_or(12, 10)); say(bit_xor(-1, 5)); say(shl(1, 62)); say(shr(-9, 1)); say(shl(1u8, 7)); say(bit_xor(255u8, 15u8)); say(shr(340282366920938463463374607431768211455u128, 127)); say(shl(3u128, 126)); 0 }",
    [], "8\n14\n-6\n4611686018427387904\n-5\n128\n240\n1\n255211775190703847597530955573826158592\n0"⟩,
  ⟨"fn main() { shl(1, 63) }",
    [], "went wrong"⟩,
  ⟨"fn main() { say(sqrt(2.0)); say(sqrt(16.0)); say(floor(-2.5)); say(ceil(-2.5)); say(trunc(-2.5)); say(round(2.5)); say(round(3.5)); say(abs(-1.25)); say(sqrt(2.0f32)); say(sqrt(-1.0)); say(1e30 * 1e30 * 1e30 * 1e300); int(9223372036854775807i128) + int(0u64) }",
    [], "1.4142135623730951\n4.0\n-3.0\n-2.0\n-2.0\n2.0\n4.0\n1.25\n1.4142135\nNaN\ninf\n9223372036854775807"⟩,
  ⟨"fn main() { say(usize(18446744073709551) * 1000usize); say(-9223372036854775808 / 1); (0 - 9223372036854775807 - 1) / -1 }",
    [], "went wrong"⟩,
  -- A whole number written without a type is of the type wanted of it
  -- where it is written, if that is a type of whole numbers.
  ⟨"fn inc(a: u8) -> u8 { a + 1 }\nfn dec(a: u8) -> u8 { 1 + a - 2 }\nfn zero() -> i128 { 0 }\nfn main() { say(inc(41)); say(dec(5u8)); say(zero()); let mut x = 7u16; x = 9; int(x) }",
    [], "42\n4\n0\n9"⟩,
  ⟨"fn inc(a: u8) -> u8 { a + 300 }\nfn main() { 0 }",
    [], "error: 1:23: in `inc`: argument 2 of `+`: `300` does not fit in `u8`"⟩,
  ⟨"fn half(x: f64) -> f64 { x / 2 }\nfn main() { 0 }",
    [], "error: 1:26: in `half`: argument 2 of `/`: expected `f64`, found `Int`"⟩,
  ⟨"fn kind(a: u8) -> Int { match(a) { 0 => 10, 255 => 20, _ => 30 } }\nfn main() { kind(0) + kind(255u8) + kind(7) }",
    [], "60"⟩,
  ⟨"fn kind(a: u8) -> Int { match(a) { 256 => 10, _ => 30 } }\nfn main() { 0 }",
    [], "error: 1:25: in `kind`: `256` does not fit in `u8`"⟩,
  ⟨"struct Rgb(u8, u8, u8)\nfn main() { match(Rgb(255, 128, 0)) { Rgb(r, g, b) => int(r) + int(g) + int(b) } }",
    [], "383"⟩,
  -- Tuples and `Result` have `Show` if their parts do.
  ⟨"fn pair() -> Result<Int, Str> { Ok(3) }\nfn main() { say((1, 2.5)); say(((), 'x', \"s\")); say(pair()); say(1 < 2); say(()); 0 }",
    [], "(1, 2.5)\n((), x, s)\nOk(3)\nOk(())\n()\n0"⟩,
  ⟨"struct P(Int)\nfn main() { say((1, P(2))); 0 }",
    [], "error: 2:13: in `main`: `P` does not implement `Show`"⟩,
  -- A trait can give a function a body, and can need another trait; what is
  -- written of a type parameter is then all it has.
  ⟨"trait Shape { fn area(Self) -> Int  fn double(s: Self) -> Int { area(s) * 2 } }\nstruct Sq(Int)\nstruct Circle(Int)\nimpl Shape for Sq { fn area(Sq(n)) { n * n } }\nimpl Shape for Circle { fn area(Circle(r)) { 3 * r * r }  fn double(c) { 0 } }\nfn main() { double(Sq(3)) + double(Circle(1)) + area(Circle(1)) }",
    [], "21"⟩,
  ⟨"trait Named { fn name(Self) -> Int }\ntrait Pet: Named { fn legs(Self) -> Int }\nstruct Dog(Int)\nimpl Named for Dog { fn name(Dog(n)) { n } }\nimpl Pet for Dog { fn legs(d) { 4 } }\nfn describe<T>(p: T) -> Int where T: Pet { name(p) * 10 + 4 }\nfn main() { describe(Dog(7)) }",
    [], "74"⟩,
  ⟨"trait Named { fn name(Self) -> Int }\ntrait Pet: Named { fn legs(Self) -> Int }\nstruct Dog(Int)\nimpl Pet for Dog { fn legs(d) { 4 } }\nfn main() { 0 }",
    [], "error: `impl Pet for Dog`: a type that has `Pet` has `Named`, and there is no `impl Named for Dog`"⟩,
  ⟨"trait Named { fn name(Self) -> Int }\ntrait Pet { fn legs(Self) -> Int }\nfn describe<T>(p: T) -> Int where T: Pet { name(p) }\nfn main() { 0 }",
    [], "error: in `describe`: `T` is not said to have `Named`: write `T: Named`"⟩,
  ⟨"trait Named { fn name(Self) -> Int }\nimpl Named for Int { fn name(n) { n } }\nfn f<T: Named>(x: T) -> Int { name(x) }\nfn g<T>(x: T) -> Int { name(x) }\nfn main() { f(1) + g(2) }",
    [], "3"⟩,
  ⟨"trait A: B { fn a(Self) -> Int }\ntrait B: A { fn b(Self) -> Int }\nfn main() { 0 }",
    [], "error: trait `B` would need a type to have `B` to have it, through `A`"⟩,
  ⟨"trait Named { fn name(Self) -> Int }\ntrait Pet: Named { fn legs(Self) -> Int }\nstruct Box<T>(T)\nimpl<T> Named for Box<T> where T: Named { fn name(b) { match(b) { Box(x) => name(x) } } }\nimpl<T> Pet for Box<T> where T: Pet { fn legs(b) { match(b) { Box(x) => legs(x) + name(x) } } }\nimpl Named for Int { fn name(n) { n } }\nimpl Pet for Int { fn legs(n) { 2 } }\nfn main() { legs(Box(5)) + name(Box(1)) }",
    [], "8"⟩,
  -- `let x: Type = value`.
  ⟨"fn main() { let x: u8 = 200; let y: (Int, f64) = (1, 2.5); let z: Option<Int> = None; say(x); say(y); match(z) { Some(n) => n, None => int(x) } }",
    [], "200\n(1, 2.5)\n200"⟩,
  ⟨"fn main() { let x: u8 = 300; 0 }",
    [], "error: 1:13: in `main`: `300` does not fit in `u8`"⟩,
  ⟨"fn main() { let x: f64 = (1, 2); 0 }",
    [], "error: 1:13: in `main`: the value of a `let` with a type: expected `f64`, found `(Int, Int)`"⟩,
  ⟨"fn f<T>(v: T) -> T { let w: T = v; w }\nfn main() { let mut n: i16 = 5; n = n + 1; int(f(n)) }",
    [], "6"⟩,
  ⟨"mod m { pub struct P(pub Int) }\nfn main() { let p: m::P = m::P(4); p.0 }",
    [], "4"⟩,
  -- A trait can take types: an implementation is of the trait at those.
  ⟨"trait From<T> { fn from(T) -> Self }\nimpl From<Int> for u8 { fn from(n) { u8(n) } }\nimpl From<u8> for Int { fn from(b) { int(b) } }\nimpl From<Int> for f64 { fn from(n) { f64(n) } }\nfn main() { let a: u8 = from(200); let b: f64 = from(3); let c: Int = from(a); say(a); say(b); c }",
    [], "200\n3.0\n200"⟩,
  ⟨"trait From<T> { fn from(T) -> Self }\nimpl From<Int> for u8 { fn from(n) { u8(n) } }\nfn main() { let a: u8 = from(2.5); 0 }",
    [], "error: 3:13: in `main`: `u8` does not implement `From<f64>`"⟩,
  ⟨"trait From<T> { fn from(T) -> Self }\nimpl From<Int> for u8 { fn from(n) { u8(n) } }\nimpl From<Int> for i16 { fn from(n) { i16(n) } }\nfn conv<T, U>(x: T) -> U where U: From<T> { from(x) }\nfn main() { let a: u8 = conv(7); let b: i16 = conv(-7); int(a) + int(b) }",
    [], "0"⟩,
  ⟨"trait From<T> { fn from(T) -> Self }\nimpl From<Int> for u8 { fn from(n) { u8(n) } }\nfn conv(x) { from(x) }\nfn main() { let a: u8 = conv(9); int(a) }",
    [], "9"⟩,
  ⟨"trait From<T> { fn from(T) -> Self }\nimpl From<Int> for u8 { fn from(n) { u8(n) } }\nimpl From<Int> for u8 { fn from(n) { u8(n) } }\nfn main() { 0 }",
    [], "error: `From<Int>` is implemented twice for `u8`"⟩,
  ⟨"trait From<T> { fn from(T) -> Self }\nimpl From for u8 { fn from(n) { u8(n) } }\nfn main() { 0 }",
    [], "error: `impl From for u8`: `From` takes 1 type arguments"⟩,
  -- A trait can leave a type to its implementations.
  ⟨"trait Container { type Item; fn first(Self) -> Item }\nstruct Ints(Int, Int)\nstruct Flags(Bool)\nimpl Container for Ints { type Item = Int; fn first(c) { c.0 } }\nimpl Container for Flags { type Item = Bool; fn first(c) { c.0 } }\nfn main() { let n = first(Ints(4, 5)) + 1; if(first(Flags(1 < 2))) { n } else { 0 } }",
    [], "5"⟩,
  ⟨"trait Container { type Item; fn first(Self) -> Item }\nstruct Ints(Int, Int)\nimpl Container for Ints { type Item = Int; fn first(c) { c.0 } }\nfn head<C>(c: C) -> C::Item where C: Container { first(c) }\nfn main() { head(Ints(7, 8)) + 1 }",
    [], "8"⟩,
  ⟨"trait Container { type Item; fn first(Self) -> Item }\nstruct Wrap<T>(T)\nimpl<T> Container for Wrap<T> { type Item = T; fn first(w) { match(w) { Wrap(x) => x } } }\nfn twice(c) { let a = first(c); a }\nfn main() { twice(Wrap(21)) * 2 }",
    [], "42"⟩,
  ⟨"trait Container { type Item; fn first(Self) -> Item }\nstruct Ints(Int, Int)\nimpl Container for Ints { fn first(c) { c.0 } }\nfn main() { 0 }",
    [], "error: `impl Container for Ints` does not say what `Item` is: write `type Item = ..;`"⟩,
  ⟨"trait Container { type Item; fn first(Self) -> Item }\nstruct Ints(Int, Int)\nimpl Container for Ints { type Item = Int; fn first(c) { c.0 } }\nfn main() { say(first(Ints(1, 2)) + 1.5); 0 }",
    [], "error: 4:13: in `main`: `Item` of `Container` for `Ints`: expected `Int`, found `f64`"⟩,
  ⟨"trait Iter { type Item; fn next(&mut Self) -> Option<Item> }\nstruct Count(Int)\nimpl Iter for Count { type Item = Int; fn next(c) { let n = (*c).0; match(n < 3) { Ok(_) => (*c).0 = n + 1; Some(n), Err(_) => None } } }\nfn sum<I>(it: &mut I) -> Int where I: Iter { match(next(it)) { Some(n) => n + sum(it), None => 0 } }\nfn main() { let mut c = Count(0); sum(&mut c) }",
    [], "3"⟩,
  ⟨"trait Iter { type Item; fn next(&mut Self) -> Option<Item> }\nstruct Count(Int)\nimpl Iter for Count { type Item = Int; fn next(c) { let n = (*c).0; match(n < 3) { Ok(_) => (*c).0 = n + 1; Some(n), Err(_) => None } } }\nfn total<I>(it: &mut I, acc: I::Item) -> I::Item where I: Iter { match(next(it)) { Some(n) => total(it, acc + n), None => acc } }\nfn main() { let mut c = Count(0); total(&mut c, 10) }",
    [], "13"⟩,
  ⟨"trait Iter { type Item; fn next(&mut Self) -> Option<Item> }\nstruct Count(Int)\nimpl Iter for Count { type Item = Int; fn next(c) { let n = (*c).0; match(n < 3) { Ok(_) => (*c).0 = n + 1; Some(n), Err(_) => None } } }\nfn total(it, acc) { match(next(it)) { Some(n) => total(it, acc + n), None => acc } }\nfn main() { let mut c = Count(0); total(&mut c, 10) }",
    [], "13"⟩,
  ⟨"trait Iter { type Item; fn next(&mut Self) -> Option<Item> }\nstruct Count(Int)\nimpl Iter for Count { type Item = Int; fn next(c) { let n = (*c).0; match(n < 3) { Ok(_) => (*c).0 = n + 1; Some(n), Err(_) => None } } }\nstruct Pairs(Int)\nimpl Iter for Pairs { type Item = (Int, Int); fn next(p) { let n = (*p).0; match(n < 2) { Ok(_) => (*p).0 = n + 1; Some((n, n * n)), Err(_) => None } } }\nfn count<I>(it: &mut I) -> Int where I: Iter { match(next(it)) { Some(_) => 1 + count(it), None => 0 } }\nfn main() { let mut c = Count(0); let mut p = Pairs(0); count(&mut c) * 10 + count(&mut p) }",
    [], "32"⟩,
  -- Whole numbers of one type as another; a trait's lifetime.
  ⟨"fn main() { let a: u8 = to(200u16); let b: i128 = to(a); let c: u64 = to(b + 1i128); let d: char = to(97); say(a); say(b); say(c); say(d); 0 }",
    [], "200\n200\n201\na\n0"⟩,
  ⟨"trait Borrowed<'a> { fn get(&'a Self) -> &'a Self }\nstruct W(Int)\nimpl Borrowed<'a> for W { fn get(w) { w } }\nfn main() { let mut w = W(5); (*get(&w)).0 }",
    [], "5"⟩,
  ⟨"struct Meters(Int)\nstruct Feet(Int)\nimpl From<Meters> for Feet { fn from(Meters(m)) { Feet(m * 3) } }\nfn main() { let f: Feet = from(Meters(2)); f.0 }",
    [], "6"⟩,
  ⟨"fn main() { let e: u8 = to(300); 0 }",
    [], "went wrong"⟩,
  -- A borrow of a field through a reference does not leave the function
  -- that makes it.
  ⟨"struct W(Int)\nfn get(w: &W) -> &Int { &(*w).0 }\nfn main() { let mut w = W(5); *get(&w) }",
    [], "error: 2:25: in `get`: a borrow of a field of what a reference points to lasts only inside the function that makes it, and here it is given back or kept: give back the reference itself, or the field's value"⟩,
  -- Arrays: `[a, b]`, `[x; n]`, `a[i]`, `a[i] = v`, `[T]`. An array is a
  -- value; a place that is not there stops the program.
  ⟨"fn main() { let a = [10, 20, 30]; say(a); say(len(a)); say(a[1]); let b = push(a, 40); say(b); say(a); say([1.5; 3]); say(b\"hi\"); a[0] + b[3] }",
    [], "[10, 20, 30]\n3\n20\n[10, 20, 30, 40]\n[10, 20, 30]\n[1.5, 1.5, 1.5]\n[104, 105]\n50"⟩,
  ⟨"fn main() { let mut a = [1, 2, 3]; a[1] = 20; a[2] = a[1] + a[0]; say(a); let mut grid = [[0; 2]; 2]; grid[1][0] = 7; say(grid); grid[1][0] }",
    [], "[1, 20, 21]\n[[0, 0], [7, 0]]\n7"⟩,
  ⟨"fn main() { let a = [1, 2, 3]; a[3] }",
    [], "went wrong"⟩,
  ⟨"fn sum(a: [Int]) -> Int { fold(a, 0, fn(acc, x) { acc + x }) }\nfn main() { let mut a: [Int] = []; a = push(a, 4); a = push(a, 5); say(get(a, 1)); say(get(a, 2)); match(pop(a)) { Some((rest, last)) => sum(rest) * 10 + last, None => 0 } }",
    [], "Ok(5)\nErr(())\n45"⟩,
  ⟨"fn fill(n, a) { if(n == 0) { a } else { fill(n - 1, push(a, n * n)) } }\nfn main() { let a = fill(100, []); each([1, 2], { x => print(x) }); a[0] + a[99] + len(a) }",
    [], "1\n2\n10101"⟩,
  ⟨"struct P { xs: [Int], n: Int }\nfn main() { let mut p = P { xs: [1, 2], n: 0 }; p.xs[1] = 9; p.xs[0] + p.xs[1] }",
    [], "10"⟩,
  ⟨"fn main() { let s = \"héllo\"; len(s) + len([s, s]) }",
    [], "7"⟩,
  ⟨"fn main() { let a = [1, 2, 3, 4, 5]; say(slice(a, 1, 4)); let cs = chars(\"hello\"); say(cs[1]); let mut up = cs; up[0] = 'J'; say(text(up)); say(text(slice(up, 1, 3))); len(cs) }",
    [], "[2, 3, 4]\ne\nJello\nel\n5"⟩,
  ⟨"fn main() { let a: [Int; 3] = [1, 2, 3]; 0 }",
    [], "error: 1:24: an array's type does not say how long it is: write `[T]`, found `;`"⟩,
  -- A pattern that binds by reference may give fields by name, be beside a
  -- clause that takes the reference whole, and be in a `let`.
  ⟨"enum Shape { Circle(Int), Rect { w: Int, h: Int } }\nfn grow(s: &mut Shape) { match(s) { &mut Rect { w, .. } => *w = *w * 2, _ => () } }\nfn main() { let mut a = Circle(1); let mut b = Rect { w: 2, h: 3 }; grow(&mut a); grow(&mut b); (a, b) }",
    [], "(Circle(1), Rect(4, 3))"⟩,
  ⟨"fn swap(p: &mut (Int, Int)) { let &mut (a, b) = p; let t = *a; *a = *b; *b = t }\nfn main() { let mut p = (1, 2); swap(&mut p); p }",
    [], "(2, 1)"⟩,
  ⟨"fn first(p: &(Int, Int)) -> Int { let &(a, _) = p; *a }\nfn main() { let mut p = (4, 5); first(&p) }",
    [], "4"⟩,
  ⟨"fn f(s: &mut Option<Int>) -> Int { match(s) { &mut Some(n) => *n = *n + 1; 1, r => 0 } }\nfn main() { let mut x = Some(1); let mut y = None; f(&mut x) + f(&mut y) + (x else { 0 }) }",
    [], "3"⟩,
  -- A borrow of a field is kept until one made while it lasts is done with,
  -- if nothing between looks at the variable itself.
  ⟨"fn main() { let mut x = (1, 2); let a = &mut x.0; print(7); let b = &mut x.1; *a = 5; *b = 6; x }",
    [], "7\n(5, 6)"⟩,
  ⟨"fn main() { let mut x = (1, 2); let a = &mut x.0; print(7); let b = &mut x.1; *a = 5; print(x.0); *b = 6; x }",
    [], "error: in `main`: the borrow of a field kept in `b` is made while another lasts and is used after that one is done with: make it before the other, or straight after it"⟩,
  -- `After = E2`: an environment a callable leaves, in which another runs
  -- only once it has. `Label<T>`: a label that takes a `T`.
  ⟨"fn seq<'e, E, E2, A, B>(a: A, b: B) -> Int where E: Environment<'e>, E2: Environment<'e>, A: RunsIn<E, (), Output = Int, After = E2>, B: RunsIn<E2, (), Output = Int> { let x = a(); x + b() }\nfn main() { let mut n = 1; seq({ n = n + 1; n }, { n * 10 }) }",
    [], "22"⟩,
  ⟨"fn seq<'e, E, E2, A, B>(a: A, b: B) -> Int where E: Environment<'e>, E2: Environment<'e>, A: RunsIn<E, (), Output = Int, After = E2>, B: RunsIn<E2, (), Output = Int> { let y = b(); y + a() }\nfn main() { 0 }",
    [], "error: in `seq`: `b` runs in the environment `E2`, which is there only once `a` has run: on some path it is called first"⟩,
  ⟨"fn seq<'e, E, E2, A, B>(c: Bool, a: A, b: B) -> Int where E: Environment<'e>, E2: Environment<'e>, A: RunsIn<E, (), Output = Int, After = E2>, B: RunsIn<E2, (), Output = Int> { match(c) { Ok(_) => a() + b(), Err(_) => b() } }\nfn main() { 0 }",
    [], "error: in `seq`: `b` runs in the environment `E2`, which is there only once `a` has run: on some path it is called first"⟩,
  ⟨"fn seq<'e, E, E2, A, B>(a: A, b: B) -> Int where E: Environment<'e>, E2: Environment<'e>, A: RunsIn<E, (), Output = Int, After = E2>, B: RunsIn<E2, (), Output = Int> { a() + b() + b() }\nfn main() { 0 }",
    [], "error: in `seq`: `b` run in the environment `E2`, which is used up by the first that is called: on some path more than one call is made"⟩,
  ⟨"fn jump<L>(out: L) -> Int where L: Label<Int> { out(5); 0 }\nfn main() { @done { jump(@done) + 1 } }",
    [], "5"⟩,
  -- A value is destroyed part by part: `Drop`'s function for its type first,
  -- then its fields, the last declared first, whatever holds them.
  ⟨"struct File(Int)\nimpl Drop for File { fn drop(f) { let File(n) = *f; print(n) } }\nstruct Pair(File, File)\nfn main() { let p = Pair(File(1), File(2)); let q = (File(3), 4, Some(File(5))); 0 }",
    [], "5\n3\n2\n1\n0"⟩,
  ⟨"struct File(Int)\nimpl Drop for File { fn drop(f) { let File(n) = *f; print(n) } }\nenum List { Nil, Cons(File, List) }\nfn main() { let mut l = Cons(File(1), Cons(File(2), Nil)); l = Nil; print(9); let m = Cons(File(7), Nil); 0 }",
    [], "2\n1\n9\n7\n0"⟩,
  ⟨"struct File(Int)\nimpl Drop for File { fn drop(f) { let File(n) = *f; print(n) } }\nstruct Dir(Int, File)\nimpl Drop for Dir { fn drop(d) { print((*d).0) } }\nfn main() { let d = Dir(10, File(11)); let e = [File(20), File(21)]; 0 }",
    [], "21\n20\n10\n11\n0"⟩,
  ⟨"struct T(Int)\nimpl Use<[1, 1]> for T {}\nimpl Drop for T { fn drop(t) { () } }\nfn main() { let T(n) = T(1); n }",
    [], "error: `impl Drop for T`: a `T` has to be used, so one is never destroyed, and `drop` would never run"⟩,
  ⟨"mod fs { pub struct File(pub Int) impl Drop for File { fn drop(f) { print((*f).0) } } pub fn open(n: Int) -> File { File(n) } pub fn close(f: File) -> Int { let File(n) = f; n } }\nuse fs::{File, open, close};\nfn main() { let f = open(3); let File(n) = open(4); n }",
    [], "error: 3:30: in `main`: `File` has `Drop`, so only the module that declares it can take one apart with a pattern: what `drop` does would not be done"⟩,
  ⟨"mod fs { pub struct File(pub Int) impl Drop for File { fn drop(f) { print((*f).0) } } pub fn open(n: Int) -> File { File(n) } pub fn close(f: File) -> Int { let File(n) = f; n } }\nuse fs::{File, open, close};\nfn main() { let f = open(3); let g = open(4); close(open(5)) }",
    [], "4\n3\n5"⟩,
  -- A module that is not `pub` is named only by the module it is written in.
  -- A `pub` function's type has no private type in it. A fixity and a
  -- coercion are their module's, and come with the function by `use`.
  ⟨"mod a { mod b { pub fn f() -> Int { 1 } } pub fn g() -> Int { b::f() } }\nfn main() { a::b::f() + a::g() }",
    [], "error: 2:13: in `main`: the first module cannot name module `a::b`, which is private to module `a`: only a `pub mod` can be named from outside the module it is written in"⟩,
  ⟨"mod a { pub mod b { pub fn f() -> Int { 1 } } }\nfn main() { a::b::f() }",
    [], "1"⟩,
  ⟨"mod a { struct S(Int) pub fn mk() -> S { S(1) } pub fn un(s: S) -> Int { s.0 } }\nfn main() { a::un(a::mk()) }",
    [], "error: `mk` is `pub`, but its type, `fn() -> a::S`, has `S` in it, which is private to its module: one who calls `mk` could not write that type (`pub struct` with fields that are not `pub` keeps what is inside private)"⟩,
  ⟨"mod a { pub struct W(pub Int) pub fn w(n: Int) -> W { W(n) } coerce w; pub fn take(x: W) -> Int { x.0 } pub fn inside() -> Int { take(3) } }\nfn main() { a::inside() + a::take(4) }",
    [], "error: 2:13: in `main`: argument 1 of `a::take`: expected `a::W`, found `Int`"⟩,
  ⟨"pub mod a { pub struct W(pub Int) pub fn w(n: Int) -> W { W(n) } coerce w; pub fn take(x: W) -> Int { x.0 } pub fn inside() -> Int { take(3) } }\nuse a::w;\nfn main() { a::inside() + a::take(4) }",
    [], "7"⟩,
  ⟨"mod a { infixl 6 +++ = cat pub fn cat(x: Int, y: Int) -> Int { x * 10 + y } pub fn f() -> Int { 1 +++ 2 } }\nuse a::cat;\nfn main() { a::f() + (3 +++ 4) }",
    [], "46"⟩,
  ⟨"mod a { pub enum E { X, Y } pub fn pick(e: E) -> Int { match(e) { X => 1, Y => 2 } } }\nmod c { use a::E; pub fn go() -> Int { a::pick(E::Y) } }\nfn main() { c::go() }",
    [], "error: 3:13: in `main`: module `c` cannot name module `a`, which is private to the first module: only a `pub mod` can be named from outside the module it is written in"⟩,
  ⟨"mod a { infixl 6 +++ = cat pub fn cat(x: Int, y: Int) -> Int { x * 10 + y } }\nfn main() { 3 +++ 4 }",
    [], "error: 2:15: operator `+++` has no infix fixity in this module (a fixity is its module's: `use` the function the operator stands for), found `+++`"⟩,
  ⟨"pub mod ops { infixl 6 +++ pub fn +++(x: Int, y: Int) -> Int { x * 10 + y } }\npub mod a { use crate::ops::+++; pub fn f() -> Int { 1 +++ 2 } }\nuse ops::*;\nfn main() { a::f() + (2 +++ 1) }",
    [], "33"⟩,
  ⟨"pub mod ops { infixl 6 +++ pub fn +++(x: Int, y: Int) -> Int { x * 10 + y } }\npub mod a { pub fn f() -> Int { 1 +++ 2 } }\nfn main() { a::f() }",
    [], "error: 2:35: operator `+++` has no infix fixity in this module (a fixity is its module's: `use` the function the operator stands for), found `+++`"⟩,
  ⟨"pub mod ops { infixl 6 <> = cat pub fn cat(x: Int, y: Int) -> Int { x * 10 + y } }\npub mod other { infixl 2 <> = sub pub fn sub(x: Int, y: Int) -> Int { x - y } }\nuse ops::cat;\nuse other::sub;\nfn main() { 1 <> 2 }",
    [], "error: the operator `<>` is brought in with one fixity where it already has another"⟩,
  -- The standard library, `std`, written in the language: a program that
  -- names it has it.
  ⟨"use std::result::{map, map_err, and_then, ok, err, is_err};\nfn half(n: Int) -> Result<Int, Str> { if(n % 2 == 0) { Ok(n / 2) } else { Err(\"odd\") } }\nfn main() { say(map(half(4), { x => x + 1 })); say(map_err(half(3), { e => length(e) })); say(and_then(half(8), half)); say(ok(half(3))); say(err(half(3))); is_err(half(1)) }",
    [], "Ok(3)\nErr(3)\nOk(2)\nErr(())\nOk(odd)\nOk(())"⟩,
  ⟨"fn main() { 1 }",
    [], "1"⟩,
  ⟨"use std::cmp::{compare, min, max, clamp, reverse, Ordering};\nfn show_o(o: Ordering) -> Int { match(o) { Ordering::Less => 0 - 1, Ordering::Equal => 0, Ordering::Greater => 1 } }\nfn main() { say(show_o(compare(1, 2))); say(show_o(reverse(compare('a', 'b')))); say(min(3, 2)); say(max(1.5, 2.5)); clamp(15, 0, 10) }",
    [], "-1\n1\n2\n2.5\n10"⟩,
  ⟨"use std::int::{abs, signum, pow, gcd, lcm, div_floor, mod_floor, digits, sqrt, is_even};\nfn main() { say(abs(0 - 5)); say(signum(0 - 3)); say(pow(2, 10)); say(gcd(12, 18)); say(lcm(4, 6)); say(div_floor(0 - 7, 2)); say(mod_floor(0 - 7, 2)); say(digits(1203)); say(sqrt(99)); is_even(4) }",
    [], "5\n-1\n1024\n6\n12\n-4\n1\n[1, 2, 0, 3]\n9\nOk(())"⟩,
  ⟨"use std::char::{is_digit, is_alpha, is_space, digit, of_digit, to_upper, to_lower, code};\nfn main() { say(is_digit('7')); say(is_alpha('_')); say(is_space(' ')); say(digit('8')); say(of_digit(3)); say(to_upper('q')); say(to_lower('Q')); code('A') }",
    [], "Ok(())\nErr(())\nOk(())\nOk(8)\nOk(3)\nQ\nq\n65"⟩,
  ⟨"use std::vec::*;\nfn main() { let a = [5, 3, 9, 1, 3]; say(sort(a)); say(map(a, { x => x * 2 })); say(filter(a, { x => x > 3 })); say(reverse(a)); say(range(2, 6)); say(sum(a)); say(maximum(a)); say(zip(a, [true, false])); say(enumerate([7, 8])); say(binary_search(sort(a), 5)); say(binary_search(sort(a), 4)); say(dedup(sort(a))); say(take(a, 2)); say(drop(a, 3)); say(contains(a, 9)); say(position(a, { x => x == 9 })); say(concat([[1], [2, 3], []])); say(swap(a, 0, 4)); say(sort_by([\"pear\", \"fig\", \"apple\"], fn(x, y) { length(x) < length(y) })); count(a, { x => x == 3 }) }",
    [], "[1, 3, 3, 5, 9]\n[10, 6, 18, 2, 6]\n[5, 9]\n[3, 1, 9, 3, 5]\n[2, 3, 4, 5]\n21\nOk(9)\n[(5, Ok(())), (3, Err(()))]\n[(0, 7), (1, 8)]\nOk(3)\nErr(3)\n[1, 3, 5, 9]\n[5, 3]\n[1, 3]\nOk(())\nOk(2)\n[1, 2, 3]\n[3, 3, 9, 1, 5]\n[fig, pear, apple]\n2"⟩,
  ⟨"use std::text::*;\nfn main() { say(reverse(\"hello\")); say(starts_with(\"hello\", \"he\")); say(ends_with(\"hello\", \"lo\")); say(find(\"hello\", \"ll\")); say(to_upper(\"Hello, World\")); say(trim(\"  hi there \\n\")); say(split(\"a,b,,c\", ',')); say(words(\" the quick  fox \")); say(join([\"a\", \"b\", \"c\"], \"-\")); say(repeat(\"ab\", 3)); say(parse_int(\"-120\")); say(parse_int(\"12x\")); say(pad_start(\"7\", 3, '0')); say(pad_end(\"7\", 3, '.')); say(take(\"hello\", 2)); say(drop(\"hello\", 2)); say(char_at(\"hey\", 1)); contains(\"hello\", \"xyz\") }",
    [], "olleh\nOk(())\nOk(())\nOk(2)\nHELLO, WORLD\nhi there\n[a, b, , c]\n[the, quick, fox]\na-b-c\nababab\nOk(-120)\nErr(())\n007\n7..\nhe\nllo\nOk(e)\nErr(())"⟩,
  ⟨"use std::map;\nfn main() { let m = map::from([(3, \"three\"), (1, \"one\"), (2, \"two\")]); say(map::get(m, 2)); say(map::get(m, 5)); say(map::keys(m)); say(map::values(map::insert(m, 1, \"uno\"))); say(map::len(m)); say(map::entries(map::remove(m, 2))); say(map::contains_key(m, 3)); let big = fold(std::vec::range(0, 40), map::new(), fn(acc, i) { map::insert(acc, (i * 7) % 40, i) }); say(map::len(big)); say(map::least(big)); say(map::greatest(big)); let counts = fold(chars(\"mississippi\"), map::new(), fn(acc, c) { map::update(acc, c, { old => (old else { 0 }) + 1 }) }); say(map::entries(counts)); map::len(map::remove(big, 7)) }",
    [], "Ok(two)\nErr(())\n[1, 2, 3]\n[uno, two, three]\n3\n[(1, one), (3, three)]\nOk(())\n40\nOk((0, 0))\nOk((39, 17))\n[(i, 4), (m, 1), (p, 2), (s, 4)]\n39"⟩,
  ⟨"use std::set;\nfn main() { let a = set::from([3, 1, 2, 3]); let b = set::from([2, 3, 4]); say(set::to_array(a)); say(set::to_array(set::union(a, b))); say(set::to_array(set::intersection(a, b))); say(set::to_array(set::difference(a, b))); say(set::contains(a, 2)); say(set::is_subset(set::from([1, 2]), a)); set::len(a) }",
    [], "[1, 2, 3]\n[1, 2, 3, 4]\n[2, 3]\n[1]\nOk(())\nOk(())\n3"⟩,
  ⟨"use std::iter;\nfn main() { say(iter::collect(iter::take(iter::map(iter::filter(iter::iterate(1, { n => n + 1 }), { n => n % 3 == 0 }), { n => n * n }), 4))); say(iter::sum(iter::range(1, 101))); say(iter::collect(iter::zip(iter::of(['a', 'b']), iter::repeat(0)))); say(iter::collect(iter::chain(iter::range(0, 2), iter::of([9])))); say(iter::find(iter::iterate(1, { n => n * 2 }), { n => n > 1000 })); say(iter::collect(iter::enumerate(iter::of([\"x\", \"y\"])))); say(iter::collect(iter::take_while(iter::range(0, 10), { n => n < 3 }))); say(iter::collect(iter::skip(iter::range(0, 5), 3))); iter::count(iter::range(0, 7)) }",
    [], "[9, 36, 81, 144]\n5050\n[(a, 0), (b, 0)]\n[0, 1, 9]\nOk(1024)\n[(0, x), (1, y)]\n[0, 1, 2]\n[3, 4]\n7"⟩,
  ⟨"use std::option;\nfn main() { say(option::map(Some(2), { x => x + 1 })); say(option::unwrap_or(None, 7)); say(option::zip(Some(1), Some('a'))); say(option::and_then(Some(3), { x => if(x > 2) { Some(x * 2) } else { None } })); say(option::is_none(option::filter(Some(4), { x => x > 5 }))); option::fold(Some(5), 1, fn(a, b) { a + b }) }",
    [], "Ok(3)\n7\nOk((1, a))\nOk(6)\nOk(())\n6"⟩,
  -- A default function is checked for each implementation that takes it,
  -- against that implementation's types.
  ⟨"trait P { fn p(Self) -> Int\n fn q(a: Self) -> Int { p(a) + 1 } }\nimpl P for Int { fn p(a) { a } }\nimpl P for char { fn p(a) { 100 } }\nstruct B<T>(T)\nimpl<T> P for B<T> where T: P { fn p(b) { match(b) { B(x) => p(x) * 2 } } }\nfn main() { q(4) + q('c') + q(B(4)) }",
    [], "115"⟩,
  -- Values made of values that can be compared can be compared.
  ⟨"fn main() { say((1, 'a') == (1, 'a')); say(Some(3) == None); say([1, 2] == [1, 2]); say(\"abc\" < \"abd\"); say((1, 2) < (1, 3)); say(true == false); say((1, 2) != (1, 3)); say((1, 2) >= (1, 3)); (\"b\" >= \"a\") }",
    [], "Ok(())\nErr(())\nOk(())\nOk(())\nOk(())\nErr(())\nOk(())\nErr(())\nOk(())"⟩,
  ⟨"mod std { pub fn answer() -> Int { 42 } }\nfn main() { std::answer() }",
    [], "42"⟩,
  -- What is unsafe can be named only where `unsafe` is written.
  ⟨"extern \"C\" { fn abs(n: i32) -> i32; }\nfn main() { abs(3i32) }",
    [], "error: 2:13: in `main`: `abs` is unsafe: it can be named only in `unsafe { .. }` or in an `unsafe fn`"⟩,
  ⟨"unsafe fn risky(n: Int) -> Int { n + 1 }\nfn main() { risky(1) }",
    [], "error: 2:13: in `main`: `risky` is unsafe: it can be named only in `unsafe { .. }` or in an `unsafe fn`"⟩,
  ⟨"unsafe fn risky(n: Int) -> Int { n + 1 }\nfn safe(n: Int) -> Int { unsafe { risky(n) } }\nfn main() { safe(1) }",
    [], "2"⟩,
  ⟨"fn main() { ptr_read(0usize, 8) }",
    [], "error: 1:13: in `main`: `ptr_read` is unsafe: it can be named only in `unsafe { .. }` or in an `unsafe fn`"⟩,
  ⟨"use std::text::{utf8, from_utf8};\nfn main() { say(utf8(\"h\\u{e9}\\u{20ac}\")); say(from_utf8([104u8, 105u8])); from_utf8(utf8(\"h\\u{e9}llo \\u{1F600}\")) == Some(\"h\\u{e9}llo \\u{1F600}\") }",
    [], "[104, 195, 169, 226, 130, 172]\nOk(hi)\nOk(())"⟩,
  ⟨"extern \"C\" { fn sin(x: f64) -> f64; }\nfn main() { 0 }",
    [], "error: 1:37: a foreign function takes and gives whole numbers, an `Int` or a type such as `i32` or `usize`, not `f64`, found `}`"⟩,
  -- An array a variable holds is changed where it is; an array of values with
  -- `Drop` is destroyed element by element, the last first.
  ⟨"fn main() { let mut a = []; let mut i = 0; while({ i < 50 }) { a = push(a, i * i); i = i + 1 }; a[7] = 0 - 1; say(len(a)); a[7] + a[49] }",
    [], "50\n2400"⟩,
  ⟨"fn fill(n: Int, out: [Int]) -> [Int] { if(n == 0) { out } else { tail fill(n - 1, push(out, n)) } }\nfn main() { let a = fill(30, []); let mut b = a; b[0] = 0; say(a[0]); say(b[0]); let mut g = [[1, 2], [3, 4]]; g[1][1] = 9; g[0] = push(g[0], 5); say(g); match(pop(b)) { Some((rest, last)) => len(rest) * 100 + last, None => 0 } }",
    [], "30\n0\n[[1, 2, 5], [3, 9]]\n2901"⟩,
  ⟨"fn main() { let a = [1, 2, 3]; a[0 - 1] }",
    [], "went wrong"⟩,
  ⟨"fn main() { let mut a = [1]; a[1] = 5; 0 }",
    [], "went wrong"⟩,
  ⟨"struct Array(Int)\nfn main() { let a = [1, 2]; match(Array(7)) { Array(n) => n + a[1] } }",
    [], "9"⟩,
  -- A callable given a reference to a variable of the function it is passed
  -- to: its type binds the region, and the program is shown to follow the
  -- region rules (`glorious survey` counts them).
  ⟨"fn apply<F>(f: F) -> Int where F: for<'a> Fn<(&'a Int,), Output = Int> { let mut x = 5; f(&x) }\nfn main() { apply({ r => *r * 2 }) }",
    [], "10"⟩,
  ⟨"fn apply(f: for<'a> fn(&'a mut Int)) { let mut x = 1; f(&mut x); print(x) }\nfn main() { apply({ r => *r = *r + 41 }); 0 }",
    [], "42\n0"⟩,
  ⟨"fn inner(f: for<'a> fn(&'a Int) -> Int) -> Int { let mut x = 3; f(&x) }\nfn outer(g: for<'a> fn(&'a Int) -> Int) -> Int { inner(g) + 1 }\nfn main() { outer({ r => *r }) }",
    [], "4"⟩,
  ⟨"fn main() { let f = { r => *r * 2 }; let mut x = 5; let mut y = 6; f(&x) + f(&y) }",
    [], "22"⟩,
  ⟨"fn twice(f, r: &mut Int) { f(r); f(r) }\nfn main() { let mut n = 1; twice({ p => *p = *p * 3 }, &mut n); n }",
    [], "9"⟩,
  -- `std::hash`: hashing, and a map that finds a key in a step or two.
  ⟨"use std::hash;\nfn main() { let m = hash::from([(\"one\", 1), (\"two\", 2), (\"three\", 3)]); say(hash::get(m, \"two\")); say(hash::get(m, \"four\")); let big = fold(std::vec::range(0, 60), hash::new(), fn(acc, i) { hash::insert(acc, i * 7, i) }); say(hash::len(big)); say(hash::get(big, 21 * 7)); let fewer = hash::remove(hash::remove(big, 7), 1000); say(hash::len(fewer)); say(hash::contains_key(fewer, 7)); say(std::vec::sort(hash::keys(hash::insert(m, \"two\", 22)))); std::vec::sum(hash::values(hash::insert(m, \"two\", 22))) }",
    [], "Ok(2)\nErr(())\n60\nOk(21)\n59\nErr(())\n[one, three, two]\n26"⟩,
  -- A `&mut` reference is not given to a resumption: the handler's arm could
  -- run again and borrow the variable again. As an operation's argument it is
  -- lent for the arm.
  ⟨"effect Ask<'a> { ask() -> &'a mut Int }\nfn main() { let mut x = 1; handle { let r = ask(); *r = *r + 1; 0 }() { ask(k) => k(&mut x) }; x }",
    [], "error: 2:83: in `main`: calling `k` may assign or borrow `x` while a value this expression is still using holds a `&mut` reference to it"⟩,
  ⟨"effect Tick<'a> { tick(&'a mut Int) }\nfn main() { let mut x = 1; handle { tick(&mut x); tick(&mut x); 0 }() { tick(r, k) => *r = *r + 1; k(()) }; x }",
    [], "3"⟩,
  -- A pattern that binds by reference asks the cell which constructor built
  -- what it holds, and reads nothing: the value need not be one that can be
  -- copied.
  ⟨"struct File(Int)\nimpl Use<[0, 1]> for File {}\nenum Slot { Empty, Full(File, Int) }\nfn count(s: &mut Slot) -> Int { match(s) { &mut Full(_, n) => *n = *n + 1; *n, &mut Empty => 0 } }\nfn main() { let mut a = Full(File(3), 1); let mut b = Empty; count(&mut a) + count(&mut a) + count(&mut b) }",
    [], "5"⟩,
  ⟨"effect Ask { ask() -> Int }\nenum Job { Idle, Waiting(fn(Int) -> Int, Int) }\nfn peek(j: &Job) -> Int { match(j) { &Waiting(_, n) => *n, &Idle => 0 } }\nfn main() { let mut j = Idle; let a = peek(&j); j = Waiting({ x => x + 1 }, 7); a + peek(&j) }",
    [], "7"⟩,
  ⟨"enum Shape { Circle(Int), Rect { w: Int, h: Int } }\nfn area(s: &Shape) -> Int { match(s) { &Circle(r) => *r * *r * 3, &Rect { w, h } => *w * *h } }\nfn main() { let mut a = Circle(2); let mut b = Rect { w: 2, h: 5 }; area(&a) + area(&b) }",
    [], "22"⟩,
  ⟨"enum Tree { Leaf(Int), Node((Tree, Tree)) }\nfn bump(t: &mut Tree) { match(t) { &mut Leaf(n) => *n = *n + 1, &mut Node((Leaf(a), _)) => *a = *a + 10, _ => () } }\nfn main() { let mut x = Node((Leaf(1), Leaf(2))); bump(&mut x); let mut y = Leaf(5); bump(&mut y); (x, y) }",
    [], "(Node((Leaf(11), Leaf(2))), Leaf(6))"⟩,
  ⟨"enum Shape { Circle(Int), Rect(Int, Int), Dot }\nfn f(s: &Shape) -> Int { match(s) { &Circle(r) => *r, &Rect(w, _) => *w } }\nfn main() { 0 }",
    [], "error: 2:26: in `f`: the clauses of this callable do not cover every case"⟩,
  ⟨"struct File(Int)\nimpl Use<[0, 1]> for File {}\nenum Slot { Empty, Full(File, Int) }\nfn id_of(s: &Slot) -> Int { match(s) { &Full(f, _) => (*f).0, &Empty => 0 } }\nfn main() { let mut a = Full(File(3), 1); id_of(&a) + id_of(&a) }",
    [], "6"⟩,
  ⟨"enum E { A(Int), B(Int) }\nfn f(e: &E, n: Int) -> Int { match((n, 0)) { (0, _) => 0, _ => match(e) { &A(x) => *x, &B(y) => *y + 100 } } }\nfn main() { let mut e = B(2); f(&e, 0) + f(&e, 1) }",
    [], "102"⟩,
  ⟨"fn f(p: &Option<Int>) -> Int { match(p) { &Some(5) => 1, &Some(n) => *n, &None => 0 } }\nfn main() { let mut a = Some(5); let mut b = Some(9); f(&a) + f(&b) }",
    [], "10"⟩,
  -- A callable given two references: its type binds both regions.
  ⟨"fn both(f: for<'a, 'b> fn(&'a Int, &'b Int) -> Int) -> Int { let mut x = 3; let mut y = 4; f(&x, &y) }\nfn main() { both(fn(a, b) { *a * 10 + *b }) }",
    [], "34"⟩,
  -- A function that calls itself with a reference to a variable of a block of its own.
  ⟨"fn go(r, n) { if(0 < n) { let mut y = n; go(&mut y, n - 1) } else { *r } }\nfn main() { let mut t = 5; go(&mut t, 3) }",
    [], "1"⟩,
  ⟨"fn go(r: &Int, n: Int) -> Int { if(0 < n) { let mut y = n; go(&y, n - 1) } else { *r } }\nfn main() { let mut t = 5; go(&t, 3) }",
    [], "1"⟩,
  -- A callable for every lifetime kept in a declared type.
  ⟨"struct V(for<'a> fn(&'a Int) -> Int)\nfn run(v: V) -> Int { match(v) { V(f) => let mut x = 4; f(&x) } }\nfn main() { run(V({ r => *r + 1 })) }",
    [], "5"⟩,
  ⟨"struct V(for<'a> fn(&'a Int) -> Int)\nfn run(v: V) -> Int { match(v) { V(f) => let mut x = 4; let mut y = 6; f(&x) + f(&y) } }\nfn main() { run(V({ r => *r + 1 })) }",
    [], "12"⟩,
  ⟨"struct V(for<'a> fn(&'a Int) -> &'a Int)\nfn run(v: V) -> Int { match(v) { V(f) => let mut x = 4; *f(&x) } }\nfn main() { run(V({ r => r })) }",
    [], "4"⟩,
  -- `drop` is not for a program to call.
  ⟨"struct File(Int)\nimpl Drop for File { fn drop(p) { match(replace(p, File(0))) { File(fd) => host_write(fd) } } }\nfn main() { let mut f = File(7); drop(&mut f); 0 }",
    [], "error: 3:34: in `main`: `drop` is run when what holds a value ends; a program does not call it"⟩,
  ⟨"fn f() { 1 }",
    [], "error: the program has no `main` function"⟩
]

/-- Programs that call foreign functions and read and write memory at an
address. The proved machines give these no meaning, so they are run on the
Rust VM alone. -/
def foreignCases : List Case := [
  ⟨"extern \"C\" { fn abs(n: i32) -> i32; fn getpid() -> i32; }\nfn main() { unsafe { say(abs(0 - 5i32)); getpid() > 0i32 } }",
    [], "5\nOk(())"⟩,
  ⟨"extern \"C\" { fn malloc(n: usize) -> usize; fn free(p: usize); fn strlen(s: usize) -> usize; fn puts(s: usize) -> i32; }\nfn main() { unsafe { let p = malloc(6usize); ptr_write(p, 8, 72); ptr_write(p + 1usize, 8, 105); ptr_write(p + 2usize, 8, 0); puts(p); say(strlen(p)); say(ptr_read(p + 1usize, 8)); ptr_write(p, 32, 0 - 2); say(ptr_read(p, 32)); say(ptr_read(p, -32)); free(p); 0 } }",
    [], "Hi\n2\n105\n-2\n4294967294\n0"⟩,
  ⟨"use std::c::{c_string, text_at, free};\nuse std::text::{utf8, from_utf8};\nextern \"C\" { fn puts(s: usize) -> i32; fn toupper(c: i32) -> i32; fn getenv(name: usize) -> usize; }\nfn main() { say(utf8(\"h\\u{e9}\\u{20ac}\")); say(from_utf8(utf8(\"h\\u{e9}llo \\u{1F600}\")) == Some(\"h\\u{e9}llo \\u{1F600}\")); unsafe { let s = c_string(\"hello from C\"); puts(s); say(text_at(s)); free(s); let name = c_string(\"GLORIOUS_TEST\"); say(getenv(name) == 0usize); free(name); toupper(97i32) } }",
    [], "[104, 195, 169, 226, 130, 172]\nOk(())\nhello from C\nOk(hello from C)\nOk(())\n65"⟩
]

end Glorious
