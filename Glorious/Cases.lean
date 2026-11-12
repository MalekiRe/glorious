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
  ⟨"fn zero() { 0 }
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
    [], "error: 1:29: in `main`: argument 2 of `match`: expected `fn(Result<Int, fn() -> Int>) -> _`, found `fn(Result<Int, ()>) -> Int`"⟩,
  ⟨"coerce nope  fn main() { 1 }",
    [], "error: `coerce nope`: there is no function `nope`"⟩,
  -- A failed `if` gives back its body, which was not run and still can be.
  ⟨"fn main() { match(if(1 != 1) { 10 }) { Ok(n) => n, Err(body) => body() + 1 } }",
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
    [], "error: in `each`: `each` is used recursively at a different type: expected `fn(fn(Int) -> _, Int) -> _`, found `fn(fn(Int) -> _, Int) -> Result<_, fn() -> _>` (this would need a type that contains itself); if the last expression of the body is not meant as the result, end it with `;`"⟩,
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
    [], "error: 4:13: in `main`: the mutable variable `f` lets go of what it holds when it is assigned or its block ends, but a `File` has to be used"⟩,
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
    [], "error: `impl Use` for `Ticket`: the fewest uses can be 0 or 1 and the most 1 or `infinity`; other bounds are not counted yet"⟩,
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
    [], "error: 2:13: in `main`: the mutable variable `saved` lets go of what it holds when it is assigned or its block ends, but a resumption of an operation declared `[1, 1]` has to be used"⟩,
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
  -- `drop` is not for a program to call.
  ⟨"struct File(Int)\nimpl Drop for File { fn drop(p) { match(replace(p, File(0))) { File(fd) => host_write(fd) } } }\nfn main() { let mut f = File(7); drop(&mut f); 0 }",
    [], "error: 3:34: in `main`: `drop` is run when what holds a value ends; a program does not call it"⟩,
  ⟨"fn f() { 1 }",
    [], "error: the program has no `main` function"⟩
]

end Glorious
