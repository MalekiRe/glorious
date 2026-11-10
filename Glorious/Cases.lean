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
  ⟨"fn main() { if(1 != 1) { 10 } }",
    [], "Err(())"⟩,
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

  -- A resumptive operation does not run the cleanups it captures: they run when
  -- the resumed computation finally leaves, exactly once.
  ⟨"effect Ask { ask() }
  fn work() { defer print(1); let x = ask(); print(x); x }
  fn main() { handle work() { ask(k) => print(0); k(42) } }",
    [], "0\n42\n1\n42"⟩,

  -- Cancelling a resumption runs the cleanups of the continuation it captured.
  -- Merely dropping it does not; the type system will have to require one or the other.
  ⟨"effect Ask { ask() }
  fn work() { defer print(1); defer print(2); ask(); print(99); 0 }
  fn main() { handle work() { ask(k) => cancel(k); 7 } }",
    [], "2\n1\n7"⟩,
  ⟨"effect Ask { ask() }
  fn work() { defer print(1); ask(); print(99); 0 }
  fn main() { handle work() { ask(k) => 7 } }",
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
    [], "error: 1:17: expected an operation name (there are no quantities: a resumption is used once), found `[`"⟩,

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
    [], "error: 1:38: in `main`: the clauses of this callable do not cover every case"⟩,
  ⟨"fn f { 0 => 1 }  fn main() { f(5) }",
    [], "error: 1:13: in `f`: the clauses of `f` do not cover every case"⟩,
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
    [], "error: in `double`: the result of a clause: expected `(Int, Int)`, found `Int`"⟩,
  ⟨"fn id<T>(x: T) -> T { x }  fn main() { (id(1), id((1, 2))) }",
    [], "(1, (1, 2))"⟩,
  ⟨"fn bad<T>(x: T) -> T { 1 }  fn main() { bad(2) }",
    [], "error: in `bad`: the result of a clause: expected `T`, found `Int`"⟩,
  ⟨"fn swap<A, B>(pair: (A, B)) -> (B, A) { (pair.1, pair.0) }  fn main() { swap((1, (2, 3))) }",
    [], "((2, 3), 1)"⟩,
  ⟨"fn incr(p: &mut Int) { *p = *p + 1 }  fn main() { let mut x = 1; incr(&mut x); x }",
    [], "2"⟩,
  ⟨"fn twice(f: fn(Int) -> Int, x: Int) -> Int { f(f(x)) }  fn main() { twice({ n => n + 3 }, 1) }",
    [], "7"⟩,
  ⟨"fn main() -> Int { (1, 2) }",
    [], "error: in `main`: the result of a clause: expected `Int`, found `(Int, Int)`"⟩,
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
    [], "error: 1:52: in `both`: the clauses of `both` do not cover every case"⟩,
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
    [], "error: in `each`: `each` is used recursively at a different type: expected `fn(fn(Int) -> _, Int) -> _`, found `fn(fn(Int) -> _, Int) -> Result<_, ()>` (this would need a type that contains itself); if the last expression of the body is not meant as the result, end it with `;`"⟩,
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
    [], "error: 2:54: in `main`: `f` is used more than once, but a value that holds a resumption can be used only once"⟩,
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
  -- Two separate callables that each use it count as two uses, even where only
  -- one of them can run.
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => match(1 < 2) { Ok(_) => k(10), Err(_) => k(20) } } }",
    [], "11"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => if(1 < 2) { k(10) } else { 0 } } }",
    [], "11"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => k(if(1 < 2) { 10 } else { 20 }) } }",
    [], "11"⟩,
  ⟨"effect Ask { ask() -> Int }\n  fn main() { handle ask() + 1 { ask(k) => if(1 < 2) { k(10) } else { k(20) } } }",
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

  -- Errors are reported, not guessed around.
  ⟨"fn main() { nope }",
    [], "error: 1:13: in `main`: unknown name `nope`"⟩,
  ⟨"fn f(x) { tail f(x) + 1 }  fn main() { f(1) }",
    [], "error: 1:11: `tail` call is not in tail position"⟩,
  ⟨"fn main() { 1 +",
    [], "error: 1:16: expected an expression, found end of input"⟩,
  ⟨"fn main() { 1 $ 2 }",
    [], "error: 1:15: unexpected character `$`"⟩,
  ⟨"fn f() { 1 }",
    [], "error: the program has no `main` function"⟩
]

end Glorious
