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
    [], "went wrong"⟩,
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
    [], "error: in `main`: the result of the scope `@out`: expected `_`, found `fn(_) -> _` (this would need a type that contains itself)"⟩,

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
    [], "went wrong"⟩,

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
    [], "error: in `main`: `x` is not a mutable variable"⟩,
  ⟨"fn main() { let x = 1; &mut x }",
    [], "error: in `main`: `x` is not a mutable variable, so it cannot be borrowed"⟩,

  -- An operation may declare how many times its resumption can be used. Each
  -- use runs the captured computation again; one use too many goes wrong.
  ⟨"effect Choice { [2, 2] choose() }
  fn main() { handle (if(choose()) { 1 } else { 2 }) * 10 { choose(k) => k(true) * 100 + k(false) } }",
    [], "1020"⟩,
  ⟨"effect Choice { [2, 2] choose() }
  fn main() { handle choose() { choose(k) => k(true); k(false); k(true) } }",
    [], "went wrong"⟩,
  ⟨"effect Choice { [2, 2] choose() }
  fn work() { defer print(1); choose() }
  fn main() { handle work() { _ => 0, choose(k) => k(true); k(false); 0 } }",
    [], "1\n1\n0"⟩,
  ⟨"effect Choice { [2, 2] choose() }  fn main() { handle choose() { choose() => true } }",
    [], "error: an arm for an operation resumed more than once must name the resumption"⟩,
  ⟨"effect Never { [0, 0] op() }  fn main() { 0 }",
    [], "error: operation `op` must allow its resumption at least one use"⟩,


  -- Types and effects are inferred. Mistakes that used to surface when a program
  -- ran are now reported before it does.
  ⟨"fn main() { 1 + (2, 3) }",
    [], "error: in `main`: argument 2 of `+`: expected `Int`, found `(Int, Int)`"⟩,
  ⟨"fn f(a, b) { a }  fn main() { f(1) }",
    [], "error: in `main`: `f` takes 2 arguments, but is given 1"⟩,
  ⟨"fn main() { let x = 5; x(1) }",
    [], "error: in `main`: `x` is called with 1 argument: expected `fn(Int) -> _`, found `Int`"⟩,
  ⟨"fn main() { (1, 2).5 }",
    [], "error: in `main`: a tuple of 2 values has no field 5"⟩,
  ⟨"fn main() { match(Some(1)) { None => 0 } }",
    [], "error: in `main`: the clauses of this callable do not cover every case"⟩,
  ⟨"fn f { 0 => 1 }  fn main() { f(5) }",
    [], "error: in `f`: the clauses of `f` do not cover every case"⟩,
  ⟨"fn main() { let (a, b) = (1, 2, 3); a }",
    [], "error: in `main`: a tuple pattern: expected `(_, _)`, found `(Int, Int, Int)`"⟩,
  ⟨"fn main() { if(1) { 2 } }",
    [], "error: in `main`: argument 1 of `if`: expected `Result<_, _>`, found `Int`"⟩,
  ⟨"effect Fail { fail(e) -> ! }  fn risky() { fail(1) }  fn main() { risky() }",
    [], "error: `main` performs effects that nothing handles: {Fail}"⟩,
  ⟨"effect Ask { ask(x) }  fn main() { handle ask(1) { ask(1) => 2 } }",
    [], "error: `main` performs effects that nothing handles: {Ask}"⟩,
  ⟨"fn main() { let mut x = 1; x = (1, 2); x }",
    [], "error: in `main`: the assigned value: expected `Int`, found `(Int, Int)`"⟩,
  ⟨"fn incr(p) { *p = *p + 1 }  fn main() { incr(5) }",
    [], "error: in `main`: argument 1 of `incr`: expected `&mut Int`, found `Int`"⟩,

  -- A declaration with inferred fields has one type throughout the program; one
  -- with type parameters is polymorphic.
  ⟨"enum Wrap { Wrap(v) }  fn main() { (Wrap(1), Wrap((1, 2))) }",
    [], "error: in `main`: argument 1 of constructor `Wrap`: expected `Int`, found `(Int, Int)`"⟩,
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
    [], "error: in `first`: `.0` reads a field of a value whose type is not known here; annotate the value it is read from"⟩,
  ⟨"fn first<A, B>(p: (A, B)) -> A { p.0 }  fn main() { (first((1, 2)), first(((3, 4), 5))) }",
    [], "(1, (3, 4))"⟩,

  -- Annotations are optional and checked when written. A function's own type
  -- parameters stand for any type, so its body cannot assume one.
  ⟨"fn double(x: Int) -> Int { x * 2 }  fn main() { double(21) }",
    [], "42"⟩,
  ⟨"fn double(x: Int) -> Int { x * 2 }  fn main() { double((1, 2)) }",
    [], "error: in `main`: argument 1 of `double`: expected `Int`, found `(Int, Int)`"⟩,
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
    [], "error: in `both`: the clauses of `both` do not cover every case"⟩,
  ⟨"fn main() { let Some(x) = Some(1); x }",
    [], "error: in `main`: the pattern of this `let` does not cover every case"⟩,
  ⟨"struct Pair<A, B>(first: A, second: B)\n  fn swap(p) { let Pair(a, b) = p; Pair(b, a) }\n  fn main() { swap(Pair(1, (2, 3))) }",
    [], "Pair((2, 3), 1)"⟩,

  -- Errors are reported, not guessed around.
  ⟨"fn main() { nope }",
    [], "error: in `main`: unknown name `nope`"⟩,
  ⟨"fn f(x) { tail f(x) + 1 }  fn main() { f(1) }",
    [], "error: `tail` call is not in tail position"⟩,
  ⟨"fn main() { 1 +",
    [], "error: 1:16: expected an expression, found end of input"⟩,
  ⟨"fn main() { 1 $ 2 }",
    [], "error: 1:15: unexpected character `$`"⟩,
  ⟨"fn f() { 1 }",
    [], "error: the program has no `main` function"⟩
]

end Glorious
