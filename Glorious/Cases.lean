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
  fn main() { if(1 < 2) { 1 } else { boom() } }",
    [], "1"⟩,
  ⟨"effect Boom { boom() -> ! }
  fn main() { (1 < 2) or { boom() } }",
    [], "Ok(())"⟩,
  ⟨"effect Boom { boom() -> ! }
  fn main() { (2 < 1) and { boom() } }",
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
    [], "went wrong"⟩,

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
    [], "went wrong"⟩,

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
  fn work() { print(1); fail(2); print(3) }
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
  ⟨"fn main() { let r = @out { defer print(1); @out(5); print(99) }; print(r); 0 }",
    [], "1\n5\n0"⟩,
  ⟨"effect Fail { fail(e) -> ! }
  fn inner() { defer print(1); fail(7); print(99) }
  fn outer() { defer print(2); inner(); print(98) }
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
  fn work() { defer print(1); defer print(2); ask(); print(99) }
  fn main() { handle work() { ask(k) => cancel(k); 7 } }",
    [], "2\n1\n7"⟩,
  ⟨"effect Ask { ask() }
  fn work() { defer print(1); ask(); print(99) }
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

  -- Errors are reported, not guessed around.
  ⟨"fn main() { nope }",
    [], "error: unknown name `nope`"⟩,
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
