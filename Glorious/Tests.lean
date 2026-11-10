import Glorious.Driver

/-!
# Front-end tests

The front-end is not proved, so these run at build time: each program is
compiled and run on both the Core machine and the bytecode machine, and the two
results must agree with each other and with the expected output.
-/

namespace Glorious.Tests

/-! Arithmetic and operator fixity, all defined in the prelude. -/

#guard evalSource "fn main() { 1 + 2 * 3 }" == "7"
#guard evalSource "fn main() { (1 + 2) * 3 - 4 }" == "5"
#guard evalSource "fn main() { 10 - 3 - 2 }" == "5"
#guard evalSource "fn main() { -7 + 2 }" == "-5"

/-! Data, tuples and projection. -/

#guard evalSource "fn main() { (1, (2, 3)) }" == "(1, (2, 3))"
#guard evalSource "fn main() { let p = (1, (2, 3)); p.1.0 + p.0 }" == "3"
#guard evalSource "fn main() { let (a, (b, c)) = (1, (2, 3)); a + b * c }" == "7"
#guard evalSource "struct Point(x, y)  fn main() { let Point(x, y) = Point(3, 4); x * x + y * y }"
  == "25"
#guard evalSource "fn main() { Some(None) }" == "Ok(Err(()))"

/-! Conditionals are library functions; only the selected branch runs. -/

#guard evalSource "fn main() { if(1 < 2) { 10 } else { 20 } }" == "10"
#guard evalSource "fn main() { if(2 < 1) { 10 } else { 20 } }" == "20"
#guard evalSource "fn main() { if(1 == 1) { 10 } }" == "Ok(10)"
#guard evalSource "fn main() { if(1 != 1) { 10 } }" == "Err(())"
#guard evalSource "effect Boom { boom() -> ! }
  fn main() { if(1 < 2) { 1 } else { boom() } }" == "1"
#guard evalSource "effect Boom { boom() -> ! }
  fn main() { (1 < 2) or { boom() } }" == "Ok(())"
#guard evalSource "effect Boom { boom() -> ! }
  fn main() { (2 < 1) and { boom() } }" == "Err(())"
#guard evalSource "fn main() { not (1 < 2) }" == "Err(())"
#guard evalSource "fn main() { (3 >= 3, 3 <= 2, 4 > 1) }" == "(Ok(()), Err(()), Ok(()))"

/-! Matching is applying a pattern callable. -/

#guard evalSource "fn main() { match(Some(41)) { Some(x) => x + 1, None => 0 } }" == "42"
#guard evalSource "fn main() { match(None) { Some(x) => x + 1, None => 0 } }" == "0"
#guard evalSource "fn main() { match((Ok(1), Err(2))) { (Ok(a), Ok(b)) => a + b, (Ok(a), Err(b)) => a - b, _ => 0 } }"
  == "-1"
#guard evalSource "fn classify { 0 => 100, 1 => 200, n => n }  fn main() { (classify(0), classify(1), classify(7)) }"
  == "(100, 200, 7)"

/-! Functions, closures and captures. -/

#guard evalSource "fn twice(f, x) { f(f(x)) }  fn main() { twice({ n => n * 3 }, 2) }" == "18"
#guard evalSource "fn adder(n) { { x => x + n } }  fn main() { let add5 = adder(5); add5(add5(1)) }"
  == "11"
#guard evalSource "fn main() { let a = 2; let f = fn(x, y) { x * a + y }; f(10, 1) }" == "21"
#guard evalSource "fn fact(n) { if(n < 2) { 1 } else { n * fact(n - 1) } }  fn main() { fact(10) }"
  == "3628800"
#guard evalSource "fn sum(n, acc) { match(n) { 0 => acc, _ => tail sum(n - 1, acc + n) } }
  fn main() { sum(100, 0) }" == "5050"
#guard evalSource "fn even(n) { match(n) { 0 => true, _ => tail odd(n - 1) } }
  fn odd(n) { match(n) { 0 => false, _ => tail even(n - 1) } }
  fn main() { even(10) }" == "Ok(())"

/-! Effects: terminal operations, resumptions, completion clauses, forwarding. -/

#guard evalSource "effect Fail { fail(error) -> ! }
  fn main() { handle 1 + fail(7) { fail(e) => e * 2 } }" == "14"
#guard evalSource "effect Ask { ask(x) }
  fn main() { handle ask(1) + ask(2) { ask(x) => x * 10 } }" == "30"
#guard evalSource "effect Ask { ask(x) }
  fn main() { handle ask(1) + ask(2) { r => r + 1000, ask(x, k) => k(x * 10) } }" == "1030"
#guard evalSource "effect Ask { ask(x) }
  fn main() { handle ask(1) + 5 { ask(x, k) => 99 } }" == "99"
#guard evalSource "effect Ask { ask(x) }
  fn main() { handle (handle ask(1) + ask(2) { ask(1) => 100 }) { ask(x) => x * 10 } }" == "120"
#guard evalSource "effect Ask { ask(x) }  effect Fail { fail(e) -> ! }
  fn main() { handle (handle ask(3) { fail(e) => 0 }) { ask(x) => x + 1 } }" == "4"
#guard evalSource "effect Ask { ask(x) }
  fn main() { handle ask(1) { ask(x, k) => k(x) + k(x) } }" == "went wrong"
#guard evalSource "effect Ask { ask(x) }  fn main() { ask(1) }" == "went wrong"

/-! State threaded through resumptions: a counter written with a handler. -/

#guard evalSource "effect Counter { next() }
  fn counting(body, start) {
      let run = handle body() {
          result => { n => (result, n) },
          next(k) => { n => (k(n))(n + 1) }
      };
      run(start)
  }
  fn main() { counting({ next() * 100 + next() * 10 + next() }, 1) }" == "(123, 4)"

/-! Labels: early exit, the implicit function label, and escape. -/

#guard evalSource "fn main() { @out { 1 + @out(10) } + 5 }" == "15"
#guard evalSource "fn main() { @out { 7 } }" == "7"
#guard evalSource "fn find(target, a, b, c) {
      let check = { x => if(x == target) { @find(Some(x)) } };
      check(a); check(b); check(c);
      None
  }
  fn main() { (find(2, 1, 2, 3), find(9, 1, 2, 3)) }" == "(Ok(2), Err(()))"
#guard evalSource "fn main() { let l = @out { @out }; l(1) }" == "went wrong"

/-! Loops are a handler, a tail call and two terminal operations. -/

#guard evalSource "effect State { get(), put(value) }
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
  }" == "10"

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

/-! The host: output is written in order, input is consumed, and both survive
effects and early exits. -/

#guard evalSource "fn main() { print(1); print((2, 3)); 4 }" == "1\n(2, 3)\n4"
#guard evalSource "fn main() { (read(), read(), read()) }" [7, 8] == "(Ok(7), Ok(8), Err(()))"
#guard evalSource "fn sum_input(total) { match(read()) { Some(n) => tail sum_input(total + n), None => total } }
  fn main() { let total = sum_input(0); print(total); total * 2 }" [1, 2, 3, 4] == "10\n20"
#guard evalSource "effect Fail { fail(e) -> ! }
  fn work() { print(1); fail(2); print(3) }
  fn main() { handle work() { fail(e) => print(e * 10); 0 } }" == "1\n20\n0"
#guard evalSource "fn countdown(n) { match(n) { 0 => (), _ => print(n); tail countdown(n - 1) } }
  fn main() { countdown(3) }" == "3\n2\n1\n()"
#guard evalSource "fn main() { loop { let x = read() else { break(0) }; print(x * x) } }" [2, 3]
  == "4\n9\n0"

/-! Errors are reported, not guessed around. -/

#guard evalSource "fn main() { nope }" == "error: unknown name `nope`"
#guard evalSource "fn f(x) { tail f(x) + 1 }  fn main() { f(1) }"
  == "error: `tail` call is not in tail position"
#guard evalSource "fn main() { 1 +" == "error: 1:16: expected an expression, found end of input"
#guard evalSource "fn main() { 1 $ 2 }" == "error: 1:15: unexpected character `$`"
#guard evalSource "fn f() { 1 }" == "error: the program has no `main` function"

end Glorious.Tests
