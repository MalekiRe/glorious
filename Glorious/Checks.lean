module

public import Glorious.Driver
public import Glorious.Cases
public import Glorious.Syntax.Flat

/-!
# What is asked of the front end besides what programs give

The front end is not proved. `glorious selftest` runs every test program, and
then asks each of these: how deep the stack gets, what is said when a program
goes wrong, which cells are still live at the end, how many cleanups ran, and
what the typing of a program's Core shows. Each is numbered, to be named when
it does not hold; most are cases of `tests/checks.cases`.
-/

public section

namespace Glorious.Checks

def counting (n : Nat) : String :=
  "fn count(i: Int, n: Int) -> Int { tail match(i == n) { Ok(_) => i, Err(_) => tail count(i + 1, n) } }
   fn main() -> Int { count(0, " ++ toString n ++ ") }"

def echoLoop : String :=
  "fn main() -> Int { loop { match(read()) { Some(x) => print(x), None => break(0) } } }"

def notTail (n : Nat) : String :=
  "fn count(i: Int, n: Int) -> Int { match(i == n) { Ok(_) => i, Err(_) => count(i + 1, n) } }
   fn main() -> Int { count(0, " ++ toString n ++ ") }"

/-- Whether a program compiled with what the checker kept of another, which
differs from it in the body of a function, gives what it gives compiled
afresh. -/
def keptAfterEdit (before after : String) : Bool :=
  match compileSource before true [] (few := true) with
  | .error _ => false
  | .ok c =>
    match compileSource after true [] (few := true) (checkKept := c.checkKept) with
    | .error _ => false
    | .ok c' => !c.checkKept.isEmpty && evalCompiled c' [] 200000 == evalSource after

def keptProgram (body : String) : String :=
  "mod m {
    pub trait D { fn d(&Self) -> Int }
    impl D for () { fn d(x: &()) -> Int { " ++ body ++ " } }
    impl<T> D for (Int, T) where T: D { fn d(p: &(Int, T)) -> Int { <T as D>::d(&p.1) + p.0 } }
    pub fn go() -> Int { d(&(2, (3, ()))) }
  }
  fn main() -> Int { m::go() }"

/-- A module's bodies made trees and made flat again are those trees. -/
def sameFlat (items : List Syntax.Item) : Bool :=
  items.all fun item => item.allBodies.all fun b => Syntax.Flat.roundTrips (Syntax.Flat.toClauses b)

/-- Of the prelude and every module of the library. (Asked as it is run:
a constant would be worked out whenever the compiler starts.) -/
def flatRoundTrips (_ : Unit) : Bool :=
  match readPrelude.get, readStd.get with
  | .ok (prelude, _), .ok std => sameFlat prelude && std.parsed.all sameFlat
  | _, _ => false

/-- What a check of `tests/checks.cases` finds of its program, written as its
`#### expect` is: what the typing of its Core shows, what is said when it goes
wrong, the cells live and the cleanups run at its end. -/
def found (kind src : String) : String :=
  match kind with
  | "owned" => reprStr (owned src)
  | "borrowChecked" => reprStr (borrowChecked src)
  | "lentBorrows" => reprStr (lentBorrows src)
  | "unprovedBorrows" => reprStr ((unprovedBorrows src).map (·.length))
  | "borrowFns" => reprStr (borrowFns src)
  | "diagnose" => diagnose src
  | "liveCells" => reprStr (liveCells src)
  | "cleanups" => reprStr (cleanups src)
  | _ => s!"no check is called `{kind}`"

/-- Each thing asked, with its number: those of `tests/checks.cases`, each
`#### case N kind`, and these. -/
def all : List (Nat × (Unit → Bool)) :=
  checkCases.map (fun c => match c.kind.splitOn " " with
    | [n, kind] => (n.toNat!, fun _ => found kind c.src == c.expect)
    | _ => (0, fun _ => false)) ++ [
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
  -- What the checker kept of a program is taken for the next only as that
  -- program has it: an implementation's function written longer before
  -- another implementation's moves where the other's calls are.
  (95, fun _ => keptAfterEdit (keptProgram "1") (keptProgram "let z = 0; 1 + z")),
  (96, fun _ => keptAfterEdit (keptProgram "let z = 0; 1 + z") (keptProgram "1")),
  -- A module's items made flat and made trees again are the items: the
  -- prelude's and every module of the library's.
  (97, fun _ => flatRoundTrips ())
]

end Glorious.Checks
