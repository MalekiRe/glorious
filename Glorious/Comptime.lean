module

public import Glorious.Elab
public import Glorious.Core.Semantics

/-!
# Constants, worked out at compile time

A constant, `const NAME: T = value;`, is a function of its own,
`NAME$const`, which every use of the name calls. Once the program is Core,
each such function is run on the Core machine, the proved one, before the
program is: what it gives is written back as the function's body, a value
built from nothing, so what runs is a value and not the work of making it.
What goes wrong in it, a failed `assert`, a division by nothing, more steps
than are given, is said where the program is compiled, with what it wrote.
-/

public section

namespace Glorious.Comptime

open Glorious.Core

/-- Core that builds a value from nothing: the right-hand sides to bind, in
order, and the atom that is the value. `next` is the place of the next
local. None for what exists only while a program runs: a callable, a
reference, a resumption, a label. -/
partial def reify (v : Value) (next : Nat) : Option (List Rhs × Atom × Nat) :=
  match v with
  | .int n => some ([], .int n, next)
  | .data tag fields => do
    let mut rhss : List Rhs := []
    let mut atoms : List Atom := []
    let mut at_ := next
    for f in fields do
      let (rs, a, after) ← reify f at_
      rhss := rhss ++ rs
      atoms := atoms ++ [a]
      at_ := after
    pure (rhss ++ [.construct tag atoms], .var at_, at_ + 1)
  | _ => none

/-- The body of a function that gives the value, its locals after the
`params` it is given. -/
def literal (v : Value) (params : Nat := 0) : Option Tm := do
  let (rhss, a, _) ← reify v params
  pure (rhss.foldr (fun r t => .let_ r t) (.ret a))

/-- How a constant is said: by its name, or as the block it is. -/
def constName (fnName : String) : String :=
  let bare := (fnName.splitOn "$const").headD fnName
  let bare := ((bare.splitOn "`").filter (!·.isEmpty)).getLastD bare
  if ((bare.splitOn "::").getLastD bare).startsWith "const%" then "a `const { .. }` block" else s!"the constant `{bare}`"

/-- Run function `fn` of the program, given nothing, for at most `fuel`
steps: the value, or what went wrong, with what it wrote (`display`). -/
def runConst (p : Program) (fn : Nat) (fuel : Nat) (display : Value → String) (arity : Nat := 0) :
    Except String Value := do
  -- (Given `()` for each place a copy at known types keeps.)
  let units := (List.range arity).map fun _ => Rhs.construct 0 []
  let main := units.foldr (fun r t => Tm.let_ r t)
    (.let_ (.closure fn []) (.call (.var arity) ((List.range arity).map Atom.var) (.ret (.var (arity + 1)))))
  let q := { p with main }
  let rec go : Nat → Config → Except String Value
    | 0, _ => throw s!"it did not finish in {fuel} steps"
    | n + 1, cfg =>
      match stepIO q cfg with
      | .next cfg' => go n cfg'
      | .halt r => pure r.value
      | .stuck =>
        let wrote := cfg.world.output.map display
        throw (if wrote.isEmpty then "it went wrong"
          else s!"it went wrong, having written: {"; ".intercalate wrote}")
  go fuel (initIO q [])

/-- The characters of a text, the prelude's `StrChar`s ending in `StrEnd`. -/
partial def textOf (names : Array String) : Value → Option (List Nat)
  | .data tag [] => if (names[tag]?.getD "").endsWith "StrEnd" then some [] else none
  | .data tag [.int c, rest] =>
    if (names[tag]?.getD "").endsWith "StrChar" then (textOf names rest).map (c.toNat :: ·) else none
  | _ => none

/-- A value as what a constant wrote is said: a text as its characters. -/
partial def shown (names : Array String) (v : Value) : String :=
  match textOf names v with
  | some codes => String.ofList (codes.map Char.ofNat)
  | none => match v with
  | .int n => toString n
  | .data tag fields =>
    if fixedBase ≤ tag then
      let codes := fields.filterMap fun | .int n => some n | _ => none
      if codes.length == fields.length then String.ofList (codes.map fun n => Char.ofNat n.toNat)
      else s!"[{", ".intercalate (fields.map (shown names))}]"
    else
      let name := names[tag]?.getD s!"#{tag}"
      if fields.isEmpty then name else s!"{name}({", ".intercalate (fields.map (shown names))})"
  | _ => "<value>"

/-- The program with each constant's function giving its value, worked out
here. -/
def evaluate (out : Elab.Output) (display : Value → String := shown out.ctorNames) (fuel : Nat := 1000000) :
    Except String Elab.Output := do
  let mut fns := out.program.fns
  for (name, i) in out.fnNames.toList.zipIdx do
    unless (name.splitOn "$const").length > 1 do continue
    -- (One generic in types, given how they have what it asks of them, is
    -- worked out in each copy at known types, `NAME$const⟨impl ..⟩`, which
    -- is given in their place nothing it reads.)
    let some f := fns[i]? | continue
    let arity := (f.clauses.head?.map (·.pats.length)).getD 0
    let plain := f.clauses.all fun c => c.pats.all fun
      | .wild | .bind => true
      | _ => false
    unless arity == 0 || ((name.splitOn "⟨").length > 1 && plain) do continue
    let v ← match runConst { out.program with fns := fns } i fuel display arity with
      | .ok v => pure v
      | .error e => throw s!"{constName name} could not be worked out at compile time: {e}"
    match literal v arity with
    | some body => fns := fns.set! i { clauses := [⟨(List.range arity).map fun _ => .wild, body⟩] }
    | none =>
      throw s!"{constName name} gives a value that is there only while a program runs (a callable, a reference): it cannot be worked out at compile time"
  pure { out with program := { out.program with fns := fns } }

end Glorious.Comptime
