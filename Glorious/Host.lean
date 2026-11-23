module

public import Glorious.Value

/-!
# The host boundary

The finite set of things a program can ask of the outside world. Both machines
call the same `Host.call`, and nothing else touches the world.
-/

@[expose] public section

namespace Glorious

/-- The world outside the program: input not yet read, and output written so
far; and cells that more than one holder reaches, by number (`heap`): what
the library's shared values and threads are kept in. -/
structure World where
  input : List Int
  output : List Value
  heap : List (Option Value) := []
  /-- The program's functions' names, by index (`call` 9). -/
  names : Array String := #[]

/-- What a finished program leaves behind. -/
structure Result where
  value : Value
  world : World

namespace Host

/--
Perform host operation `id`.

* `0`, one argument: write the value; the result is unit.
* `1`, no arguments: read an integer; the result is the pair `(1, n)`, or
  `(0, 0)` when the input is exhausted.
* `6`, one argument: a new shared cell holding the value; the result is its
  number.
* `7`, a cell's number: the value it holds, taken out (the cell is then
  empty); none if it is empty.
* `8`, a cell's number and a value: the value put in it; the result is unit.
* `9`, a value: the pair of the name of the function it is a callable of,
  as an array of its characters' codes (none, of any other value), and the
  value itself, given back.
-/
def call (w : World) (id : Nat) (args : List Value) : Option (Value × World) :=
  if id = 0 then
    match args with
    | [v] => some (.data 0 [], { w with output := w.output ++ [v] })
    | _ => none
  else if id = 1 then
    match args with
    | [] =>
      match w.input with
      | n :: rest => some (.data 0 [.int 1, .int n], { w with input := rest })
      | [] => some (.data 0 [.int 0, .int 0], w)
    | _ => none
  else if id = 6 then
    match args with
    | [v] => some (.int w.heap.length, { w with heap := w.heap ++ [some v] })
    | _ => none
  else if id = 7 then
    match args with
    | [.int n] =>
      match w.heap[n.toNat]? with
      | some (some v) => if 0 ≤ n then some (v, { w with heap := w.heap.set n.toNat none }) else none
      | _ => none
    | _ => none
  else if id = 8 then
    match args with
    | [.int n, v] =>
      if 0 ≤ n ∧ n.toNat < w.heap.length then some (.data 0 [], { w with heap := w.heap.set n.toNat (some v) }) else none
    | _ => none
  else if id = 9 then
    match args with
    | [v] =>
      let name := match v with
        | .clo f _ => (w.names[f]?).getD ""
        | _ => ""
      let codes := name.toList.map fun c => Value.int c.toNat
      some (.data 0 [.data (arrayBase + codes.length) codes, v], w)
    | _ => none
  else none

/-%proof (commented out while the machines become bytes)
/-- A host operation never retracts output. -/
theorem call_output {w w' : World} {id : Nat} {args : List Value} {r : Value}
    (h : call w id args = some (r, w')) : w.output <+: w'.output := by
  unfold call at h
  repeat' split at h
  all_goals (simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h)
  all_goals (try obtain ⟨_, rfl⟩ := h)
  all_goals (first | exact List.prefix_append _ _ | exact List.prefix_refl _ | simp_all)
%proof-/

end Host

end Glorious
