import Glorious.Value

/-!
# The host boundary

The finite set of things a program can ask of the outside world. Both machines
call the same `Host.call`, and nothing else touches the world.
-/

namespace Glorious

/-- The world outside the program: input not yet read, and output written so far. -/
structure World where
  input : List Int
  output : List Value

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
-/
def call (w : World) (id : Nat) (args : List Value) : Option (Value × World) :=
  if id = 0 then
    match args with
    | [v] => some (.data 0 [], ⟨w.input, w.output ++ [v]⟩)
    | _ => none
  else if id = 1 then
    match args with
    | [] =>
      match w.input with
      | n :: rest => some (.data 0 [.int 1, .int n], ⟨rest, w.output⟩)
      | [] => some (.data 0 [.int 0, .int 0], w)
    | _ => none
  else none

/-- A host operation never retracts output. -/
theorem call_output {w w' : World} {id : Nat} {args : List Value} {r : Value}
    (h : call w id args = some (r, w')) : w.output <+: w'.output := by
  unfold call at h
  split at h
  · split at h
    · simp at h
      obtain ⟨_, rfl⟩ := h
      exact List.prefix_append _ _
    · simp at h
  · split at h
    · split at h
      · split at h
        · simp at h
          obtain ⟨_, rfl⟩ := h
          exact List.prefix_refl _
        · simp at h
          obtain ⟨_, rfl⟩ := h
          exact List.prefix_refl _
      · simp at h
    · simp at h

end Host

end Glorious
