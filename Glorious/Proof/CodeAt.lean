module

public import Glorious.Bytecode.Ast

/-!
# Code positions

`CodeAt code pc is` says the instructions `is` sit in `code` starting at `pc`.
-/

@[expose] public section

namespace Glorious

open Bytecode (Instr Code)

theorem drop_eq_cons {α : Type} {l : List α} {n : Nat} {a : α} {t : List α}
    (h : l.drop n = a :: t) : l[n]? = some a ∧ l.drop (n + 1) = t := by
  induction l generalizing n with
  | nil => simp at h
  | cons x xs ih =>
    cases n with
    | zero =>
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    | succ n =>
      simp at h
      simpa using ih h

theorem getElem?_append_of_eq_some {α : Type} {l l' : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : (l ++ l')[i]? = some a := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simpa using h
    | succ i => simpa using ih (by simpa using h)

/-- The instructions `is` sit in `code` starting at position `pc`. -/
def CodeAt (code : Code) (pc : Nat) (is : Code) : Prop :=
  ∃ post, code.drop pc = is ++ post

namespace CodeAt

variable {code : Code} {pc : Nat} {i : Instr} {is a b : Code}

theorem zero (code : Code) : CodeAt code 0 code := ⟨[], by simp⟩

theorem head (h : CodeAt code pc (i :: is)) : code[pc]? = some i := by
  obtain ⟨post, h⟩ := h
  have h' : code.drop pc = i :: (is ++ post) := h
  exact (drop_eq_cons h').1

theorem tail (h : CodeAt code pc (i :: is)) : CodeAt code (pc + 1) is := by
  obtain ⟨post, h⟩ := h
  have h' : code.drop pc = i :: (is ++ post) := h
  exact ⟨post, (drop_eq_cons h').2⟩

theorem append_left (h : CodeAt code pc (a ++ b)) : CodeAt code pc a := by
  obtain ⟨post, h⟩ := h
  exact ⟨b ++ post, by rw [h, List.append_assoc]⟩

theorem append_right : ∀ {pc : Nat}, CodeAt code pc (a ++ b) → CodeAt code (pc + a.length) b := by
  induction a with
  | nil => intro pc h; simpa using h
  | cons i a ih =>
    intro pc h
    have h' : CodeAt code pc (i :: (a ++ b)) := h
    have e : pc + (i :: a).length = pc + 1 + a.length := by
      simp only [List.length_cons]; omega
    rw [e]
    exact ih h'.tail

end CodeAt

end Glorious
