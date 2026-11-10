import Glorious.Typing.Static

/-!
# Deciding whether two types are equal

A type checker that runs has to compare types. `Ty` contains lists of itself,
which the `deriving` handler does not cover, so the comparison is written out
and proved to decide equality. There is one function for each shape a type is
nested in, so that the recursion is structural and the kernel can run it.
-/

namespace Glorious.Typing

mutual

def Ty.beq : Ty → Ty → Bool
  | .int, .int => true
  | .tuple a, .tuple b => Ty.beqList a b
  | .data n a, .data m b => n == m && Ty.beqList a b
  | .fn p r e, .fn p' r' e' => Ty.beqList p p' && Ty.beq r r' && Ty.beqRow e e'
  | .ref a, .ref b => Ty.beq a b
  | _, _ => false
termination_by structural a => a

def Ty.beqList : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.beq a b && Ty.beqList as bs
  | _, _ => false
termination_by structural a => a

def Ty.beqRow :
    List (Nat × List Ty × Option Ty) → List (Nat × List Ty × Option Ty) → Bool
  | [], [] => true
  | x :: as, y :: bs => Ty.beqEntry x y && Ty.beqRow as bs
  | _, _ => false
termination_by structural a => a

def Ty.beqEntry : Nat × List Ty × Option Ty → Nat × List Ty × Option Ty → Bool
  | (op, x), (op', y) => op == op' && Ty.beqPair x y
termination_by structural a => a

def Ty.beqPair : List Ty × Option Ty → List Ty × Option Ty → Bool
  | (ps, r), (ps', r') => Ty.beqList ps ps' && Ty.beqOpt r r'
termination_by structural a => a

def Ty.beqOpt : Option Ty → Option Ty → Bool
  | none, none => true
  | some a, some b => Ty.beq a b
  | _, _ => false
termination_by structural a => a

end

mutual

theorem Ty.beq_eq : ∀ (a b : Ty), Ty.beq a b = true → a = b
  | .int, .int, _ => rfl
  | .tuple a, .tuple b, h => by
    simp only [Ty.beq] at h
    rw [Ty.beqList_eq a b h]
  | .data n a, .data m b, h => by
    simp only [Ty.beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, Ty.beqList_eq a b h.2]
  | .fn p r e, .fn p' r' e', h => by
    simp only [Ty.beq, Bool.and_eq_true] at h
    rw [Ty.beqList_eq p p' h.1.1, Ty.beq_eq r r' h.1.2, Ty.beqRow_eq e e' h.2]
  | .ref a, .ref b, h => by
    simp only [Ty.beq] at h
    rw [Ty.beq_eq a b h]
  | .int, .tuple _, h | .int, .data _ _, h | .int, .fn _ _ _, h | .int, .ref _, h
  | .tuple _, .int, h | .tuple _, .data _ _, h | .tuple _, .fn _ _ _, h | .tuple _, .ref _, h
  | .data _ _, .int, h | .data _ _, .tuple _, h | .data _ _, .fn _ _ _, h | .data _ _, .ref _, h
  | .fn _ _ _, .int, h | .fn _ _ _, .tuple _, h | .fn _ _ _, .data _ _, h | .fn _ _ _, .ref _, h
  | .ref _, .int, h | .ref _, .tuple _, h | .ref _, .data _ _, h | .ref _, .fn _ _ _, h => by
    simp [Ty.beq] at h

theorem Ty.beqList_eq : ∀ (a b : List Ty), Ty.beqList a b = true → a = b
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [Ty.beqList, Bool.and_eq_true] at h
    rw [Ty.beq_eq a b h.1, Ty.beqList_eq as bs h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [Ty.beqList] at h

theorem Ty.beqRow_eq : ∀ (a b : List (Nat × List Ty × Option Ty)), Ty.beqRow a b = true → a = b
  | [], [], _ => rfl
  | x :: as, y :: bs, h => by
    simp only [Ty.beqRow, Bool.and_eq_true] at h
    rw [Ty.beqEntry_eq x y h.1, Ty.beqRow_eq as bs h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [Ty.beqRow] at h

theorem Ty.beqEntry_eq : ∀ (a b : Nat × List Ty × Option Ty), Ty.beqEntry a b = true → a = b
  | (op, x), (op', y), h => by
    simp only [Ty.beqEntry, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, Ty.beqPair_eq x y h.2]

theorem Ty.beqPair_eq : ∀ (a b : List Ty × Option Ty), Ty.beqPair a b = true → a = b
  | (ps, r), (ps', r'), h => by
    simp only [Ty.beqPair, Bool.and_eq_true] at h
    rw [Ty.beqList_eq ps ps' h.1, Ty.beqOpt_eq r r' h.2]

theorem Ty.beqOpt_eq : ∀ (a b : Option Ty), Ty.beqOpt a b = true → a = b
  | none, none, _ => rfl
  | some a, some b, h => by
    simp only [Ty.beqOpt] at h
    rw [Ty.beq_eq a b h]
  | none, some _, h | some _, none, h => by simp [Ty.beqOpt] at h

end

mutual

theorem Ty.beq_refl : ∀ (a : Ty), Ty.beq a a = true
  | .int => by simp [Ty.beq]
  | .tuple a => by simp only [Ty.beq, Ty.beqList_refl a]
  | .data n a => by simp [Ty.beq, Ty.beqList_refl a]
  | .fn p r e => by simp [Ty.beq, Ty.beqList_refl p, Ty.beq_refl r, Ty.beqRow_refl e]
  | .ref a => by simp only [Ty.beq, Ty.beq_refl a]

theorem Ty.beqList_refl : ∀ (a : List Ty), Ty.beqList a a = true
  | [] => by simp [Ty.beqList]
  | a :: as => by simp [Ty.beqList, Ty.beq_refl a, Ty.beqList_refl as]

theorem Ty.beqRow_refl : ∀ (a : List (Nat × List Ty × Option Ty)), Ty.beqRow a a = true
  | [] => by simp [Ty.beqRow]
  | x :: as => by simp [Ty.beqRow, Ty.beqEntry_refl x, Ty.beqRow_refl as]

theorem Ty.beqEntry_refl : ∀ (a : Nat × List Ty × Option Ty), Ty.beqEntry a a = true
  | (op, x) => by simp [Ty.beqEntry, Ty.beqPair_refl x]

theorem Ty.beqPair_refl : ∀ (a : List Ty × Option Ty), Ty.beqPair a a = true
  | (ps, r) => by simp [Ty.beqPair, Ty.beqList_refl ps, Ty.beqOpt_refl r]

theorem Ty.beqOpt_refl : ∀ (a : Option Ty), Ty.beqOpt a a = true
  | none => by simp [Ty.beqOpt]
  | some a => by simp only [Ty.beqOpt, Ty.beq_refl a]

end

instance : DecidableEq Ty := fun a b =>
  if h : Ty.beq a b = true then isTrue (Ty.beq_eq a b h)
  else isFalse (fun e => h (e ▸ Ty.beq_refl a))

deriving instance DecidableEq for FnSig

end Glorious.Typing
