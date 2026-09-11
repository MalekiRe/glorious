import Std

/-! The three *principal* classes of language §7. A requested interval is a
    permission, not a test for the principal class. This module deliberately
    has no fourth ordinary class for resumptions. -/
namespace Glorious

inductive Principal where
  | duplicable
  | affine
  | exact
  deriving DecidableEq, Repr, BEq

namespace Principal

def permits : Principal → Nat → Prop
  | .duplicable, _ => True
  | .affine, n => n ≤ 1
  | .exact, n => n = 1

instance (p : Principal) (n : Nat) : Decidable (p.permits n) := by
  cases p <;> simp only [permits] <;> infer_instance

def MayDiscard (p : Principal) : Prop := p.permits 0
def MayCopy (p : Principal) : Prop := ∀ n, p.permits n

instance (p : Principal) : Decidable p.MayDiscard := inferInstanceAs (Decidable (p.permits 0))

/-- Intersection of resident capabilities, including inactive enum variants.
    An empty aggregate starts at `duplicable`; a manual declaration may then
    restrict it (in particular, an exact fieldless owner remains exact). -/
def meet : Principal → Principal → Principal
  | .exact, _ | _, .exact => .exact
  | .affine, _ | _, .affine => .affine
  | .duplicable, .duplicable => .duplicable

theorem meet_permits (p q : Principal) (n : Nat) :
    (p.meet q).permits n ↔ p.permits n ∧ q.permits n := by
  cases p <;> cases q <;> simp [meet, permits] <;> omega

theorem meet_comm (p q : Principal) : p.meet q = q.meet p := by
  cases p <;> cases q <;> rfl

theorem meet_assoc (p q r : Principal) : (p.meet q).meet r = p.meet (q.meet r) := by
  cases p <;> cases q <;> cases r <;> rfl

def residents (fields : List Principal) : Principal :=
  fields.foldr meet .duplicable

theorem residents_permits (fields : List Principal) (n : Nat) :
    (residents fields).permits n ↔ ∀ p ∈ fields, p.permits n := by
  induction fields with
  | nil => simp [residents, permits]
  | cons p ps ih => simpa only [residents, List.foldr_cons, meet_permits,
      List.mem_cons, forall_eq_or_imp] using and_congr_right (fun _ => ih)

/-- `declared` may narrow, never widen, a structural capability. -/
def Restricts (declared structural : Principal) : Prop :=
  ∀ n, declared.permits n → structural.permits n

theorem restricts_trans {p q r : Principal}
    (hpq : Restricts p q) (hqr : Restricts q r) : Restricts p r :=
  fun n hn => hqr n (hpq n hn)

theorem exact_not_discardable : ¬ MayDiscard .exact := by
  simp [MayDiscard, permits]

theorem copy_iff_duplicable (p : Principal) : MayCopy p ↔ p = .duplicable := by
  cases p with
  | duplicable => simp [MayCopy, permits]
  | affine => simp only [MayCopy, permits]; constructor <;> intro h
              · have := h 2; omega
              · cases h
  | exact => simp only [MayCopy, permits]; constructor <;> intro h
             · have := h 0; omega
             · cases h

theorem once_is_not_exactness (p : Principal) : p.permits 1 := by
  cases p <;> simp [permits]

end Principal

/-- Internal analysis quantities. `none` is infinity, not missing evidence.
    Unknown analysis is represented separately, never as this interval. -/
structure Quantity where
  lower : Nat
  upper : Option Nat
  deriving DecidableEq, Repr

namespace Quantity

def Contains (q : Quantity) (n : Nat) : Prop :=
  q.lower ≤ n ∧ match q.upper with | none => True | some u => n ≤ u

def Valid (q : Quantity) : Prop :=
  match q.upper with | none => True | some u => q.lower ≤ u

def allowedBy (q : Quantity) (p : Principal) : Prop :=
  q.Valid ∧ ∀ n, q.Contains n → p.permits n

def sequential (a b : Quantity) : Quantity :=
  ⟨a.lower + b.lower,
    match a.upper, b.upper with
    | some x, some y => some (x + y)
    | _, _ => none⟩

def alternative (a b : Quantity) : Quantity :=
  ⟨min a.lower b.lower,
    match a.upper, b.upper with
    | some x, some y => some (max x y)
    | _, _ => none⟩

theorem sequential_sound {a b : Quantity} {m n : Nat}
    (hm : a.Contains m) (hn : b.Contains n) :
    (a.sequential b).Contains (m + n) := by
  rcases a with ⟨al, au⟩
  rcases b with ⟨bl, bu⟩
  cases au <;> cases bu <;> simp_all [Contains, sequential] <;> omega

theorem alternative_left {a b : Quantity} {n : Nat} (h : a.Contains n) :
    (a.alternative b).Contains n := by
  rcases a with ⟨al, au⟩
  rcases b with ⟨bl, bu⟩
  cases au <;> cases bu <;> simp_all [Contains, alternative] <;> omega

theorem alternative_right {a b : Quantity} {n : Nat} (h : b.Contains n) :
    (a.alternative b).Contains n := by
  rcases a with ⟨al, au⟩
  rcases b with ⟨bl, bu⟩
  cases au <;> cases bu <;> simp_all [Contains, alternative] <;> omega

theorem requested_once (p : Principal) : allowedBy ⟨1, some 1⟩ p := by
  constructor
  · simp [Valid]
  · intro n hn
    have heq : n = 1 := by simp [Contains] at hn; omega
    subst n
    exact p.once_is_not_exactness

end Quantity
end Glorious
