import GloriousLanguage.StaticAtomTransport
import GloriousLanguage.AtomInstantiation

/-! A larger universe has genuinely more admitted atoms. A finite-support
bijection absorbs that new level into the infinitely many atoms of the old
boundary level, fixing any prescribed finite source support. -/
namespace Glorious.Language

theorem Occurs.sizeOf_le {needle term : Term} (occurs : Occurs needle term) : sizeOf needle ≤ sizeOf term := by
  induction occurs with
  | here => exact Nat.le_refl _
  | child member _ ih => exact Nat.le_trans ih (Nat.le_of_lt (Term.child_sizeOf member))

theorem Occurs.rigid_id_bound {id : Identity} {kind : Kind} {level : Nat} {term : Term}
    (occurs : Occurs (.rigid id kind level) term) : id < sizeOf term := by
  have bounded := occurs.sizeOf_le
  change 1 + id + sizeOf kind + level ≤ sizeOf term at bounded
  simp only [Identity] at *
  omega

theorem Occurs.variable_id_bound {id : Identity} {kind : Kind} {level : Nat} {term : Term}
    (occurs : Occurs (.variable id kind level) term) : id < sizeOf term := by
  have bounded := occurs.sizeOf_le
  change 1 + id + sizeOf kind + level ≤ sizeOf term at bounded
  simp only [Identity] at *
  omega

theorem AtomRenaming.fixed_term (rename : AtomRenaming) (term : Term)
    (regions : ∀ id, Occurs (.runtimeRegion id) term → rename.region id = id)
    (rigids : ∀ id kind level, Occurs (.rigid id kind level) term → rename.rigid id kind level = (id,level))
    (variables : ∀ id kind level, Occurs (.variable id kind level) term → rename.inference id kind level = (id,level)) :
    rename.term term = term := by
  apply AtomHomomorphism.fixed_term (map := rename.term) (by
    intro source
    cases source <;> simp only [AtomRenaming.term,Term.mapChildren]) term
  · intro _ _ _
    simp only [AtomRenaming.term]
  · intro atom occurs
    cases atom <;> try exact True.intro
    case runtimeRegion id => simp only [AtomRenaming.term,regions id occurs]
    case rigid id kind level => simp only [AtomRenaming.term,rigids id kind level occurs]
    case «variable» id kind level => simp only [AtomRenaming.term,variables id kind level occurs]

namespace UniverseEmbedding

def level (cutoff ambient : Nat) : Nat :=
  if ambient < cutoff then ambient else ambient + 1

def forward (cutoff seed id atomLevel : Nat) : Nat × Nat :=
  if atomLevel < cutoff then (id,atomLevel)
  else if cutoff < atomLevel then (id,atomLevel + 1)
  else if id < seed then (id,atomLevel)
  else if (id - seed) % 2 = 0 then (seed + (id - seed) / 2,cutoff)
  else ((id - seed) / 2,cutoff + 1)

def backward (cutoff seed id atomLevel : Nat) : Nat × Nat :=
  if atomLevel < cutoff then (id,atomLevel)
  else if cutoff + 1 < atomLevel then (id,atomLevel - 1)
  else if atomLevel = cutoff then
    if id < seed then (id,atomLevel) else (seed + 2 * (id - seed),cutoff)
  else (seed + 2 * id + 1,cutoff)

theorem backward_forward (cutoff seed id atomLevel : Nat) :
    backward cutoff seed (forward cutoff seed id atomLevel).1
      (forward cutoff seed id atomLevel).2 = (id,atomLevel) := by
  simp only [forward,backward]
  repeat' (first | split | apply Prod.ext)
  all_goals omega

theorem forward_backward (cutoff seed id atomLevel : Nat) :
    forward cutoff seed (backward cutoff seed id atomLevel).1
      (backward cutoff seed id atomLevel).2 = (id,atomLevel) := by
  simp only [backward,forward]
  repeat' (first | split | apply Prod.ext)
  all_goals omega

theorem forward_bound (cutoff seed id atomLevel ambient : Nat) :
    (forward cutoff seed id atomLevel).2 ≤ level cutoff ambient ↔ atomLevel ≤ ambient := by
  unfold forward level
  repeat' split
  all_goals omega

theorem forward_fixed (cutoff seed id atomLevel : Nat)
    (bounded : atomLevel ≤ cutoff) (small : id < seed) :
    forward cutoff seed id atomLevel = (id,atomLevel) := by
  by_cases lower : atomLevel < cutoff
  · simp only [forward,if_pos lower]
  · simp only [forward,if_neg lower,if_neg (by omega : ¬cutoff < atomLevel),if_pos small]

def embedding (cutoff seed : Nat) : AtomEmbedding where
  region := id
  rigid := fun id _ atomLevel => forward cutoff seed id atomLevel
  inference := fun id _ atomLevel => forward cutoff seed id atomLevel
  inverse := {
    region := id
    rigid := fun id _ atomLevel => backward cutoff seed id atomLevel
    inference := fun id _ atomLevel => backward cutoff seed id atomLevel }
  levelMap := level cutoff
  region_left := fun _ => rfl
  region_right := fun _ => rfl
  rigid_left := fun id _ atomLevel => backward_forward cutoff seed id atomLevel
  rigid_right := fun id _ atomLevel => forward_backward cutoff seed id atomLevel
  inference_left := fun id _ atomLevel => backward_forward cutoff seed id atomLevel
  inference_right := fun id _ atomLevel => forward_backward cutoff seed id atomLevel
  rigid_bound := fun id _ atomLevel ambient => forward_bound cutoff seed id atomLevel ambient
  inference_bound := fun id _ atomLevel ambient => forward_bound cutoff seed id atomLevel ambient

theorem fixed_term (cutoff seed : Nat) {term : Term} (small : sizeOf term ≤ seed)
    (rigids : NoLeak cutoff term)
    (variables : ∀ id kind level, Occurs (.variable id kind level) term → level ≤ cutoff) :
    (embedding cutoff seed).term term = term := by
  apply AtomRenaming.fixed_term
  · intro id _
    rfl
  · intro id kind level occurs
    exact forward_fixed cutoff seed id level (rigids id kind level occurs)
      (Nat.lt_of_lt_of_le occurs.rigid_id_bound small)
  · intro id kind level occurs
    exact forward_fixed cutoff seed id level (variables id kind level occurs)
      (Nat.lt_of_lt_of_le occurs.variable_id_bound small)

/-- The existing finite term projection supplies a support bound. No fresh
atom enumeration or semantic fact table is needed. -/
theorem fixed_terms (cutoff : Nat) (terms : List Term)
    (bounded : ∀ term ∈ terms, NoLeak cutoff term ∧
      ∀ id kind level, Occurs (.variable id kind level) term → level ≤ cutoff) :
    ∀ term ∈ terms, (embedding cutoff (sizeOf terms)).term term = term := by
  intro term member
  exact fixed_term cutoff (sizeOf terms) (Nat.le_of_lt (List.sizeOf_lt_of_mem member))
    (bounded term member).1 (bounded term member).2

end UniverseEmbedding

end Glorious.Language
