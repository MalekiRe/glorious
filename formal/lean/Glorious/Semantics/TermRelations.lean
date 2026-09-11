import Glorious.Semantics.Model
import Glorious.Proof.Behavior

/-! The substitution contract sits below normalization so every semantic
consumer uses the same proof-producing implementation and child traversal. -/
namespace Glorious.Semantics

abbrev Substitution := List (Id × Term)

namespace Spec

def SameHead (a b : Term) : Prop :=
  a.mapChildren (fun _ => .unit) = b.mapChildren (fun _ => .unit)

/-- Selection is ordered; a shadowed entry cannot supply a replacement. -/
inductive FirstBinding (identity : Id) : Substitution → Term → Prop where
  | head {value rest} : FirstBinding identity ((identity, value) :: rest) value
  | tail {other value rest selected} (different : other ≠ identity)
      (found : FirstBinding identity rest selected) :
      FirstBinding identity ((other, value) :: rest) selected

inductive Substitutes (arguments : Substitution) : Term → Term → Prop where
  | parameter {identity kind value} (selected : FirstBinding identity arguments value)
      (kinded : value.kind = kind) : Substitutes arguments (.param identity kind) value
  | free {identity kind} (absent : ∀ value, (identity, value) ∉ arguments) :
      Substitutes arguments (.param identity kind) (.param identity kind)
  | node {before after}
      (notParameter : ∀ identity kind, before ≠ .param identity kind)
      (head : SameHead before after)
      (children : Glorious.Proof.Forall₂ (Substitutes arguments) before.children after.children) :
      Substitutes arguments before after

theorem lookup_first {identity : Id} {arguments : Substitution} {value : Term}
    (found : lookup identity arguments = some value) : FirstBinding identity arguments value := by
  induction arguments with
  | nil => simp [lookup] at found
  | cons entry rest ih =>
    rcases entry with ⟨other, replacement⟩
    by_cases same : other = identity
    · subst other
      simp [lookup] at found
      subst replacement
      exact .head
    · apply FirstBinding.tail same
      apply ih
      simpa [lookup, same] using found

theorem lookup_absent {identity : Id} {arguments : Substitution}
    (absent : lookup identity arguments = none) : ∀ value, (identity, value) ∉ arguments := by
  induction arguments with
  | nil => simp
  | cons entry rest ih =>
    rcases entry with ⟨other, replacement⟩
    by_cases same : other = identity
    · simp [lookup, same] at absent
    · have tail := ih (by simpa [lookup, same] using absent)
      intro value
      simp only [List.mem_cons, Prod.mk.injEq, not_or]
      exact ⟨fun equal => same equal.1.symm, tail value⟩

end Spec

open Glorious.Proof

private theorem bind_ok_iff (action : Check α) (next : α → Check β) (value : β) :
    (action >>= next) = .ok value ↔ ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action <;> simp [bind, Except.bind]

private theorem pure_ok_iff (a b : α) : (pure a : Check α) = .ok b ↔ a = b := by
  change Except.ok a = Except.ok b ↔ a = b
  simp only [Except.ok.injEq]

theorem mapM_related {relation : α → β → Prop} {f : α → Check β}
    (sound : ∀ input output, f input = .ok output → relation input output)
    {before : List α} {after : List β} (accepted : before.mapM f = .ok after) :
    Forall₂ relation before after := by
  induction before generalizing after with
  | nil => simp only [List.mapM_nil, pure_ok_iff] at accepted; subst after; exact .nil
  | cons first rest ih =>
    simp only [List.mapM_cons, bind_ok_iff, pure_ok_iff] at accepted
    obtain ⟨value, firstAccepted, values, restAccepted, rfl⟩ := accepted
    exact .cons (sound first value firstAccepted) (ih restAccepted)

theorem Forall₂.append (first : Forall₂ relation a b) (second : Forall₂ relation c d) :
    Forall₂ relation (a ++ c) (b ++ d) := by
  induction first with
  | nil => exact second
  | cons head _ ih => exact .cons head ih

theorem Forall₂.map_constant (related : Forall₂ relation a b) (value : γ) :
    a.map (fun _ => value) = b.map (fun _ => value) := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, ih]

/-- The existing structural traversal preserves the constructor and relates
every child, in order, without a second semantic traversal. -/
theorem Term.mapChildrenM_related {relation : Term → Term → Prop} {f : Term → Check Term}
    (sound : ∀ input output, f input = .ok output → relation input output)
    {before after : Term} (accepted : before.mapChildrenM f = .ok after) :
    Spec.SameHead before after ∧ Forall₂ relation before.children after.children := by
  cases before <;> simp only [Term.mapChildrenM, bind_ok_iff, pure_ok_iff] at accepted
  all_goals
    repeat first
      | obtain ⟨value, transformed, accepted⟩ := accepted
        have related := sound _ _ transformed
      | obtain ⟨values, transformed, accepted⟩ := accepted
        have related := mapM_related sound transformed
        have arity := Forall₂.map_constant related Term.unit
    try subst after
    constructor
    · simp_all [Spec.SameHead, Term.mapChildren]
    · simp only [Term.children]
      first | assumption | exact .nil
            | exact .cons (by assumption) .nil
            | exact .cons (by assumption) (.cons (by assumption) .nil)
            | exact .cons (by assumption) (.cons (by assumption) (.cons (by assumption) .nil))
            | exact .cons (by assumption) (.cons (by assumption) (by assumption))
            | exact Forall₂.append (by assumption) (by assumption)

theorem checkedValue_sound {relation : α → β → Prop}
    (f : (input : α) → Check { output : β // relation input output })
    (input : α) (output : β) (accepted : (f input).map Subtype.val = .ok output) :
    relation input output := by
  cases produced : f input with
  | error diagnostic => simp [produced, Except.map] at accepted
  | ok result =>
    simp only [produced, Except.map, Except.ok.injEq] at accepted
    subst output
    exact result.property

def Term.mapChildrenCertified {relation : Term → Term → Prop}
    (f : (input : Term) → Check { output : Term // relation input output }) (before : Term) :
    Check { after : Term // Spec.SameHead before after ∧
      Forall₂ relation before.children after.children } :=
  match accepted : before.mapChildrenM (fun term => (f term).map Subtype.val) with
  | .error diagnostic => .error diagnostic
  | .ok after => .ok ⟨after, Term.mapChildrenM_related (checkedValue_sound f) accepted⟩

private def substituteChildren {arguments : Substitution}
    (f : (input : Term) → Check { output : Term // Spec.Substitutes arguments input output })
    (before : Term) (notParameter : ∀ identity kind, before ≠ .param identity kind) :
    Check { after : Term // Spec.Substitutes arguments before after } := do
  let result ← before.mapChildrenCertified f
  return ⟨result.val, .node notParameter result.property.1 result.property.2⟩

/-- Successful substitution carries its declarative derivation. Kind mismatch
and exhaustion reject here, before any normalization or lowering consumer. -/
def substituteCertified : Nat → (arguments : Substitution) → (before : Term) →
    Check { after : Term // Spec.Substitutes arguments before after }
  | 0, _, _ => reject .resourceLimit "substitution depth exhausted"
  | fuel + 1, arguments, before => by
    cases before with
    | param identity kind =>
      exact match selected : lookup identity arguments with
      | none => .ok ⟨.param identity kind, .free (Spec.lookup_absent selected)⟩
      | some value =>
        if kinded : value.kind = kind then
          .ok ⟨value, .parameter (Spec.lookup_first selected) kinded⟩
        else reject .kindMismatch "generic replacement has the wrong kind"
    | _ => exact substituteChildren (substituteCertified fuel arguments) _ (by intros; simp)

/-- Existing consumers project the certified producer, never an unchecked
parallel implementation. Proofs are erased by Lean after kernel checking. -/
def substitute (fuel : Nat) (arguments : Substitution) (before : Term) : Check Term :=
  (substituteCertified fuel arguments before).map Subtype.val

theorem Spec.substitute_sound (fuel : Nat) (arguments : Substitution) (before after : Term)
    (accepted : substitute fuel arguments before = .ok after) : Spec.Substitutes arguments before after :=
  checkedValue_sound (substituteCertified fuel arguments) before after accepted

theorem Term.mapChildren_kind (f : Term → Term) (term : Term) :
    (term.mapChildren f).kind = term.kind := by
  cases term <;> rfl

theorem Spec.SameHead.kind_eq {before after : Term} (same : Spec.SameHead before after) :
    before.kind = after.kind := by
  have kinds := congrArg Term.kind same
  simpa only [Term.mapChildren_kind] using kinds

theorem Spec.Substitutes.kind_eq {arguments : Substitution} {before after : Term}
    (substitution : Spec.Substitutes arguments before after) : before.kind = after.kind := by
  cases substitution with
  | parameter _ kinded => exact kinded.symm
  | free _ => rfl
  | node _ head _ => exact head.kind_eq

theorem substitute_kind (fuel : Nat) (arguments : Substitution) (before after : Term)
    (accepted : substitute fuel arguments before = .ok after) : before.kind = after.kind :=
  (Spec.substitute_sound fuel arguments before after accepted).kind_eq

end Glorious.Semantics
