import GloriousLanguage.Terms

/-! Ordered child positions are the existing constructor projection, exposed
pointwise so context-indexed judgments can recurse directly through them. -/
namespace Glorious.Language

theorem ListRel.at {α β : Type} {relation : α → β → Prop} {left : List α} {right : List β}
    (related : ListRel relation left right) {index : Nat} {first : α} {second : β}
    (leftAt : left[index]? = some first) (rightAt : right[index]? = some second) : relation first second := by
  induction related generalizing index with
  | nil => simp at leftAt
  | cons head _ tail =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at leftAt rightAt
      subst_vars
      exact head
    | succ index => exact tail leftAt rightAt

theorem ListRel.of_at {α β : Type} {relation : α → β → Prop} {left : List α} {right : List β}
    (lengths : left.length = right.length)
    (related : ∀ (index : Nat) first second, left[index]? = some first → right[index]? = some second →
      relation first second) : ListRel relation left right := by
  induction left generalizing right with
  | nil =>
    obtain rfl := List.eq_nil_of_length_eq_zero lengths.symm
    exact .nil
  | cons first left ih =>
    cases right with
    | nil => simp at lengths
    | cons second right =>
      exact .cons (related 0 first second rfl rfl)
        (ih (Nat.succ.inj lengths) (fun index a b leftAt rightAt => related (index+1) a b leftAt rightAt))

theorem SameHead.children_length {left right : Term} (same : SameHead left right) :
    left.children.length = right.children.length := by
  have unchanged (term : Term) : (term.mapChildren (fun _ => .unit)).children.length = term.children.length := by
    cases term <;> simp [Term.mapChildren,Term.children]
  have lengths := congrArg (fun term => term.children.length) same
  simpa only [unchanged] using lengths

/-- Only these constructor heads retain ordered, injective child positions.
Aliases and associated projections must expand before inspecting their result;
row union is not an ordered injective constructor. -/
def Term.StructuralHead : Term → Prop
  | .alias _ _ | .projection _ _ _ _ _ | .row _ _ => False
  | _ => True

theorem SameHead.structuralHead_iff {left right : Term} (same : SameHead left right) :
    left.StructuralHead ↔ right.StructuralHead := by
  have unchanged (term : Term) : (term.mapChildren (fun _ => .unit)).StructuralHead = term.StructuralHead := by
    cases term <;> rfl
  have classified := congrArg Term.StructuralHead same
  rw [unchanged,unchanged] at classified
  exact Iff.of_eq classified

end Glorious.Language
