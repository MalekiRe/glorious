import GloriousLanguage.Foundation

/-! Finite identity support below an allocation frontier. The same elementary
relation is used for the actual storage addresses and activation identities
present in executable control; it carries no independent runtime inventory. -/
namespace Glorious.Language

def RootSupport.Below (roots : List Identity) (limit : Identity) : Prop :=
  ∀ root ∈ roots, root < limit

theorem RootSupport.Below.mono {roots : List Identity} {first last : Identity}
    (bounded : RootSupport.Below roots first) (limit : first ≤ last) : RootSupport.Below roots last :=
  fun root member => Nat.lt_of_lt_of_le (bounded root member) limit

@[simp] theorem RootSupport.below_nil (limit : Identity) : RootSupport.Below [] limit := by
  simp [Below]

@[simp] theorem RootSupport.below_cons {root : Identity} {roots : List Identity} {limit : Identity} :
    RootSupport.Below (root :: roots) limit ↔ root < limit ∧ RootSupport.Below roots limit := by
  simp [Below]

@[simp] theorem RootSupport.below_append {left right : List Identity} {limit : Identity} :
    RootSupport.Below (left ++ right) limit ↔ RootSupport.Below left limit ∧ RootSupport.Below right limit := by
  simp [Below, or_imp, forall_and]

@[simp] theorem RootSupport.below_flatMap {α : Type} {items : List α}
    {support : α → List Identity} {limit : Identity} :
    RootSupport.Below (items.flatMap support) limit ↔ ∀ item ∈ items, RootSupport.Below (support item) limit := by
  simp only [Below, List.mem_flatMap]
  constructor
  · intro bounded item member root inside
    exact bounded root ⟨item,member,inside⟩
  · rintro bounded root ⟨item,member,inside⟩
    exact bounded item member root inside

end Glorious.Language
