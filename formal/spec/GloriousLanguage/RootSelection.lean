import GloriousLanguage.Control

/-! Existence of the exact ordered cleanup lists used by actual execution.
The finite-table argument supplies witnesses of `RootsWhere`; it does not add
another runtime root inventory or presume that cleanup can already execute. -/
namespace Glorious.Language.Kernel

theorem RootsWhere.exists {world : World} (unique : world.roots.Unique)
    (selected : Identity → Root → Prop) : ∃ roots, RootsWhere world selected roots := by
  classical
  let present : Identity → Prop := fun id => ∃ root, world.roots.get id = some root ∧ selected id root
  let eligible := (world.roots.map Prod.fst).filter (fun id => decide (present id))
  let birth := fun id => ((world.roots.get id).map Root.born).getD 0
  let newer := fun a b => decide (birth b ≤ birth a)
  let roots := eligible.mergeSort newer
  have ordered : roots.Pairwise (fun a b => newer a b = true) := by
    apply List.pairwise_mergeSort
    · intro a b c first last
      simp only [newer,decide_eq_true_eq] at first last ⊢
      exact Nat.le_trans last first
    · intro a b
      simp only [newer,Bool.or_eq_true,decide_eq_true_eq]
      exact Nat.le_total _ _
  have nodup : roots.Nodup :=
    (List.mergeSort_perm eligible newer).nodup_iff.mpr (unique.filter _)
  refine ⟨roots,⟨nodup,?_⟩,?_⟩
  · intro i j a b left right first last leftAt rightAt before
    obtain ⟨hi,first⟩ := List.getElem?_eq_some_iff.mp first
    obtain ⟨hj,last⟩ := List.getElem?_eq_some_iff.mp last
    have order := (List.pairwise_iff_getElem.mp ordered) i j hi hj before
    simpa only [first,last,newer,birth,leftAt,rightAt,Option.map_some,Option.getD_some,
      decide_eq_true_eq] using order
  · intro id
    change id ∈ eligible.mergeSort newer ↔ present id
    rw [List.mem_mergeSort]
    change id ∈ (world.roots.map Prod.fst).filter (fun id => decide (present id)) ↔ present id
    simp only [List.mem_filter,decide_eq_true_eq]
    refine ⟨And.right,fun chosen => ⟨?_,chosen⟩⟩
    obtain ⟨root,found,_⟩ := chosen
    exact List.mem_map.mpr ⟨(id,root),Table.mem_of_get found,rfl⟩

theorem ScopeRoots.exists {world : World} (unique : world.roots.Unique)
    (activation scope : Identity) (kept : List Identity) : ∃ roots, ScopeRoots world activation scope kept roots :=
  RootsWhere.exists unique _

theorem ActivationRoots.exists {world : World} (unique : world.roots.Unique)
    (activation : Identity) (kept : List Identity) : ∃ roots, ActivationRoots world activation kept roots :=
  RootsWhere.exists unique _

end Glorious.Language.Kernel

namespace Glorious.Language.Execution

theorem AbandonedRoots.exists {world : World} (unique : world.roots.Unique)
    (frames : List Frame) (kept : List Identity) : ∃ roots, AbandonedRoots world frames kept roots :=
  Kernel.RootsWhere.exists unique _

theorem DelimitedRoots.exists {world : World} (unique : world.roots.Unique)
    (handler : InstalledHandler) (frames : List Frame) (kept : List Identity) :
    ∃ roots, DelimitedRoots world handler frames kept roots :=
  Kernel.RootsWhere.exists unique _

end Glorious.Language.Execution
