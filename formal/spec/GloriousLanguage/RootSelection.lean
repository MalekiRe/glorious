import GloriousLanguage.Control
import GloriousLanguage.AllocationPreservation

/-! Existence and preservation of exact ordered cleanup root lists. The finite
table supplies `RootsWhere`; actual writes and fresh allocations preserve its
eligibility and birth order without a second runtime root inventory. -/
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

/-- Exact root selection transports through retained eligibility and birth
order. Both directions concern the actual tables, not a second inventory. -/
theorem RootsWhere.frame {before after : World} {past future : Identity → Root → Prop} {roots : List Identity}
    (selected : RootsWhere before past roots)
    (forward : ∀ identity root, before.roots.get identity = some root → past identity root →
      ∃ current, after.roots.get identity = some current ∧ future identity current ∧ current.born = root.born)
    (backward : ∀ identity root, after.roots.get identity = some root → future identity root →
      ∃ original, before.roots.get identity = some original ∧ past identity original) : RootsWhere after future roots := by
  refine ⟨⟨selected.1.1,?_⟩,?_⟩
  · intro i j a b left right first last leftAt rightAt order
    obtain ⟨oldLeft,oldLeftAt,leftSelected⟩ := (selected.2 a).mp (List.mem_of_getElem? first)
    obtain ⟨oldRight,oldRightAt,rightSelected⟩ := (selected.2 b).mp (List.mem_of_getElem? last)
    obtain ⟨currentLeft,currentLeftAt,_,leftBorn⟩ := forward a oldLeft oldLeftAt leftSelected
    obtain ⟨currentRight,currentRightAt,_,rightBorn⟩ := forward b oldRight oldRightAt rightSelected
    have leftEq : currentLeft = left := Option.some.inj (currentLeftAt.symm.trans leftAt)
    have rightEq : currentRight = right := Option.some.inj (currentRightAt.symm.trans rightAt)
    subst currentLeft
    subst currentRight
    rw [leftBorn,rightBorn]
    exact selected.1.2 i j a b oldLeft oldRight first last oldLeftAt oldRightAt order
  · intro identity
    constructor
    · intro member
      obtain ⟨root,found,marked⟩ := (selected.2 identity).mp member
      obtain ⟨current,found,marked,_⟩ := forward identity root found marked
      exact ⟨current,found,marked⟩
    · rintro ⟨root,found,marked⟩
      exact (selected.2 identity).mpr (backward identity root found marked)

theorem ActivationRoots.of_locations {before after : World} {activation : Identity} {kept roots : List Identity}
    (selected : ActivationRoots before activation kept roots)
    (locations : ∀ identity, (after.roots.get identity).map Root.location = (before.roots.get identity).map Root.location) :
    ActivationRoots after activation kept roots := by
  apply selected.frame
  · intro identity root found marked
    have currentAt : (after.roots.get identity).map Root.location = some root.location := by rw [locations identity,found]; rfl
    obtain ⟨current,atCurrent,shape⟩ := Option.map_eq_some_iff.mp currentAt
    have home := congrArg Root.home shape
    have live := congrArg Root.live shape
    have born := congrArg Root.born shape
    change current.home = root.home at home
    change current.live = root.live at live
    exact ⟨current,atCurrent,⟨live.trans marked.1,by simpa only [OwnedByActivation,home] using marked.2.1,marked.2.2⟩,born⟩
  · intro identity root found marked
    have originalAt : (before.roots.get identity).map Root.location = some root.location := by rw [← locations identity,found]; rfl
    obtain ⟨original,atOriginal,shape⟩ := Option.map_eq_some_iff.mp originalAt
    have home := congrArg Root.home shape
    have live := congrArg Root.live shape
    change original.home = root.home at home
    change original.live = root.live at live
    exact ⟨original,atOriginal,live.trans marked.1,by simpa only [OwnedByActivation,home] using marked.2.1,marked.2.2⟩

theorem _root_.Glorious.Language.Allocates.activationRoots {program : Glorious.Language.Program} {before after : World}
    {home region type layout mutable address} {activation : Identity} {kept roots : List Identity}
    (allocated : Allocates program before home region type layout mutable address after) (valid : before.WellFormed)
    (selected : ActivationRoots before activation kept roots) (outside : ¬ HomeOwnedByActivation home activation) :
    ActivationRoots after activation kept roots := by
  cases allocated
  apply selected.frame
  · intro identity root found marked
    have apart : identity ≠ before.nextRoot := Nat.ne_of_lt (World.root_bound valid found)
    exact ⟨root,by simpa only [Table.get_set_other _ _ _ _ apart] using found,marked,rfl⟩
  · intro identity root found marked
    by_cases same : identity = before.nextRoot
    · subst identity
      simp only [Table.get_set,Option.some.injEq] at found
      subst root
      exact False.elim (outside marked.2.1)
    · exact ⟨root,by simpa only [Table.get_set_other _ _ _ _ same] using found,marked⟩


theorem _root_.Glorious.Language.FreshRegion.activationRoots {before after : World} {region activation : Identity}
    {kept roots : List Identity} (fresh : FreshRegion before region after)
    (selected : ActivationRoots before activation kept roots) : ActivationRoots after activation kept roots := by
  obtain ⟨_,rfl⟩ := fresh
  exact selected

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
