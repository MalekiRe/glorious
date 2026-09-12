import GloriousLanguage.ReferenceTransferPreservation

/-! Preservation for fresh storage creation. Allocation introduces an empty
home, not a resident owner; existing addresses, loans and pointer origins keep
their original authority. -/
namespace Glorious.Language

theorem Allocates.loans {program : Program} {before after : World} {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) :
    after.loans = before.loans := by cases allocated; rfl

theorem Allocates.nextLoan {program : Program} {before after : World} {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) :
    after.nextLoan = before.nextLoan := by cases allocated; rfl

theorem Allocates.created_addressType {program : Program} {before after : World}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) :
    AddressType program after address type := by
  cases allocated with
  | @fresh base _ _ =>
    exact ⟨0,.root (root := ⟨home,0,region,base,layout,type,none,mutable,before.clock,true,List.replicate layout.size none⟩)
      (Table.get_set _ _ _) rfl⟩

theorem Allocates.fields_nil {program : Program} {before after : World}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) : address.fields = [] := by
  cases allocated; rfl

theorem Allocates.created_vacant {program : Program} {before after : World}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) : after.Vacant address := by
  cases allocated with
  | @fresh base _ _ =>
    refine ⟨⟨home,0,region,base,layout,type,none,mutable,before.clock,true,List.replicate layout.size none⟩,?_,Or.inl ⟨rfl,rfl⟩⟩
    simp [World.root,Table.get_set]

theorem World.freshRoot {world : World} {originBound : Identity} (valid : world.WellFormedWithOrigins originBound) :
    world.roots.get world.nextRoot = none := by
  cases found : world.roots.get world.nextRoot with
  | none => rfl
  | some root => exact False.elim (Nat.lt_irrefl _ (World.root_bound valid found))

theorem Allocates.roots {program : Program} {before after : World} {home region type layout mutable address}
    {originBound : Identity} (valid : before.WellFormedWithOrigins originBound)
    (allocated : Allocates program before home region type layout mutable address after)
    {id : Identity} {root : Root} (found : before.roots.get id = some root) : after.roots.get id = some root := by
  cases allocated
  simpa only [Table.get_set_other _ _ _ _ (Nat.ne_of_lt (World.root_bound valid found))] using found

theorem Allocates.root {program : Program} {before after : World} {home region type layout mutable address}
    {originBound : Identity} (valid : before.WellFormedWithOrigins originBound)
    (allocated : Allocates program before home region type layout mutable address after)
    {observed : Address} {root : Root} (found : before.root observed = some root) : after.root observed = some root := by
  obtain ⟨selected,live,generation⟩ := World.root_found found
  simp [World.root,allocated.roots valid selected,live,generation]

theorem Allocates.read {program : Program} {before after : World} {home region type layout mutable address}
    {originBound : Identity} (valid : before.WellFormedWithOrigins originBound)
    (allocated : Allocates program before home region type layout mutable address after)
    (observed : Address) : after.read observed = before.read observed := by
  cases allocated
  by_cases same : observed.root = before.nextRoot
  · simp [World.read,World.root,same,Table.get_set,World.freshRoot valid]
  · simp [World.read,World.root,Table.get_set_other _ _ _ _ same]

theorem Allocates.resident {program : Program} {before after : World} {home region type layout mutable address}
    {originBound : Identity} (valid : before.WellFormedWithOrigins originBound)
    (allocated : Allocates program before home region type layout mutable address after)
    {observed : Address} {value : Value} : after.Resident observed value ↔ before.Resident observed value := by
  simp only [World.resident_iff_stores,World.Stores,allocated.read valid]

theorem Allocates.located {program : Program} {before after : World} {home region type layout mutable address}
    {originBound : Identity} (valid : before.WellFormedWithOrigins originBound)
    (allocated : Allocates program before home region type layout mutable address after)
    {observed : Address} (located : before.Located observed) : after.Located observed := by
  rcases located with ⟨value,stored⟩ | ⟨root,selected,vacant⟩
  · exact Or.inl ⟨value,by simpa only [World.Stores,allocated.read valid] using stored⟩
  · exact Or.inr ⟨root,allocated.root valid selected,vacant⟩

theorem Allocates.wellFormedWithOrigins {program : Program} {before after : World} {home region type layout mutable address}
    {originBound : Identity} (valid : before.WellFormedWithOrigins originBound)
    (allocated : Allocates program before home region type layout mutable address after) :
    after.WellFormedWithOrigins originBound := by
  have resident : ∀ {observed value}, after.Resident observed value ↔ before.Resident observed value :=
    allocated.resident valid
  have root : ∀ {observed root}, before.root observed = some root → after.root observed = some root :=
    allocated.root valid
  have located : ∀ {observed}, before.Located observed → after.Located observed := allocated.located valid
  cases allocated with
  | @fresh base request extent =>
    obtain ⟨regionLive,_,layoutValid,maximum,layoutOf⟩ := request
    obtain ⟨positive,aligned,within,disjoint⟩ := extent
    rcases valid with ⟨rootsUnique,loansUnique,proofsUnique,regionsUnique,proofs,packs,owners,ownersUnique,
      roots,regions,bases,ranges,loans,references,overlaps,parents,locations⟩
    refine ⟨rootsUnique.set _ _,loansUnique,proofsUnique,regionsUnique,?_,?_,?_,?_,?_,regions,?_,?_,?_,?_,?_,?_,?_⟩
    · intro id available found
      obtain ⟨identity,bound,brand,active,recorded⟩ := proofs id available found
      refine ⟨identity,bound,brand,?_,recorded⟩
      intro live
      obtain ⟨region,reserved⟩ := active live
      refine ⟨region,?_⟩
      intro place member
      obtain ⟨selected,found⟩ := Option.isSome_iff_exists.mp (reserved place member)
      simp [root found]
    · intro address value pack live head
      exact packs address value pack (resident.mp live) head
    · intro address value live
      exact owners address value (resident.mp live)
    · intro a b x y first second same
      exact ownersUnique a b x y (resident.mp first) (resident.mp second) same
    · intro id actual found
      by_cases fresh : id = before.nextRoot
      · subst id
        simp only [Table.get_set] at found
        cases found
        refine ⟨Nat.lt_succ_self _,fun _ => regionLive,layoutValid,by simp,?_⟩
        intro byte member n equal
        have absent : byte = none := List.eq_of_mem_replicate member
        simp [absent] at equal
      · have original : before.roots.get id = some actual := by
          simpa only [Table.get_set_other _ _ _ _ fresh] using found
        obtain ⟨bound,rest⟩ := roots id actual original
        exact ⟨Nat.lt_succ_of_lt bound,rest⟩
    · intro id actual found live
      by_cases fresh : id = before.nextRoot
      · subst id
        simp only [Table.get_set] at found
        cases found
        exact ⟨positive,aligned⟩
      · exact bases id actual (by simpa only [Table.get_set_other _ _ _ _ fresh] using found) live
    · intro a b left right first second different leftLive rightLive
      by_cases leftFresh : a = before.nextRoot
      · subst a
        simp only [Table.get_set] at first
        cases first
        have oldRight : before.roots.get b = some right := by
          simpa only [Table.get_set_other _ _ _ _ (Ne.symm different)] using second
        exact disjoint b right oldRight rightLive
      · have oldLeft : before.roots.get a = some left := by
          simpa only [Table.get_set_other _ _ _ _ leftFresh] using first
        by_cases rightFresh : b = before.nextRoot
        · subst b
          simp only [Table.get_set] at second
          cases second
          rcases disjoint a left oldLeft leftLive with empty | empty | before | after
          · exact Or.inr (Or.inl empty)
          · exact Or.inl empty
          · exact Or.inr (Or.inr (Or.inr before))
          · exact Or.inr (Or.inr (Or.inl after))
        · exact ranges a b left right oldLeft
            (by simpa only [Table.get_set_other _ _ _ _ rightFresh] using second) different leftLive rightLive
    · intro id loan found
      obtain ⟨identity,bound,live⟩ := loans id loan found
      refine ⟨identity,bound,?_⟩
      intro active
      obtain ⟨region,selected⟩ := live active
      refine ⟨region,?_⟩
      obtain ⟨actual,found⟩ := Option.isSome_iff_exists.mp selected
      simp [root found]
    · intro address value id live head
      exact references address value id (resident.mp live) head
    · intro a b left right first second leftLive rightLive overlap unique
      rcases overlaps a b left right first second leftLive rightLive overlap unique with ancestry | ancestry
      · exact Or.inl (AncestorLoan.transport (before := before) rfl ancestry)
      · exact Or.inr (AncestorLoan.transport (before := before) rfl ancestry)
    · exact parents
    · exact ⟨fun id loan found live => located (locations.1 id loan found live),locations.2⟩

theorem Allocates.wellFormed {program : Program} {before after : World} {home region type layout mutable address}
    (valid : before.WellFormed) (allocated : Allocates program before home region type layout mutable address after) :
    after.WellFormed := by
  have checked := allocated.wellFormedWithOrigins valid
  cases allocated
  exact checked

theorem Allocates.locationExtension {program : Program} {before after : World}
    {home region type layout mutable address} {originBound : Identity}
    (valid : before.WellFormedWithOrigins originBound)
    (allocated : Allocates program before home region type layout mutable address after) :
    before.LocationExtension after := by
  intro identity root selected
  rw [allocated.roots valid selected]
  rfl

theorem Allocates.supportFramed {program : RuntimeProgram} {before after : World}
    {home region type layout mutable address} {originBound : Identity} {value : Value} {access : Access}
    (valid : before.WellFormedWithOrigins originBound)
    (allocated : Allocates program.declarations before home region type layout mutable address after)
    (ready : value.ResourcesAccessible program before access) : value.SupportFramed before after := by
  intro observed supported
  obtain ⟨root,selected⟩ := ready.support_root supported
  refine ⟨allocated.read valid observed,?_⟩
  rw [allocated.roots valid (World.root_found selected).1,(World.root_found selected).1]

theorem Allocates.handoffReady {program : RuntimeProgram} {before after : World}
    {home region type layout mutable address} {originBound : Identity}
    {value : Value} {access : Access} {footprint : List Address}
    (valid : before.WellFormedWithOrigins originBound)
    (allocated : Allocates program.declarations before home region type layout mutable address after)
    (ready : value.HandoffReady program before access footprint) :
    value.HandoffReady program after access footprint :=
  ready.frame (allocated.locationExtension valid) allocated.loans (allocated.supportFramed valid ready.1)

end Glorious.Language
