import GloriousLanguage.BulkMoveConstruction
import GloriousLanguage.LifecyclePreservation

/-! Constructive teardown of the authenticated empty buffer. Its owning
claims, storage retirement and region closure are separate actual transitions,
all derived from the same pre-world admission consumed by reallocation. -/
namespace Glorious.Language
namespace Memory

theorem BufferAt.root {before : World} {allocation : ResolvedPlace} {pointer : RawPointer}
    {domain : Identity} {value : Value} (buffer : BufferAt before allocation pointer domain value) :
    ∃ root, before.root allocation.address = some root ∧ root.value = some value ∧
      root.home = .allocation domain := by
  obtain ⟨id,root,_,_,address,_,found,live,home,generation,_,contents⟩ := buffer
  exact ⟨root,by simp [World.root,address,found,live,generation],contents,home⟩

theorem BufferAt.whole {before : World} {allocation : ResolvedPlace} {pointer : RawPointer}
    {domain : Identity} {value : Value} (buffer : BufferAt before allocation pointer domain value) :
    allocation.address.fields = [] := by
  obtain ⟨_,_,_,_,address,_⟩ := buffer
  simp [address]

theorem BufferAt.stores {before : World} {allocation : ResolvedPlace} {pointer : RawPointer}
    {domain : Identity} {value : Value} (buffer : BufferAt before allocation pointer domain value) :
    before.Stores allocation.address value := by
  obtain ⟨root,found,contents,_⟩ := buffer.root
  simp [World.Stores,World.read,found,contents,buffer.whole,Value.atPath]

theorem ReleasesBuffer.exists {program : Program} {before : World} {allocation : ResolvedPlace}
    {pointer : RawPointer} {domain : Identity} {value : Value}
    (buffer : BufferAt before allocation pointer domain value)
    (shell : value.shellLive = false) (resources : value.resources = [])
    (holes : ∀ field ∈ value.fields, field = none)
    (ready : ReleasesStorageClaimsReady before allocation)
    (unreserved : ∀ id available, before.availability.get id = some available → available.active = true →
      ∀ place ∈ available.reserved, place.address.root ≠ allocation.address.root)
    (regional : ∀ root, before.root allocation.address = some root → BufferRegionReady before allocation root.region) :
    ∃ after, ReleasesBuffer program before allocation pointer domain after := by
  obtain ⟨root,atRoot,contents,home⟩ := buffer.root
  obtain ⟨selected,live,generation⟩ := World.root_found atRoot
  have region := regional root atRoot
  let unclaimed : World := { before with loans := before.loans.map fun (key,loan) =>
    (key,if loan.referent.root = allocation.address.root then { loan with live := false } else loan) }
  have claims : ReleasesStorageClaims before allocation unclaimed := .release ready
  have noLoans : ∀ id loan, unclaimed.loans.get id = some loan → loan.live = true →
      loan.referent.root ≠ allocation.address.root := by
    intro id loan found active
    obtain ⟨original,_,same⟩ := Option.map_eq_some_iff.mp
      ((Table.get_map_values before.loans
        (fun loan => if loan.referent.root = allocation.address.root then { loan with live := false } else loan) id).symm.trans found)
    by_cases onRoot : original.referent.root = allocation.address.root
    · simp only [onRoot,ite_true] at same
      subst loan
      cases active
    · simp only [onRoot,ite_false] at same
      exact same ▸ onRoot
  have safe : CanEndStorage unclaimed allocation.address.root := by
    refine ⟨noLoans,unreserved,?_⟩
    intro actual found suspension
    have equal : root = actual := Option.some.inj (selected.symm.trans found)
    subst actual
    simp [home]
  let cleared : World := { unclaimed with roots := unclaimed.roots.set allocation.address.root { root with value := none } }
  have unclaimedAt : unclaimed.root allocation.address = some root := atRoot
  have written : unclaimed.write allocation.address none = some cleared := by
    simp [World.write,unclaimedAt,buffer.whole,cleared]
  have clearedRoot : cleared.roots.get allocation.address.root = some { root with value := none } :=
    Table.get_set _ _ _
  have clearedSafe : CanEndStorage cleared allocation.address.root :=
    safe.sameHomes (by simp [cleared,unclaimed,Table.get_set,selected]) rfl rfl
  let retired : World := { cleared with roots := cleared.roots.set allocation.address.root { root with value := none, live := false, generation := root.generation+1 } }
  have retirement : Retires cleared allocation.address.root retired := .vacant clearedRoot live rfl clearedSafe
  have regionEnds : Execution.RegionCanEnd retired root.region := by
    refine ⟨?_,?_,region.availability,?_⟩
    · intro id actual found active sameRegion
      by_cases sameRoot : id = allocation.address.root
      · subst id
        have actualEq := Option.some.inj ((Table.get_set _ _ _).symm.trans found)
        subst actual
        cases active
      · have old : before.roots.get id = some actual := by
          simpa only [retired,cleared,unclaimed,Table.get_set_other _ _ _ _ sameRoot] using found
        exact sameRoot (region.roots id actual old active sameRegion)
    · intro id loan found active sameRegion
      obtain ⟨original,old,same⟩ := Option.map_eq_some_iff.mp
        ((Table.get_map_values before.loans
          (fun loan => if loan.referent.root = allocation.address.root then { loan with live := false } else loan) id).symm.trans found)
      by_cases onRoot : original.referent.root = allocation.address.root
      · simp only [onRoot,ite_true] at same
        subst loan
        cases active
      · simp only [onRoot,ite_false] at same
        subst loan
        exact onRoot (region.loans id original old active sameRegion)
    · intro address resident pack stored head
      obtain ⟨original,old,same⟩ := World.clear_resident_origin written (retirement.resident.mp stored)
      have headEq : resident.head = original.head := by
        simpa only [Value.shell,Value.withFields,Value.head] using congrArg Value.head same
      exact region.packs address original pack old (headEq.symm.trans head)
  exact ⟨_,.release buffer atRoot shell resources holes claims safe written retirement ⟨regionEnds,rfl⟩⟩

end Memory
end Glorious.Language
