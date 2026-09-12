import GloriousLanguage.BufferAllocationFraming
import GloriousLanguage.BufferReleaseConstruction

/-! Reallocation frames the old allocation's actual claim and lifetime
admission through the fresh independent owner and the actual resident move. -/
namespace Glorious.Language.Memory

theorem AllocatesBuffer.resident_cases {program : Program} {before after : World}
    {custody : ClaimCustody} {allocation : ResolvedPlace} {domain : Identity}
    {element : Term} {count base : Nat} {pointer : RawPointer}
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    {address : Address} {value : Value} (resident : after.Resident address value) :
    before.Resident address value ∨ value.head = .array ∧ value.resources = [] := by
  cases allocated
  obtain ⟨root,whole,found,live,generation,contents,inside⟩ := resident
  by_cases same : address.root = before.nextRoot
  · rw [same,Table.get_set] at found
    cases found
    cases contents
    obtain ⟨_,rfl⟩ := inside.holes
    exact Or.inr ⟨rfl,rfl⟩
  · exact Or.inl ⟨root,whole,(Table.get_set_other _ _ _ _ same).symm.trans found,
      live,generation,contents,inside⟩

theorem AllocatesBuffer.references_before {program : Program} {before after : World}
    {custody : ClaimCustody} {allocation : ResolvedPlace} {domain : Identity}
    {element : Term} {count base : Nat} {pointer : RawPointer}
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    {id : Identity} (referenced : after.References id) : before.References id := by
  obtain ⟨address,value,resident,head⟩ := referenced
  rcases allocated.resident_cases resident with old | ⟨array,_⟩
  · exact ⟨address,value,old,head⟩
  · rw [array] at head
    cases head

theorem AllocatesBuffer.resourceReferences_before {program : Program} {before after : World}
    {custody : ClaimCustody} {allocation : ResolvedPlace} {domain : Identity}
    {element : Term} {count base : Nat} {pointer : RawPointer}
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    {id : Identity} (referenced : after.ResourceReferences id) : before.ResourceReferences id := by
  obtain ⟨address,value,binding,resident,member,parent⟩ := referenced
  rcases allocated.resident_cases resident with old | ⟨_,empty⟩
  · exact ⟨address,value,binding,old,member,parent⟩
  · simp [empty] at member

theorem AllocatesBuffer.loan_cases {program : Program} {before after : World}
    {custody : ClaimCustody} {allocation : ResolvedPlace} {domain : Identity}
    {element : Term} {count base : Nat} {pointer : RawPointer}
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    {id : Identity} {loan : Loan} (found : after.loans.get id = some loan) :
    before.loans.get id = some loan ∨
      loan.referent.root = before.nextRoot ∧ loan.region = before.nextRegion ∧ loan.guards = [] := by
  cases allocated
  by_cases same : id = before.nextLoan
  · subst id
    simp only [Table.get_set] at found
    cases found
    exact Or.inr ⟨rfl,rfl,rfl⟩
  · exact Or.inl ((Table.get_set_other _ _ _ _ same).symm.trans found)

theorem AllocatesBuffer.root_cases {program : Program} {before after : World}
    {custody : ClaimCustody} {allocation : ResolvedPlace} {domain : Identity}
    {element : Term} {count base : Nat} {pointer : RawPointer}
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    {id : Identity} {root : Root} (found : after.roots.get id = some root) :
    before.roots.get id = some root ∨ root.region = before.nextRegion := by
  cases allocated
  by_cases same : id = before.nextRoot
  · subst id
    simp only [Table.get_set] at found
    cases found
    exact Or.inr rfl
  · exact Or.inl ((Table.get_set_other _ _ _ _ same).symm.trans found)

theorem AllocatesBuffer.release_ready {program : Program} {before after : World}
    {custody : ClaimCustody} {allocation old : ResolvedPlace} {domain : Identity}
    {element : Term} {count base : Nat} {pointer : RawPointer}
    (valid : before.WellFormed)
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    (ready : ReleasesStorageClaimsReady before old) : ReleasesStorageClaimsReady after old := by
  obtain ⟨root,located⟩ := ready.permission.root
  have rootBound := World.root_bound valid (World.root_found located).1
  refine ⟨?_,ready.whole,allocated.permitted valid ready.permission,?_,?_⟩
  · obtain ⟨id,owner,authority,found,live,kind,unused⟩ := ready.claim
    exact ⟨id,owner,authority,allocated.old_loan valid found,live,kind,
      fun used => unused (allocated.resourceReferences_before used)⟩
  · intro key loan found live onRoot
    rcases allocated.loan_cases found with oldFound | ⟨fresh,_,_⟩
    · obtain ⟨kind,noReference,noResource⟩ := ready.safe key loan oldFound live onRoot
      exact ⟨kind,fun used => noReference (allocated.references_before used),
        fun used => noResource (allocated.resourceReferences_before used)⟩
    · exact False.elim (Nat.ne_of_lt rootBound (onRoot.symm.trans fresh))
  · intro key loan guard carrier found live member selected onRoot
    rcases allocated.loan_cases found with oldFound | ⟨_,_,empty⟩
    · rcases allocated.loan_cases selected with oldSelected | ⟨fresh,_,_⟩
      · exact ready.dependencies key loan guard carrier oldFound live member oldSelected onRoot
      · exact False.elim (Nat.ne_of_lt rootBound (onRoot.symm.trans fresh))
    · simp [empty] at member

theorem AllocatesBuffer.region_ready {program : Program} {before after : World}
    {custody : ClaimCustody} {allocation old : ResolvedPlace} {domain region : Identity}
    {element : Term} {count base : Nat} {pointer : RawPointer}
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    (bounded : region < before.nextRegion) (ready : BufferRegionReady before old region) :
    BufferRegionReady after old region := by
  refine ⟨?_,?_,?_,?_⟩
  · intro id root found live sameRegion
    rcases allocated.root_cases found with oldFound | fresh
    · exact ready.roots id root oldFound live sameRegion
    · exact False.elim (Nat.ne_of_lt bounded (sameRegion.symm.trans fresh))
  · intro id loan found live sameRegion
    rcases allocated.loan_cases found with oldFound | ⟨_,fresh,_⟩
    · exact ready.loans id loan oldFound live sameRegion
    · exact False.elim (Nat.ne_of_lt bounded (sameRegion.symm.trans fresh))
  · cases allocated
    exact ready.availability
  · intro address value pack resident head
    rcases allocated.resident_cases resident with old | ⟨array,_⟩
    · exact ready.packs address value pack old head
    · rw [array] at head
      cases head

theorem BulkMove.release_ready {program : RuntimeProgram} {before after : World}
    {sources destinations : List ResolvedPlace} {allocation : ResolvedPlace}
    (moved : BulkMove program before sources destinations after)
    (ready : ReleasesStorageClaimsReady before allocation) : ReleasesStorageClaimsReady after allocation := by
  have loans := congrArg World.loans moved.rest
  refine ⟨?_,ready.whole,ready.permission.transport moved.locations loans,?_,?_⟩
  · obtain ⟨id,owner,authority,found,live,kind,unused⟩ := ready.claim
    exact ⟨id,owner,authority,by simpa only [loans] using found,live,kind,
      fun used => unused (moved.resourceReferences_before used)⟩
  · intro key loan found live onRoot
    obtain ⟨kind,noReference,noResource⟩ := ready.safe key loan (by simpa only [loans] using found) live onRoot
    exact ⟨kind,fun used => noReference (moved.references_before used),
      fun used => noResource (moved.resourceReferences_before used)⟩
  · simpa only [loans] using ready.dependencies

theorem BulkMove.region_ready {program : RuntimeProgram} {before after : World}
    {sources destinations : List ResolvedPlace} {allocation : ResolvedPlace} {region : Identity}
    (moved : BulkMove program before sources destinations after)
    (ready : BufferRegionReady before allocation region) : BufferRegionReady after allocation region := by
  have loans := congrArg World.loans moved.rest
  have availability := congrArg World.availability moved.rest
  refine ⟨?_,by simpa only [loans] using ready.loans,by simpa only [availability] using ready.availability,?_⟩
  · intro id root found live sameRegion
    have locations := moved.locations id
    rw [found] at locations
    obtain ⟨original,selected,same⟩ := Option.map_eq_some_iff.mp locations.symm
    have liveEq := congrArg Root.live same
    have regionEq := congrArg Root.region same
    exact ready.roots id original selected (liveEq.trans live) (regionEq.trans sameRegion)
  · intro address value pack resident head
    obtain ⟨oldAddress,original,selected,same⟩ := moved.resident_origin resident
    have headEq : value.head = original.head := by
      simpa only [Value.shell,Value.withFields,Value.head] using congrArg Value.head same
    exact ready.packs oldAddress original pack selected (headEq.symm.trans head)

end Glorious.Language.Memory
