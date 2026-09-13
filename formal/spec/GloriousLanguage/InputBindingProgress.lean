import GloriousLanguage.HandoffProgress
import GloriousLanguage.InputTyping
import GloriousLanguage.InputLending

/-! Constructing the actual common resident/raw binder. Positive requests
describe source location typing and physical layouts; they contain no completed
loan, custody handoff, allocation or resulting world. -/
namespace Glorious.Language

theorem Authority.BorrowRegion.live {world : World} {authority : Authority}
    {address : Address} {region : Identity} {access : Access}
    (valid : world.WellFormed) (permission : Permitted world authority access address)
    (borrowed : authority.BorrowRegion world address region) : region ∈ world.liveRegions := by
  induction authority with
  | owner =>
      obtain ⟨root,selected⟩ := permission.root
      obtain ⟨declared,found,regionAt⟩ := borrowed
      have source := World.root_found selected
      have same := Option.some.inj (found.symm.trans source.1)
      subst declared
      rw [← regionAt]
      exact (valid.2.2.2.2.2.2.2.2.1 _ _ source.1).2.1 source.2.1
  | loan identity =>
      obtain ⟨loan,selected,live,_⟩ := permission.2
      obtain ⟨declared,found,regionAt⟩ := borrowed
      have same := Option.some.inj (found.symm.trans selected)
      subst declared
      rw [← regionAt]
      exact ((valid.2.2.2.2.2.2.2.2.2.2.2.2.1 _ _ selected).2.2 live).1
  | shared backing ih => exact ih permission.2.2 borrowed
  | guarded backing carrier ih => exact ih permission.2.1 borrowed

theorem Authority.BorrowRegion.allocates {program : Program} {before after : World}
    {authority : Authority} {source : Address} {loanRegion : Identity}
    {home region type layout mutable address}
    (valid : before.WellFormed)
    (allocated : Allocates program before home region type layout mutable address after)
    (borrowed : authority.BorrowRegion before source loanRegion) :
    authority.BorrowRegion after source loanRegion := by
  induction authority with
  | owner => obtain ⟨root,found,atRegion⟩ := borrowed; exact ⟨root,allocated.roots valid found,atRegion⟩
  | loan identity => simpa only [Authority.BorrowRegion,allocated.loans] using borrowed
  | shared backing ih | guarded backing carrier ih => exact ih borrowed

theorem FormsLoan.exists {program : RuntimeProgram} {purpose : LoanPurpose} {before : World}
    {authority : Authority} {mode : Mutability} {region : Identity} {referent destination : Address} {value : Value}
    (stored : before.Stores referent value) (sourceType : AddressType program.declarations before referent value.type)
    (initialized : value.Initialized) (live : region ∈ before.liveRegions)
    (admitted : purpose.Admitted program.declarations value.type)
    (ready : value.ResourcesAccessible program before (if mode = .shared then .shared else .unique))
    (permission : Permitted before authority (if mode = .shared then .shared else .unique) referent)
    (vacant : before.Vacant destination)
    (destinationType : AddressType program.declarations before destination (.reference mode (.runtimeRegion region) value.type)) :
    ∃ after, FormsLoan program purpose before authority mode region referent destination after := by
  obtain ⟨written,write⟩ := vacant.write_exists
    (some (.resident before.nextOwner (.reference mode (.runtimeRegion region) value.type)
      (.reference before.nextLoan) true []))
  exact ⟨_,.borrow stored sourceType initialized live admitted ready permission vacant destinationType rfl write⟩

namespace Kernel

/-- A lent resident additionally needs its actual declared referent location;
a stored value alone does not prove a physical field-offset derivation. Erased
ports perform no resident allocation and therefore require no invented layout. -/
def InvocationInput.StorageRequest (program : RuntimeProgram) (world : World)
    (region : Identity) (input : InvocationInput) : Prop :=
  match input.formal with
  | .resident localSlot =>
      if input.access = .owned then
        ∃ layout, AllocationRequest program.declarations world region localSlot.type layout
      else ∃ loanRegion layout,
        input.authority.BorrowRegion world input.storage loanRegion ∧
        AddressType program.declarations world input.storage localSlot.type ∧
        AllocationRequest program.declarations world region
          (.reference (if input.access = .shared then .shared else .unique)
            (.runtimeRegion loanRegion) localSlot.type) layout
  | .storage _ _ | .allocation _ _ | .loan _ _ => True

/-- A receiver or resident input requests the actual temporary reference
layout only when it lends. Owning a receiver is a no-allocation transition;
missing loan layout or source-location evidence is not physical exhaustion. -/
def LendsResident.Request (program : RuntimeProgram) (world : World) (region : Identity)
    (address : Address) (authority : Authority) (access : Access) (type : Term) : Prop :=
  access ≠ .owned → ∃ loanRegion layout,
    authority.BorrowRegion world address loanRegion ∧ AddressType program.declarations world address type ∧
    AllocationRequest program.declarations world region
      (.reference (if access = .shared then .shared else .unique) (.runtimeRegion loanRegion) type) layout

theorem LendsResident.success_or_exhausted {program : RuntimeProgram} {before : World}
    {activation scope region : Identity} {address : Address} {authority : Authority}
    {access : Access} {value : Value}
    (valid : before.WellFormed) (stored : before.Stores address value) (initialized : value.Initialized)
    (ready : value.ResourcesAccessible program before access) (permission : Permitted before authority access address)
    (request : LendsResident.Request program before region address authority access value.type) :
    (∃ lease permission after,
      LendsResident program activation scope region before address authority access lease permission after) ∨
      LendsResidentExhausted program region before address authority access := by
  by_cases owned : access = .owned
  · subst access
    exact Or.inl ⟨none,authority,before,.owned⟩
  · obtain ⟨loanRegion,layout,borrowRegion,sourceType,request⟩ := request owned
    let mode : Mutability := if access = .shared then .shared else .unique
    have modes : access = .shared ∧ mode = .shared ∨ access = .unique ∧ mode = .unique := by
      cases access <;> simp_all [mode]
    have accessAt : access = if mode = .shared then .shared else .unique := by
      cases access <;> simp_all [mode]
    rcases request.success_or_exhausted (.temporary activation scope) true with
      ⟨handle,allocated,allocation⟩ | exhausted
    · have live := borrowRegion.live valid permission
      have regionState : allocated.liveRegions = before.liveRegions := by cases allocation; rfl
      have accessAfter := permission.locationExtension (allocation.locationExtension valid) allocation.loans
      have readyAfter := (allocation.handoffReady valid
        (show value.HandoffReady program before access [] from ⟨ready,by simp⟩)).1
      obtain ⟨after,formed⟩ := FormsLoan.exists ((allocation.read valid address).trans stored)
        (allocation.addressType valid sourceType) initialized (by simpa only [regionState] using live)
        (show LoanPurpose.invocation.Admitted program.declarations value.type from trivial)
        (accessAt ▸ readyAfter) (accessAt ▸ accessAfter) allocation.created_vacant allocation.created_addressType
      exact Or.inl ⟨_,_,after,.lent modes stored borrowRegion allocation formed⟩
    · exact Or.inr (.lent modes stored initialized ready permission borrowRegion exhausted)

/-- Every one of the six real input cases is constructed from its pre-state
logical readiness and positive storage request. Only resident allocation may
exhaust; raw claims and custody transfers retain their actual identities. -/
theorem BindsInputAt.success_or_exhausted {program : RuntimeProgram} {before : World}
    {recipient : ClaimCustody} {activation scope region : Identity} {input : InvocationInput}
    (valid : before.WellFormed) (ready : input.Ready program before)
    (request : input.StorageRequest program before region) :
    (∃ binding after, BindsInputAt program recipient activation scope region before input binding after) ∨
      BindsInputExhausted program region before input := by
  cases input with
  | mk origin formal source authority access =>
    cases formal with
    | resident localSlot =>
      obtain ⟨value,stored,initialized,type,resources,permission⟩ := ready
      by_cases owned : access = .owned
      · subst access
        obtain ⟨layout,request⟩ := request
        rcases request.success_or_exhausted (.localSlot activation scope) localSlot.mutable with
          ⟨destination,allocated,allocation⟩ | exhausted
        · have fresh := resources.1.supportOutside_fresh valid (Nat.le_of_eq allocation.fresh_root.1.symm)
          have moveReady : value.MoveReady program before [source,destination] := by
            refine ⟨resources.1,?_⟩
            intro address member
            simp only [List.mem_cons,List.not_mem_nil,or_false] at member
            rcases member with rfl | rfl
            · exact resources.2 address (by simp [InvocationInput.clearedStorage])
            · exact fresh
          have readyAfter := allocation.handoffReady valid moveReady
          have permittedAfter := permission.locationExtension (allocation.locationExtension valid) allocation.loans
          obtain ⟨root,selected⟩ := permission.root
          have bound := World.root_bound valid (World.root_found selected).1
          have separated : ¬ source.Overlaps destination := by
            intro overlap
            have same := overlap.1.trans allocation.fresh_root.1
            exact Nat.lt_irrefl _ (same ▸ bound)
          obtain ⟨after,moved⟩ := Transfers.exists ((allocation.read valid source).trans stored)
            initialized readyAfter permittedAfter allocation.created_vacant separated
            (by simpa only [type] using allocation.created_addressType)
          exact Or.inl ⟨_,after,.owned ⟨value,stored,initialized,type,resources,permission⟩
            rfl trivial stored type allocation moved⟩
        · exact Or.inr (.owned ⟨value,stored,initialized,type,resources,permission⟩ rfl trivial exhausted)
      · have request : ∃ loanRegion layout, authority.BorrowRegion before source loanRegion ∧
            AddressType program.declarations before source localSlot.type ∧
            AllocationRequest program.declarations before region
              (.reference (if access = .shared then .shared else .unique) (.runtimeRegion loanRegion) localSlot.type) layout := by
          simpa only [InvocationInput.StorageRequest,owned,if_false] using request
        obtain ⟨loanRegion,layout,borrowRegion,sourceType,request⟩ := request
        rcases LendsResident.success_or_exhausted valid stored initialized resources.1 permission
          (fun _ => ⟨loanRegion,layout,borrowRegion,by simpa only [type] using sourceType,
            by simpa only [type] using request⟩) with ⟨lease,lentAuthority,after,lent⟩ | exhausted
        · exact Or.inl ⟨_,after,.lent ⟨value,stored,initialized,type,resources,permission⟩
            owned trivial stored initialized type permission lent⟩
        · exact Or.inr (.lent ⟨value,stored,initialized,type,resources,permission⟩ trivial exhausted)
    | storage identity type =>
      obtain ⟨locatedType,located,permission⟩ := ready
      obtain ⟨root,selected⟩ := permission.root
      exact Or.inl ⟨_,_,.storage ⟨locatedType,located,permission⟩ rfl locatedType (.claim selected located permission)⟩
    | allocation identity type =>
      obtain ⟨owned,located,claim,authorityForm⟩ := ready
      rcases authorityForm with ⟨loan,loanAt⟩ | ⟨backing,guard,guarded,permission⟩
      · obtain ⟨selected,current,root,domain,parent,found,rest⟩ := claim
        have loanAuthority : authority = .loan loan := loanAt
        have same : selected = loan := Option.some.inj (parent.symm.trans (congrArg Authority.parentLoan loanAuthority))
        subst selected
        have claimed : AllocationClaim before authority source := ⟨loan,current,root,domain,parent,found,rest⟩
        exact Or.inl ⟨_,_,.allocation ⟨owned,located,claimed,Or.inl ⟨loan,loanAt⟩⟩ rfl owned located
          (.transfer loanAt claimed found)⟩
      · obtain ⟨root,selected⟩ := permission.root
        exact Or.inl ⟨_,_,.guardedAllocation ⟨owned,located,claim,Or.inr ⟨backing,guard,guarded,permission⟩⟩
          rfl owned guarded located (.claim claim permission selected)⟩
    | loan identity type =>
      obtain ⟨owned,located,loan,current,found,live,kind,referent,authorityForm⟩ := ready
      rcases authorityForm with ⟨loanAt,unique⟩ | ⟨backing,shared,parent,mode⟩
      · exact Or.inl ⟨_,_,.loan ⟨owned,located,loan,current,found,live,kind,referent,Or.inl ⟨loanAt,unique⟩⟩
          rfl owned located (.unique loanAt found live kind unique referent)⟩
      · exact Or.inl ⟨_,_,.loan ⟨owned,located,loan,current,found,live,kind,referent,Or.inr ⟨backing,shared,parent,mode⟩⟩
          rfl owned located (.shared shared parent found live kind mode referent)⟩

end Kernel
end Glorious.Language
