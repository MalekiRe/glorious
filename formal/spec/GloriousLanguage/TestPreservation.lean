import GloriousLanguage.ControlPreservation
import GloriousLanguage.MemoryPreservation

/-! Pattern-test results publish their binding facts and carrier atomically.
The proof retains the actual owner-allocation frontier at private intermediate
worlds, while allowing facts to name the enclosing result's future owner. -/
namespace Glorious.Language

theorem Typing.WorldTypedWithOrigins.stored_root_type {program : Kernel.Program} {world : World}
    {originBound : Identity} (typed : Typing.WorldTypedWithOrigins program world originBound)
    {address : Address} {value : Value} {type : Term} (whole : address.fields = [])
    (stored : world.Stores address value) (located : AddressType program.declarations world address type) :
    value.type = type := by
  obtain ⟨root,found,typeEq⟩ := (AddressType.root_iff whole).mp located
  have read : root.value = some value := by simpa [World.Stores,World.read,found,whole,Value.atPath] using stored
  exact (typed.2.2.1 address.root root value (World.root_found found).1 read).trans typeEq

theorem Typing.WorldTypedWithOrigins.stored_root_addressType {program : Kernel.Program} {world : World}
    {originBound : Identity} (typed : Typing.WorldTypedWithOrigins program world originBound)
    {address : Address} {value : Value} (whole : address.fields = []) (stored : world.Stores address value) :
    AddressType program.declarations world address value.type := by
  obtain ⟨root,found⟩ := (World.Located.root_iff whole).mp (Or.inl ⟨value,stored⟩)
  apply (AddressType.root_iff whole).mpr
  have read : root.value = some value := by simpa [World.Stores,World.read,found,whole,Value.atPath] using stored
  exact ⟨root,found,(typed.2.2.1 address.root root value (World.root_found found).1 read).symm⟩

theorem World.advanceProof_wellFormedWithOrigins {world : World} {originBound next : Identity}
    (valid : world.WellFormedWithOrigins originBound) (monotone : world.nextProof ≤ next) :
    (world.withProofs world.availability next).WellFormedWithOrigins originBound := by
  rcases valid with ⟨rootsUnique,loansUnique,proofsUnique,regionsUnique,proofs,packs,owners,unique,
    roots,regions,bases,ranges,loans,references,overlaps,parents,locations⟩
  refine ⟨rootsUnique,loansUnique,proofsUnique,regionsUnique,?_,?_,owners,unique,
    roots,regions,bases,ranges,loans,references,?_,parents,locations⟩
  · intro id proof found
    obtain ⟨identity,bound,brand,active⟩ := proofs id proof found
    exact ⟨identity,Nat.lt_of_lt_of_le bound monotone,brand,active⟩
  · intro address value pack resident head
    obtain ⟨brand,region,length,distinct,facts⟩ := packs address value pack resident head
    exact ⟨Nat.lt_of_lt_of_le brand monotone,region,length,distinct,facts⟩
  · intro a b left right first second leftLive rightLive overlap unique
    exact (overlaps a b left right first second leftLive rightLive overlap unique).imp
      (fun ancestry => ancestry.transport (before := world) rfl)
      (fun ancestry => ancestry.transport (before := world) rfl)

theorem World.advanceProof_worldTypedWithOrigins {program : Kernel.Program} {world : World} {originBound next : Identity}
    (typed : Typing.WorldTypedWithOrigins program world originBound) (monotone : world.nextProof ≤ next) :
    Typing.WorldTypedWithOrigins program (world.withProofs world.availability next) originBound := by
  refine ⟨World.advanceProof_wellFormedWithOrigins typed.1 monotone,?_,typed.2.2⟩
  intro address value resident
  exact (typed.2.1 address value resident).extendProofs (fun _ _ found => found)

namespace Execution

theorem Temporary.whole {program : Kernel.Program} {context : Context} {type : Term}
    {before after : World} {address : Address} (temporary : Temporary program context type before address after) :
    address.fields = [] := by
  obtain ⟨_,allocated⟩ := temporary
  cases allocated
  rfl

theorem Temporary.addressType {program : Kernel.Program} {context : Context} {type : Term}
    {before after : World} {address : Address} (temporary : Temporary program context type before address after) :
    AddressType program.declarations after address type := by
  obtain ⟨_,allocated⟩ := temporary
  cases allocated
  apply (AddressType.root_iff rfl).mpr
  simp [World.root,Table.get_set]

theorem Temporary.nextOwner {program : Kernel.Program} {context : Context} {type : Term}
    {before after : World} {address : Address} (temporary : Temporary program context type before address after) :
    after.nextOwner = before.nextOwner := by
  obtain ⟨_,allocated⟩ := temporary
  cases allocated
  rfl

theorem Temporary.worldTypedWithOrigins {program : Kernel.Program} {context : Context} {type : Term}
    {before after : World} {address : Address} {originBound : Identity}
    (typed : Typing.WorldTypedWithOrigins program before originBound)
    (temporary : Temporary program context type before address after) :
    Typing.WorldTypedWithOrigins program after originBound := by
  obtain ⟨_,allocated⟩ := temporary
  exact allocated.worldTypedWithOrigins typed

theorem Temporary.addressType_retained {program : Kernel.Program} {context : Context} {type : Term}
    {before after : World} {destination address : Address} {residentType : Term} {originBound : Identity}
    (valid : before.WellFormedWithOrigins originBound)
    (temporary : Temporary program context type before destination after)
    (located : AddressType program.declarations before address residentType) :
    AddressType program.declarations after address residentType := by
  obtain ⟨_,allocated⟩ := temporary
  exact located.retained (fun _ found => allocated.roots valid found) (allocated.read valid)

theorem StoresUnit.worldTypedWithOrigins {program : Kernel.Program} {before after : World} {destination originBound}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTypedWithOrigins program before originBound)
    (stored : StoresUnit program before destination after) : Typing.WorldTypedWithOrigins program after originBound := by
  apply stored.2.worldTypedWithOrigins valid inventory typed (by simp) (by simp)
  intro values inputs
  cases inputs
  exact .unit

theorem CopiesObservations.root_type {program : Kernel.Program} {context : Context}
    {before after : World} {observations bindings}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (copied : CopiesObservations program context before observations bindings after)
    {address : Address} {type : Term} (whole : address.fields = [])
    (located : AddressType program.declarations before address type) :
    AddressType program.declarations after address type := by
  induction copied with
  | nil => exact located
  | copy _ _ temporary copied _ ih =>
    exact ih (copied.worldTyped valid inventory (temporary.worldTyped typed))
      (AddressType.root_transport copied.locations whole (temporary.addressType_retained typed.1 located))
  | borrow _ _ temporary borrowed _ ih =>
    exact ih (borrowed.worldTyped valid inventory (temporary.worldTyped typed))
      (AddressType.root_transport borrowed.locations whole (temporary.addressType_retained typed.1 located))

theorem CopiesObservations.binding_types {program : Kernel.Program} {context : Context}
    {before after : World} {observations bindings}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (copied : CopiesObservations program context before observations bindings after) :
    ∀ entry ∈ bindings, entry.2.fields = [] ∧ AddressType program.declarations after entry.2 entry.1.type := by
  induction copied with
  | nil => intro entry member; cases member
  | copy _ _ temporary copied rest ih =>
    have middle := copied.worldTyped valid inventory (temporary.worldTyped typed)
    intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨temporary.whole,rest.root_type valid inventory middle temporary.whole
        (AddressType.root_transport copied.locations temporary.whole temporary.addressType)⟩
    · exact ih middle entry member
  | borrow _ _ temporary borrowed rest ih =>
    have middle := borrowed.worldTyped valid inventory (temporary.worldTyped typed)
    intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨temporary.whole,rest.root_type valid inventory middle temporary.whole
        (AddressType.root_transport borrowed.locations temporary.whole temporary.addressType)⟩
    · exact ih middle entry member

theorem UnitFields.nextOwner {program : Kernel.Program} {context : Context} {before after : World} {types selected pack fields}
    (assembled : UnitFields program context before types selected pack fields after) : before.nextOwner ≤ after.nextOwner := by
  induction assembled with
  | done => exact Nat.le_refl _
  | selected _ _ _ ih => exact ih
  | unitBefore temporary unit _ ih | unitAfter temporary unit _ ih =>
    have created := congrArg World.nextOwner unit.2.rest
    rw [temporary.nextOwner] at created
    dsimp only at created
    rw [created] at ih
    exact Nat.le_trans (Nat.le_succ _) ih

theorem UnitFields.worldTypedWithOrigins {program : Kernel.Program} {context : Context}
    {before after : World} {types selected pack fields originBound}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTypedWithOrigins program before originBound)
    (assembled : UnitFields program context before types selected pack fields after) :
    Typing.WorldTypedWithOrigins program after originBound := by
  induction assembled with
  | done => exact typed
  | selected _ _ _ ih => exact ih typed
  | unitBefore temporary unit _ ih | unitAfter temporary unit _ ih =>
    exact ih (unit.worldTypedWithOrigins valid inventory (temporary.worldTypedWithOrigins typed))

theorem UnitFields.root_type {program : Kernel.Program} {context : Context}
    {before after : World} {types selected pack fields originBound}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTypedWithOrigins program before originBound)
    (assembled : UnitFields program context before types selected pack fields after)
    {address : Address} {type : Term} (whole : address.fields = [])
    (located : AddressType program.declarations before address type) : AddressType program.declarations after address type := by
  induction assembled with
  | done => exact located
  | selected _ _ _ ih => exact ih typed located
  | unitBefore temporary unit _ ih | unitAfter temporary unit _ ih =>
    exact ih (unit.worldTypedWithOrigins valid inventory (temporary.worldTypedWithOrigins typed))
      (AddressType.root_transport unit.2.locations whole (temporary.addressType_retained typed.1 located))

theorem UnitFields.field_types {program : Kernel.Program} {context : Context}
    {before after : World} {types selected pack fields originBound}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTypedWithOrigins program before originBound) (whole : pack.fields = [])
    (assembled : UnitFields program context before types selected pack fields after) :
    ListRel (fun address type => address.fields = [] ∧ AddressType program.declarations after address type) fields types := by
  induction assembled with
  | done => exact .nil
  | selected stored same rest ih =>
    exact .cons ⟨whole,rest.root_type valid inventory typed whole
      (same ▸ typed.stored_root_addressType whole stored)⟩ (ih typed whole)
  | unitBefore temporary unit rest ih | unitAfter temporary unit rest ih =>
    have created := unit.worldTypedWithOrigins valid inventory (temporary.worldTypedWithOrigins typed)
    exact .cons ⟨temporary.whole,rest.root_type valid inventory created temporary.whole
      (AddressType.root_transport unit.2.locations temporary.whole temporary.addressType)⟩ (ih created whole)

theorem binding_fields {program : Kernel.Program} {world : World} {bindings : List (Kernel.Local × Address)}
    {values : List Value} {originBound : Identity}
    (typed : Typing.WorldTypedWithOrigins program world originBound)
    (located : ∀ entry ∈ bindings, entry.2.fields = [] ∧ AddressType program.declarations world entry.2 entry.1.type)
    (inputs : ListRel (fun source value => world.Stores source.address value)
      (bindings.map (fun entry => (⟨entry.2,.owner⟩ : ResolvedPlace))) values) :
    Typing.FieldsTyped program world (values.map some) (bindings.map (fun entry => entry.1.type)) := by
  induction bindings generalizing values with
  | nil => cases inputs; exact .nil
  | cons entry rest ih =>
    cases inputs with
    | cons stored remaining =>
      obtain ⟨whole,atType⟩ := located entry List.mem_cons_self
      exact .resident (typed.2.1 entry.2 _ (World.resident_iff_stores.mpr stored))
        (typed.stored_root_type whole stored atType)
        (ih (fun child member => located child (List.mem_cons_of_mem _ member)) remaining)

theorem rooted_fields {program : Kernel.Program} {world : World} {addresses : List Address} {types : List Term}
    {values : List Value} {originBound : Identity}
    (typed : Typing.WorldTypedWithOrigins program world originBound)
    (located : ListRel (fun address type => address.fields = [] ∧ AddressType program.declarations world address type) addresses types)
    (inputs : ListRel (fun source value => world.Stores source.address value)
      (addresses.map (fun address => (⟨address,.owner⟩ : ResolvedPlace))) values) :
    Typing.FieldsTyped program world (values.map some) types := by
  induction located generalizing values with
  | nil => cases inputs; exact .nil
  | cons first rest ih =>
    cases inputs with
    | cons stored remaining =>
      exact .resident (typed.2.1 _ _ (World.resident_iff_stores.mpr stored))
        (typed.stored_root_type first.1 stored first.2) (ih remaining)

theorem PacksBindings.nextOwner {program : Kernel.Program} {context : Context}
    {before after : World} {pattern resultOrigin positive bindings pack}
    (packed : PacksBindings program context before pattern resultOrigin positive bindings pack after) :
    after.nextOwner = before.nextOwner+1 := by
  obtain ⟨allocated,created,type,_,temporary,_,constructed,rfl⟩ := packed
  change created.nextOwner = _
  rw [congrArg World.nextOwner constructed.rest,temporary.nextOwner]

theorem PacksBindings.whole {program : Kernel.Program} {context : Context}
    {before after : World} {pattern resultOrigin positive bindings pack}
    (packed : PacksBindings program context before pattern resultOrigin positive bindings pack after) :
    pack.fields = [] := by
  obtain ⟨_,_,_,_,temporary,_⟩ := packed
  exact temporary.whole

theorem PacksBindings.worldTypedWithOrigins {program : Kernel.Program} {context : Context}
    {before after : World} {pattern resultOrigin positive bindings pack originBound}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTypedWithOrigins program before originBound)
    (located : ∀ entry ∈ bindings, entry.2.fields = [] ∧ AddressType program.declarations before entry.2 entry.1.type)
    (future : resultOrigin < originBound)
    (packed : PacksBindings program context before pattern resultOrigin positive bindings pack after) :
    Typing.WorldTypedWithOrigins program after originBound := by
  obtain ⟨allocated,created,type,rfl,temporary,distinct,constructed,rfl⟩ := packed
  have allocatedTyped := temporary.worldTypedWithOrigins typed
  have proofBase : allocated.nextProof = before.nextProof := by
    obtain ⟨_,allocation⟩ := temporary
    cases allocation
    rfl
  have regionLive : context.region ∈ allocated.liveRegions := by
    obtain ⟨_,allocation⟩ := temporary
    cases allocation with
    | fresh live _ _ _ _ _ _ _ _ => exact live
  have registered : Typing.WorldTypedWithOrigins program
      (allocated.withProofs allocated.availability (before.nextProof+1)) originBound :=
    World.advanceProof_worldTypedWithOrigins allocatedTyped (by rw [proofBase]; exact Nat.le_succ _)
  have result := (constructed.withProofs allocated.availability (before.nextProof+1)).worldTypedWithOrigins
    valid inventory registered (by simp) ?_ ?_
  · have unchanged := congrArg World.availability constructed.rest
    simpa only [World.withProofs,unchanged] using result
  · intro actual same
    cases ValueHead.bindings.inj same
    refine ⟨Nat.lt_succ_self _,regionLive,by simp,distinct,?_⟩
    intro fact member
    have same : fact = ⟨resultOrigin,pattern,positive⟩ := List.mem_singleton.mp member
    simpa only [same] using future
  · intro values inputs
    apply Typing.ValueTyped.bindings (pack := ⟨before.nextProof,context.region,
      bindings.map (fun entry => entry.1.id),[⟨resultOrigin,pattern,positive⟩]⟩) ?_ rfl rfl ?_ distinct
    · apply binding_fields registered ?_ inputs
      intro entry member
      obtain ⟨whole,atType⟩ := located entry member
      exact ⟨whole,(temporary.addressType_retained typed.1 atType).retained
        (fun _ found => found) (fun _ => rfl)⟩
    · simpa only [List.length_map] using inputs.length_eq.symm

theorem TestResult.worldTyped {program : Kernel.Program} {context : Context}
    {before after : World} {destination type pattern positive observations}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (tested : TestResult program context before destination type pattern positive observations after) :
    Typing.WorldTyped program after := by
  cases tested with
  | @result carrier arguments copied bindings packed pack fields assembled after manifest resultType observed made carrierFields constructed =>
    have copiedTyped := observed.worldTyped valid inventory typed
    have bindingTypes := observed.binding_types valid inventory typed
    obtain ⟨types,head,length,selected,units,assembledFields⟩ := carrierFields
    have originBound : copied.nextOwner ≤ assembled.nextOwner+1 := by
      have one := made.nextOwner
      have many := assembledFields.nextOwner
      rw [one] at many
      exact Nat.le_trans (Nat.le_succ _) (Nat.le_trans many (Nat.le_succ _))
    have packedTyped := made.worldTypedWithOrigins valid inventory (copiedTyped.mono originBound)
      bindingTypes (Nat.lt_succ_self _)
    have assembledTyped := assembledFields.worldTypedWithOrigins valid inventory packedTyped
    have fieldTypes := assembledFields.field_types valid inventory packedTyped made.whole
    have result := constructed.worldTypedWithOrigins valid inventory assembledTyped (by simp) (by simp) (by
      intro values inputs
      exact Typing.ValueTyped.aggregate head (rooted_fields assembledTyped fieldTypes inputs))
    simpa only [Typing.WorldTyped,congrArg World.nextOwner constructed.rest] using result

/-- Every control transition preserves full world typing, including atomic
publication of test binding facts and their enclosing result owner. -/
theorem ControlStep.worldTyped {program : Kernel.Program} {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (step : ControlStep program before event after) :
    Typing.WorldTyped program after.world := by
  cases step <;> try exact typed
  case leave => apply Protect.worldTyped valid inventory typed; assumption
  case reserve resolved types distinct disjoint exclusive typeEq allocation created =>
    rw [typeEq] at allocation created
    apply reserve_worldTyped valid inventory typed allocation ?_ created
    intro place member
    have allowed := resolved.permitted place member
    obtain ⟨root,found⟩ := allowed.root
    exact Option.isSome_iff_exists.mpr ⟨root,found⟩
  case available moved => exact moved.worldTyped valid inventory typed
  case destroyAvailable =>
    apply World.deactivateAvailability_worldTyped
    · apply World.clear_worldTyped typed <;> assumption
    · have written := by assumption
      have proofs := congrArg World.availability (World.write_rest written)
      simpa only [proofs] using (by assumption)
  case destroySpentAvailable => apply World.clear_worldTyped typed <;> assumption
  case contextualCall consumed used =>
    apply used.worldTyped (consumed.worldTyped typed)
    intro access
    apply Permitted.transport consumed.locations consumed.loans
    rw [← access]
    assumption
  case positiveTest allocation tested => exact tested.worldTyped valid inventory (allocation.worldTyped typed)
  case negativeTest allocation tested => exact tested.worldTyped valid inventory (allocation.worldTyped typed)
  case bindings moved => exact moved.worldTyped valid inventory typed

end Execution
end Glorious.Language
