import GloriousLanguage.InputTyping
import GloriousLanguage.LocalPreservation
import GloriousLanguage.BindingDomain

/-! A local's declared storage type is not evidence that its contents can be
read. Whole-root locals retain their allocation's type after movement or
retirement; lent subobjects retain the actual invocation loan and a resident
reference handle that prevents its release. A successful runtime read recovers usable typing.

This is the persistent storage component of the source/runtime context
boundary, not a second source analysis or a permission judgment. -/
namespace Glorious.Language

namespace Typing

inductive BindingStorageTyped (program : Program) (world : World) : Address → Term → Prop where
  | root {address type} : address.fields = [] →
      (world.roots.get address.root).map Root.type = some type →
      BindingStorageTyped program world address type
  | lent {address type id loan} : world.loans.get id = some loan → loan.live = true →
      loan.referent = address → world.References id → AddressType program world address type →
      BindingStorageTyped program world address type

end Typing

theorem InvocationAddress.bindingStorageTyped {program : Program} {world : World} {address : Address} {type : Term}
    (origin : InvocationAddress world address) (located : AddressType program world address type) :
    Typing.BindingStorageTyped program world address type := by
  rcases origin with whole | ⟨id,loan,found,live,referent,referenced⟩
  · obtain ⟨root,found,rfl⟩ := (AddressType.root_iff whole).mp located
    exact .root whole (by rw [(World.root_found found).1]; rfl)
  · exact .lent found live referent referenced located

theorem Typing.BindingStorageTyped.read {program : Kernel.Program} {world : World}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program world) {address : Address} {type : Term} {value : Value}
    (binding : Typing.BindingStorageTyped program.declarations world address type)
    (stored : world.Stores address value) :
    AddressType program.declarations world address type ∧ Typing.ValueTyped program world value ∧ value.type = type := by
  have located : AddressType program.declarations world address type := by
    cases binding with
    | root whole declared =>
      obtain ⟨root,found,_⟩ := Option.bind_eq_some_iff.mp stored
      have atType : root.type = type := by
        rw [(World.root_found found).1] at declared
        exact Option.some.inj declared
      exact (AddressType.root_iff whole).mpr ⟨root,found,atType⟩
    | lent _ _ _ _ located => exact located
  obtain ⟨offset,atOffset⟩ := located
  exact ⟨⟨offset,atOffset⟩,World.stores_typed typed.roots stored,
    atOffset.stored_type valid inventory typed.roots stored⟩

/-- The persistent fact is derived from the real invocation binding, not
substituted for its stronger immediate post-bind location theorem. -/
theorem Kernel.BindsInputsFor.bindingStorageTypes {recipient : ClaimCustody} {footprint : List Address} {program : Kernel.Program} {before after : World}
    {activation scope region inputs bindings}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (bound : Kernel.BindsInputsFor program recipient activation scope region footprint before inputs bindings after) :
    ListRel (fun input binding => binding.key = input.formal.key ∧
      (input.formal.IsResident →
        Typing.BindingStorageTyped program.declarations after binding.address input.formal.type)) inputs bindings :=
  (bound.inputTypes valid inventory typed).imp (fun _ _ checked =>
    ⟨checked.1,fun resident => (checked.2 resident).1.bindingStorageTyped (checked.2 resident).2⟩)

theorem Kernel.BindsInputsFor.residentStorageTypes {recipient : ClaimCustody} {footprint : List Address}
    {program : Kernel.Program} {before after : World} {activation scope region inputs bindings}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (bound : Kernel.BindsInputsFor program recipient activation scope region footprint before inputs bindings after) :
    ListRel (fun localSlot binding => binding.key = .localSlot localSlot.id ∧
      Typing.BindingStorageTyped program.declarations after binding.address localSlot.type)
      (inputs.filterMap (fun input => input.formal.resident?)) bindings.locals := by
  apply ListRel.resident_inputs
  exact (bound.bindingStorageTypes valid inventory typed).imp (fun input binding pair =>
    ⟨pair.1,fun localSlot formal => by
      have resident : input.formal.IsResident := by simp [formal,Kernel.InputFormal.IsResident]
      exact ⟨by simpa only [formal,Kernel.InputFormal.key] using pair.1,
        by simpa only [formal,Kernel.InputFormal.type] using pair.2 resident⟩⟩)

theorem Kernel.BindsInputsFor.read_formal {recipient : ClaimCustody} {footprint : List Address} {program : Kernel.Program} {before after : World}
    {activation scope region inputs bindings}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (bound : Kernel.BindsInputsFor program recipient activation scope region footprint before inputs bindings after)
    {input : Kernel.InvocationInput} (member : input ∈ inputs) {binding : Kernel.Binding} {value : Value}
    (resident : input.formal.IsResident) (selected : bindings.SelectsKey input.formal.key binding)
    (stored : after.Stores binding.address value) :
    Typing.ValueTyped program after value ∧ value.type = input.formal.type := by
  obtain ⟨actual,present,identity,storage⟩ := (bound.bindingStorageTypes valid inventory typed).member_left member
  have same := selected.2.2 actual present identity
  subst actual
  exact ((storage resident).read valid inventory (bound.worldTyped valid inventory typed) stored).2

theorem World.root_types_of_locations {before after : World}
    (locations : ∀ id, (after.roots.get id).map Root.location = (before.roots.get id).map Root.location)
    (id : Identity) : (after.roots.get id).map Root.type = (before.roots.get id).map Root.type := by
  simpa only [Option.map_map,Function.comp_def,Root.location] using congrArg (Option.map Root.type) (locations id)

theorem Typing.BindingStorageTyped.roots_loans {program : Program} {before after : World}
    (roots : after.roots = before.roots) (loans : after.loans = before.loans)
    {address : Address} {type : Term} (binding : Typing.BindingStorageTyped program before address type) :
    Typing.BindingStorageTyped program after address type := by
  cases binding with
  | root whole declared => exact .root whole (by simpa only [roots] using declared)
  | lent found live referent referenced located =>
    exact .lent (by simpa only [loans] using found) live referent
      (referenced.roots_congr roots) (located.roots_congr roots)

theorem Typing.BindingStorageTyped.roots_retained {program : Program} {before after : World}
    (roots : after.roots = before.roots)
    (retained : ∀ identity original, before.loans.get identity = some original →
      ∃ current, after.loans.get identity = some current ∧ current.permissionState = original.permissionState)
    {address : Address} {type : Term} (binding : Typing.BindingStorageTyped program before address type) :
    Typing.BindingStorageTyped program after address type := by
  cases binding with
  | root whole declared => exact .root whole (by simpa only [roots] using declared)
  | lent found live referent referenced located =>
      exact (InvocationAddress.retained roots retained (Or.inr ⟨_,_,found,live,referent,referenced⟩)).bindingStorageTyped
        (located.roots_congr roots)

theorem Typing.BindingStorageTyped.nextOwner {program : Program} {world : World}
    {address : Address} {type : Term} (binding : Typing.BindingStorageTyped program world address type) (next : Identity) :
    Typing.BindingStorageTyped program { world with nextOwner := next } address type :=
  binding.roots_loans (before := world) (after := { world with nextOwner := next }) rfl rfl

theorem Allocates.bindingStorageTyped {program : Program} {before after : World}
    {home region type layout mutable address originBound} (valid : before.WellFormedWithOrigins originBound)
    (allocated : Allocates program before home region type layout mutable address after)
    {observed : Address} {expected : Term} (binding : Typing.BindingStorageTyped program before observed expected) :
    Typing.BindingStorageTyped program after observed expected := by
  cases binding with
  | root whole declared =>
    obtain ⟨root,found,atType⟩ := Option.map_eq_some_iff.mp declared
    exact .root whole (by rw [allocated.roots valid found]; exact congrArg some atType)
  | lent found live referent referenced located =>
    have loan : after.loans = before.loans := by cases allocated; rfl
    exact .lent (by simpa only [loan] using found) live referent
      (allocated.references valid referenced) (allocated.addressType valid located)

theorem Allocates.created_bindingStorageTyped {program : Program} {before after : World}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) :
    Typing.BindingStorageTyped program after address type := by
  cases allocated
  exact .root rfl (by rw [Table.get_set]; rfl)

theorem World.write_vacant_bindingStorageTyped {program : Program} {before after : World}
    {address : Address} {replacement : Option Value} (valid : before.WellFormed)
    (vacant : before.Vacant address) (written : before.write address replacement = some after)
    {observed : Address} {type : Term} (binding : Typing.BindingStorageTyped program before observed type) :
    Typing.BindingStorageTyped program after observed type := by
  cases binding with
  | root whole declared => exact .root whole (by rw [World.root_types_of_locations (World.write_locations written)]; exact declared)
  | lent found live referent referenced located =>
    refine .lent (by simpa only [World.write_loans written] using found) live referent
      (World.write_vacant_references vacant written referenced) ?_
    apply (World.write_address_types written ?_).mp located
    rw [← referent]
    exact vacant.no_located_descendant (World.liveLoanLocations valid _ _ found live)

theorem World.clear_nonreference_leaf_bindingStorageTyped {program : Program} {before after : World}
    {address : Address} {value : Value} {authority : Authority}
    (valid : before.WellFormed) (stored : before.Stores address value) (fields : value.fields = [])
    (notReference : ∀ id, value.head ≠ .reference id)
    (permission : Permitted before authority .owned address) (cleared : before.write address none = some after)
    {observed : Address} {type : Term} (binding : Typing.BindingStorageTyped program before observed type) :
    Typing.BindingStorageTyped program after observed type := by
  cases binding with
  | root whole declared =>
    exact .root whole (by rw [World.root_types_of_locations (World.write_locations cleared)]; exact declared)
  | lent found live referent referenced located =>
    refine .lent (by simpa only [World.write_loans cleared] using found) live referent
      (World.write_nonreference_leaf_references stored fields notReference cleared referenced) ?_
    apply (World.write_address_types cleared ?_).mp located
    rw [← referent]
    exact permission.owned_no_loan_descendant (World.loanParents valid) found live

theorem Transfers.bindingStorageTyped {program : RuntimeProgram} {before after : World}
    {authority source destination} (valid : before.WellFormed)
    (transferred : Transfers program before authority source destination after)
    {address : Address} {type : Term} (binding : Typing.BindingStorageTyped program.declarations before address type) :
    Typing.BindingStorageTyped program.declarations after address type := by
  cases binding with
  | root whole declared => exact .root whole (by rw [World.root_types_of_locations transferred.locations]; exact declared)
  | lent found live referent referenced located =>
    exact .lent (by simpa only [transferred.loans] using found) live referent (transferred.references referenced)
      (transferred.invocation_addressType valid (Or.inr ⟨_,_,found,live,referent,referenced⟩) located)

theorem FormsLoan.bindingStorageTyped {program : RuntimeProgram} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination} (valid : before.WellFormed)
    (borrowed : FormsLoan program purpose before authority mode region referent destination after)
    {address : Address} {type : Term} (binding : Typing.BindingStorageTyped program.declarations before address type) :
    Typing.BindingStorageTyped program.declarations after address type := by
  cases binding with
  | root whole declared =>
    refine .root whole ?_
    cases borrowed with
    | borrow _ _ _ _ _ _ _ _ _ _ written =>
      rw [World.root_types_of_locations (World.write_locations written)]
      exact declared
  | lent found live referent referenced located =>
    exact .lent (borrowed.old_loan valid found) live referent (borrowed.references referenced)
      (borrowed.invocation_addressType valid (Or.inr ⟨_,_,found,live,referent,referenced⟩) located)

theorem Copies.bindingStorageTyped {program : RuntimeProgram} {before after : World}
    {authority source destination} (valid : before.WellFormed)
    (copied : Copies program before authority source destination after)
    {address : Address} {type : Term} (binding : Typing.BindingStorageTyped program.declarations before address type) :
    Typing.BindingStorageTyped program.declarations after address type := by
  cases copied with
  | copy _ _ _ _ vacant _ _ written =>
    have retained := World.write_vacant_bindingStorageTyped valid vacant written binding
    cases retained with
    | root whole declared => exact .root whole declared
    | lent found live referent referenced located =>
      refine .lent found live referent (referenced.roots_congr rfl) ?_
      apply AddressType.roots_congr _ located
      rfl

theorem Acquires.bindingStorageTyped {program : RuntimeProgram} {before after : World}
    {authority force source destination} (valid : before.WellFormed)
    (acquired : Acquires program before authority force source destination after)
    {address : Address} {type : Term} (binding : Typing.BindingStorageTyped program.declarations before address type) :
    Typing.BindingStorageTyped program.declarations after address type := by
  cases acquired with
  | explicitMove moved => exact moved.bindingStorageTyped valid binding
  | copy copied => exact copied.bindingStorageTyped valid binding
  | move _ _ _ moved => exact moved.bindingStorageTyped valid binding

theorem NewValue.bindingStorageTyped {program : RuntimeProgram} {before after : World}
    {destination type head sources originBound} (valid : before.WellFormedWithOrigins originBound)
    (constructed : NewValue program before destination type head sources after)
    {address : Address} {expected : Term} (binding : Typing.BindingStorageTyped program.declarations before address expected) :
    Typing.BindingStorageTyped program.declarations after address expected := by
  cases binding with
  | root whole declared => exact .root whole (by rw [World.root_types_of_locations constructed.locations]; exact declared)
  | @lent id loan found live referent referenced located =>
    have loans := congrArg World.loans constructed.rest
    refine .lent (by simpa only [loans] using found) live referent (constructed.references referenced) ?_
    cases constructed with
    | construct vacant _ ready _ cleared written =>
      have outside : ∀ source ∈ sources.map ResolvedPlace.address, ¬ source.ProperPrefix address := by
        intro source member
        obtain ⟨actual,present,rfl⟩ := List.mem_map.mp member
        rw [← referent]
        exact (ready.2.2.2 actual present).owned_no_loan_descendant (World.loanParents valid) found live
      exact ((World.write_address_types written
        (vacant.no_located_descendant (referent ▸ World.liveLoanLocations valid id loan found live))).mp
          (cleared.address_type located outside)).retained (fun _ selected => selected) (fun _ => rfl)

theorem Kernel.LendsResident.bindingStorageTyped {program : RuntimeProgram} {before after : World}
    {activation scope region source authority access lease permission} (valid : before.WellFormed)
    (lent : Kernel.LendsResident program activation scope region before source authority access lease permission after)
    {address : Address} {type : Term} (binding : Typing.BindingStorageTyped program.declarations before address type) :
    Typing.BindingStorageTyped program.declarations after address type := by
  cases lent with
  | owned => exact binding
  | lent _ _ _ allocated borrowed =>
    exact borrowed.bindingStorageTyped (allocated.wellFormed valid) (allocated.bindingStorageTyped valid binding)

theorem Kernel.BindsInputAt.preserves_bindingStorageType {recipient : ClaimCustody} {program : RuntimeProgram} {before after : World}
    {activation scope region input result} (valid : before.WellFormed)
    (bound : Kernel.BindsInputAt program recipient activation scope region before input result after)
    {address : Address} {type : Term} (binding : Typing.BindingStorageTyped program.declarations before address type) :
    Typing.BindingStorageTyped program.declarations after address type := by
  cases bound with
  | lent _ _ _ _ _ _ _ lent => exact lent.bindingStorageTyped valid binding
  | owned _ _ _ _ _ allocated transferred =>
    exact transferred.bindingStorageTyped (allocated.wellFormed valid) (allocated.bindingStorageTyped valid binding)
  | storage _ _ _ claimed =>
    apply binding.roots_retained (by cases claimed; rfl)
    exact fun _ loan found => ⟨loan,claimed.old_loan valid found,rfl⟩
  | allocation _ _ _ _ transferred =>
    exact binding.roots_retained (by cases transferred; rfl) (fun _ _ found => transferred.retained found)
  | guardedAllocation _ _ _ _ _ claimed =>
    apply binding.roots_retained (by cases claimed; rfl)
    exact fun _ loan found => ⟨loan,claimed.old_loan valid found,rfl⟩
  | loan _ _ _ _ transferred =>
    exact binding.roots_retained (by cases transferred <;> rfl) (fun _ _ found => transferred.retained found)

theorem Kernel.BindsPattern.preserves_bindingStorageType {program : RuntimeProgram} {before after : World}
    {activation scope region localSlot source authority access result} (valid : before.WellFormed)
    (bound : Kernel.BindsPattern program activation scope region before localSlot source authority access result after)
    {address : Address} {type : Term} (binding : Typing.BindingStorageTyped program.declarations before address type) :
    Typing.BindingStorageTyped program.declarations after address type := by
  cases bound with
  | owned input => exact input.preserves_bindingStorageType valid binding
  | borrowed _ _ allocated borrowed =>
    exact borrowed.bindingStorageTyped (allocated.wellFormed valid) (allocated.bindingStorageTyped valid binding)

/-- Both owned and borrowed pattern locals get their actual allocated
storage type; borrowing creates an owned reference value, not an unguarded
alias of the pattern subject. -/
theorem Kernel.BindsPattern.bindingStorageType {program : Kernel.Program} {before after : World}
    {activation scope region localSlot source authority access binding}
    (typed : Typing.WorldTyped program before)
    (bound : Kernel.BindsPattern program activation scope region before localSlot source authority access binding after) :
    binding.key = .localSlot localSlot.id ∧
      Typing.BindingStorageTyped program.declarations after binding.address localSlot.type := by
  cases bound with
  | owned input =>
    have checked := input.inputType typed (by trivial)
    exact ⟨checked.1,checked.2.1.bindingStorageTyped checked.2.2⟩
  | borrowed _ _ allocated borrowed =>
    exact ⟨rfl,borrowed.bindingStorageTyped (allocated.wellFormed typed.1) allocated.created_bindingStorageTyped⟩

theorem Kernel.BindsInputsFor.preserves_bindingStorageType {recipient : ClaimCustody} {footprint : List Address} {program : Kernel.Program} {before after : World}
    {activation scope region inputs bindings}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (bound : Kernel.BindsInputsFor program recipient activation scope region footprint before inputs bindings after)
    {address : Address} {type : Term} (binding : Typing.BindingStorageTyped program.declarations before address type) :
    Typing.BindingStorageTyped program.declarations after address type := by
  induction bound using Kernel.BindsInputsFor.inductionOn with
  | nil => exact binding
  | cons _ first _ ih =>
    exact ih (first.worldTyped valid inventory typed) (first.preserves_bindingStorageType typed.1 binding)

theorem Execution.FinishesReceiver.bindingStorageTyped {program : Program} {before after : World}
    {receiver : ResolvedPlace} {access : Access}
    (finished : Execution.FinishesReceiver before receiver access after) (valid : before.WellFormed)
    {address : Address} {type : Term} (binding : Typing.BindingStorageTyped program before address type) :
    Typing.BindingStorageTyped program after address type := by
  cases finished with
  | lent => exact binding
  | owned stored _ head fields _ permission written =>
    cases binding with
    | root whole declared =>
      exact .root whole (by rw [World.root_types_of_locations (World.write_locations written)]; exact declared)
    | lent found live referent referenced located =>
      obtain ⟨identity,arguments,head⟩ := head
      refine .lent (by simpa only [World.write_loans written] using found) live referent
        (World.write_nonreference_shell_references stored fields
          (by intro key; rw [head]; exact ValueHead.noConfusion) written referenced) ?_
      apply (World.write_address_types written ?_).mp located
      rw [← referent]
      exact permission.owned_no_loan_descendant (World.loanParents valid) found live

theorem Execution.FinishesEntry.bindingStorageTyped {program : Program} {before after : World}
    {source : Execution.EntrySource} (finished : Execution.FinishesEntry before source after)
    (valid : before.WellFormed) {address : Address} {type : Term}
    (binding : Typing.BindingStorageTyped program before address type) :
    Typing.BindingStorageTyped program after address type := by
  cases finished with
  | supplied => exact binding
  | resident finished | contextual finished => exact finished.bindingStorageTyped valid binding

theorem Execution.Captures.bindingStorageTyped {program : Kernel.Program} {context : Execution.Context}
    {before after : World} {captures addresses}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (captured : Execution.Captures program context before captures addresses after)
    {address : Address} {type : Term} (binding : Typing.BindingStorageTyped program.declarations before address type) :
    Typing.BindingStorageTyped program.declarations after address type := by
  induction captured with
  | nil => exact binding
  | owned _ _ temporary acquired _ ih =>
    obtain ⟨_,allocated⟩ := temporary
    have middle := allocated.worldTyped typed
    exact ih (acquired.worldTyped valid inventory middle)
      (acquired.bindingStorageTyped middle.1 (allocated.bindingStorageTyped typed.1 binding))
  | borrowed _ _ _ temporary borrowed _ ih =>
    obtain ⟨_,allocated⟩ := temporary
    have middle := allocated.worldTyped typed
    exact ih (borrowed.worldTyped valid inventory middle)
      (borrowed.bindingStorageTyped middle.1 (allocated.bindingStorageTyped typed.1 binding))

/-- Every actual atomic transition preserves declared local storage, including
empty old capture slots and the fresh initializer destination. -/
theorem Execution.AtomStep.bindingStorageTyped {program : Kernel.Program} {before after : Execution.State} {event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (step : Execution.AtomStep program before event after)
    {address : Address} {type : Term} (binding : Typing.BindingStorageTyped program.declarations before.world address type) :
    Typing.BindingStorageTyped program.declarations after.world address type := by
  cases step with
  | constant _ _ destination written =>
    exact (World.write_vacant_bindingStorageTyped typed.1 destination.vacant written binding).nextOwner _
  | acquire _ _ acquired => exact acquired.bindingStorageTyped typed.1 binding
  | borrow _ _ borrowed => exact borrowed.bindingStorageTyped typed.1 binding
  | construct _ _ _ _ _ constructed => exact constructed.bindingStorageTyped typed.1 binding
  | closure _ _ captures _ _ constructed =>
    exact constructed.bindingStorageTyped (captures.worldTyped valid inventory typed).1
      (captures.bindingStorageTyped valid inventory typed binding)
  | function _ _ _ _ constructed => exact constructed.bindingStorageTyped typed.1 binding
  | operation _ _ constructed => exact constructed.bindingStorageTyped typed.1 binding
  | label _ _ _ constructed => exact constructed.bindingStorageTyped typed.1 binding
  | primitive => exact binding

theorem Retires.root_types {before after : World} {id : Identity}
    (retired : Retires before id after) (observed : Identity) :
    (after.roots.get observed).map Root.type = (before.roots.get observed).map Root.type := by
  cases retired with
  | vacant found _ _ _ =>
    by_cases same : observed = id
    · subst observed
      rw [Table.get_set,found]
      rfl
    · rw [Table.get_set_other _ _ _ _ same]

theorem Retires.addressType {program : Program} {before after : World} {id : Identity}
    (retired : Retires before id after) {address : Address} {type : Term}
    (different : address.root ≠ id) (located : AddressType program before address type) :
    AddressType program after address type := by
  obtain ⟨offset,located⟩ := located
  refine ⟨offset,?_⟩
  induction located with
  | root found live => exact .root (by rw [retired.roots_other different]; exact found) live
  | child _ field ih => exact .child (ih different) (field.transport (by rw [retired.read]))

theorem Retires.bindingStorageTyped {program : Program} {before after : World} {id : Identity}
    (retired : Retires before id after) {address : Address} {type : Term}
    (binding : Typing.BindingStorageTyped program before address type) :
    Typing.BindingStorageTyped program after address type := by
  cases binding with
  | root whole declared => exact .root whole (by rw [retired.root_types]; exact declared)
  | lent found live referent referenced located =>
    have safe : CanEndStorage before id := by cases retired; assumption
    have loans : after.loans = before.loans := by cases retired; rfl
    exact .lent (by simpa only [loans] using found) live referent (retired.references referenced)
      (retired.addressType (referent ▸ safe.1 _ _ found live) located)

/-- Release consumes only loans without resident handles. The same actual
guard carried by a lent binding therefore rules out ending its own loan. -/
theorem EndsLoan.bindingStorageTyped {program : RuntimeProgram} {before after : World} {id : Identity}
    (ended : EndsLoan program before id after) {address : Address} {type : Term}
    (binding : Typing.BindingStorageTyped program.declarations before address type) :
    Typing.BindingStorageTyped program.declarations after address type := by
  have roots : after.roots = before.roots := by cases ended; rfl
  cases binding with
  | root whole declared => exact .root whole (by simpa only [roots] using declared)
  | lent found live referent referenced located =>
    have guarded : InvocationAddress before address := Or.inr ⟨_,_,found,live,referent,referenced⟩
    exact InvocationAddress.bindingStorageTyped (guarded.endsLoan ended) (located.roots_congr roots)

theorem ReturnsStorageLoan.bindingStorageTyped {program : Program} {before after : World} {id : Identity}
    (returned : ReturnsStorageLoan before id after) {address : Address} {type : Term}
    (binding : Typing.BindingStorageTyped program before address type) :
    Typing.BindingStorageTyped program after address type := by
  cases returned with
  | returned _ _ _ _ absent _ =>
    cases binding with
    | root whole declared => exact .root whole declared
    | @lent key loan found live referent referenced located =>
      have different : key ≠ id := fun same => absent (same ▸ referenced)
      refine .lent (by rw [Table.get_set_other _ _ _ _ different]; exact found) live referent
        (referenced.roots_congr rfl) ?_
      apply AddressType.roots_congr _ located
      rfl

theorem Execution.RetiresEmpty.bindingStorageTyped {program : Program} {before after : World}
    {retired : List Address} (disposed : Execution.RetiresEmpty before retired after)
    {address : Address} {type : Term} (binding : Typing.BindingStorageTyped program before address type) :
    Typing.BindingStorageTyped program after address type := by
  induction disposed with
  | nil => exact binding
  | cons _ retired _ ih => exact ih (retired.bindingStorageTyped binding)

end Glorious.Language
