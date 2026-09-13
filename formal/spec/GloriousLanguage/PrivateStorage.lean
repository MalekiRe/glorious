import GloriousLanguage.ForeignAuthority
import GloriousLanguage.ControlStorageOrigin

/-! The saved destructor handle is made private by actual temporary allocation,
borrowing and ordinary owned-input binding. These are entry facts, not
post-return certificates or an alternate invocation evaluator. -/
namespace Glorious.Language

/-- A proof view of one actual vacant internal slot. The current control
proof, not this storage predicate, establishes that executable operands omit
its identity. Exact root retention preserves generation, home and liveness. -/
structure World.PrivateSlot (world : World) (id : Identity) (root : Root) : Prop where
  found : world.roots.get id = some root
  vacant : root.value = none
  safe : CanEndStorage world id
  internalHome : Foreign.InternalHome root

theorem World.PrivateSlot.bound {world : World} {id : Identity} {root : Root}
    (slot : world.PrivateSlot id root) (well : world.WellFormed) : id < world.nextRoot :=
  World.root_bound well slot.found

theorem World.PrivateSlot.stored_outside {world : World} {id : Identity} {root : Root}
    (slot : world.PrivateSlot id root) {address : Address} {value : Value}
    (stored : world.Stores address value) : address.root ≠ id := by
  intro same
  obtain ⟨other,whole,found,_,_,resident,_⟩ := World.resident_iff_stores.mpr stored
  have equal := Option.some.inj (found.symm.trans (same ▸ slot.found))
  subst other
  rw [slot.vacant] at resident
  cases resident

theorem World.PrivateSlot.transport {before after : World} {id : Identity} {root : Root}
    (slot : before.PrivateSlot id root) (roots : after.roots.get id = before.roots.get id)
    (safe : CanEndStorage after id) : after.PrivateSlot id root :=
  ⟨roots.trans slot.found,slot.vacant,safe,slot.internalHome⟩

theorem World.PrivateSlot.write {before after : World} {id : Identity} {root : Root}
    {address : Address} {value : Option Value} (slot : before.PrivateSlot id root)
    (written : before.write address value = some after) (outside : address.root ≠ id) :
    after.PrivateSlot id root :=
  slot.transport (World.write_roots_other written outside.symm) (World.write_canEndStorage written slot.safe)

theorem World.PrivateSlot.loan_set {world : World} {id key nextLoan : Identity} {root : Root} {loan : Loan}
    (slot : world.PrivateSlot id root) (outside : loan.live = true → loan.referent.root ≠ id) :
    ({ world with loans := world.loans.set key loan, nextLoan := nextLoan } : World).PrivateSlot id root := by
  refine ⟨slot.found,slot.vacant,⟨?_,slot.safe.2⟩,slot.internalHome⟩
  intro actual entry found live
  by_cases same : actual = key
  · subst actual
    have equal := Option.some.inj (found.symm.trans (Table.get_set _ _ _))
    subst entry
    exact outside live
  · exact slot.safe.1 actual entry (by simpa only [Table.get_set_other _ _ _ _ same] using found) live

theorem World.PrivateSlot.availability_set {world : World} {id key : Identity} {root : Root}
    {available : Availability} (slot : world.PrivateSlot id root)
    (outside : available.active = true → ∀ place ∈ available.reserved, place.address.root ≠ id) :
    ({ world with availability := world.availability.set key available } : World).PrivateSlot id root := by
  refine ⟨slot.found,slot.vacant,⟨slot.safe.1,?_,slot.safe.2.2⟩,slot.internalHome⟩
  intro actual entry found active place member
  by_cases same : actual = key
  · subst actual
    have equal := Option.some.inj (found.symm.trans (Table.get_set _ _ _))
    subst entry
    exact outside active place member
  · exact slot.safe.2.1 actual entry
      (by simpa only [Table.get_set_other _ _ _ _ same] using found) active place member

theorem ClaimsStorage.private_slot {custody : ClaimCustody} {before after : World}
    {authority : Authority} {access : Access} {address : Address} {loan id : Identity} {root : Root}
    (claimed : ClaimsStorage custody before authority access address loan after)
    (slot : before.PrivateSlot id root) (outside : address.root ≠ id) : after.PrivateSlot id root := by
  cases claimed
  exact slot.loan_set (fun _ => outside)

theorem ClaimsAllocation.private_slot {custody : ClaimCustody} {before after : World}
    {authority : Authority} {address : Address} {loan id : Identity} {root : Root}
    (claimed : ClaimsAllocation custody before authority address loan after)
    (slot : before.PrivateSlot id root) (outside : address.root ≠ id) : after.PrivateSlot id root := by
  cases claimed
  exact slot.loan_set (fun _ => outside)

theorem TransfersAllocation.private_slot {recipient : ClaimCustody} {before after : World}
    {place : ResolvedPlace} {id : Identity} {root : Root}
    (moved : TransfersAllocation recipient before place after) (slot : before.PrivateSlot id root) :
    after.PrivateSlot id root := by
  cases moved with
  | transfer _ _ found =>
    have prior := slot.safe.1 _ _ found
    exact slot.loan_set prior

theorem TransfersStorageLoan.private_slot {recipient : ClaimCustody} {before after : World}
    {place : ResolvedPlace} {id : Identity} {root : Root}
    (moved : TransfersStorageLoan recipient before place after) (slot : before.PrivateSlot id root) :
    after.PrivateSlot id root := by
  cases moved with
  | unique _ found _ _ _ _ =>
    have prior := slot.safe.1 _ _ found
    exact slot.loan_set prior
  | shared => exact slot


theorem Allocates.canEndStorage {program : Program} {before after : World}
    {home region type layout mutable address}
    (well : before.WellFormed) (allocated : Allocates program before home region type layout mutable address after)
    (released : ∀ suspension, home ≠ .suspended suspension) :
    CanEndStorage after address.root := by
  cases allocated
  refine ⟨fun _ _ found live => Nat.ne_of_lt (World.live_loan_root_bound well found live),
    fun _ _ found active _ member => Nat.ne_of_lt (World.reserved_root_bound well found active member),?_⟩
  intro root found suspension
  simp only [Table.get_set,Option.some.injEq] at found
  subst root
  exact released suspension

theorem Allocates.preserves_canEndStorage {program : Program} {before after : World}
    {home region type layout mutable address} {id : Identity}
    (allocated : Allocates program before home region type layout mutable address after)
    (safe : CanEndStorage before id) (bound : id < before.nextRoot) : CanEndStorage after id := by
  apply safe.sameHomes (after := after)
  · cases allocated
    rw [Table.get_set_other _ _ _ _ (Nat.ne_of_lt bound)]
  · exact allocated.loans
  · cases allocated; rfl

theorem FormsLoan.canEndStorage {program : RuntimeProgram} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent handle} {id : Identity}
    (borrowed : FormsLoan program purpose before authority mode region referent handle after)
    (safe : CanEndStorage before id) (separate : referent.root ≠ id) : CanEndStorage after id := by
  cases borrowed with
  | borrow _ _ _ _ _ _ _ _ _ _ written =>
    refine ⟨?_,?_,?_⟩
    · intro key loan found live
      by_cases fresh : key = before.nextLoan
      · subst key
        have equal := Option.some.inj (found.symm.trans (Table.get_set _ _ _))
        exact equal ▸ separate
      · exact safe.1 key loan (by simpa only [Table.get_set_other _ _ _ _ fresh] using found) live
    · intro key available found active place member
      have unchanged := congrArg World.availability (World.write_rest written)
      exact safe.2.1 key available (by simpa only [unchanged] using found) active place member
    · exact (World.write_canEndStorage written safe).2.2

theorem Transfers.canEndStorage {program : RuntimeProgram} {before after : World}
    {authority source destination} {id : Identity}
    (moved : Transfers program before authority source destination after) (safe : CanEndStorage before id) :
    CanEndStorage after id := by
  cases moved with
  | move _ _ _ _ _ _ _ cleared written => exact World.write_canEndStorage written (World.write_canEndStorage cleared safe)

theorem Allocates.private_slot {program : Program} {before after : World} {id : Identity} {root : Root}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after)
    (bound : id < before.nextRoot) (slot : before.PrivateSlot id root) : after.PrivateSlot id root :=
  slot.transport (allocated.roots_other bound) (allocated.preserves_canEndStorage slot.safe bound)

theorem Allocates.fresh_avoids {program : Program} {before after : World} {id : Identity}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after)
    (bound : id < before.nextRoot) : address.root ≠ id := by
  cases allocated
  exact (Nat.ne_of_lt bound).symm

theorem FormsLoan.private_slot {program : RuntimeProgram} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent handle} {id : Identity} {root : Root}
    (borrowed : FormsLoan program purpose before authority mode region referent handle after)
    (slot : before.PrivateSlot id root) (outside : handle.root ≠ id) : after.PrivateSlot id root := by
  have sourceOutside : referent.root ≠ id := by
    cases borrowed with
    | borrow stored _ _ _ _ _ _ _ _ _ => exact slot.stored_outside stored
  exact slot.transport (borrowed.roots_other outside.symm) (borrowed.canEndStorage slot.safe sourceOutside)

theorem Transfers.private_slot {program : RuntimeProgram} {before after : World} {authority source destination}
    {id : Identity} {root : Root} (moved : Transfers program before authority source destination after)
    (slot : before.PrivateSlot id root) (outside : destination.root ≠ id) : after.PrivateSlot id root := by
  have sourceOutside : source.root ≠ id := by
    cases moved with
    | move stored _ _ _ _ _ _ _ => exact slot.stored_outside stored
  exact slot.transport (moved.roots_other sourceOutside.symm outside.symm) (moved.canEndStorage slot.safe)

theorem Copies.private_slot {program : RuntimeProgram} {before after : World} {authority source destination}
    {id : Identity} {root : Root} (copied : Copies program before authority source destination after)
    (slot : before.PrivateSlot id root) (outside : destination.root ≠ id) : after.PrivateSlot id root := by
  cases copied with
  | copy _ _ _ _ _ _ _ written =>
    have current := slot.write written outside
    exact ⟨current.found,current.vacant,current.safe,current.internalHome⟩

theorem Acquires.wellFormed {program : RuntimeProgram} {before after : World} {authority force source destination}
    (acquired : Acquires program before authority force source destination after)
    (well : before.WellFormed) : after.WellFormed := by
  cases acquired with
  | explicitMove moved | move _ _ _ moved => exact Transfers.wellFormed well moved
  | copy copied => exact Copies.wellFormed well copied

theorem Acquires.private_slot {program : RuntimeProgram} {before after : World} {authority force source destination}
    {id : Identity} {root : Root} (acquired : Acquires program before authority force source destination after)
    (slot : before.PrivateSlot id root) (outside : destination.root ≠ id) : after.PrivateSlot id root := by
  cases acquired with
  | explicitMove moved | move _ _ _ moved => exact moved.private_slot slot outside
  | copy copied => exact copied.private_slot slot outside

theorem Clears.private_slot {before after : World} {addresses : List Address} {id : Identity} {root : Root}
    (cleared : Clears before addresses after) (slot : before.PrivateSlot id root)
    (outside : ∀ address ∈ addresses, address.root ≠ id) : after.PrivateSlot id root := by
  induction cleared with
  | nil => exact slot
  | cons first _ ih =>
    exact ih (slot.write first (outside _ List.mem_cons_self))
      (fun _ member => outside _ (List.mem_cons_of_mem _ member))

theorem NewValue.private_slot {program : RuntimeProgram} {before after : World} {destination type head sources}
    {id : Identity} {root : Root} (created : NewValue program before destination type head sources after)
    (slot : before.PrivateSlot id root) (outside : destination.root ≠ id) : after.PrivateSlot id root := by
  cases created with
  | construct _ _ values _ cleared written =>
    have sourcesOutside : ∀ address ∈ sources.map ResolvedPlace.address, address.root ≠ id := by
      intro address member
      obtain ⟨source,present,rfl⟩ := List.mem_map.mp member
      obtain ⟨value,_,stored⟩ := values.1.member_left present
      exact slot.stored_outside stored
    have current := (cleared.private_slot slot sourcesOutside).write written outside
    exact ⟨current.found,current.vacant,current.safe,current.internalHome⟩

theorem Retires.private_slot {before after : World} {target id : Identity} {root : Root}
    (retired : Retires before target after) (slot : before.PrivateSlot id root) (outside : target ≠ id) :
    after.PrivateSlot id root := by
  apply slot.transport (retired.roots_other outside.symm)
  apply slot.safe.sameHomes
  · rw [retired.roots_other outside.symm]
  · cases retired; rfl
  · cases retired; rfl

theorem EndsLoan.private_slot {program : RuntimeProgram} {before after : World} {loan id : Identity} {root : Root}
    (ended : EndsLoan program before loan after) (slot : before.PrivateSlot id root) : after.PrivateSlot id root := by
  apply slot.transport
  · cases ended; rfl
  · exact ended.releaseFrame.canEndStorage slot.safe

/-- Moving an entire source root to distinct storage retains the source's
location and leaves its exact value slot empty. -/
theorem Transfers.source_root {program : RuntimeProgram} {before after : World}
    {authority : Authority} {source destination : Address} {root : Root}
    (moved : Transfers program before authority source destination after)
    (whole : source.fields = []) (selected : before.root source = some root)
    (separate : destination.root ≠ source.root) :
    after.roots.get source.root = some { root with value := none } := by
  cases moved with
  | @move value cleared _ _ _ _ _ _ _ _ empty filled =>
    have clearedAt : cleared = { before with roots := before.roots.set source.root { root with value := none } } := by
      simpa [World.write,selected,whole] using empty.symm
    obtain ⟨_,_,_,result⟩ := World.write_value_update filled
    rw [result,Table.get_set_other _ _ _ _ separate.symm,clearedAt]
    exact Table.get_set _ _ _

namespace Kernel

theorem ResolvesPlace.avoids_root {world : World} {environment : Environment}
    {place : Place} {address : Address} {authority : Authority} {id : Identity}
    (resolved : ResolvesPlace world environment place address authority)
    (outside : ∀ binding ∈ environment, binding.address.root ≠ id) (safe : CanEndStorage world id) :
    address.root ≠ id := by
  cases resolved with
  | localSlot selected projections => exact projections.avoids_root (outside _ selected.1) safe.1

theorem LendsResident.private_slot {program : RuntimeProgram} {before after : World}
    {activation scope region address authority access lease permission} {id : Identity} {root : Root}
    (lent : LendsResident program activation scope region before address authority access lease permission after)
    (well : before.WellFormed) (slot : before.PrivateSlot id root) : after.PrivateSlot id root := by
  cases lent with
  | owned => exact slot
  | lent _ _ _ allocated borrowed =>
    have outside := allocated.fresh_avoids (slot.bound well)
    exact borrowed.private_slot (allocated.private_slot (slot.bound well) slot) outside

theorem BindsInputAt.private_slot {program : RuntimeProgram} {recipient : ClaimCustody} {before after : World}
    {activation scope region input binding} {id : Identity} {root : Root}
    (bound : BindsInputAt program recipient activation scope region before input binding after)
    (well : before.WellFormed) (slot : before.PrivateSlot id root) (sourceOutside : input.storage.root ≠ id) :
    after.PrivateSlot id root ∧ binding.address.root ≠ id := by
  cases bound with
  | lent _ _ _ _ _ _ _ lent => exact ⟨lent.private_slot well slot,sourceOutside⟩
  | owned _ _ _ _ _ allocated transferred =>
    have outside := allocated.fresh_avoids (slot.bound well)
    exact ⟨transferred.private_slot (allocated.private_slot (slot.bound well) slot) outside,outside⟩
  | storage _ _ _ claimed | guardedAllocation _ _ _ _ _ claimed =>
    exact ⟨claimed.private_slot slot sourceOutside,sourceOutside⟩
  | allocation _ _ _ _ moved | loan _ _ _ _ moved => exact ⟨moved.private_slot slot,sourceOutside⟩

/-- Every input kind preserves an omitted private slot. Erased ports need the
actual source footprint: unlike residents, they may name vacant storage. -/
theorem BindsInputsAttemptFor.private_slot {program : RuntimeProgram} {recipient : ClaimCustody}
    {footprint : List Address} {before after : World} {activation scope region inputs bindings}
    {outcome : PreparationOutcome} {id : Identity} {root : Root}
    (bound : BindsInputsAttemptFor program recipient activation scope region footprint before inputs bindings after outcome)
    (well : before.WellFormed) (slot : before.PrivateSlot id root)
    (outside : ∀ input ∈ inputs, input.storage.root ≠ id) :
    after.PrivateSlot id root ∧ ∀ binding ∈ bindings, binding.address.root ≠ id := by
  induction bound with
  | nil | exhausted => exact ⟨slot,by simp⟩
  | cons _ first _ ih =>
    obtain ⟨middle,firstOutside⟩ := first.private_slot well slot (outside _ List.mem_cons_self)
    obtain ⟨finish,restOutside⟩ := ih (first.wellFormed well) middle
      (fun input member => outside input (List.mem_cons_of_mem _ member))
    refine ⟨finish,?_⟩
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact firstOutside
    · exact restOutside binding member

theorem BindsPattern.private_slot {program : RuntimeProgram} {before after : World}
    {activation scope region localSlot source authority access binding} {id : Identity} {root : Root}
    (bound : BindsPattern program activation scope region before localSlot source authority access binding after)
    (well : before.WellFormed) (slot : before.PrivateSlot id root) :
    after.PrivateSlot id root ∧ binding.address.root ≠ id := by
  cases bound with
  | owned bound =>
    obtain ⟨value,stored,_⟩ := bound.ready
    exact bound.private_slot well slot (slot.stored_outside stored)
  | borrowed _ _ allocated borrowed =>
    have outside := allocated.fresh_avoids (slot.bound well)
    exact ⟨borrowed.private_slot (allocated.private_slot (slot.bound well) slot) outside,outside⟩

/-- The common owned binder moves the original handle to a fresh callee slot;
it does not leave a second copy in the caller or hand that original slot to
the callee environment. -/
theorem BindsInputAt.owned_private_root {program : RuntimeProgram} {recipient : ClaimCustody} {before after : World}
    {activation scope region : Identity} {input : InvocationInput} {binding : Binding} {root : Root}
    (well : before.WellFormed)
    (bound : BindsInputAt program recipient activation scope region before input binding after)
    (resident : input.formal.IsResident) (owned : input.access = .owned) (whole : input.storage.fields = [])
    (selected : before.root input.storage = some root) (safe : CanEndStorage before input.storage.root) :
    after.roots.get input.storage.root = some { root with value := none } ∧
      CanEndStorage after input.storage.root ∧ binding.address.root ≠ input.storage.root := by
  cases bound with
  | lent _ borrowed _ _ _ _ _ _ => exact False.elim (borrowed owned)
  | storage _ formal _ _ | allocation _ formal _ _ _ | guardedAllocation _ formal _ _ _ _ | loan _ formal _ _ _ =>
    simp only [formal,InputFormal.IsResident] at resident
  | owned _ _ _ _ _ allocation transferred =>
    have originalBound := World.root_bound well (World.root_found selected).1
    have separate := allocation.fresh_avoids originalBound
    have beforeSafe := allocation.preserves_canEndStorage safe originalBound
    exact ⟨transferred.source_root whole (allocation.root well selected) separate,
      transferred.canEndStorage beforeSafe,separate⟩

end Kernel

namespace Execution

theorem FreshRegion.private_slot {before after : World} {region id : Identity} {root : Root}
    (fresh : FreshRegion before region after) (slot : before.PrivateSlot id root) : after.PrivateSlot id root := by
  rw [fresh.2]
  exact ⟨slot.found,slot.vacant,slot.safe,slot.internalHome⟩

theorem Temporary.private_slot {program : Kernel.Program} {context : Context} {before after : World}
    {type : Term} {address : Address} {id : Identity} {root : Root}
    (allocated : Temporary program context type before address after)
    (well : before.WellFormed) (slot : before.PrivateSlot id root) : after.PrivateSlot id root :=
  allocated.choose_spec.private_slot (slot.bound well) slot

theorem Protect.private_slot {program : Kernel.Program} {context : Context} {before after : World}
    {source destination : Address} {authority : Authority} {id : Identity} {root : Root}
    (kept : Protect program context before source authority destination after)
    (well : before.WellFormed) (slot : before.PrivateSlot id root) :
    after.PrivateSlot id root ∧ destination.root ≠ id := by
  obtain ⟨_,_,_,allocated,transferred⟩ := kept
  have outside : destination.root ≠ id := by
    obtain ⟨_,allocated⟩ := allocated
    cases allocated
    exact (Nat.ne_of_lt (slot.bound well)).symm
  exact ⟨transferred.private_slot (allocated.private_slot well slot) outside,outside⟩

theorem ConsumesReceiver.private_slot {before after : World} {address authority access}
    {id : Identity} {root : Root} (consumed : ConsumesReceiver before address authority access after)
    (slot : before.PrivateSlot id root) : after.PrivateSlot id root := by
  cases consumed with
  | lent _ => exact slot
  | owned stored _ _ _ written => exact slot.write written (slot.stored_outside stored)

theorem ConsumesAvailability.private_slot {before after : World} {address : Address} {authority : Authority}
    {key : Identity} {access : Access} {id : Identity} {root : Root}
    (consumed : ConsumesAvailability before address authority key access after)
    (slot : before.PrivateSlot id root) : after.PrivateSlot id root := by
  cases consumed with
  | lent _ => exact slot
  | owned stored _ _ _ _ _ written =>
    exact (slot.write written (slot.stored_outside stored)).availability_set (by simp)

theorem FinishesReceiver.private_slot {before after : World} {receiver : ResolvedPlace} {access : Access}
    {id : Identity} {root : Root} (finished : FinishesReceiver before receiver access after)
    (slot : before.PrivateSlot id root) : after.PrivateSlot id root := by
  cases finished with
  | lent => exact slot
  | owned stored _ _ _ _ _ written => exact slot.write written (slot.stored_outside stored)

theorem FinishesEntry.private_slot {before after : World} {source : EntrySource} {id : Identity} {root : Root}
    (finished : FinishesEntry before source after) (slot : before.PrivateSlot id root) : after.PrivateSlot id root := by
  cases finished with
  | supplied => exact slot
  | resident inner | contextual inner => exact inner.private_slot slot

theorem PreparesEntryAttempt.private_slot {program : Kernel.Program} {context : Context} {function : Kernel.Function}
    {before after : World} {source : EntrySource} {inputs : List Kernel.InvocationInput}
    {outcome : Kernel.PreparationOutcome} {id : Identity} {root : Root}
    (prepared : PreparesEntryAttempt program context function before source inputs after outcome)
    (well : before.WellFormed) (slot : before.PrivateSlot id root) : after.PrivateSlot id root := by
  cases prepared with
  | supplied | residentExhausted | contextualReceiverExhausted => exact slot
  | resident _ _ lent _ consumed => exact consumed.private_slot (lent.private_slot well slot)
  | contextual _ _ _ _ receiver witness _ consumed finished =>
    exact finished.private_slot (consumed.private_slot
      (witness.private_slot (receiver.wellFormed well) (receiver.private_slot well slot)))
  | contextualWitnessExhausted _ _ _ _ lent _ => exact lent.private_slot well slot

theorem EntrySource.original_input_root {source : EntrySource} {function : Kernel.Function} {input : Kernel.InvocationInput}
    (member : input ∈ source.originalInputs function) : input.storage.root ∈ source.rootSupport := by
  cases source with
  | supplied inputs => exact List.mem_flatMap.mpr ⟨input,member,by simp [Kernel.InvocationInput.rootSupport]⟩
  | contextual receiver access witness witnessAccess inputs =>
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_flatMap.mpr ⟨input,member,by simp [Kernel.InvocationInput.rootSupport]⟩))
  | resident receiver access inputs =>
    rcases List.mem_append.mp member with capture | argument
    · obtain ⟨⟨formal,index⟩,_,rfl⟩ := List.mem_map.mp capture
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨input,argument,by simp [Kernel.InvocationInput.rootSupport]⟩)

theorem PreparesEntry.inputs_avoid_root {program : Kernel.Program} {context : Context} {function : Kernel.Function}
    {before after : World} {source : EntrySource} {inputs : List Kernel.InvocationInput} {id : Identity}
    (prepared : PreparesEntry program context function before source inputs after)
    (outside : id ∉ source.rootSupport) : ∀ input ∈ inputs, input.storage.root ≠ id := by
  intro input member same
  have present : input.storage.root ∈ inputs.map (fun input => input.storage.root) := List.mem_map.mpr ⟨input,member,rfl⟩
  rw [prepared.map_inputs (fun input => input.storage.root) (by intros; rfl)] at present
  obtain ⟨original,originalMember,equal⟩ := List.mem_map.mp present
  exact outside ((equal.trans same) ▸ EntrySource.original_input_root originalMember)

theorem EnterWorldAttempt.private_slot {program : Kernel.Program} {before : State} {after : World}
    {caller context : Context} {function : Kernel.Function} {source : EntrySource} {outcome : Kernel.PreparationOutcome}
    {id : Identity} {root : Root}
    (attempted : EnterWorldAttempt program before caller function source context after outcome)
    (well : before.world.WellFormed) (slot : before.world.PrivateSlot id root) (outside : id ∉ source.rootSupport) :
    after.PrivateSlot id root ∧ id ∉ context.rootSupport := by
  cases attempted with
  | inputs _ fresh prepares _ bound finish contextEq _ =>
    obtain ⟨boundSlot,bindings⟩ := bound.private_slot (prepares.wellFormed (fresh.wellFormed well))
      (prepares.private_slot (fresh.wellFormed well) (FreshRegion.private_slot fresh slot)) (prepares.inputs_avoid_root outside)
    have contextOutside : id ∉ context.rootSupport := by
      rw [contextEq]
      simp only [Context.rootSupport,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.mem_append,not_or]
      constructor <;> intro member <;>
        obtain ⟨binding,present,same⟩ := List.mem_map.mp member <;>
        exact bindings binding present same
    refine ⟨?_,contextOutside⟩
    cases outcome with
    | complete => exact finish.private_slot boundSlot
    | exhausted => rw [finish]; exact boundSlot
  | preparationExhausted _ fresh prepares contextEq _ =>
    exact ⟨prepares.private_slot (fresh.wellFormed well) (FreshRegion.private_slot fresh slot),
      by simp [contextEq,Context.rootSupport]⟩

/-- The hook's temporary root has no incoming live loans or reservations.
The newly formed loan names Self, not the fresh reference-handle root. -/
theorem Temporary.borrowed_handle_private {program : Kernel.Program} {before allocated after : World}
    {context : Context} {value : Value} {address handle : Address} {authority : Authority}
    (well : before.WellFormed) (stored : before.Stores address value)
    (temporary : Temporary program context (.reference .unique (.runtimeRegion context.region) value.type)
      before handle allocated)
    (borrowed : Borrows program allocated authority .unique context.region address handle after) :
    ∃ root, after.root handle = some root ∧ root.home = .temporary context.activation context.scope ∧
      handle.fields = [] ∧ CanEndStorage after handle.root := by
  obtain ⟨layout,allocation⟩ := temporary
  obtain ⟨root,selected,home,_,whole⟩ := allocation.new_root
  obtain ⟨changed,found,location⟩ := World.root_transport borrowed.locations selected
  have addressBound : address.root < before.nextRoot := by
    obtain ⟨root,found⟩ := (Option.bind_eq_some_iff.mp stored).imp fun _ selected => selected.1
    exact World.root_bound well (World.root_found found).1
  have fresh : handle.root = before.nextRoot := by cases allocation; rfl
  have separate : address.root ≠ handle.root := fresh.symm ▸ Nat.ne_of_lt addressBound
  refine ⟨changed,found,?_,whole,borrowed.canEndStorage (allocation.canEndStorage well (by intros; simp)) separate⟩
  have same : changed.home = root.home := by simpa [Root.location] using congrArg Root.home location
  exact same.trans home

/-- The actual ordinary supplied entry consumes the single owned hook input.
Its saved caller slot is empty and private before the body starts. -/
theorem EnterWorld.owned_handle_private {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Kernel.Function} {input : Kernel.InvocationInput} {root : Root}
    (typed : Typing.WorldTyped program before.world)
    (entered : EnterWorld program before caller function (.supplied [input]) callee after)
    (resident : input.formal.IsResident)
    (owned : input.access = .owned) (whole : input.storage.fields = [])
    (selected : before.world.root input.storage = some root) (safe : CanEndStorage before.world input.storage.root) :
    after.roots.get input.storage.root = some { root with value := none } ∧
      CanEndStorage after input.storage.root ∧
      (∀ binding ∈ callee.environment, binding.address.root ≠ input.storage.root) := by
  obtain ⟨withRegion,prepared,inputs,environment,declaration,boundWorld,selectedFunction,fresh,preparation,incoming,bound,finished,context,unsafeOk⟩ := entered.prepared
  cases preparation
  cases finished
  cases bound with
  | cons _ first rest =>
    cases rest
    have selectedRegion : withRegion.root input.storage = some root := by rw [fresh.2]; exact selected
    have safeRegion : CanEndStorage withRegion input.storage.root := by rw [fresh.2]; exact safe
    obtain ⟨vacant,privateRoot,outside⟩ := first.owned_private_root (fresh.worldTyped typed).1 resident owned whole selectedRegion safeRegion
    refine ⟨vacant,privateRoot,?_⟩
    rw [context]
    intro binding member
    simp only [List.mem_singleton] at member
    exact member ▸ outside

end Execution
end Glorious.Language
