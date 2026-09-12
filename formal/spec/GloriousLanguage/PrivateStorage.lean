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

theorem FormsLoan.canEndStorage {program : Program} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent handle} {id : Identity}
    (borrowed : FormsLoan program purpose before authority mode region referent handle after)
    (safe : CanEndStorage before id) (separate : referent.root ≠ id) : CanEndStorage after id := by
  cases borrowed with
  | @borrow value middle parent _ _ _ _ _ _ _ _ _ written =>
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

theorem Transfers.canEndStorage {program : Program} {before after : World}
    {authority source destination} {id : Identity}
    (moved : Transfers program before authority source destination after) (safe : CanEndStorage before id) :
    CanEndStorage after id := by
  cases moved with
  | move _ _ _ _ _ _ cleared written => exact World.write_canEndStorage written (World.write_canEndStorage cleared safe)

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

theorem FormsLoan.private_slot {program : Program} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent handle} {id : Identity} {root : Root}
    (borrowed : FormsLoan program purpose before authority mode region referent handle after)
    (slot : before.PrivateSlot id root) (outside : handle.root ≠ id) : after.PrivateSlot id root := by
  have sourceOutside : referent.root ≠ id := by
    cases borrowed with
    | borrow stored _ _ _ _ _ _ _ _ _ => exact slot.stored_outside stored
  exact slot.transport (borrowed.roots_other outside.symm) (borrowed.canEndStorage slot.safe sourceOutside)

theorem Transfers.private_slot {program : Program} {before after : World} {authority source destination}
    {id : Identity} {root : Root} (moved : Transfers program before authority source destination after)
    (slot : before.PrivateSlot id root) (outside : destination.root ≠ id) : after.PrivateSlot id root := by
  have sourceOutside : source.root ≠ id := by
    cases moved with
    | move stored _ _ _ _ _ _ _ => exact slot.stored_outside stored
  exact slot.transport (moved.roots_other sourceOutside.symm outside.symm) (moved.canEndStorage slot.safe)

theorem Copies.private_slot {program : Program} {before after : World} {authority source destination}
    {id : Identity} {root : Root} (copied : Copies program before authority source destination after)
    (slot : before.PrivateSlot id root) (outside : destination.root ≠ id) : after.PrivateSlot id root := by
  cases copied with
  | copy _ _ _ _ _ _ written =>
    have current := slot.write written outside
    exact ⟨current.found,current.vacant,current.safe,current.internalHome⟩

theorem Acquires.wellFormed {program : Program} {before after : World} {authority force source destination}
    (acquired : Acquires program before authority force source destination after)
    (well : before.WellFormed) : after.WellFormed := by
  cases acquired with
  | explicitMove moved | move _ _ _ moved => exact Transfers.wellFormed well moved
  | copy copied => exact Copies.wellFormed well copied

theorem Acquires.private_slot {program : Program} {before after : World} {authority force source destination}
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

theorem NewValue.private_slot {program : Program} {before after : World} {destination type head sources}
    {id : Identity} {root : Root} (created : NewValue program before destination type head sources after)
    (slot : before.PrivateSlot id root) (outside : destination.root ≠ id) : after.PrivateSlot id root := by
  cases created with
  | construct _ _ values _ _ _ cleared written =>
    have sourcesOutside : ∀ address ∈ sources.map ResolvedPlace.address, address.root ≠ id := by
      intro address member
      obtain ⟨source,present,rfl⟩ := List.mem_map.mp member
      obtain ⟨value,_,stored⟩ := values.member_left present
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

theorem EndsLoan.private_slot {before after : World} {loan id : Identity} {root : Root}
    (ended : EndsLoan before loan after) (slot : before.PrivateSlot id root) : after.PrivateSlot id root := by
  apply slot.transport
  · cases ended; rfl
  · exact ended.releaseFrame.canEndStorage slot.safe

/-- Moving an entire source root to distinct storage retains the source's
location and leaves its exact value slot empty. -/
theorem Transfers.source_root {program : Program} {before after : World}
    {authority : Authority} {source destination : Address} {root : Root}
    (moved : Transfers program before authority source destination after)
    (whole : source.fields = []) (selected : before.root source = some root)
    (separate : destination.root ≠ source.root) :
    after.roots.get source.root = some { root with value := none } := by
  cases moved with
  | @move value cleared _ _ _ _ _ _ _ empty filled =>
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

theorem LendsResident.private_slot {program : Language.Program} {before after : World}
    {activation scope region address authority access lease permission} {id : Identity} {root : Root}
    (lent : LendsResident program activation scope region before address authority access lease permission after)
    (well : before.WellFormed) (slot : before.PrivateSlot id root) : after.PrivateSlot id root := by
  cases lent with
  | owned => exact slot
  | lent _ _ allocated borrowed =>
    have outside := allocated.fresh_avoids (slot.bound well)
    exact borrowed.private_slot (allocated.private_slot (slot.bound well) slot) outside

theorem BindsInput.private_slot {program : Language.Program} {before after : World}
    {activation scope region input binding} {id : Identity} {root : Root}
    (bound : BindsInput program activation scope region before input binding after)
    (well : before.WellFormed) (slot : before.PrivateSlot id root) :
    after.PrivateSlot id root ∧ binding.address.root ≠ id := by
  cases bound with
  | lent _ stored _ _ _ lent => exact ⟨lent.private_slot well slot,slot.stored_outside stored⟩
  | owned _ _ _ allocated transferred =>
    have outside := allocated.fresh_avoids (slot.bound well)
    exact ⟨transferred.private_slot (allocated.private_slot (slot.bound well) slot) outside,outside⟩

/-- Every capture and ordinary argument uses the same privacy-preserving
input binder. It cannot make the hidden empty caller slot a callee binding. -/
theorem BindsInputs.private_slot {program : Language.Program} {before after : World}
    {activation scope region inputs bindings} {id : Identity} {root : Root}
    (bound : BindsInputs program activation scope region before inputs bindings after)
    (well : before.WellFormed) (slot : before.PrivateSlot id root) :
    after.PrivateSlot id root ∧ ∀ binding ∈ bindings, binding.address.root ≠ id := by
  induction bound with
  | nil => exact ⟨slot,by simp⟩
  | cons first _ ih =>
    obtain ⟨middle,firstOutside⟩ := first.private_slot well slot
    obtain ⟨finish,restOutside⟩ := ih (first.wellFormed well) middle
    refine ⟨finish,?_⟩
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact firstOutside
    · exact restOutside binding member

theorem BindsPattern.private_slot {program : Language.Program} {before after : World}
    {activation scope region localSlot source authority access binding} {id : Identity} {root : Root}
    (bound : BindsPattern program activation scope region before localSlot source authority access binding after)
    (well : before.WellFormed) (slot : before.PrivateSlot id root) :
    after.PrivateSlot id root ∧ binding.address.root ≠ id := by
  cases bound with
  | owned bound => exact bound.private_slot well slot
  | borrowed _ _ allocated borrowed =>
    have outside := allocated.fresh_avoids (slot.bound well)
    exact ⟨borrowed.private_slot (allocated.private_slot (slot.bound well) slot) outside,outside⟩

/-- The common owned binder moves the original handle to a fresh callee slot;
it does not leave a second copy in the caller or hand that original slot to
the callee environment. -/
theorem BindsInput.owned_private_root {program : Language.Program} {before after : World}
    {activation scope region : Identity} {input : InvocationInput} {binding : Binding} {root : Root}
    (well : before.WellFormed)
    (bound : BindsInput program activation scope region before input binding after)
    (owned : input.access = .owned) (whole : input.storage.fields = [])
    (selected : before.root input.storage = some root) (safe : CanEndStorage before input.storage.root) :
    after.roots.get input.storage.root = some { root with value := none } ∧
      CanEndStorage after input.storage.root ∧ binding.address.root ≠ input.storage.root := by
  cases bound with
  | lent borrowed _ _ _ _ _ => exact False.elim (borrowed owned)
  | @owned address allocated _ layout value _ _ _ allocation transferred =>
    have originalBound := World.root_bound well (World.root_found selected).1
    have fresh : address.root = before.nextRoot := by cases allocation; rfl
    have separate : address.root ≠ input.storage.root := fresh ▸ (Nat.ne_of_lt originalBound).symm
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

theorem PreparesEntry.private_slot {program : Kernel.Program} {context : Context} {function : Kernel.Function}
    {before after : World} {source : EntrySource} {inputs : List Kernel.InvocationInput} {id : Identity} {root : Root}
    (prepared : PreparesEntry program context function before source inputs after)
    (well : before.WellFormed) (slot : before.PrivateSlot id root) : after.PrivateSlot id root := by
  cases prepared with
  | supplied => exact slot
  | resident lent _ => exact lent.private_slot well slot
  | contextual receiver witness => exact witness.private_slot (receiver.wellFormed well) (receiver.private_slot well slot)

theorem EnterWorld.private_slot {program : Kernel.Program} {before : State} {after : World}
    {caller context : Context} {function : Kernel.Function} {source : EntrySource} {id : Identity} {root : Root}
    (entered : EnterWorld program before caller function source context after)
    (well : before.world.WellFormed) (slot : before.world.PrivateSlot id root) :
    after.PrivateSlot id root ∧ id ∉ context.rootSupport := by
  obtain ⟨withRegion,prepared,inputs,environment,declaration,_,fresh,prepares,bound,rfl,_⟩ := entered
  obtain ⟨afterSlot,bindings⟩ := bound.private_slot (prepares.wellFormed (fresh.wellFormed well))
    (prepares.private_slot (fresh.wellFormed well) (FreshRegion.private_slot fresh slot))
  refine ⟨afterSlot,?_⟩
  intro member
  obtain ⟨binding,present,same⟩ := List.mem_map.mp member
  exact bindings binding present same

/-- The hook's temporary root has no incoming live loans or reservations.
The newly formed loan names Self, not the fresh reference-handle root. -/
theorem Temporary.borrowed_handle_private {program : Kernel.Program} {before allocated after : World}
    {context : Context} {value : Value} {address handle : Address} {authority : Authority}
    (well : before.WellFormed) (stored : before.Stores address value)
    (temporary : Temporary program context (.reference .unique (.runtimeRegion context.region) value.type)
      before handle allocated)
    (borrowed : Borrows program.declarations allocated authority .unique context.region address handle after) :
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
    (owned : input.access = .owned) (whole : input.storage.fields = [])
    (selected : before.world.root input.storage = some root) (safe : CanEndStorage before.world input.storage.root) :
    after.roots.get input.storage.root = some { root with value := none } ∧
      CanEndStorage after input.storage.root ∧
      (∀ binding ∈ callee.environment, binding.address.root ≠ input.storage.root) := by
  obtain ⟨withRegion,prepared,inputs,environment,declaration,_,fresh,preparation,bound,context,_⟩ := entered
  cases preparation
  cases bound with
  | cons first rest =>
    cases rest
    have selectedRegion : withRegion.root input.storage = some root := by rw [fresh.2]; exact selected
    have safeRegion : CanEndStorage withRegion input.storage.root := by rw [fresh.2]; exact safe
    obtain ⟨vacant,privateRoot,outside⟩ := first.owned_private_root (fresh.worldTyped typed).1 owned whole selectedRegion safeRegion
    refine ⟨vacant,privateRoot,?_⟩
    rw [context]
    intro binding member
    simp only [List.mem_singleton] at member
    exact member ▸ outside

end Execution
end Glorious.Language
