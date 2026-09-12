import GloriousLanguage.DropReturn
import GloriousLanguage.ForeignAuthority

/-! The saved destructor handle is made private by actual temporary allocation,
borrowing and ordinary owned-input binding. These are entry facts, not
post-return certificates or an alternate invocation evaluator. -/
namespace Glorious.Language

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

/-- Two actual machine steps establish saved-handle privacy at the hook body,
including its vacant live caller-owned root and exclusion from the callee's
environment. No after-entry storage certificate is an input. -/
theorem LocalStep.hook_entry_private {program : Kernel.Program} {before entering body : State}
    {address : Address} {hook : DeclId}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (dispatch : LocalStep program before (some (.hookEnter address hook)) entering)
    (entry : LocalStep program entering none body) :
    ∃ (caller callee : Context) (function : Kernel.Function) (authority : Authority)
      (handle : Address) (loan : Identity) (next : Task) (root : Root),
      entering.frames = .hook caller address authority handle loan next :: before.frames ∧
      body.task = .run callee function.body ∧
      body.world.roots.get handle.root = some root ∧ root.live = true ∧ root.value = none ∧
      root.home = .temporary caller.activation caller.scope ∧ handle.fields = [] ∧
      handle.root = before.world.nextRoot ∧
      CanEndStorage body.world handle.root ∧
      (∀ binding ∈ callee.environment, binding.address.root ≠ handle.root) := by
  have afterTyped := dispatch.worldTyped valid inventory typed
  cases dispatch with
  | @destroyHook context _ authority next value _ function allocated handle after loan task stored _ _ selected temporary borrowed identity =>
    obtain ⟨root,found,home,whole,privateRoot⟩ := temporary.borrowed_handle_private typed.1 stored borrowed
    have live := (World.root_found found).2.1
    have fresh : handle.root = before.world.nextRoot := by
      obtain ⟨_,allocated⟩ := temporary
      cases allocated
      rfl
    cases entry <;> try contradiction
    case enter caller actual source callee final task entered =>
      cases task
      have moved := entered.owned_handle_private afterTyped rfl whole found privateRoot
      exact ⟨context,callee,function,authority,handle,loan,next,{ root with value := none },rfl,rfl,
        moved.1,live,rfl,home,whole,fresh,moved.2.1,moved.2.2⟩

end Execution
end Glorious.Language
