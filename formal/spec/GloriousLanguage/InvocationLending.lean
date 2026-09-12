import GloriousLanguage.ReceiverPreservation
import GloriousLanguage.LocalPreservation
import GloriousLanguage.ReferencePersistence

/-! The actual invocation boundary owns its loans in the fresh callee.
Receiver exclusion survives the common binding of every capture and argument;
the original caller authority is not regained by entering the body. -/
namespace Glorious.Language

theorem Allocates.loans {program : Program} {before after : World} {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) :
    after.loans = before.loans := by cases allocated; rfl

theorem Allocates.nextLoan {program : Program} {before after : World} {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) :
    after.nextLoan = before.nextLoan := by cases allocated; rfl

theorem Allocates.new_root {program : Program} {before after : World} {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) :
    ∃ root, after.root address = some root ∧ root.home = home ∧ root.region = region ∧ address.fields = [] := by
  cases allocated
  exact ⟨_,by simp [World.root,Table.get_set]; rfl,rfl,rfl,rfl⟩

/-- A newly created loan continues to exclude its parent in any later
well-formed world retaining that loan. Binding further invocation inputs is
one such transition; merely restricting the callee's own view is insufficient. -/
theorem FormsLoan.excludes_parent_retained {program : Program} {purpose : LoanPurpose}
    {before after later : World} {authority : Authority} {mode : Mutability}
    {region : Identity} {referent handle : Address} {access : Access}
    (valid : before.WellFormed) (future : later.WellFormed)
    (borrowed : FormsLoan program purpose before authority mode region referent handle after)
    (retained : ∀ id loan, after.loans.get id = some loan → later.loans.get id = some loan)
    (conflict : Conflict access mode) : ¬ Permitted later authority access referent := by
  cases borrowed with
  | @borrow value middle parent _ _ _ _ _ permitted _ _ _ _ =>
    intro allowed
    have found := retained before.nextLoan
      ⟨before.nextLoan,parent,referent,mode,region,true⟩ (Table.get_set _ _ _)
    obtain ⟨ancestor,selected,ancestry⟩ := allowed.conflicting_parent found rfl
      (Address.Prefix.refl referent).overlaps conflict
    obtain ⟨old,oldFound,_⟩ := permitted.parentLoan selected
    exact Nat.not_lt_of_ge (ancestry.identity_le (World.loanParents future)) (World.loanBounds valid oldFound)

namespace Kernel

theorem LendsResident.wellFormed {program : Language.Program} {before after : World}
    {activation scope region address authority access lease permission}
    (lent : LendsResident program activation scope region before address authority access lease permission after)
    (valid : before.WellFormed) : after.WellFormed := by
  cases lent with
  | owned => exact valid
  | lent _ _ allocated borrowed => exact borrowed.wellFormed (allocated.wellFormed valid)

theorem BindsInput.wellFormed {program : Language.Program} {before after : World}
    {activation scope region input binding}
    (bound : BindsInput program activation scope region before input binding after)
    (valid : before.WellFormed) : after.WellFormed := by
  cases bound with
  | lent _ _ _ _ _ lent => exact lent.wellFormed valid
  | owned _ _ _ allocated transferred => exact transferred.wellFormed (allocated.wellFormed valid)

theorem BindsInputs.wellFormed {program : Language.Program} {before after : World}
    {activation scope region inputs bindings}
    (bound : BindsInputs program activation scope region before inputs bindings after)
    (valid : before.WellFormed) : after.WellFormed := by
  induction bound with
  | nil => exact valid
  | cons first _ ih => exact ih (first.wellFormed valid)

theorem BindsPattern.wellFormed {program : Language.Program} {before after : World}
    {activation scope region localSlot source authority access binding}
    (bound : BindsPattern program activation scope region before localSlot source authority access binding after)
    (valid : before.WellFormed) : after.WellFormed := by
  cases bound with
  | owned bound => exact bound.wellFormed valid
  | borrowed _ _ allocated borrowed => exact borrowed.wellFormed (allocated.wellFormed valid)

theorem LendsResident.lent_authority {program : Language.Program} {before after : World}
    {activation scope region address authority access lease permission}
    (lent : LendsResident program activation scope region before address authority access lease permission after)
    (borrowed : access ≠ .owned) : ∃ loan, permission = .loan loan := by
  cases lent with
  | owned => exact False.elim (borrowed rfl)
  | lent => exact ⟨_,rfl⟩

theorem BindsInput.lent_authority {program : Language.Program} {before after : World}
    {activation scope region input binding}
    (bound : BindsInput program activation scope region before input binding after)
    (borrowed : input.access ≠ .owned) : ∃ loan, binding.authority = .loan loan := by
  cases bound with
  | owned owning _ _ _ _ => exact False.elim (borrowed owning)
  | lent _ _ _ _ _ lent => exact lent.lent_authority borrowed

theorem LendsResident.shared_no_mutation {program : Language.Program} {before after : World}
    {activation scope region address authority lease permission} {requested : Access}
    (lent : LendsResident program activation scope region before address authority .shared lease permission after)
    (writes : requested ≠ .shared) : ¬ Permitted after permission requested address := by
  cases lent with
  | lent modes _ _ formed =>
    rcases modes with ⟨_,rfl⟩ | ⟨impossible,_⟩
    · cases formed
      intro permitted
      obtain ⟨_,active,found,_,_,_,_,mode,_⟩ := permitted
      simp only [Table.get_set,Option.some.injEq] at found
      subst active
      cases mode writes
    · cases impossible

theorem BindsInput.shared_no_mutation {program : Language.Program} {before after : World}
    {activation scope region input binding} {requested : Access}
    (bound : BindsInput program activation scope region before input binding after)
    (shared : input.access = .shared) (writes : requested ≠ .shared) :
    ¬ Permitted after binding.authority requested binding.address := by
  cases bound with
  | owned owning _ _ _ _ => cases owning.symm.trans shared
  | lent _ _ _ _ _ lent => exact (shared ▸ lent).shared_no_mutation writes

theorem LendsResident.loan_retained {program : Language.Program} {before after : World}
    {activation scope region address authority access lease permission}
    (valid : before.WellFormed)
    (lent : LendsResident program activation scope region before address authority access lease permission after)
    {id : Identity} {loan : Loan} (found : before.loans.get id = some loan) :
    after.loans.get id = some loan := by
  cases lent with
  | owned => exact found
  | lent _ _ allocated borrowed =>
    exact borrowed.old_loan (allocated.wellFormed valid) (by simpa only [allocated.loans] using found)

theorem LendsResident.excludes_parent_retained {program : Language.Program} {before after later : World}
    {activation scope region address authority access lease permission} {requested : Access}
    (valid : before.WellFormed) (future : later.WellFormed)
    (lent : LendsResident program activation scope region before address authority access lease permission after)
    (borrowed : access ≠ .owned) (conflict : requested ≠ .shared ∨ access = .unique)
    (retained : ∀ id loan, after.loans.get id = some loan → later.loans.get id = some loan) :
    ¬ Permitted later authority requested address := by
  cases lent with
  | owned => exact False.elim (borrowed rfl)
  | lent modes _ allocated formed =>
    apply formed.excludes_parent_retained (allocated.wellFormed valid) future retained
    rcases conflict with writes | unique
    · exact Or.inl writes
    · rcases modes with ⟨shared,_⟩ | ⟨_,mode⟩
      · cases shared.symm.trans unique
      · exact Or.inr mode

theorem BindsInput.loan_retained {program : Language.Program} {before after : World}
    {activation scope region input binding}
    (valid : before.WellFormed)
    (bound : BindsInput program activation scope region before input binding after)
    {id : Identity} {loan : Loan} (found : before.loans.get id = some loan) :
    after.loans.get id = some loan := by
  cases bound with
  | lent _ _ _ _ _ lent => exact lent.loan_retained valid found
  | owned _ _ _ allocated transferred => simpa only [transferred.loans,allocated.loans] using found

theorem BindsInputs.loan_retained {program : Kernel.Program} {before after : World}
    {activation scope region inputs bindings}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (bound : BindsInputs program.declarations activation scope region before inputs bindings after)
    {id : Identity} {loan : Loan} (found : before.loans.get id = some loan) :
    after.loans.get id = some loan := by
  induction bound with
  | nil => exact found
  | cons first _ ih => exact ih (first.worldTyped valid inventory typed) (first.loan_retained typed.1 found)

/-- Capture and argument origins make no difference to exclusivity. Every
lent input obtains its own loan, which the remaining bindings retain. -/
theorem BindsInputs.lent_parent_exclusive {program : Kernel.Program} {before after : World}
    {activation scope region inputs bindings} {input : InvocationInput} {requested : Access}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (bound : BindsInputs program.declarations activation scope region before inputs bindings after)
    (member : input ∈ inputs) (borrowed : input.access ≠ .owned)
    (conflict : requested ≠ .shared ∨ input.access = .unique) :
    ¬ Permitted after input.authority requested input.storage := by
  induction bound with
  | nil => simp at member
  | cons first rest ih =>
    have middleTyped := first.worldTyped valid inventory typed
    rcases List.mem_cons.mp member with rfl | member
    · have afterTyped := rest.worldTyped valid inventory middleTyped
      cases first with
      | owned owning _ _ _ _ => exact False.elim (borrowed owning)
      | lent _ _ _ _ _ lent =>
        exact lent.excludes_parent_retained typed.1 afterTyped.1 borrowed conflict
          (fun _ _ found => rest.loan_retained valid inventory middleTyped found)
    · exact ih middleTyped member

theorem LendsResident.root_retained {program : Language.Program} {before after : World}
    {activation scope region address authority access lease permission}
    (valid : before.WellFormed)
    (lent : LendsResident program activation scope region before address authority access lease permission after)
    {observed : Address} {root : Root} (found : before.root observed = some root) :
    ∃ changed, after.root observed = some changed ∧ changed.location = root.location := by
  cases lent with
  | owned => exact ⟨root,found,rfl⟩
  | lent _ _ allocated borrowed =>
    exact World.root_transport borrowed.locations (allocated.root valid found)

theorem BindsInput.root_retained {program : Language.Program} {before after : World}
    {activation scope region input binding}
    (valid : before.WellFormed)
    (bound : BindsInput program activation scope region before input binding after)
    {observed : Address} {root : Root} (found : before.root observed = some root) :
    ∃ changed, after.root observed = some changed ∧ changed.location = root.location := by
  cases bound with
  | lent _ _ _ _ _ lent => exact lent.root_retained valid found
  | owned _ _ _ allocated transferred =>
    exact World.root_transport transferred.locations (allocated.root valid found)

theorem BindsInputs.root_retained {program : Language.Program} {before after : World}
    {activation scope region inputs bindings}
    (valid : before.WellFormed)
    (bound : BindsInputs program activation scope region before inputs bindings after)
    {observed : Address} {root : Root} (found : before.root observed = some root) :
    ∃ changed, after.root observed = some changed ∧ changed.location = root.location := by
  induction bound generalizing root with
  | nil => exact ⟨root,found,rfl⟩
  | cons first _ ih =>
    obtain ⟨middle,selected,location⟩ := first.root_retained valid found
    obtain ⟨changed,present,equal⟩ := ih (first.wellFormed valid) selected
    exact ⟨changed,present,equal.trans location⟩

/-- Each actual binding names live storage. This fact depends on allocation
and transfer, not on a separately assumed typing of the output environment. -/
theorem BindsInput.binding_root {program : Language.Program} {before after : World}
    {activation scope region input binding}
    (bound : BindsInput program activation scope region before input binding after)
    (valid : before.WellFormed) : ∃ root, after.root binding.address = some root := by
  cases bound with
  | lent _ stored _ _ _ lent =>
    obtain ⟨root,found,_⟩ := Option.bind_eq_some_iff.mp stored
    obtain ⟨changed,present,_⟩ := lent.root_retained valid found
    exact ⟨changed,present⟩
  | owned _ _ _ allocated transferred =>
    obtain ⟨root,found,_,_,_⟩ := allocated.new_root
    obtain ⟨changed,present,_⟩ := World.root_transport transferred.locations found
    exact ⟨changed,present⟩

theorem BindsInputs.binding_roots {program : Language.Program} {before after : World}
    {activation scope region inputs bindings}
    (bound : BindsInputs program activation scope region before inputs bindings after)
    (valid : before.WellFormed) :
    ∀ binding ∈ bindings, ∃ root, after.root binding.address = some root := by
  induction bound with
  | nil => simp
  | cons first rest ih =>
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨root,found⟩ := first.binding_root valid
      obtain ⟨changed,present,_⟩ := rest.root_retained (first.wellFormed valid) found
      exact ⟨changed,present⟩
    · exact ih (first.wellFormed valid) binding member

theorem BindsInputs.bindings_root_bound {program : Language.Program} {before after : World}
    {activation scope region inputs bindings}
    (bound : BindsInputs program activation scope region before inputs bindings after)
    (valid : before.WellFormed) : ∀ binding ∈ bindings, binding.address.root < after.nextRoot := by
  intro binding member
  obtain ⟨root,found⟩ := bound.binding_roots valid binding member
  exact World.root_bound (bound.wellFormed valid) (World.root_found found).1

theorem BindsPattern.binding_root {program : Language.Program} {before after : World}
    {activation scope region localSlot source authority access binding}
    (bound : BindsPattern program activation scope region before localSlot source authority access binding after)
    (valid : before.WellFormed) : ∃ root, after.root binding.address = some root := by
  cases bound with
  | owned bound => exact bound.binding_root valid
  | borrowed _ _ allocated borrowed =>
    obtain ⟨root,found,_,_,_⟩ := allocated.new_root
    obtain ⟨changed,present,_⟩ := World.root_transport borrowed.locations found
    exact ⟨changed,present⟩

theorem BindsPattern.root_bound {program : Language.Program} {before after : World}
    {activation scope region localSlot source authority access binding}
    (bound : BindsPattern program activation scope region before localSlot source authority access binding after)
    (valid : before.WellFormed) : binding.address.root < after.nextRoot := by
  obtain ⟨root,found⟩ := bound.binding_root valid
  exact World.root_bound (bound.wellFormed valid) (World.root_found found).1

/-- The actual temporary allocation and loan formation jointly produce the
invocation guard. Its resident handle, dynamic home and returned authority
all refer to the same lease identity, not an independent ownership table. -/
theorem LendsResident.lease_origin {program : Language.Program} {before after : World}
    {activation scope region address authority access lease permission}
    (lent : LendsResident program activation scope region before address authority access lease permission after)
    (borrowed : access ≠ .owned) :
    ∃ witness root owner mode type, lease = some witness ∧ permission = .loan witness.loan ∧
      witness.handle.fields = [] ∧ after.root witness.handle = some root ∧
      root.home = .temporary activation scope ∧ root.region = region ∧
      after.Stores witness.handle (.resident owner (.reference mode (.runtimeRegion region) type)
        (.reference witness.loan) true []) ∧
      after.loans.get witness.loan = some ⟨witness.loan,authority.parentLoan,address,mode,region,true⟩ := by
  cases lent with
  | owned => exact False.elim (borrowed rfl)
  | lent _ _ allocated formed =>
    obtain ⟨original,selected,home,atRegion,whole⟩ := allocated.new_root
    obtain ⟨retained,found,same⟩ := World.root_transport formed.locations selected
    obtain ⟨type,stored,loan⟩ := formed.created_handle
    refine ⟨_,retained,_,_,type,rfl,rfl,whole,found,?_,?_,stored,loan⟩
    · have unchanged : retained.home = original.home := by
        simpa only [Root.location] using congrArg Root.home same
      exact unchanged.trans home
    · have unchanged : retained.region = original.region := by
        simpa only [Root.location] using congrArg Root.region same
      exact unchanged.trans atRegion

/-- The lifetime witness is real storage owned by the activation supplied to
the common loan producer, with the same fresh identity recorded in the loan. -/
theorem LendsResident.lease_owned {program : Language.Program} {before after : World}
    {activation scope region address authority access lease permission}
    (lent : LendsResident program activation scope region before address authority access lease permission after)
    (borrowed : access ≠ .owned) :
    ∃ witness root, lease = some witness ∧ after.root witness.handle = some root ∧
      root.home = .temporary activation scope ∧ root.region = region ∧ witness.handle.fields = [] := by
  obtain ⟨witness,root,_,_,_,selected,_,whole,found,home,atRegion,_,_⟩ := lent.lease_origin borrowed
  exact ⟨witness,root,selected,found,home,atRegion,whole⟩

end Kernel

namespace Execution

open Kernel

/-- Every admitted ordinary entry retains the whole-receiver loan after
binding all captured and explicit inputs. This includes proper-tail entry. -/
theorem EnterWorld.resident_exclusive {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {receiver : ResolvedPlace}
    {access : Access} {arguments : List InvocationInput} {requested : Access}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (entered : EnterWorld program before caller function (.resident receiver access arguments) callee after)
    (borrowed : access ≠ .owned) (conflict : requested ≠ .shared ∨ access = .unique) :
    ¬ Permitted after receiver.authority requested receiver.address := by
  obtain ⟨withRegion,prepared,inputs,environment,declaration,_,fresh,preparation,bound,_,_⟩ := entered
  have regionTyped := fresh.worldTyped typed
  have preparedTyped := preparation.worldTyped valid inventory regionTyped
  have afterTyped := bound.worldTyped valid inventory preparedTyped
  cases preparation with
  | resident lent _ =>
    exact Kernel.LendsResident.excludes_parent_retained regionTyped.1 afterTyped.1 lent borrowed conflict
      (fun _ _ found => bound.loan_retained valid inventory preparedTyped found)

/-- The contextual witness is locked by a real callee-owned loan, even when
the reservation has no captured fields. Its original authority cannot re-enter
the same unique environment while the entered invocation is active. -/
theorem EnterWorld.contextual_witness_exclusive {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {receiver witness : ResolvedPlace}
    {receiverAccess witnessAccess : Access} {inputs : List InvocationInput} {requested : Access}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (entered : EnterWorld program before caller function
      (.contextual receiver receiverAccess witness witnessAccess inputs) callee after)
    (borrowed : witnessAccess ≠ .owned) (conflict : requested ≠ .shared ∨ witnessAccess = .unique) :
    ¬ Permitted after witness.authority requested witness.address := by
  obtain ⟨withRegion,prepared,inputs,environment,declaration,_,fresh,preparation,bound,_,_⟩ := entered
  have regionTyped := fresh.worldTyped typed
  have preparedTyped := preparation.worldTyped valid inventory regionTyped
  have afterTyped := bound.worldTyped valid inventory preparedTyped
  cases preparation with
  | contextual receiverLoan witnessLoan =>
    exact Kernel.LendsResident.excludes_parent_retained
      (receiverLoan.worldTyped valid inventory regionTyped).1 afterTyped.1 witnessLoan borrowed conflict
      (fun _ _ found => bound.loan_retained valid inventory preparedTyped found)

theorem EnterWorld.contextual_receiver_exclusive {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {receiver witness : ResolvedPlace}
    {receiverAccess witnessAccess : Access} {inputs : List InvocationInput} {requested : Access}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (entered : EnterWorld program before caller function
      (.contextual receiver receiverAccess witness witnessAccess inputs) callee after)
    (borrowed : receiverAccess ≠ .owned) (conflict : requested ≠ .shared ∨ receiverAccess = .unique) :
    ¬ Permitted after receiver.authority requested receiver.address := by
  obtain ⟨_,_,_,_,_,_,fresh,preparation,bound,_,_⟩ := entered
  have regionTyped := fresh.worldTyped typed
  have preparedTyped := preparation.worldTyped valid inventory regionTyped
  have afterTyped := bound.worldTyped valid inventory preparedTyped
  cases preparation with
  | contextual receiverLoan witnessLoan =>
    exact Kernel.LendsResident.excludes_parent_retained regionTyped.1 afterTyped.1 receiverLoan borrowed conflict
      (fun _ _ found => bound.loan_retained valid inventory preparedTyped
        (Kernel.LendsResident.loan_retained (receiverLoan.worldTyped valid inventory regionTyped).1 witnessLoan found))

theorem EnterWorld.supplied_exclusive {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {inputs : List InvocationInput}
    {input : InvocationInput} {requested : Access}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (entered : EnterWorld program before caller function (.supplied inputs) callee after)
    (member : input ∈ inputs) (borrowed : input.access ≠ .owned)
    (conflict : requested ≠ .shared ∨ input.access = .unique) :
    ¬ Permitted after input.authority requested input.storage := by
  obtain ⟨_,_,_,_,_,_,fresh,preparation,bound,_,_⟩ := entered
  cases preparation with
  | supplied => exact bound.lent_parent_exclusive valid inventory (fresh.worldTyped typed) member borrowed conflict

theorem EnterWorld.contextual_inputs_exclusive {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {receiver witness : ResolvedPlace}
    {receiverAccess witnessAccess : Access} {inputs : List InvocationInput} {input : InvocationInput} {requested : Access}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (entered : EnterWorld program before caller function
      (.contextual receiver receiverAccess witness witnessAccess inputs) callee after)
    (member : input ∈ inputs) (borrowed : input.access ≠ .owned)
    (conflict : requested ≠ .shared ∨ input.access = .unique) :
    ¬ Permitted after input.authority requested input.storage := by
  obtain ⟨_,_,_,_,_,_,fresh,preparation,bound,_,_⟩ := entered
  have preparedTyped := preparation.worldTyped valid inventory (fresh.worldTyped typed)
  cases preparation with
  | contextual => exact bound.lent_parent_exclusive valid inventory preparedTyped member borrowed conflict

theorem EnterWorld.fresh_context {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {source : EntrySource}
    (entered : EnterWorld program before caller function source callee after) :
    callee.activation = before.nextActivation ∧ callee.scope = before.world.nextRegion ∧ callee.region = before.world.nextRegion := by
  obtain ⟨_,_,_,_,_,_,_,_,_,context,_⟩ := entered
  simp [context]

theorem EnterWorld.resident_lease_owned {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {receiver : ResolvedPlace}
    {access : Access} {arguments : List InvocationInput}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (entered : EnterWorld program before caller function (.resident receiver access arguments) callee after)
    (borrowed : access ≠ .owned) :
    ∃ handle root, after.root handle = some root ∧ root.home = .temporary before.nextActivation before.world.nextRegion ∧
      root.region = before.world.nextRegion := by
  obtain ⟨_,_,_,_,_,_,fresh,preparation,bound,context,_⟩ := entered
  have preparedTyped := preparation.worldTyped valid inventory (fresh.worldTyped typed)
  cases preparation with
  | resident lent _ =>
    obtain ⟨witness,root,_,selected,home,region,_⟩ := Kernel.LendsResident.lease_owned lent borrowed
    obtain ⟨changed,present,location⟩ := bound.root_retained preparedTyped.1 selected
    have sameHome : changed.home = .temporary callee.activation callee.scope := by
      have same : changed.home = root.home := by simpa [Root.location] using congrArg Root.home location
      exact same.trans home
    have sameRegion : changed.region = callee.region := by
      have same : changed.region = root.region := by simpa [Root.location] using congrArg Root.region location
      exact same.trans region
    refine ⟨witness.handle,changed,present,?_,?_⟩
    · simpa only [context] using sameHome
    · simpa only [context] using sameRegion

/-- Entering a proper-tail call cannot place its receiver handle in the
activation being retired. The actual callee cleanup inventory includes it. -/
theorem EnterWorld.resident_lease_cleanup {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {receiver : ResolvedPlace}
    {access : Access} {arguments : List InvocationInput} {roots : List Identity}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (entered : EnterWorld program before caller function (.resident receiver access arguments) callee after)
    (borrowed : access ≠ .owned) (cleanup : ActivationRoots after callee.activation [] roots) :
    ∃ handle root, after.root handle = some root ∧ root.home = .temporary before.nextActivation before.world.nextRegion ∧
      root.region = before.world.nextRegion ∧ handle.root ∈ roots := by
  obtain ⟨handle,root,present,home,region⟩ := entered.resident_lease_owned valid inventory typed borrowed
  have fields := World.root_found present
  refine ⟨handle,root,present,home,region,(cleanup.2 handle.root).mpr ⟨root,fields.1,fields.2.1,?_,by simp⟩⟩
  exact Or.inr ⟨before.world.nextRegion,by simpa only [entered.fresh_context.1] using home⟩

theorem EnterWorld.resident_lease_outside_caller {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {receiver : ResolvedPlace}
    {access : Access} {arguments : List InvocationInput} {roots kept : List Identity}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (entered : EnterWorld program before caller function (.resident receiver access arguments) callee after)
    (borrowed : access ≠ .owned) (fresh : caller.activation < before.nextActivation)
    (cleanup : ActivationRoots after caller.activation kept roots) :
    ∃ handle root, after.root handle = some root ∧ root.home = .temporary before.nextActivation before.world.nextRegion ∧
      root.region = before.world.nextRegion ∧ handle.root ∉ roots := by
  obtain ⟨handle,root,present,home,region⟩ := entered.resident_lease_owned valid inventory typed borrowed
  refine ⟨handle,root,present,home,region,?_⟩
  intro member
  obtain ⟨other,found,_,owned,_⟩ := (cleanup.2 handle.root).mp member
  have same : root = other := Option.some.inj ((World.root_found present).1.symm.trans found)
  subst other
  rcases owned with ⟨scope,equal⟩ | ⟨scope,equal⟩
  · rw [home] at equal
    cases equal
  · have same := Home.temporary.inj (home.symm.trans equal)
    exact (Nat.ne_of_lt fresh) same.1.symm

theorem LocalStep.enter_world {program : Kernel.Program} {before after : State} {event : Option Event}
    {caller : Context} {function : Function} {source : EntrySource} {tail : Bool}
    (task : before.task = .enter caller function source tail)
    (step : LocalStep program before event after) :
    ∃ callee, EnterWorld program before caller function source callee after.world := by
  cases step <;> simp_all
  all_goals exact ⟨_,by assumption⟩

/-- Exclusivity is a property of the actual transition, not just a prepared
input list. Both ordinary and proper-tail entries use the same proof. -/
theorem LocalStep.resident_entry_exclusive {program : Kernel.Program} {before after : State} {event : Option Event}
    {caller : Context} {function : Function} {receiver : ResolvedPlace} {access : Access}
    {arguments : List InvocationInput} {tail : Bool} {requested : Access}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .enter caller function (.resident receiver access arguments) tail)
    (step : LocalStep program before event after)
    (borrowed : access ≠ .owned) (conflict : requested ≠ .shared ∨ access = .unique) :
    ¬ Permitted after.world receiver.authority requested receiver.address := by
  obtain ⟨_,entered⟩ := step.enter_world task
  exact entered.resident_exclusive valid inventory typed borrowed conflict

theorem LocalStep.contextual_entry_exclusive {program : Kernel.Program} {before after : State} {event : Option Event}
    {caller : Context} {function : Function} {receiver witness : ResolvedPlace}
    {receiverAccess witnessAccess : Access} {inputs : List InvocationInput} {tail : Bool} {requested : Access}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .enter caller function (.contextual receiver receiverAccess witness witnessAccess inputs) tail)
    (step : LocalStep program before event after)
    (borrowed : witnessAccess ≠ .owned) (conflict : requested ≠ .shared ∨ witnessAccess = .unique) :
    ¬ Permitted after.world witness.authority requested witness.address := by
  obtain ⟨_,entered⟩ := step.enter_world task
  exact entered.contextual_witness_exclusive valid inventory typed borrowed conflict

end Execution
end Glorious.Language
