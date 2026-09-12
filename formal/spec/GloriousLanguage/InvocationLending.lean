import GloriousLanguage.ReceiverPreservation
import GloriousLanguage.LocalPreservation

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

theorem BindsInputs.root_retained {program : Kernel.Program} {before after : World}
    {activation scope region inputs bindings}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (bound : BindsInputs program.declarations activation scope region before inputs bindings after)
    {observed : Address} {root : Root} (found : before.root observed = some root) :
    ∃ changed, after.root observed = some changed ∧ changed.location = root.location := by
  induction bound generalizing root with
  | nil => exact ⟨root,found,rfl⟩
  | cons first _ ih =>
    obtain ⟨middle,selected,location⟩ := first.root_retained typed.1 found
    obtain ⟨changed,present,equal⟩ := ih (first.worldTyped valid inventory typed) selected
    exact ⟨changed,present,equal.trans location⟩

/-- The lifetime witness is real storage owned by the activation supplied to
the common loan producer, with the same fresh identity recorded in the loan. -/
theorem LendsResident.lease_owned {program : Language.Program} {before after : World}
    {activation scope region address authority access lease permission}
    (lent : LendsResident program activation scope region before address authority access lease permission after)
    (borrowed : access ≠ .owned) :
    ∃ witness root, lease = some witness ∧ after.root witness.handle = some root ∧
      root.home = .temporary activation scope ∧ root.region = region ∧ witness.handle.fields = [] := by
  cases lent with
  | owned => exact False.elim (borrowed rfl)
  | lent _ _ allocation formed =>
    obtain ⟨root,selected,home,lifetime,whole⟩ := allocation.new_root
    obtain ⟨changed,present,location⟩ := World.root_transport formed.locations selected
    refine ⟨_,changed,rfl,present,?_,?_,whole⟩
    · have same : changed.home = root.home := by simpa [Root.location] using congrArg Root.home location
      exact same.trans home
    · have same : changed.region = root.region := by simpa [Root.location] using congrArg Root.region location
      exact same.trans lifetime

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
    obtain ⟨changed,present,location⟩ := bound.root_retained valid inventory preparedTyped selected
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
