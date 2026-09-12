import GloriousLanguage.InputLending
import GloriousLanguage.ReceiverPreservation
import GloriousLanguage.LocalPreservation
import GloriousLanguage.ReferencePersistence

/-! The actual invocation boundary owns its loans in the fresh callee.
Receiver exclusion survives the common binding of every capture and argument;
the original caller authority is not regained by entering the body. -/
namespace Glorious.Language

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
