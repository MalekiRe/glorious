import GloriousLanguage.InputLending
import GloriousLanguage.ReceiverPreservation
import GloriousLanguage.LocalPreservation
import GloriousLanguage.ReferencePersistence

/-! The actual invocation boundary owns its loans in the fresh callee.
Receiver exclusion survives the common binding of every capture and argument;
the original caller authority is not regained by entering the body. The
receiver and witness statements are indexed by the real `PreparationOutcome`,
so an exhausted entry — which stops at the world its successfully bound prefix
produced — is covered by the same retention argument as a completed one. Each
proof first exposes the entered world with the actual finishing step; for a
borrowed receiver that step leaves the world the binder produced. -/
namespace Glorious.Language

namespace Execution

open Kernel

/-- The ordered binder retains every prepared row, up to its permission
projection, in a later world whose loan table holds the binder's rows. The
finishing step of an entry supplies that equality: a completed entry's shell
step leaves the loan table alone, and an exhausted attempt leaves the world
equal to the binder's. -/
theorem Kernel.retained_through_entry {program : Kernel.Program} {after bound : World}
    {outcome : Kernel.PreparationOutcome}
    {prepared : World} {inputs : List Kernel.InvocationInput} {environment : Kernel.Environment}
    {recipient : ClaimCustody} {activation scope region : Identity}
    (valid : prepared.WellFormed)
    (chained : Kernel.BindsInputsAttemptFor program.toRuntimeProgram recipient activation scope region
      (inputs.flatMap Kernel.InvocationInput.clearedStorage) prepared inputs environment bound outcome)
    (loansAfter : bound.loans = after.loans) :
    ∀ id loan, prepared.loans.get id = some loan →
      ∃ current, after.loans.get id = some current ∧ current.permissionState = loan.permissionState := by
  intro id loan found
  obtain ⟨current,atBound,shape⟩ := Kernel.BindsInputsAttemptFor.loan_retained valid chained found
  exact ⟨current,by rw [← loansAfter]; exact atBound,shape⟩

/-- Every admitted ordinary entry retains the whole-receiver loan after
binding all captured and explicit inputs. This includes proper-tail entry and
the exhausted prefix of a failed one. -/
theorem EnterWorldAttempt.resident_exclusive {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {receiver : ResolvedPlace}
    {access : Access} {arguments : List InvocationInput} {requested : Access}
    {outcome : Kernel.PreparationOutcome}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (attempt : EnterWorldAttempt program before caller function (.resident receiver access arguments) callee after outcome)
    (borrowed : access ≠ .owned) (conflict : requested ≠ .shared ∨ access = .unique) :
    ¬ Permitted after receiver.authority requested receiver.address := by
  have attemptKept := attempt
  obtain ⟨withRegion,prepared,inputs,environment,declaration,bound,selected,fresh,preparation,incoming,chained,finished,contextEq,unsafeAllowed⟩ := attempt
  have regionTyped := fresh.worldTyped typed
  have preparedTyped := preparation.worldTyped valid inventory regionTyped
  have afterTyped := EnterWorldAttempt.worldTyped valid inventory typed attemptKept
  have loansAfter : bound.loans = after.loans := by
    cases outcome with
    | complete => exact (finished.loans).symm
    | exhausted => cases finished; rfl
  cases preparation with
  | resident callable instanced lent capturesProof consumedProof =>
    refine Kernel.LendsResident.excludes_parent_retained (valid := regionTyped.1) (future := afterTyped.1)
      lent borrowed conflict ?_
    intro id loan found
    have atPrepared : prepared.loans.get id = some loan := by rw [consumedProof.loans]; exact found
    exact Kernel.retained_through_entry preparedTyped.1 chained loansAfter id loan atPrepared

/-- The contextual witness is locked by a real callee-owned loan, even when
the reservation has no captured fields. Its original authority cannot re-enter
the same unique environment while the entered invocation is active. -/
theorem EnterWorldAttempt.contextual_witness_exclusive {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {receiver witness : ResolvedPlace}
    {receiverAccess witnessAccess : Access} {inputs : List InvocationInput} {requested : Access}
    {outcome : Kernel.PreparationOutcome}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (attempt : EnterWorldAttempt program before caller function
      (.contextual receiver receiverAccess witness witnessAccess inputs) callee after outcome)
    (borrowed : witnessAccess ≠ .owned) (conflict : requested ≠ .shared ∨ witnessAccess = .unique) :
    ¬ Permitted after witness.authority requested witness.address := by
  have attemptKept := attempt
  obtain ⟨withRegion,prepared,inputs',environment,declaration,bound,selected,fresh,preparation,incoming,chained,finished,contextEq,unsafeAllowed⟩ := attempt
  have regionTyped := fresh.worldTyped typed
  have preparedTyped := preparation.worldTyped valid inventory regionTyped
  have afterTyped := EnterWorldAttempt.worldTyped valid inventory typed attemptKept
  have loansAfter : bound.loans = after.loans := by
    cases outcome with
    | complete => exact (finished.loans).symm
    | exhausted => cases finished; rfl
  cases preparation with
  | contextual callable instanced witnessEvidence reservations receiverLent witnessLent capturesProof consumedReceiver consumedAvailability =>
    refine Kernel.LendsResident.excludes_parent_retained
      (valid := (receiverLent.worldTyped valid inventory regionTyped).1) (future := afterTyped.1)
      witnessLent borrowed conflict ?_
    intro id loan found
    have atPrepared : prepared.loans.get id = some loan := by
      rw [consumedAvailability.loans, consumedReceiver.loans]
      exact found
    exact Kernel.retained_through_entry preparedTyped.1 chained loansAfter id loan atPrepared

theorem EnterWorldAttempt.contextual_receiver_exclusive {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {receiver witness : ResolvedPlace}
    {receiverAccess witnessAccess : Access} {inputs : List InvocationInput} {requested : Access}
    {outcome : Kernel.PreparationOutcome}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (attempt : EnterWorldAttempt program before caller function
      (.contextual receiver receiverAccess witness witnessAccess inputs) callee after outcome)
    (borrowed : receiverAccess ≠ .owned) (conflict : requested ≠ .shared ∨ receiverAccess = .unique) :
    ¬ Permitted after receiver.authority requested receiver.address := by
  have attemptKept := attempt
  obtain ⟨withRegion,prepared,inputs',environment,declaration,bound,selected,fresh,preparation,incoming,chained,finished,contextEq,unsafeAllowed⟩ := attempt
  have regionTyped := fresh.worldTyped typed
  have preparedTyped := preparation.worldTyped valid inventory regionTyped
  have afterTyped := EnterWorldAttempt.worldTyped valid inventory typed attemptKept
  have loansAfter : bound.loans = after.loans := by
    cases outcome with
    | complete => exact (finished.loans).symm
    | exhausted => cases finished; rfl
  cases preparation with
  | contextual callable instanced witnessEvidence reservations receiverLent witnessLent capturesProof consumedReceiver consumedAvailability =>
    have priorTyped := (receiverLent.worldTyped valid inventory regionTyped).1
    refine Kernel.LendsResident.excludes_parent_retained (valid := regionTyped.1) (future := afterTyped.1)
      receiverLent borrowed conflict ?_
    intro id loan found
    have atLent : _ := witnessLent.loan_retained priorTyped found
    have atPrepared : prepared.loans.get id = some loan := by
      rw [consumedAvailability.loans, consumedReceiver.loans]
      exact atLent
    exact Kernel.retained_through_entry preparedTyped.1 chained loansAfter id loan atPrepared

theorem EnterWorld.supplied_exclusive {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {inputs : List InvocationInput}
    {input : InvocationInput} {requested : Access}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (entered : EnterWorld program before caller function (.supplied inputs) callee after)
    (member : input ∈ inputs) (borrowed : input.access ≠ .owned)
    (conflict : requested ≠ .shared ∨ input.access = .unique) :
    ¬ Permitted after input.authority requested input.storage := by
  obtain ⟨withRegion,prepared,inputs',environment,declaration,bound,selected,fresh,preparation,incoming,chained,finished,contextEq,unsafeAllowed⟩ := entered
  have preparedTyped := preparation.worldTyped valid inventory (fresh.worldTyped typed)
  cases preparation with
  | supplied =>
    cases finished with
    | supplied =>
      exact Kernel.BindsInputsFor.lent_parent_exclusive preparedTyped.1 chained (by simpa using member) borrowed conflict

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
  have enteredKept := entered
  obtain ⟨withRegion,prepared,inputs',environment,declaration,bound,selected,fresh,preparation,incoming,chained,finished,contextEq,unsafeAllowed⟩ := entered
  have preparedTyped := preparation.worldTyped valid inventory (fresh.worldTyped typed)
  have afterTyped := EnterWorld.worldTyped valid inventory typed enteredKept
  cases preparation with
  | contextual callable instanced witnessEvidence reservations receiverLent witnessLent capturesProof consumedReceiver consumedAvailability =>
    cases finished with
    | contextual receiverFinished =>
      cases receiverFinished with
      | lent notOwned =>
        exact Kernel.BindsInputsFor.lent_parent_exclusive preparedTyped.1 chained (by simpa using member) borrowed conflict
      | owned stored shell callableHead holes resources permittedEaten written =>
        refine Kernel.BindsInputsFor.lent_parent_exclusive_retained preparedTyped.1 afterTyped.1 chained
          (by simpa using member) borrowed conflict ?_
        intro id loan found
        exact ⟨loan,by rw [World.write_loans written]; exact found,rfl⟩

/-- Completed ordinary entry, the specialization of the outcome-indexed
statement where the entered world is the one the ordered binder produced. -/
theorem EnterWorld.resident_exclusive {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {receiver : ResolvedPlace}
    {access : Access} {arguments : List InvocationInput} {requested : Access}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (entered : EnterWorld program before caller function (.resident receiver access arguments) callee after)
    (borrowed : access ≠ .owned) (conflict : requested ≠ .shared ∨ access = .unique) :
    ¬ Permitted after receiver.authority requested receiver.address :=
  EnterWorldAttempt.resident_exclusive valid inventory typed entered borrowed conflict

theorem EnterWorld.contextual_witness_exclusive {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {receiver witness : ResolvedPlace}
    {receiverAccess witnessAccess : Access} {inputs : List InvocationInput} {requested : Access}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (entered : EnterWorld program before caller function
      (.contextual receiver receiverAccess witness witnessAccess inputs) callee after)
    (borrowed : witnessAccess ≠ .owned) (conflict : requested ≠ .shared ∨ witnessAccess = .unique) :
    ¬ Permitted after witness.authority requested witness.address :=
  EnterWorldAttempt.contextual_witness_exclusive valid inventory typed entered borrowed conflict

theorem EnterWorld.contextual_receiver_exclusive {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {receiver witness : ResolvedPlace}
    {receiverAccess witnessAccess : Access} {inputs : List InvocationInput} {requested : Access}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (entered : EnterWorld program before caller function
      (.contextual receiver receiverAccess witness witnessAccess inputs) callee after)
    (borrowed : receiverAccess ≠ .owned) (conflict : requested ≠ .shared ∨ receiverAccess = .unique) :
    ¬ Permitted after receiver.authority requested receiver.address :=
  EnterWorldAttempt.contextual_receiver_exclusive valid inventory typed entered borrowed conflict

theorem EnterWorld.fresh_context {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {source : EntrySource}
    (entered : EnterWorld program before caller function source callee after) :
    callee.activation = before.nextActivation ∧ callee.scope = before.world.nextRegion ∧ callee.region = before.world.nextRegion := by
  obtain ⟨withRegion,prepared,inputs,environment,declaration,bound,selected,fresh,preparation,incoming,chained,finished,contextEq,unsafeAllowed⟩ := entered
  simp [contextEq]

theorem EnterWorld.resident_lease_owned {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {receiver : ResolvedPlace}
    {access : Access} {arguments : List InvocationInput}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (entered : EnterWorld program before caller function (.resident receiver access arguments) callee after)
    (borrowed : access ≠ .owned) :
    ∃ handle root, after.root handle = some root ∧ root.home = .temporary before.nextActivation before.world.nextRegion ∧
      root.region = before.world.nextRegion := by
  obtain ⟨withRegion,prepared,inputs,environment,declaration,bound,selected,fresh,preparation,incoming,chained,finished,contextEq,unsafeAllowed⟩ := entered
  have regionTyped := fresh.worldTyped typed
  have preparedTyped := preparation.worldTyped valid inventory regionTyped
  cases preparation with
  | resident callable instanced lent capturesProof consumedProof =>
    cases consumedProof with
    | lent consumeBorrowed =>
      obtain ⟨witness,root,_,rootSelected,home,atRegion,_⟩ := Kernel.LendsResident.lease_owned lent borrowed
      obtain ⟨changed,present,location⟩ := Kernel.BindsInputsAttemptFor.root_retained preparedTyped.1 chained rootSelected
      cases finished with
      | resident receiverFinished =>
        cases receiverFinished with
        | lent finishBorrowed =>
          have sameHome : changed.home = .temporary before.nextActivation before.world.nextRegion := by
            have same : changed.home = root.home := by
              simpa [Root.location] using congrArg Root.home location
            simpa only [contextEq] using same.trans home
          have sameRegion : changed.region = before.world.nextRegion := by
            have same : changed.region = root.region := by
              simpa [Root.location] using congrArg Root.region location
            simpa only [contextEq] using same.trans atRegion
          exact ⟨witness.handle,changed,present,sameHome,sameRegion⟩
        | owned stored shell callableHead holes resources permittedEaten written =>
          exact False.elim (borrowed rfl)
    | owned stored shell callableHead permittedEaten written =>
      exact False.elim (borrowed rfl)

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

/-- Every local entry step — completed or exhausted — is one outcome-indexed
enter attempt on the actual transition. -/
theorem LocalStep.enter_world {program : Kernel.Program} {before after : State} {event : Option Event}
    {caller : Context} {function : Function} {source : EntrySource} {tail : Bool}
    (task : before.task = .enter caller function source tail)
    (step : LocalStep program before event after) :
    ∃ callee entered outcome, EnterWorldAttempt program before caller function source callee entered outcome ∧
      (after.world = entered ∨ ∃ custody, RelinquishesCustody entered custody after.world) := by
  cases step with
  | evaluateExhausted => simp_all
  | bindExhausted => simp_all
  | invokeExhausted => simp_all
  | enterExhausted stepTask attempt =>
    rw [task] at stepTask
    cases stepTask
    exact ⟨_,_,.exhausted,attempt,Or.inl rfl⟩
  | resultExhausted => simp_all
  | activationReturnExhausted => simp_all
  | scopeReturnExhausted => simp_all
  | evaluate => simp_all
  | bind => simp_all
  | result => simp_all
  | discard => simp_all
  | assign => simp_all
  | transfer => simp_all
  | invoke => simp_all
  | tailRequest => simp_all
  | call => simp_all
  | enter stepTask entered =>
    rw [task] at stepTask
    cases stepTask
    exact ⟨_,_,.complete,entered,Or.inl rfl⟩
  | enterTail stepTask entered relinquished _ _ _ _ =>
    rw [task] at stepTask
    cases stepTask
    exact ⟨_,_,.complete,entered,Or.inr ⟨_,relinquished⟩⟩
  | bindReturn => simp_all
  | activationReturn => simp_all
  | topReturn => simp_all
  | scope => simp_all
  | scopeReturn => simp_all
  | label => simp_all
  | labelReturn => simp_all
  | choose => simp_all
  | patternDone => simp_all
  | patternBind => simp_all
  | patternShell => simp_all
  | patternDispose => simp_all
  | unsafeAllowed => simp_all
  | cleanupDone => simp_all
  | cleanupRoot => simp_all
  | destroyVacant => simp_all
  | destroyHook => simp_all
  | hookReturned => simp_all
  | destroyStructural => simp_all
  | destroyReference => simp_all
  | fieldsDone => simp_all
  | fieldNext => simp_all
  | shellDone => simp_all
  | retire => simp_all
  | regionEnd => simp_all
  | loanEnd => simp_all
  | loanAlreadyEnded => simp_all
  | releaseReferenced => simp_all
  | releaseResourceHeld => simp_all
  | releaseBorrowed => simp_all
  | releaseOwnedClaim => simp_all
  | releaseStorageRetained => simp_all
  | releaseStorageReturned => simp_all
  | releaseRoot => simp_all
  | releaseChild => simp_all
  | releaseAlreadyEnded => simp_all
  | endLoan => simp_all
  | abort => simp_all

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
  obtain ⟨callee,entered,outcome,attempt,finish⟩ := step.enter_world task
  have negated := EnterWorldAttempt.resident_exclusive valid inventory typed attempt borrowed conflict
  rcases finish with same | ⟨custody,relinquished⟩
  · intro allowed
    exact negated (same ▸ allowed)
  · intro allowed
    exact negated (relinquished.permitted_reflected allowed)

theorem LocalStep.contextual_entry_exclusive {program : Kernel.Program} {before after : State} {event : Option Event}
    {caller : Context} {function : Function} {receiver witness : ResolvedPlace}
    {receiverAccess witnessAccess : Access} {inputs : List InvocationInput} {tail : Bool} {requested : Access}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .enter caller function (.contextual receiver receiverAccess witness witnessAccess inputs) tail)
    (step : LocalStep program before event after)
    (borrowed : witnessAccess ≠ .owned) (conflict : requested ≠ .shared ∨ witnessAccess = .unique) :
    ¬ Permitted after.world witness.authority requested witness.address := by
  obtain ⟨callee,entered,outcome,attempt,finish⟩ := step.enter_world task
  have negated := EnterWorldAttempt.contextual_witness_exclusive valid inventory typed attempt borrowed conflict
  rcases finish with same | ⟨custody,relinquished⟩
  · intro allowed
    exact negated (same ▸ allowed)
  · intro allowed
    exact negated (relinquished.permitted_reflected allowed)

end Execution
end Glorious.Language
