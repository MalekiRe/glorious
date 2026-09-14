import GloriousLanguage.InputBatchProgress
import GloriousLanguage.RootSelection

/-! Proper-tail cleanup is admitted at the original invocation boundary.
The actual entry determines residual residents and preserves their remaining
reference and raw-resource graphs. No entered-world cleanup certificate is
supplied by admission. -/
namespace Glorious.Language.Execution

open Kernel

/-- Caller cleanup observes only the residuals of its original residents.
Unsafe invariants are checked on those exact residual values in the original
world; neither arbitrary field insensitivity nor future closure is assumed.
Restoration targets of caller-relevant loans must remain whole. -/
structure EntrySource.CleanupAdmitted (program : Kernel.Program) (world : World)
    (function : Function) (caller : Identity) (roots : List Identity) (source : EntrySource) : Prop where
  selected : ActivationRoots world caller [] roots
  suspensible : Suspensible program world roots
  custody : world.CustodyCovered (.activation caller) (source.originalInputs function)
  lent : ∀ address ∈ source.lentStorage, address.root ∉ roots
  residuals : ∀ address original, address.root ∈ roots → world.Resident address original →
    ∀ residual, original.AfterClearing address (source.clearedStorage function) residual →
      residual.InvariantClosed program world ∧ source.PassiveCompatible world function residual
  restoration : ∀ identity loan, world.loans.get identity = some loan → loan.live = true →
    (loan.kind = .restoring ∨ loan.kind = .destructor) →
    (loan.referent.root ∈ roots ∨ ∃ address value, address.root ∈ roots ∧ world.Resident address value ∧ value.head = .reference identity) →
    (∀ written ∈ source.clearedStorage function, ¬ written.Overlaps loan.referent) ∧
    (∀ value, world.Stores loan.referent value → source.PassiveCompatible world function value)

/-- Closure of every actual surviving caller resident follows from original
closure, exact residual invariants and the real entry's graph frame. Values
fully moved into the callee impose no surviving custody obligation. -/
theorem EntrySource.CleanupAdmitted.residents_closed {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {source : EntrySource} {roots : List Identity}
    (cleanup : source.CleanupAdmitted program before.world function caller.activation roots)
    (admitted : source.Admitted program before.world caller.region function)
    (entered : EnterWorld program before caller function source callee after) (valid : before.world.WellFormed) :
    ∀ address value, address.root ∈ roots → after.Resident address value →
      value.ResourcesClosed program after ∧ value.LoansRestored program after := by
  intro address value included stored
  obtain ⟨root,found,_⟩ := (cleanup.selected.2 address.root).mp included
  have bounded := World.root_bound valid found
  obtain ⟨original,resident,pruned⟩ := entered.resident_residual valid (admitted.clearedStorage_bound valid) bounded stored
  have originalReady := cleanup.suspensible.2 address original included resident
  have closed := originalReady.1.afterClearing pruned (fun path prior residual located observed =>
    (cleanup.residuals { address with fields := address.fields ++ path } prior included (resident.nested located) residual observed).1)
  have restored := originalReady.2.afterClearing pruned
  obtain ⟨batch,framed⟩ := entered.passiveFrame valid closed restored admitted.inputs.recorded
    (cleanup.residuals address original included resident value pruned).2
  exact ⟨closed.frame_batch batch framed,restored.frame_batch batch framed⟩

/-- Original caller-relevant restoration targets remain initialized and
closed through the actual complete entry, including raw custody changes. -/
theorem EntrySource.CleanupAdmitted.restoration_closed {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {source : EntrySource} {roots : List Identity}
    (cleanup : source.CleanupAdmitted program before.world function caller.activation roots)
    (admitted : source.Admitted program before.world caller.region function)
    (entered : EnterWorld program before caller function source callee after) (valid : before.world.WellFormed)
    {identity : Identity} {loan : Loan} (found : before.world.loans.get identity = some loan) (live : loan.live = true)
    (kind : loan.kind = .restoring ∨ loan.kind = .destructor)
    (relevant : loan.referent.root ∈ roots ∨ ∃ address value, address.root ∈ roots ∧ before.world.Resident address value ∧ value.head = .reference identity) :
    after.Initialized loan.referent ∧ after.ResourcesClosed program loan.referent := by
  have original := cleanup.suspensible.1 identity loan found live kind relevant
  have conditions := cleanup.restoration identity loan found live kind relevant
  have read := entered.read_outside valid (World.live_loan_root_bound valid found live) conditions.1
  constructor
  · obtain ⟨value,stored,initialized⟩ := original.1
    exact ⟨value,read.trans stored,initialized⟩
  · intro value stored
    have prior : before.world.Stores loan.referent value := read.symm.trans stored
    have ready := original.2 value prior
    obtain ⟨batch,framed⟩ := entered.passiveFrame valid ready.1 ready.2 admitted.inputs.recorded (conditions.2 value prior)
    exact ⟨ready.1.frame_batch batch framed,ready.2.frame_batch batch framed⟩


/-- Proper-tail cleanup readiness is produced from original admission and
actual entry. New restoring loans come only from the source's lent storage;
retained reference handles obtain restoration from the canonical graph. -/
theorem EntrySource.CleanupAdmitted.enter_suspensible {program : Kernel.Program} {before : State} {after : World}
    {caller callee : Context} {function : Function} {source : EntrySource} {roots : List Identity}
    (cleanup : source.CleanupAdmitted program before.world function caller.activation roots)
    (admitted : source.Admitted program before.world caller.region function)
    (entered : EnterWorld program before caller function source callee after) (valid : before.world.WellFormed) :
    Suspensible program after roots := by
  have residents := cleanup.residents_closed admitted entered valid
  refine ⟨?_,residents⟩
  intro identity loan found live kind relevant
  rcases relevant with included | ⟨address,value,included,resident,head⟩
  · rcases entered.restoring_origin found kind with ⟨original,originalAt,shape⟩ | ⟨address,member,referent⟩
    · have kinds := congrArg Loan.kind shape
      have alive := congrArg Loan.live shape
      have referent := congrArg Loan.referent shape
      change loan.kind = original.kind at kinds
      change loan.live = original.live at alive
      change loan.referent = original.referent at referent
      have ready := cleanup.restoration_closed admitted entered valid originalAt (alive ▸ live) (kinds ▸ kind)
        (Or.inl (by rw [← referent]; exact included))
      simpa only [referent] using ready
    · exact False.elim (cleanup.lent address member (referent ▸ included))
  · have ready := residents address value included resident
    have reachable : value.ReachableReference after .owner .shared identity .owner .shared := ⟨value,.resident .root,head⟩
    obtain ⟨current,selected,_,initialized,closed⟩ := ready.2 identity .owner .shared reachable
    have same : current = loan := Option.some.inj (selected.symm.trans found)
    subst current
    exact ⟨initialized,fun target stored => ⟨closed target stored,ready.2.referent reachable found stored⟩⟩


/-- Original admission constructs the complete proper-tail transition, or the
actual resource-exhausted prefix. Caller roots, custody discharge and cleanup
closure are derived from entry, never assumed of its successor world. -/
theorem EntrySource.Admitted.tailStep {program : Kernel.Program} {before : State}
    {caller outer : Context} {function : Function} {source : EntrySource}
    {regions roots : List Identity} {rest : List Frame}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (admitted : source.Admitted program before.world caller.region function)
    (cleanup : source.CleanupAdmitted program before.world function caller.activation roots)
    (task : before.task = .enter caller function source true)
    (callerUnsafe : function.signature.unsafeAllowed = true → caller.unsafeAllowed = true)
    (different : before.nextActivation ≠ caller.activation)
    (frames : TailFrames before.frames caller.activation outer regions rest) :
    ∃ event after, LocalStep program before event after := by
  obtain ⟨callee,world,outcome,entered⟩ := admitted.enterWorldAttempt valid inventory typed callerUnsafe
  cases outcome with
  | exhausted => exact ⟨some (.fatal .resource),_,.enterExhausted task entered⟩
  | complete =>
      have custodyDifferent : ClaimCustody.activation before.nextActivation ≠ .activation caller.activation :=
        fun same => different (ClaimCustody.activation.inj same)
      have handed := EnterWorld.custody_handedOff entered typed.1 custodyDifferent cleanup.custody
      let released := world.RequestReturns (.activation caller.activation)
      have relinquished : RelinquishesCustody world (.activation caller.activation) released := .relinquish handed
      have selected : ActivationRoots released caller.activation [] roots :=
        (entered.activationRoots typed.1 cleanup.selected different).of_locations (fun _ => rfl)
      have ready := (cleanup.enter_suspensible admitted entered typed.1).relinquished relinquished
      exact ⟨some (.tail caller.activation callee.activation),_,
        .enterTail task entered relinquished frames selected ready cleanup.lent⟩


end Glorious.Language.Execution
