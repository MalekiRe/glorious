import GloriousLanguage.SuspensionOrigins

/-! Actual ordinary source transitions preserve the shared suspension
inventory. Capturing and settling effects use their dedicated producer
proofs; ordinary computation cannot invent or retire suspended storage. -/
namespace Glorious.Language.Execution

open _root_.Glorious.Language.Kernel

theorem RelinquishesCustody.suspensionExtension {before after : World} {custody : ClaimCustody}
    (relinquished : RelinquishesCustody before custody after) : before.SuspensionExtension after := by
  have rows : ∀ id loan, before.loans.get id = some loan →
      ∃ current, after.loans.get id = some current :=
    fun id loan found => (relinquished.retained found).imp fun _ h => h.1
  cases relinquished
  refine World.SuspensionExtension.of_locations ?_ ?_ ?_
  · exact Nat.le_refl _
  · intro id; rfl
  · intro current recorded
    exact recorded.transport rows

theorem ReturnsResources.suspensionExtension {program : Kernel.Program} {source receiver : Context}
    {before after : World} {result : Address} {context : Context}
    (returned : ReturnsResources program source receiver before result context after) :
    before.SuspensionExtension after := by
  cases returned with
  | localReturn => exact .refl _
  | invocationReturn _ _ _ bindings relinquished =>
    exact (bindings.suspensionExtension).trans (RelinquishesCustody.suspensionExtension relinquished)

theorem ReturnsStorageLoan.suspensionExtension {before after : World} {id : Identity}
    (returned : ReturnsStorageLoan before id after) : before.SuspensionExtension after := by
  refine ⟨returned.homeExtension,?_,?_,returned.recorded⟩
  · intro rootId root suspension bound found home
    cases returned
    exact congrArg (Option.map Root.location) found
  · intro rootId root suspension found home
    cases returned
    exact ⟨root,found,rfl⟩

/- `suspendRoots` and `restoreRoots` rewrite each root row's `home`. Because
`Root.location` keeps the home field, neither preserves `World.SuspensionExtension`
unconditionally: a row that is *already* suspended with a different suspension
identity would lose the location the invariant retains. The real arms below
therefore need the guarded form - the selected roots are still live when the
capture relocates them (the `DelimitedRoots`/`SuspendPermission` facts) - not an
unconditional producer. -/


theorem ProtectsAttemptFor.suspensionExtension {program : Kernel.Program} {context : Context}
    {footprint : List Address} {before after : World} {sources : List ResolvedPlace}
    {destinations : List Address} {outcome : PreparationOutcome}
    (kept : ProtectsAttemptFor program context footprint before sources destinations after outcome) :
    before.SuspensionExtension after := by
  induction kept with
  | nil => exact .refl _
  | cons _ head _ ih => exact head.suspensionExtension.trans ih
  | exhausted _ _ => exact .refl _


theorem LocalStep.suspensionExtension {program : Kernel.Program} {before after : State} {event : Option Event}
    (step : LocalStep program before event after) : before.world.SuspensionExtension after.world := by
  cases step <;> try exact .refl _
  case evaluate allocated => exact allocated.suspensionExtension (by intro id; simp)
  case bind allocated => exact allocated.suspensionExtension (by intro id; simp)
  case result kept => exact kept.suspensionExtension
  case transfer moved => exact moved.suspensionExtension
  case invoke allocated => exact allocated.suspensionExtension (by intro id; simp)
  case enter entered => exact entered.suspensionExtension
  case enterExhausted _ attempt => exact attempt.suspensionExtension
  case labelReturn _ _ returned => exact ReturnsResources.suspensionExtension returned
  case releaseStorageReturned _ _ returned =>
    exact _root_.Glorious.Language.Execution.ReturnsStorageLoan.suspensionExtension returned
  case enterTail _ entered handed _ _ _ _ =>
    exact (EnterWorldAttempt.suspensionExtension entered).trans
      (RelinquishesCustody.suspensionExtension handed)
  case bindReturn _ _ transfer returned =>
    exact (transfer.suspensionExtension).trans (ReturnsResources.suspensionExtension returned)
  case activationReturn _ _ _ kept returned _ _ =>
    exact (Protect.suspensionExtension kept).trans (ReturnsResources.suspensionExtension returned)
  case scope _ fresh _ => exact fresh.suspensionExtension
  case scopeReturn _ _ kept returned _ _ =>
    exact (Protect.suspensionExtension kept).trans (ReturnsResources.suspensionExtension returned)
  case patternBind bound => exact bound.suspensionExtension
  case patternShell consumed => exact consumed.suspensionExtension
  case destroyHook _ _ _ _ _ temporary forms _ =>
    exact (temporary.suspensionExtension).trans (forms.suspensionExtension)
  case destroyReference _ _ _ _ _ written =>
    exact World.write_suspensionExtension written
  case shellDone _ _ _ _ relinq written =>
    exact (RelinquishesCustody.suspensionExtension relinq).trans
      (World.write_suspensionExtension written)
  case retire retired => exact retired.suspensionExtension
  case regionEnd ended => exact ended.suspensionExtension
  case loanEnd ended => exact ended.suspensionExtension
  case releaseRoot ended => exact ended.suspensionExtension
  case releaseChild ended => exact ended.suspensionExtension

theorem AtomStep.suspensionExtension {program : Kernel.Program} {before after : State} {event : Option Event}
    (step : AtomStep program before event after) : before.world.SuspensionExtension after.world := by
  cases step with
  | constant _ _ _ written =>
    exact (World.write_suspensionExtension written).trans
      (.of_roots (Nat.le_refl _) rfl (fun _ recorded => recorded))
  | acquire _ _ acquired => exact acquired.suspensionExtension
  | borrow _ _ borrowed => exact borrowed.suspensionExtension
  | construct _ _ _ _ _ constructed => exact constructed.suspensionExtension
  | closure _ _ captured _ _ constructed => exact captured.suspensionExtension.trans constructed.suspensionExtension
  | function _ _ _ _ constructed => exact constructed.suspensionExtension
  | operation _ _ constructed => exact constructed.suspensionExtension
  | label _ _ _ constructed => exact constructed.suspensionExtension
  | primitive => exact .refl _

theorem ControlStep.suspensionExtension {program : Kernel.Program} {before after : State} {event : Option Event}
    (step : ControlStep program before event after) : before.world.SuspensionExtension after.world := by
  cases step <;> try exact .refl _
  case leave => exact Protect.suspensionExtension (by assumption)
  case reserve resolved types distinct disjoint exclusive typeEq allocation created =>
    exact ((allocation.suspensionExtension (by intro id; simp)).trans created.suspensionExtension).trans
      (.of_roots (Nat.le_refl _) rfl (fun _ recorded => recorded))
  case available moved => exact moved.suspensionExtension
  case destroyAvailable =>
    apply World.SuspensionExtension.trans
    · apply World.write_suspensionExtension; assumption
    · exact .of_roots (Nat.le_refl _) rfl (fun _ recorded => recorded)
  case destroySpentAvailable => apply World.write_suspensionExtension; assumption
  case positiveTest allocation tested => exact (allocation.suspensionExtension (by intro id; simp)).trans tested.suspensionExtension
  case negativeTest allocation tested => exact (allocation.suspensionExtension (by intro id; simp)).trans tested.suspensionExtension
  case bindings moved => exact moved.suspensionExtension

theorem LocalStep.suspensions {program : Kernel.Program} {before after : State} {event : Option Event}
    (valid : before.SuspensionsWellFormed) (well : before.world.WellFormed)
    (step : LocalStep program before event after) : after.SuspensionsWellFormed :=
  valid.transport well step.suspensionExtension (by cases step <;> rfl) (by cases step <;> exact Nat.le_refl _)

theorem AtomStep.suspensions {program : Kernel.Program} {before after : State} {event : Option Event}
    (valid : before.SuspensionsWellFormed) (well : before.world.WellFormed)
    (step : AtomStep program before event after) : after.SuspensionsWellFormed :=
  valid.transport well step.suspensionExtension (by cases step <;> rfl) (by cases step <;> exact Nat.le_refl _)

theorem ControlStep.suspensions {program : Kernel.Program} {before after : State} {event : Option Event}
    (valid : before.SuspensionsWellFormed) (well : before.world.WellFormed)
    (step : ControlStep program before event after) : after.SuspensionsWellFormed :=
  valid.transport well step.suspensionExtension (by cases step <;> rfl) (by cases step <;> exact Nat.le_refl _)

/-- Effect instructions that do not change the suspension table use only
ordinary storage producers. Exceptional inventory changes are kept explicit. -/
theorem EffectStep.ordinary_suspensionExtension {program : Kernel.Program} {before after : State} {event : Option Event}
    (step : EffectStep program before event after)
    (notCapture : ∀ id, event ≠ some (.suspend id)) (notReplay : ∀ id last, event ≠ some (.replay id last))
    (notCancel : ∀ id, event ≠ some (.cancel id)) (notFatal : event ≠ some (.fatal .resource)) :
    before.world.SuspensionExtension after.world := by
  cases step <;> try exact .refl _
  case install task installed => exact installed.suspensionExtension
  case terminalPayloadExhausted => exact False.elim (notFatal rfl)
  case suspendPayloadExhausted => exact False.elim (notFatal rfl)
  case suspendTailPayloadExhausted => exact False.elim (notFatal rfl)
  case suspendContinuationExhausted => exact False.elim (notFatal rfl)
  case resumeLastExhausted => exact False.elim (notFatal rfl)
  case resumeCopyExhausted => exact False.elim (notFatal rfl)
  case terminal task selected terminal continuation routes started keptTransfer roots cancelable plan =>
    exact started.suspensionExtension.trans keptTransfer.suspensionExtension
  case suspend => exact False.elim (notCapture _ rfl)
  case suspendTailArm => exact False.elim (notCapture _ rfl)
  case resumeLast => exact False.elim (notReplay _ _ rfl)
  case resumeCopy => exact False.elim (notReplay _ _ rfl)
  case resumeReturns task frames keptTransfer => exact keptTransfer.suspensionExtension
  case completionIdentity task frames completion started keptTransfer roots permission =>
    exact started.suspensionExtension.trans keptTransfer.suspensionExtension
  case completion task frames started keptTransfer roots permission arm plan =>
    exact started.suspensionExtension.trans keptTransfer.suspensionExtension
  case completed task frames activation keptTransfer roots permission => exact keptTransfer.suspensionExtension
  case serviced task frames activation keptTransfer roots permission => exact keptTransfer.suspensionExtension
  case disposeContinuation task stored head permission suspension cleared => exact World.write_suspensionExtension cleared
  case cancel => exact False.elim (notCancel _ rfl)

theorem EffectStep.ordinary_suspensions {program : Kernel.Program} {before after : State} {event : Option Event}
    (valid : before.SuspensionsWellFormed) (well : before.world.WellFormed)
    (step : EffectStep program before event after)
    (notCapture : ∀ id, event ≠ some (.suspend id)) (notReplay : ∀ id last, event ≠ some (.replay id last))
    (notCancel : ∀ id, event ≠ some (.cancel id)) (notFatal : event ≠ some (.fatal .resource)) :
    after.SuspensionsWellFormed := by
  have change := step.resumption_change
  have table : after.resumptions = before.resumptions ∧ after.nextContinuation = before.nextContinuation := by
    cases change with
    | unchanged table counter _ _ _ => exact ⟨table,counter⟩
    | create => exact False.elim (notCapture _ rfl)
    | last => exact False.elim (notReplay _ _ rfl)
    | copy => exact False.elim (notReplay _ _ rfl)
    | cancel => exact False.elim (notCancel _ rfl)
  exact valid.transport well (step.ordinary_suspensionExtension notCapture notReplay notCancel notFatal)
    table.1 (Nat.le_of_eq table.2.symm)

/-- Full effect preservation covers both capture forms, the last and copied
replay, cancellation, and every ordinary handler transition. -/
theorem EffectStep.suspension_storage {program : Kernel.Program} {before after : State} {event : Option Event}
    (programValid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (valid : before.SuspensionsWellFormed) (typed : Typing.WorldTyped program before.world)
    (step : EffectStep program before event after) (notFatal : event ≠ some (.fatal .resource)) :
    after.SuspensionsWellFormed ∧
      ∀ (authority : Authority), authority.Recorded before.world.loans → authority.Recorded after.world.loans := by
  by_cases capture : ∃ id, event = some (.suspend id)
  · obtain ⟨id,rfl⟩ := capture
    exact step.create_suspension_storage programValid inventory valid typed
  by_cases replay : ∃ id last, event = some (.replay id last)
  · obtain ⟨id,last,rfl⟩ := replay
    cases last with
    | false => exact step.copy_suspension_storage valid typed
    | true => exact step.last_suspension_storage valid typed
  by_cases cancel : ∃ id, event = some (.cancel id)
  · obtain ⟨id,rfl⟩ := cancel
    exact step.cancel_suspension_storage valid
  have notCapture := fun id same => capture ⟨id,same⟩
  have notReplay := fun id last same => replay ⟨id,last,same⟩
  have notCancel := fun id same => cancel ⟨id,same⟩
  exact ⟨step.ordinary_suspensions valid typed.1 notCapture notReplay notCancel notFatal,
    (step.ordinary_suspensionExtension notCapture notReplay notCancel notFatal).recorded⟩

theorem EffectStep.suspensions {program : Kernel.Program} {before after : State} {event : Option Event}
    (programValid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (valid : before.SuspensionsWellFormed) (typed : Typing.WorldTyped program before.world)
    (step : EffectStep program before event after) (notFatal : event ≠ some (.fatal .resource)) :
    after.SuspensionsWellFormed :=
  (step.suspension_storage programValid inventory valid typed notFatal).1

end Glorious.Language.Execution
