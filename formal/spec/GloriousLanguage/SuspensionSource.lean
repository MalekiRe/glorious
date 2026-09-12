import GloriousLanguage.SuspensionOrigins

/-! Actual ordinary source transitions preserve the shared suspension
inventory. Capturing and settling effects use their dedicated producer
proofs; ordinary computation cannot invent or retire suspended storage. -/
namespace Glorious.Language.Execution

open Kernel

theorem LocalStep.suspensionExtension {program : Kernel.Program} {before after : State} {event : Option Event}
    (step : LocalStep program before event after) : before.world.SuspensionExtension after.world := by
  cases step <;> try exact .refl _
  case evaluate allocated => exact allocated.suspensionExtension (by intro id; simp)
  case bind allocated => exact allocated.suspensionExtension (by intro id; simp)
  case result kept => exact kept.suspensionExtension
  case transfer moved => exact moved.suspensionExtension
  case invoke allocated => exact allocated.suspensionExtension (by intro id; simp)
  case call consumed => exact consumed.suspensionExtension
  case enter entered => exact entered.suspensionExtension
  case enterTail => apply EnterWorld.suspensionExtension; assumption
  case bindReturn moved => exact moved.suspensionExtension
  case activationReturn => apply Protect.suspensionExtension; assumption
  case scope => apply FreshRegion.suspensionExtension; assumption
  case scopeReturn => apply Protect.suspensionExtension; assumption
  case patternBind bound => exact bound.suspensionExtension
  case patternShell consumed => exact consumed.suspensionExtension
  case destroyHook =>
    apply World.SuspensionExtension.trans
    · apply Temporary.suspensionExtension; assumption
    · apply FormsLoan.suspensionExtension; assumption
  case destroyReference => apply World.write_suspensionExtension; assumption
  case shellDone => apply World.write_suspensionExtension; assumption
  case retire retired => exact retired.suspensionExtension
  case regionEnd ended => exact ended.suspensionExtension
  case loanEnd ended => exact ended.suspensionExtension
  case releaseRoot ended => exact ended.suspensionExtension
  case releaseChild ended => exact ended.suspensionExtension

theorem AtomStep.suspensionExtension {program : Kernel.Program} {before after : State} {event : Option Event}
    (step : AtomStep program before event after) : before.world.SuspensionExtension after.world := by
  cases step with
  | constant _ _ _ written => exact (World.write_suspensionExtension written).trans (.of_roots (Nat.le_refl _) rfl)
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
  case leave => apply Protect.suspensionExtension; assumption
  case reserve resolved types distinct disjoint exclusive typeEq allocation created =>
    exact ((allocation.suspensionExtension (by intro id; simp)).trans created.suspensionExtension).trans
      (.of_roots (Nat.le_refl _) rfl)
  case available moved => exact moved.suspensionExtension
  case destroyAvailable =>
    apply World.SuspensionExtension.trans
    · apply World.write_suspensionExtension; assumption
    · exact .of_roots (Nat.le_refl _) rfl
  case destroySpentAvailable => apply World.write_suspensionExtension; assumption
  case contextualCall consumed used => exact consumed.suspensionExtension.trans used.suspensionExtension
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
    (notCancel : ∀ id, event ≠ some (.cancel id)) : before.world.SuspensionExtension after.world := by
  cases step <;> try exact .refl _
  case install task installed => exact installed.suspensionExtension
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
    (notCancel : ∀ id, event ≠ some (.cancel id)) : after.SuspensionsWellFormed := by
  have change := step.resumption_change
  have table : after.resumptions = before.resumptions ∧ after.nextContinuation = before.nextContinuation := by
    cases change with
    | unchanged table counter _ _ => exact ⟨table,counter⟩
    | create => exact False.elim (notCapture _ rfl)
    | last => exact False.elim (notReplay _ _ rfl)
    | copy => exact False.elim (notReplay _ _ rfl)
    | cancel => exact False.elim (notCancel _ rfl)
  exact valid.transport well (step.ordinary_suspensionExtension notCapture notReplay notCancel)
    table.1 (Nat.le_of_eq table.2.symm)

/-- Full effect preservation covers both capture forms, the last and copied
replay, cancellation, and every ordinary handler transition. -/
theorem EffectStep.suspensions {program : Kernel.Program} {before after : State} {event : Option Event}
    (programValid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (valid : before.SuspensionsWellFormed) (typed : Typing.WorldTyped program before.world)
    (step : EffectStep program before event after) : after.SuspensionsWellFormed := by
  by_cases capture : ∃ id, event = some (.suspend id)
  · obtain ⟨id,rfl⟩ := capture
    exact step.create_suspensions programValid inventory valid typed
  by_cases replay : ∃ id last, event = some (.replay id last)
  · obtain ⟨id,last,rfl⟩ := replay
    cases last with
    | false => exact step.copy_suspensions valid typed
    | true => exact step.last_suspensions valid typed
  by_cases cancel : ∃ id, event = some (.cancel id)
  · obtain ⟨id,rfl⟩ := cancel
    exact step.cancel_suspensions valid
  exact step.ordinary_suspensions valid typed.1
    (fun id same => capture ⟨id,same⟩) (fun id last same => replay ⟨id,last,same⟩) (fun id same => cancel ⟨id,same⟩)

end Glorious.Language.Execution
