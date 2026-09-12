import GloriousLanguage.SuspensionOrigins

/-! Actual foreign entry, host transitions and callback handoffs preserve the
same suspension inventory as ordinary source execution. The host's operational
mutation contract produces storage preservation; no post-state inventory or
separate foreign ownership ledger is assumed. -/
namespace Glorious.Language.Foreign

open Kernel Execution

theorem Mutation.suspensionExtension {program : Kernel.Program} {policy : AuthorityPolicy} {before after : World}
    (changed : Mutation program policy before after)
    (noSuspendedHome : ∀ home region, policy.home home region → ∀ id, home ≠ .suspended id) :
    before.SuspensionExtension after := by
  refine ⟨changed.homeExtension.counter,?_,?_⟩
  · intro id root suspension bound found home
    exact changed.suspended_location bound found home
  · intro id root suspension found home
    obtain ⟨original,originalAt,location⟩ := changed.suspended_origin noSuspendedHome found home
    exact ⟨original,originalAt,location.symm⟩

theorem Mutations.suspensionExtension {program : Kernel.Program} {policy : AuthorityPolicy} {before after : World}
    (changed : Mutations program policy before after)
    (noSuspendedHome : ∀ home region, policy.home home region → ∀ id, home ≠ .suspended id) :
    before.SuspensionExtension after := by
  induction changed with
  | refl => exact .refl _
  | cons first _ ih => exact (first.suspensionExtension noSuspendedHome).trans ih

theorem Model.Lawful.host_suspensionExtension {program : Kernel.Program} {model : Model}
    {session : ForeignSession} {imported : Import} {contract : Contract} {before after : World}
    {observation next : List Nat} {action : HostAction}
    (lawful : model.Lawful program) (well : before.WellFormed)
    (selected : Selected program model session.call imported contract) (active : contract.session before session)
    (step : model.step session.call.binding.declaration before session observation after action next) :
    before.SuspensionExtension after :=
  (lawful.step _ _ _ _ _ _ _ _ selected well active step).1.suspensionExtension
    (fun _ _ admitted id => Policy.no_suspended_home admitted id)

/-- The entire foreign-step family, including both callback handoffs, uses
the actual ordinary allocation, lending, move, consume and retirement paths. -/
theorem Step.suspensionExtension {program : Kernel.Program} {model : Model}
    {before after : State} {event : Option Event}
    (lawful : model.Lawful program) (well : before.world.WellFormed)
    (step : Step program model before event after) : before.world.SuspensionExtension after.world := by
  cases step with
  | enter _ _ protectedWorld _ _ _ => exact protectedWorld.suspensionExtension
  | host _ _ selected active step => exact lawful.host_suspensionExtension well selected active step
  | result _ _ selected active step _ transferred =>
    exact (lawful.host_suspensionExtension well selected active step).trans transferred.suspensionExtension
  | callback _ _ selected active step _ _ _ _ _ _ _ _ _ lent _ _ consumed =>
    exact (lawful.host_suspensionExtension well selected active step).trans
      (Kernel.LendsResident.suspensionExtension lent |>.trans consumed.suspensionExtension)
  | callbackResult _ _ _ _ protectedWorld retired =>
    exact protectedWorld.suspensionExtension.trans retired.suspensionExtension
  | callbackReturned => exact .refl _
  | fault _ _ selected active step => exact lawful.host_suspensionExtension well selected active step

/-- Historical capture bounds, exact active ownership and fresh suspension
identities survive every actual foreign transition. This is preservation from
the incoming invariant, not admission of the desired postcondition. -/
theorem Step.suspensions {program : Kernel.Program} {model : Model}
    {before after : State} {event : Option Event}
    (lawful : model.Lawful program) (well : before.world.WellFormed)
    (suspensions : before.SuspensionsWellFormed)
    (step : Step program model before event after) : after.SuspensionsWellFormed := by
  apply suspensions.transport well (step.suspensionExtension lawful well)
  · cases step <;> rfl
  · cases step <;> exact Nat.le_refl _

end Glorious.Language.Foreign
