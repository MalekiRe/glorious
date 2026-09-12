import GloriousLanguage.ForeignAuthority

/-! Callback registration preserves the exact handed-off authority. A host
can retain a granted callback, but neither retaining its numeric address nor
passing it through multiple host states upgrades its invocation authority. -/
namespace Glorious.Language.Foreign

open Kernel Execution

theorem RegistrationsPermitted.new_authority {program : Kernel.Program} {contract : Contract} {model : Model}
    {initial current : World} {session : ForeignSession} {before after : List Nat} {registration : Registration}
    (permitted : RegistrationsPermitted program contract model initial current session before after)
    (member : registration ∈ model.registrations after) (active : registration.active = true)
    (new : registration ∉ model.registrations before) :
    Accessible program model contract initial current session registration.place ∧
      (registration.retained = true → contract.retainable current session registration.owner) :=
  (permitted registration member active).resolve_left new

/-- Initial registration is checked against the actual call handoff, not the
new registry itself. In particular, a newly registered record cannot seed its
own stronger authority. -/
theorem Model.Lawful.start_registration_authority {program : Kernel.Program} {model : Model}
    {initial : ForeignSession} {imported : Import} {contract : Contract} {world : World} {state : List Nat}
    {registration : Registration}
    (lawful : model.Lawful program) (well : world.WellFormed)
    (selected : Selected program model initial.call imported contract) (typed : CallTyped program world initial.call)
    (precondition : contract.precondition world initial)
    (started : model.start initial.call.binding.declaration world initial state)
    (member : registration ∈ model.registrations state) (active : registration.active = true)
    (new : registration ∉ model.registrations initial.state) :
    Accessible program model contract world world initial registration.place ∧
      (registration.retained = true → contract.retainable world initial registration.owner) :=
  (lawful.start initial imported contract world state selected well typed precondition started).2.2.new_authority
    member active new

/-- Source callback completion grants only the exact protected result added
by `returned`, together with the pre-existing session handoffs. -/
theorem Model.Lawful.returned_registration_authority {program : Kernel.Program} {model : Model}
    {session : ForeignSession} {imported : Import} {contract : Contract} {world : World}
    {current next : List Nat} {callback : Identity} {result : Address} {registration : Registration}
    (lawful : model.Lawful program) (well : world.WellFormed)
    (selected : Selected program model session.call imported contract)
    (postcondition : contract.callbackPostcondition world session current callback result)
    (returned : model.callbackReturned session.call.binding.declaration world session current callback result next)
    (member : registration ∈ model.registrations next) (active : registration.active = true)
    (new : registration ∉ model.registrations current) :
    Accessible program model contract world world (session.returned result current) registration.place ∧
      (registration.retained = true → contract.retainable world (session.returned result current) registration.owner) :=
  (lawful.callbackReturned session imported contract world current callback result next
    selected well postcondition returned).2.2.new_authority member active new

/-- Proof view of a grant at an actual host-transition boundary. It records
the existing protocol's precise access judgment; it introduces no alternative
source of authority and is never an admission premise. -/
def RegistrationGranted (program : Kernel.Program) (model : Model) (before after : State)
    (registration : Registration) : Prop :=
  ∃ session next imported contract, before.task = .foreign session next ∧
    Selected program model session.call imported contract ∧ contract.session before.world session ∧
    Accessible program model contract before.world after.world session registration.place ∧
    (registration.retained = true → contract.retainable after.world session registration.owner)

theorem Step.continue_registrations {program : Kernel.Program} {model : Model} {before after : State}
    {event : Option Event} {session continued : ForeignSession} {next following : Code} {registration : Registration}
    (lawful : model.Lawful program) (well : before.world.WellFormed)
    (step : Step program model before event after)
    (task : before.task = .foreign session next) (result : after.task = .foreign continued following)
    (member : registration ∈ model.registrations after.hostState) (active : registration.active = true) :
    registration ∈ model.registrations before.hostState ∨ RegistrationGranted program model before after registration := by
  cases step with
  | enter original => cases original.symm.trans task
  | host original state selected sessionActive changed =>
    cases original.symm.trans task
    have permits := (lawful.step _ _ _ _ _ _ _ _ selected well sessionActive changed).2.2.2.2.2.2.2.2
    rcases permits registration member active with old | granted
    · exact Or.inl (state ▸ old)
    · exact Or.inr ⟨_,_,_,_,task,selected,sessionActive,granted⟩
  | result => cases result
  | callback => cases result
  | callbackResult original => cases original.symm.trans task
  | callbackReturned original => cases original.symm.trans task
  | fault => cases result

/-- Across arbitrarily many actual host continuations, every active record is
either the exact original record or has an actual earlier authority grant on
that execution. Retaining, unregistering and re-registering cannot erase the
need for the precise callback authority at its point of introduction. -/
theorem HostRun.registration_origin {program : Kernel.Program} {model : Model} {before after : State}
    {events : List Event} {registration : Registration}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (lawful : model.Lawful program) (typed : Typing.WorldTyped program before.world)
    (run : HostRun program model before events after)
    (member : registration ∈ model.registrations after.hostState) (active : registration.active = true) :
    registration ∈ model.registrations before.hostState ∨
      ∃ earlier later prior suffix event,
        HostRun program model before prior earlier ∧ Step program model earlier event later ∧
        HostRun program model later suffix after ∧ RegistrationGranted program model earlier later registration ∧
        events = prior ++ event.toList ++ suffix := by
  induction run with
  | refl task => exact Or.inl member
  | @cons before middle after event events session next task step rest ih =>
    have middleTyped := step.worldTyped valid inventory lawful typed
    rcases ih middleTyped member with atMiddle | ⟨earlier,later,prior,suffix,grantEvent,first,grant,last,authority,trace⟩
    · obtain ⟨continued,following,middleTask⟩ := rest.start
      rcases step.continue_registrations lawful typed.1 task middleTask atMiddle active with old | grant
      · exact Or.inl old
      · exact Or.inr ⟨before,middle,[],events,event,.refl task,step,rest,grant,rfl⟩
    · exact Or.inr ⟨earlier,later,event.toList ++ prior,suffix,grantEvent,.cons task step first,grant,last,authority,
        by simp only [trace,List.append_assoc]⟩

end Glorious.Language.Foreign
