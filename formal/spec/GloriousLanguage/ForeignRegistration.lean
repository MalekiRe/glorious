import GloriousLanguage.ForeignAuthority
import GloriousLanguage.ExecutionPreservation

/-! Callback registration preserves the exact handed-off authority. A host
can retain a granted callback, but neither retaining its numeric address nor
passing it through multiple host states upgrades its invocation authority. -/
namespace Glorious.Language.Foreign

open Kernel Execution

theorem RegistrationOrigin.active_authority {program : Kernel.Program} {contract : Contract} {model : Model}
    {initial current : World} {session : ForeignSession} {previous : List Nat} {registration : Registration}
    (origin : RegistrationOrigin program contract model initial current session previous registration)
    (active : registration.active = true) :
    registration ∈ model.registrations previous ∨
      (Accessible program model contract initial current session registration.place ∧
        (registration.retained = true → contract.retainable current session registration.owner)) := by
  cases origin with
  | existing member => exact Or.inl member
  | unregister => cases active
  | register granted retention => exact Or.inr ⟨granted,retention⟩

theorem RegistrationsPermitted.active_authority {program : Kernel.Program} {contract : Contract} {model : Model}
    {initial current : World} {session : ForeignSession} {before after : List Nat} {registration : Registration}
    (permitted : RegistrationsPermitted program contract model initial current session before after)
    (member : registration ∈ model.registrations after) (active : registration.active = true) :
    registration ∈ model.registrations before ∨
      (Accessible program model contract initial current session registration.place ∧
        (registration.retained = true → contract.retainable current session registration.owner)) :=
  (permitted registration member).active_authority active

theorem RegistrationsPermitted.new_authority {program : Kernel.Program} {contract : Contract} {model : Model}
    {initial current : World} {session : ForeignSession} {before after : List Nat} {registration : Registration}
    (permitted : RegistrationsPermitted program contract model initial current session before after)
    (member : registration ∈ model.registrations after) (active : registration.active = true)
    (new : registration ∉ model.registrations before) :
    Accessible program model contract initial current session registration.place ∧
      (registration.retained = true → contract.retainable current session registration.owner) :=
  (permitted.active_authority member active).resolve_left new

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

/-- Proof view of a grant at an actual registry-changing producer. The host
mutation world is distinguished from subsequent source transfer/lending. Start
and callback return use their real handoffs, not a fabricated host continuation.
This view is derived from execution and never an admission premise. -/
inductive RegistrationGranted (program : Kernel.Program) (model : Model) (before after : State)
    (registration : Registration) : Prop where
  | enter {context destination binding arguments operands next addresses prepared signature imported contract state} :
      before.task = .primitive context destination binding arguments operands next →
      Protects program context before.world operands addresses prepared →
      Selected program model ⟨context,destination,binding,arguments,signature,addresses⟩ imported contract →
      contract.precondition prepared
        ⟨⟨context,destination,binding,arguments,signature,addresses⟩,before.hostState,AmbientExposed before.frames⟩ →
      model.start binding.declaration prepared
        ⟨⟨context,destination,binding,arguments,signature,addresses⟩,before.hostState,AmbientExposed before.frames⟩ state →
      after.hostState = state →
      Accessible program model contract prepared prepared
        ⟨⟨context,destination,binding,arguments,signature,addresses⟩,before.hostState,AmbientExposed before.frames⟩ registration.place →
      (registration.retained = true → contract.retainable prepared
        ⟨⟨context,destination,binding,arguments,signature,addresses⟩,before.hostState,AmbientExposed before.frames⟩ registration.owner) →
      RegistrationGranted program model before after registration
  | host {session next imported contract observation current action state} :
      before.task = .foreign session next →
      Selected program model session.call imported contract → contract.session before.world session →
      model.step session.call.binding.declaration before.world session observation current action state →
      after.hostState = state → Accessible program model contract before.world current session registration.place →
      (registration.retained = true → contract.retainable current session registration.owner) →
      RegistrationGranted program model before after registration
  | returned {session callback result next imported contract state} :
      before.task = .foreignCallbackReturned session callback result next →
      Selected program model session.call imported contract →
      contract.callbackPostcondition before.world session before.hostState callback result →
      model.callbackReturned session.call.binding.declaration before.world session before.hostState callback result state →
      after.hostState = state →
      Accessible program model contract before.world before.world (session.returned result before.hostState) registration.place →
      (registration.retained = true →
        contract.retainable before.world (session.returned result before.hostState) registration.owner) →
      RegistrationGranted program model before after registration

/-- All real registry-changing boundaries use the same origin law, including
an interrupted host action that immediately enters a source callback. -/
theorem Step.registrations {program : Kernel.Program} {model : Model} {before after : State}
    {event : Option Event} {registration : Registration}
    (valid : ProgramWellFormed program.declarations) (inventory : BodyInventory program)
    (lawful : model.Lawful program) (typed : Typing.WorldTyped program before.world)
    (step : Step program model before event after)
    (member : registration ∈ model.registrations after.hostState) (active : registration.active = true) :
    registration ∈ model.registrations before.hostState ∨ RegistrationGranted program model before after registration := by
  cases step with
  | enter task selected protectedWorld callTyped precondition started =>
    have permission := (lawful.start _ _ _ _ _ selected
      (protectedWorld.worldTyped valid inventory typed).1 callTyped precondition started).2.2
    rcases permission.active_authority member active with old | ⟨access,retention⟩
    · exact Or.inl old
    · exact Or.inr (.enter task protectedWorld selected precondition started rfl access retention)
  | host task state selected sessionActive changed
  | result task state selected sessionActive changed _ _
  | callback task state selected sessionActive changed _ _ _ _ _ _ _ _ _ _ _ _ _
  | fault task state selected sessionActive changed =>
    have permission := (lawful.step _ _ _ _ _ _ _ _ selected typed.1 sessionActive changed).2.2.2.2.2.2.2.2
    rcases permission.active_authority member active with old | ⟨access,retention⟩
    · exact Or.inl (state ▸ old)
    · exact Or.inr (.host task selected sessionActive changed rfl access retention)
  | callbackResult => exact Or.inl member
  | callbackReturned task selected postcondition returned =>
    have permission := (lawful.callbackReturned _ _ _ _ _ _ _ _ selected typed.1 postcondition returned).2.2
    rcases permission.active_authority member active with old | ⟨access,retention⟩
    · exact Or.inl old
    · exact Or.inr (.returned task selected postcondition returned rfl access retention)

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
    rcases permits.active_authority member active with old | granted
    · exact Or.inl (state ▸ old)
    · exact Or.inr (.host task selected sessionActive changed rfl granted.1 granted.2)
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

namespace Glorious.Language.Execution

theorem Step.registrations {program : Kernel.Program} {host : Foreign.Model} {before after : State}
    {event : Option Event} {registration : Foreign.Registration}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (step : Step program host before event after)
    (member : registration ∈ host.registrations after.hostState) (active : registration.active = true) :
    registration ∈ host.registrations before.hostState ∨ Foreign.RegistrationGranted program host before after registration := by
  rcases step.host_state with unchanged | foreign
  · exact Or.inl (unchanged ▸ member)
  · exact foreign.registrations valid inventory lawful typed member active

/-- Through arbitrary source execution and nested callbacks, every active
record is the exact admitted original or received its exact authority at a real
earlier registry-changing boundary on this execution, with the actual trace split. -/
theorem Run.registration_origin {program : Kernel.Program} {host : Foreign.Model} {before after : State}
    {events : List Event} {registration : Foreign.Registration}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (run : Run program host before events after)
    (member : registration ∈ host.registrations after.hostState) (active : registration.active = true) :
    registration ∈ host.registrations before.hostState ∨
      ∃ earlier later prior suffix event,
        Run program host before prior earlier ∧ Step program host earlier event later ∧
        Run program host later suffix after ∧ Foreign.RegistrationGranted program host earlier later registration ∧
        events = prior ++ event.toList ++ suffix := by
  induction run with
  | refl => exact Or.inl member
  | @silent before middle after events step rest ih =>
    rcases ih (step.worldTyped valid inventory lawful typed) member with atMiddle |
        ⟨earlier,later,prior,suffix,grantEvent,first,grant,last,authority,trace⟩
    · rcases step.registrations valid inventory lawful typed atMiddle active with old | grant
      · exact Or.inl old
      · exact Or.inr ⟨before,middle,[],events,none,.refl,step,rest,grant,rfl⟩
    · exact Or.inr ⟨earlier,later,prior,suffix,grantEvent,.silent step first,grant,last,authority,trace⟩
  | @visible before middle after event events step rest ih =>
    rcases ih (step.worldTyped valid inventory lawful typed) member with atMiddle |
        ⟨earlier,later,prior,suffix,grantEvent,first,grant,last,authority,trace⟩
    · rcases step.registrations valid inventory lawful typed atMiddle active with old | grant
      · exact Or.inl old
      · exact Or.inr ⟨before,middle,[],events,some event,.refl,step,rest,grant,rfl⟩
    · exact Or.inr ⟨earlier,later,event :: prior,suffix,grantEvent,.visible step first,grant,last,authority,
        by simpa only [List.cons_append] using congrArg (List.cons event) trace⟩

end Glorious.Language.Execution
