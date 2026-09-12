import GloriousLanguage.ControlOriginPreservation
import GloriousLanguage.ForeignRegistration

/-! Opaque registry authority has an actual origin before it can be used.
External-domain grants are root authority, projected loans are authenticated
by the shared place resolver, and registration changes consume that same
access path. Historical recording is derived, never a post-permission axiom. -/
namespace Glorious.Language

theorem Authority.recorded_of_no_parent {authority : Authority} {loans : Table Loan}
    (root : authority.parentLoan = none) : authority.Recorded loans := by
  induction authority with
  | owner => trivial
  | loan => cases root
  | shared backing ih => exact ih root

theorem Authority.lend_recorded_iff {authority : Authority} {access : Access} {loans : Table Loan} :
    (authority.lend access).Recorded loans ↔ authority.Recorded loans := by
  unfold Authority.lend
  split <;> rfl

namespace Foreign

open Kernel Execution

theorem Model.AuthoritiesRecorded.mono {model : Model} {before after : World} {state : List Nat}
    (recorded : model.AuthoritiesRecorded before state)
    (retained : ∀ (authority : Authority), authority.Recorded before.loans → authority.Recorded after.loans) :
    model.AuthoritiesRecorded after state :=
  fun registration member => retained _ (recorded registration member)

theorem Model.AuthoritiesRecorded.empty {model : Model} {world : World} {state : List Nat}
    (empty : model.registrations state = []) : model.AuthoritiesRecorded world state := by
  intro registration member
  simp [empty] at member

theorem Model.AuthoritiesRecorded.excludes_future_loan {model : Model} {world : World}
    {state : List Nat} {loan : Identity} (well : world.WellFormed)
    (recorded : model.AuthoritiesRecorded world state) (future : world.nextLoan ≤ loan) :
    ∀ registration ∈ model.registrations state, registration.authority.parentLoan ≠ some loan := by
  intro registration member parent
  exact Nat.not_lt_of_ge future ((recorded registration member).loan_bound well parent)

theorem Reachable.recorded {program : Language.Program} {world : World}
    {seeds : ResolvedPlace → Prop} {place : ResolvedPlace}
    (reachable : Reachable program world seeds place)
    (recorded : ∀ place, seeds place → place.authority.Recorded world.loans) : place.authority.Recorded world.loans := by
  induction reachable with
  | seed member => exact recorded _ member
  | project _ resolved ih => exact resolved.recorded ih
  | pointer => split <;> trivial

theorem AccessSeed.recorded {program : Kernel.Program} {model : Model} {contract : Contract}
    {initial current : World} {session : ForeignSession} {place : ResolvedPlace}
    (known : AuthoritySupport.Recorded (session.known.map ResolvedPlace.authority) current.loans)
    (registry : model.AuthoritiesRecorded current session.state)
    (seed : AccessSeed program model contract initial current session place) : place.authority.Recorded current.loans := by
  rcases seed with member | ⟨registration,member,_,_,rfl,_⟩ | ⟨_,root,_⟩ | ⟨_,_,owner,_⟩
  · exact AuthoritySupport.recorded_map.mp known place member
  · exact Authority.lend_recorded_iff.mpr (registry registration member)
  · exact Authority.recorded_of_no_parent root
  · rw [owner]
    trivial

theorem Accessible.recorded {program : Kernel.Program} {model : Model} {contract : Contract}
    {initial current : World} {session : ForeignSession} {place : ResolvedPlace}
    (known : AuthoritySupport.Recorded (session.known.map ResolvedPlace.authority) current.loans)
    (registry : model.AuthoritiesRecorded current session.state)
    (accessible : Accessible program model contract initial current session place) : place.authority.Recorded current.loans :=
  Reachable.recorded accessible (fun _ seed => AccessSeed.recorded known registry seed)

theorem RegistrationOrigin.recorded {program : Kernel.Program} {model : Model} {contract : Contract}
    {initial current : World} {session : ForeignSession} {previous : List Nat} {registration : Registration}
    (known : AuthoritySupport.Recorded (session.known.map ResolvedPlace.authority) current.loans)
    (registry : model.AuthoritiesRecorded current session.state)
    (old : model.AuthoritiesRecorded current previous)
    (origin : RegistrationOrigin program contract model initial current session previous registration) :
    registration.authority.Recorded current.loans := by
  cases origin with
  | existing member => exact old _ member
  | @unregister original member => exact old original member
  | register accessible _ => exact Authority.lend_recorded_iff.mp (accessible.recorded known registry)

theorem HostStateEvolution.recorded {program : Kernel.Program} {model : Model} {contract : Contract}
    {initial current : World} {session : ForeignSession} {before after : List Nat}
    (known : AuthoritySupport.Recorded (session.known.map ResolvedPlace.authority) current.loans)
    (previous : model.AuthoritiesRecorded current before) (state : session.state = before)
    (permitted : HostStateEvolution program contract model initial current session before after) :
    model.AuthoritiesRecorded current after := by
  intro registration member
  exact (permitted.registrations registration member).recorded known (state ▸ previous) previous

theorem Model.Lawful.start_authorities_recorded {program : Kernel.Program} {model : Model}
    {initial : ForeignSession} {imported : Import} {contract : Contract} {world : World} {state : List Nat}
    (lawful : model.Lawful program) (well : world.WellFormed)
    (selected : Selected program model initial.call imported contract) (typed : CallTyped program world initial.call)
    (precondition : contract.precondition world initial)
    (started : model.start initial.call.binding.declaration world initial state)
    (known : AuthoritySupport.Recorded (initial.known.map ResolvedPlace.authority) world.loans)
    (registry : model.AuthoritiesRecorded world initial.state) : model.AuthoritiesRecorded world state :=
  (lawful.start _ _ _ _ _ selected well typed precondition started).2.2.recorded known registry rfl

theorem Model.Lawful.host_authorities_recorded {program : Kernel.Program} {model : Model}
    {session : ForeignSession} {imported : Import} {contract : Contract} {before after : World}
    {observation next : List Nat} {action : HostAction}
    (lawful : model.Lawful program) (well : before.WellFormed)
    (selected : Selected program model session.call imported contract) (active : contract.session before session)
    (step : model.step session.call.binding.declaration before session observation after action next)
    (known : AuthoritySupport.Recorded session.authoritySupport before.loans)
    (registry : model.AuthoritiesRecorded before session.state) : model.AuthoritiesRecorded after next := by
  have retained := (lawful.host_suspensionExtension well selected active step).recorded
  exact (lawful.step _ _ _ _ _ _ _ _ selected well active step).2.2.2.2.2.2.2.2.recorded
    (ForeignSession.known_authority_support (known.mono retained)) (registry.mono retained) rfl

theorem Model.Lawful.returned_authorities_recorded {program : Kernel.Program} {model : Model}
    {session : ForeignSession} {imported : Import} {contract : Contract} {world : World}
    {current next : List Nat} {registration : Identity} {result : Address}
    (lawful : model.Lawful program) (well : world.WellFormed)
    (selected : Selected program model session.call imported contract)
    (postcondition : contract.callbackPostcondition world session current registration result)
    (returned : model.callbackReturned session.call.binding.declaration world session current registration result next)
    (known : AuthoritySupport.Recorded session.authoritySupport world.loans)
    (registry : model.AuthoritiesRecorded world current) : model.AuthoritiesRecorded world next :=
  (lawful.callbackReturned _ _ _ _ _ _ _ _ selected well postcondition returned).2.2.recorded
    (ForeignSession.known_authority_support (ForeignSession.returned_authority_support known)) registry rfl

/-- Every real host state transition carries registry provenance. Callback
results, input lending and ordinary transfer may change storage afterwards;
their existing loan-table preservation transports the same registry evidence. -/
theorem Step.host_authorities {program : Kernel.Program} {model : Model} {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : model.Lawful program) (typed : Typing.WorldTyped program before.world)
    (taskRecorded : AuthoritySupport.Recorded before.task.authoritySupport before.world.loans)
    (frameRecorded : AuthoritySupport.Recorded (before.frames.flatMap Frame.authoritySupport) before.world.loans)
    (registry : model.AuthoritiesRecorded before.world before.hostState)
    (step : Step program model before event after) : model.AuthoritiesRecorded after.world after.hostState := by
  have retained := (step.suspensionExtension lawful typed.1).recorded
  have registryAfter := registry.mono retained
  have taskAfter := (step.authority_support lawful typed.1 taskRecorded frameRecorded).1
  cases step
  all_goals simp_all only [Task.authoritySupport,Frame.authoritySupport,List.flatMap_cons,
    AuthoritySupport.recorded_append]
  case enter selected kept callTyped precondition started =>
    exact lawful.start_authorities_recorded (kept.worldTyped valid inventory typed).1 selected callTyped precondition started
      (ForeignSession.known_authority_support taskAfter) registryAfter
  case host selected active transition =>
    exact lawful.host_authorities_recorded typed.1 selected active transition taskRecorded registry
  case result selected active transition _ transferred =>
    exact (lawful.host_authorities_recorded typed.1 selected active transition taskRecorded registry).mono
      transferred.suspensionExtension.recorded
  case callback selected active transition _ lent _ _ consumed =>
    exact (lawful.host_authorities_recorded typed.1 selected active transition taskRecorded registry).mono
      (lent.suspensionExtension.trans consumed.suspensionExtension).recorded
  case callbackReturned selected postcondition returned =>
    exact lawful.returned_authorities_recorded typed.1 selected postcondition returned taskRecorded registryAfter
  case fault selected active transition =>
    exact lawful.host_authorities_recorded typed.1 selected active transition taskRecorded registry

end Foreign

namespace Execution

/-- Source steps retain opaque registry state and historical loan records.
The foreign family changes that state only through the actual registration
origin laws above. No assertion of a valid post-registry is a premise. -/
theorem Step.host_authorities {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (control : before.ControlWellFormed) (registry : host.AuthoritiesRecorded before.world before.hostState)
    (step : Step program host before event after) : host.AuthoritiesRecorded after.world after.hostState := by
  have retained := (step.suspension_storage valid inventory lawful typed control.suspensions).2
  have old := registry.mono retained
  rcases step.host_state with unchanged | foreign
  · exact unchanged ▸ old
  · exact foreign.host_authorities valid inventory lawful typed control.taskAuthorities control.frameAuthorities registry

/-- Arbitrary source execution, callbacks and opaque host transitions share
one registry-origin invariant. Ended and unregistered authorities retain
history without becoming permission to access their former referents. -/
theorem Run.host_authorities {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (control : before.ControlWellFormed) (registry : host.AuthoritiesRecorded before.world before.hostState)
    (run : Run program host before trace after) : host.AuthoritiesRecorded after.world after.hostState := by
  induction run with
  | refl => exact registry
  | silent step _ ih | visible step _ ih =>
    exact ih (step.worldTyped valid inventory lawful typed) (step.controlWellFormed valid inventory lawful typed control)
      (step.host_authorities valid inventory lawful typed control registry)

end Execution

namespace Contracts

theorem InitialInvocation.host_authorities {program : Kernel.Program} {host : Foreign.Model} {function : Kernel.Function}
    {inputs : List Kernel.InvocationInput} {state : Execution.State}
    (initial : InitialInvocation program host function inputs state) : host.AuthoritiesRecorded state.world state.hostState :=
  initial.2.2.2.1

theorem InitialInvocation.run_host_authorities {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput} {start finish : Execution.State}
    {trace : List Execution.Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (initial : InitialInvocation program host function inputs start)
    (run : Execution.Run program host start trace finish) : host.AuthoritiesRecorded finish.world finish.hostState :=
  run.host_authorities valid inventory lawful initial.1.1 initial.control initial.host_authorities

/-- Canonical invocation consumes the whole-execution origin theorem: an
active callback is an exact admitted initial record or has an actual grant on
this invocation, including grants made around source callback execution. -/
theorem InitialInvocation.run_registration_origin {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput} {start finish : Execution.State}
    {trace : List Execution.Event} {registration : Foreign.Registration}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (initial : InitialInvocation program host function inputs start)
    (run : Execution.Run program host start trace finish)
    (member : registration ∈ host.registrations finish.hostState) (active : registration.active = true) :
    registration ∈ host.registrations start.hostState ∨
      ∃ earlier later prior suffix event,
        Execution.Run program host start prior earlier ∧ Execution.Step program host earlier event later ∧
        Execution.Run program host later suffix finish ∧ Foreign.RegistrationGranted program host earlier later registration ∧
        trace = prior ++ event.toList ++ suffix :=
  run.registration_origin valid inventory lawful initial.1.1 member active

theorem Observes.host_authorities {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {observation : Observation}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (observed : Observes program host function observation) :
    ∃ start finish, InitialInvocation program host function observation.input start ∧
      start.world = observation.before ∧ Execution.Run program host start observation.events finish ∧
      finish.world = observation.after ∧ AtOutcome finish observation.outcome ∧
      host.AuthoritiesRecorded start.world start.hostState ∧ host.AuthoritiesRecorded finish.world finish.hostState := by
  obtain ⟨start,finish,initial,before,run,after,outcome⟩ := observed
  exact ⟨start,finish,initial,before,run,after,outcome,initial.host_authorities,
    initial.run_host_authorities valid inventory lawful run⟩

theorem Diverges.host_authorities {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput}
    {states : Nat → Execution.State} {events : Nat → Option Execution.Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (infinite : Diverges program host function inputs states events) :
    ∀ n, host.AuthoritiesRecorded (states n).world (states n).hostState := by
  intro n
  exact infinite.1.run_host_authorities valid inventory lawful (Execution.Run.prefix infinite.2 n)

end Contracts

namespace Specification

theorem reachable_host_authorities {program : Kernel.Program} {host : Foreign.Model}
    {function : Kernel.Function} {inputs : List Kernel.InvocationInput} {state : Execution.State}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (reachable : (Semantics program host function inputs).Reachable state) :
    host.AuthoritiesRecorded state.world state.hostState := by
  obtain ⟨start,trace,initial,run⟩ := reachable_execution_iff.mp reachable
  exact initial.run_host_authorities valid inventory lawful run

end Specification
end Glorious.Language
