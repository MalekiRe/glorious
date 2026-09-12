import GloriousLanguage.SuspensionOwnership
import GloriousLanguage.Contracts

/-! Retained external storage never acquires a source cleanup home. Ordinary
storage producers publish exact home preservation through the shared extension
product. Capture and restoration use the actual delimited inventory and active
suspension ownership. This proves cleanup separation, not stored-value liveness
or exclusivity against explicit aliases. -/
namespace Glorious.Language

open Kernel

theorem World.HomeExtension.root_home {before after : World} {id : Identity} {root : Root}
    (preserved : before.HomeExtension after) (bound : id < before.nextRoot)
    (found : before.roots.get id = some root) :
    ∃ current, after.roots.get id = some current ∧ current.home = root.home := by
  have homes := preserved.homes id bound
  rw [found] at homes
  exact Option.map_eq_some_iff.mp homes

namespace Execution

theorem DelimitedRoots.retains_external {world : World} {handler : InstalledHandler} {inner : List Frame}
    {kept roots : List Identity} {id rootId : Identity} {root : Root} {domain : Identity}
    (selected : DelimitedRoots world handler inner kept roots)
    (found : world.roots.get rootId = some root)
    (external : root.home = .external domain ∨ root.home = .allocation domain) :
    (suspendRoots world roots id).roots.get rootId = some root := by
  have outside : rootId ∉ roots := by
    intro member
    obtain ⟨original,originalAt,_,activation,scope,home⟩ := selected.selected member
    have same : root = original := Option.some.inj (found.symm.trans originalAt)
    subst original
    rcases external with external | external <;> simp [external] at home
  simp only [suspendRoots.get,found,Option.map_some,outside,↓reduceIte]

theorem State.SuspensionsWellFormed.external_not_captured {state : State} {id rootId : Identity}
    {suspension : Suspension} {root : Root} {domain : Identity}
    (valid : state.SuspensionsWellFormed) (selected : state.resumptions.get id = some suspension)
    (active : suspension.active = true) (found : state.world.roots.get rootId = some root)
    (external : root.home = .external domain ∨ root.home = .allocation domain) :
    rootId ∉ suspension.roots := by
  intro member
  obtain ⟨original,originalAt,_,home⟩ := (valid.active id suspension selected active rootId).mp member
  have same : root = original := Option.some.inj (found.symm.trans originalAt)
  subst original
  rcases external with external | external <;> simp [external] at home

theorem State.SuspensionsWellFormed.restore_external {state : State} {id rootId : Identity}
    {suspension : Suspension} {root : Root} {domain : Identity}
    (valid : state.SuspensionsWellFormed) (selected : state.resumptions.get id = some suspension)
    (active : suspension.active = true) (found : state.world.roots.get rootId = some root)
    (external : root.home = .external domain ∨ root.home = .allocation domain) :
    (restoreRoots state.world suspension.homes).roots.get rootId = some root := by
  have outside := valid.external_not_captured selected active found external
  have absent := (valid.origin id suspension selected).home_none outside
  simp only [restoreRoots.get,found,Option.map_some,absent,Option.getD_none]

/-- Every real effect transition retains an external/allocation home. In
particular, historical saved homes cannot overwrite an unrelated current owner:
restoration requires the selected suspension's actual active root inventory. -/
theorem EffectStep.external_home {program : Kernel.Program} {before after : State} {event : Option Event}
    {rootId : Identity} {root : Root} {domain : Identity}
    (valid : before.SuspensionsWellFormed) (well : before.world.WellFormed)
    (step : EffectStep program before event after) (found : before.world.roots.get rootId = some root)
    (external : root.home = .external domain ∨ root.home = .allocation domain) :
    ∃ current, after.world.roots.get rootId = some current ∧ current.home = root.home := by
  have bound := World.root_bound well found
  by_cases capture : ∃ id, event = some (.suspend id)
  · obtain ⟨id,rfl⟩ := capture
    cases step with
    | suspend _ _ _ _ _ _ _ started kept selected _ _ created _ _ =>
      have moved := started.suspensionExtension.toHomeExtension.trans kept.suspensionExtension.toHomeExtension
      obtain ⟨current,currentAt,home⟩ := moved.root_home bound found
      have suspended := selected.retains_external (id := before.nextContinuation) currentAt
        (by simpa only [home] using external)
      obtain ⟨last,lastAt,lastHome⟩ := created.suspensionExtension.toHomeExtension.root_home
        (Nat.lt_of_lt_of_le bound moved.counter) suspended
      exact ⟨last,lastAt,lastHome.trans home⟩
    | suspendTailArm _ _ _ _ _ _ _ _ started kept selected _ _ _ _ =>
      have moved := started.suspensionExtension.toHomeExtension.trans kept.suspensionExtension.toHomeExtension
      obtain ⟨current,currentAt,home⟩ := moved.root_home bound found
      exact ⟨current,selected.retains_external currentAt (by simpa only [home] using external),home⟩
  by_cases replay : ∃ id last, event = some (.replay id last)
  · obtain ⟨id,last,rfl⟩ := replay
    cases last with
    | true =>
      cases step with
      | resumeLast _ selected active _ restored kept =>
        subst restored
        have restored := valid.restore_external selected active.1 found external
        exact kept.suspensionExtension.toHomeExtension.root_home bound restored
    | false =>
      cases step with
      | resumeCopy _ selected _ _ copied kept =>
        exact ((copied.suspensionExtension well (valid.origin _ _ selected)).toHomeExtension.trans
          kept.suspensionExtension.toHomeExtension).root_home bound found
  by_cases cancel : ∃ id, event = some (.cancel id)
  · obtain ⟨id,rfl⟩ := cancel
    cases step with
    | cancel _ selected active _ _ => exact ⟨root,valid.restore_external selected active.1 found external,rfl⟩
  exact (step.ordinary_suspensionExtension (fun id same => capture ⟨id,same⟩)
    (fun id last same => replay ⟨id,last,same⟩)
    (fun id same => cancel ⟨id,same⟩)).toHomeExtension.root_home bound found

theorem Step.external_home {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event} {rootId : Identity} {root : Root} {domain : Identity}
    (lawful : host.Lawful program) (well : before.world.WellFormed)
    (suspensions : before.SuspensionsWellFormed) (step : Step program host before event after)
    (found : before.world.roots.get rootId = some root)
    (external : root.home = .external domain ∨ root.home = .allocation domain) :
    ∃ current, after.world.roots.get rootId = some current ∧ current.home = root.home := by
  have bound := World.root_bound well found
  rcases step with localStep | atom | effect | control | primitive | foreign
  · exact localStep.suspensionExtension.toHomeExtension.root_home bound found
  · exact atom.suspensionExtension.toHomeExtension.root_home bound found
  · exact effect.external_home suspensions well found external
  · exact control.suspensionExtension.toHomeExtension.root_home bound found
  · exact primitive.suspensionExtension.toHomeExtension.root_home bound found
  · exact (foreign.suspensionExtension lawful well).toHomeExtension.root_home bound found

/-- Existing exterior ownership survives arbitrary interleaving of source
code, host mutation, nested callback lending/consumption, capture and replay.
The root's live bit and resident value are deliberately not claimed invariant. -/
theorem Run.external_home {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} {rootId : Identity} {root : Root} {domain : Identity}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (suspensions : before.SuspensionsWellFormed) (run : Run program host before trace after)
    (found : before.world.roots.get rootId = some root)
    (external : root.home = .external domain ∨ root.home = .allocation domain) :
    ∃ current, after.world.roots.get rootId = some current ∧ current.home = root.home := by
  induction run generalizing root with
  | refl => exact ⟨root,found,rfl⟩
  | silent step _ ih | visible step _ ih =>
    obtain ⟨current,currentAt,home⟩ := step.external_home lawful typed.1 suspensions found external
    obtain ⟨last,lastAt,lastHome⟩ := ih (step.worldTyped valid inventory lawful typed)
      (step.suspensions valid inventory lawful typed suspensions) currentAt (by simpa only [home] using external)
    exact ⟨last,lastAt,lastHome.trans home⟩

end Execution

namespace Foreign

open Execution

theorem Registration.Valid.retained_home {program : Kernel.Program} {world : World}
    {runtimes : List Identity} {registration : Registration}
    (valid : registration.Valid program world runtimes) (active : registration.active = true)
    (retained : registration.retained = true) :
    ∃ root domain, world.roots.get registration.owner.root = some root ∧
      (root.home = .external domain ∨ root.home = .allocation domain) := by
  obtain ⟨_,_,_,_,_,lifetime⟩ := valid active
  obtain ⟨root,domain,found,home⟩ := lifetime retained
  exact ⟨root,domain,(World.root_found found).1,home⟩

theorem Registration.Valid.retained_home_extension {program : Kernel.Program} {before after : World}
    {runtimes : List Identity} {registration : Registration}
    (valid : registration.Valid program before runtimes) (well : before.WellFormed)
    (preserved : before.HomeExtension after) (active : registration.active = true)
    (retained : registration.retained = true) :
    ∃ root domain, after.roots.get registration.owner.root = some root ∧
      (root.home = .external domain ∨ root.home = .allocation domain) := by
  obtain ⟨root,domain,found,home⟩ := valid.retained_home active retained
  obtain ⟨current,currentAt,currentHome⟩ := preserved.root_home (World.root_bound well found) found
  exact ⟨current,domain,currentAt,by simpa only [currentHome] using home⟩

/-- A real registry-changing producer establishes retained storage's exterior
home in its mutation world, and actual callback lending/consumption preserves
that home. Only callback-result cleanup leaves the registry untouched. This
does not reassert initialized callable contents after source receiver moves. -/
theorem Step.retained_home_origin {program : Kernel.Program} {model : Model}
    {before after : State} {event : Option Event} {registration : Registration}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : model.Lawful program) (typed : Typing.WorldTyped program before.world)
    (step : Step program model before event after)
    (member : registration ∈ model.registrations after.hostState) (active : registration.active = true)
    (retained : registration.retained = true) :
    registration ∈ model.registrations before.hostState ∨
      ∃ root domain, after.world.roots.get registration.owner.root = some root ∧
        (root.home = .external domain ∨ root.home = .allocation domain) := by
  cases step with
  | enter _ selected protectedWorld callTyped precondition started =>
    have registry := (lawful.start _ _ _ _ _ selected
      (protectedWorld.worldTyped valid inventory typed).1 callTyped precondition started).2.1
    exact Or.inr ((registry.2 registration member).retained_home active retained)
  | host _ _ selected sessionActive changed
  | fault _ _ selected sessionActive changed =>
    have registry := (lawful.step _ _ _ _ _ _ _ _ selected typed.1 sessionActive changed).2.2.2.1
    exact Or.inr ((registry.2 registration member).retained_home active retained)
  | result _ _ selected sessionActive changed _ transferred =>
    have law := lawful.step _ _ _ _ _ _ _ _ selected typed.1 sessionActive changed
    exact Or.inr ((law.2.2.2.1.2 registration member).retained_home_extension
      (law.1.worldTyped valid inventory typed).1 transferred.authorityStable.homes active retained)
  | callback _ _ selected sessionActive changed _ lent _ _ consumed =>
    have law := lawful.step _ _ _ _ _ _ _ _ selected typed.1 sessionActive changed
    exact Or.inr ((law.2.2.2.1.2 registration member).retained_home_extension
      (law.1.worldTyped valid inventory typed).1
      (lent.suspensionExtension.toHomeExtension.trans consumed.suspensionExtension.toHomeExtension) active retained)
  | callbackResult => exact Or.inl member
  | callbackReturned _ _ selected postcondition returned =>
    have registry := (lawful.callbackReturned _ _ _ _ _ _ _ _ selected typed.1 postcondition returned).2.1
    exact Or.inr ((registry.2 registration member).retained_home active retained)

end Foreign

namespace Execution

theorem Step.retained_home_origin {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event} {registration : Foreign.Registration}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (step : Step program host before event after)
    (member : registration ∈ host.registrations after.hostState) (active : registration.active = true)
    (retained : registration.retained = true) :
    registration ∈ host.registrations before.hostState ∨
      ∃ root domain, after.world.roots.get registration.owner.root = some root ∧
        (root.home = .external domain ∨ root.home = .allocation domain) := by
  rcases step.host_state with unchanged | foreign
  · exact Or.inl (unchanged ▸ member)
  · exact foreign.retained_home_origin valid inventory lawful typed member active retained

/-- Every active retained record is either the exact initial record or has
an exterior owner home established by an actual registry-changing transition
and preserved through the rest of execution. Forged initial registry records
are not silently granted storage ownership. -/
theorem Run.retained_home_origin {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} {registration : Foreign.Registration}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (suspensions : before.SuspensionsWellFormed) (run : Run program host before trace after)
    (member : registration ∈ host.registrations after.hostState) (active : registration.active = true)
    (retained : registration.retained = true) :
    registration ∈ host.registrations before.hostState ∨
      ∃ root domain, after.world.roots.get registration.owner.root = some root ∧
        (root.home = .external domain ∨ root.home = .allocation domain) := by
  induction run with
  | refl => exact Or.inl member
  | silent step rest ih | visible step rest ih =>
    have middleTyped := step.worldTyped valid inventory lawful typed
    have middleSuspensions := step.suspensions valid inventory lawful typed suspensions
    rcases ih middleTyped middleSuspensions member with previous | home
    · rcases step.retained_home_origin valid inventory lawful typed previous active retained with original |
        ⟨root,domain,found,home⟩
      · exact Or.inl original
      · obtain ⟨current,currentAt,currentHome⟩ := rest.external_home valid inventory lawful middleTyped
          middleSuspensions found home
        exact Or.inr ⟨current,domain,currentAt,by simpa only [currentHome] using home⟩
    · exact Or.inr home

theorem Run.retained_home {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} {registration : Foreign.Registration}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (suspensions : before.SuspensionsWellFormed) (run : Run program host before trace after)
    (initial : ∀ registration ∈ host.registrations before.hostState,
      registration.Valid program before.world (host.runtimes before.hostState))
    (member : registration ∈ host.registrations after.hostState) (active : registration.active = true)
    (retained : registration.retained = true) :
    ∃ root domain, after.world.roots.get registration.owner.root = some root ∧
      (root.home = .external domain ∨ root.home = .allocation domain) := by
  rcases run.retained_home_origin valid inventory lawful typed suspensions member active retained with original | home
  · obtain ⟨root,domain,found,home⟩ := (initial registration original).retained_home active retained
    obtain ⟨current,currentAt,currentHome⟩ := run.external_home valid inventory lawful typed suspensions found home
    exact ⟨current,domain,currentAt,by simpa only [currentHome] using home⟩
  · exact home

/-- This is exactly the implicit cleanup ownership used by scope/activation
selection and active continuation cancellation, not a permission to read or
move the root's resident contents. -/
theorem State.external_cleanup_separation {state : State} {rootId : Identity} {root : Root} {domain : Identity}
    (suspensions : state.SuspensionsWellFormed) (found : state.world.roots.get rootId = some root)
    (external : root.home = .external domain ∨ root.home = .allocation domain) :
    (∀ activation scope kept roots, ScopeRoots state.world activation scope kept roots → rootId ∉ roots) ∧
    (∀ activation kept roots, ActivationRoots state.world activation kept roots → rootId ∉ roots) ∧
    ∀ id suspension, state.resumptions.get id = some suspension → suspension.active = true → rootId ∉ suspension.roots := by
  refine ⟨?_,?_,fun _ _ selected active => suspensions.external_not_captured selected active found external⟩
  · intro activation scope kept roots cleanup member
    obtain ⟨other,otherAt,_,owned,_⟩ := (cleanup.2 rootId).mp member
    have same : root = other := Option.some.inj (found.symm.trans otherAt)
    subst other
    rcases external with home | home <;> simp [OwnedByScope,HomeOwnedByScope,home] at owned
  · intro activation kept roots cleanup member
    obtain ⟨other,otherAt,_,owned,_⟩ := (cleanup.2 rootId).mp member
    have same : root = other := Option.some.inj (found.symm.trans otherAt)
    subst other
    rcases external with home | home <;> simp [OwnedByActivation,HomeOwnedByActivation,home] at owned

theorem Run.retained_cleanup_separation {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} {registration : Foreign.Registration}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (suspensions : before.SuspensionsWellFormed) (run : Run program host before trace after)
    (initial : ∀ registration ∈ host.registrations before.hostState,
      registration.Valid program before.world (host.runtimes before.hostState))
    (member : registration ∈ host.registrations after.hostState) (active : registration.active = true)
    (retained : registration.retained = true) :
    (∀ activation scope kept roots, ScopeRoots after.world activation scope kept roots → registration.owner.root ∉ roots) ∧
    (∀ activation kept roots, ActivationRoots after.world activation kept roots → registration.owner.root ∉ roots) ∧
    ∀ id suspension, after.resumptions.get id = some suspension → suspension.active = true →
      registration.owner.root ∉ suspension.roots := by
  obtain ⟨root,domain,found,home⟩ := run.retained_home valid inventory lawful typed suspensions initial member active retained
  exact State.external_cleanup_separation (run.suspensions valid inventory lawful typed suspensions) found home

theorem Run.new_retained_cleanup_separation {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} {registration : Foreign.Registration}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (suspensions : before.SuspensionsWellFormed) (run : Run program host before trace after)
    (new : registration ∉ host.registrations before.hostState)
    (member : registration ∈ host.registrations after.hostState) (active : registration.active = true)
    (retained : registration.retained = true) :
    (∀ activation scope kept roots, ScopeRoots after.world activation scope kept roots → registration.owner.root ∉ roots) ∧
    (∀ activation kept roots, ActivationRoots after.world activation kept roots → registration.owner.root ∉ roots) ∧
    ∀ id suspension, after.resumptions.get id = some suspension → suspension.active = true →
      registration.owner.root ∉ suspension.roots := by
  obtain ⟨root,domain,found,home⟩ :=
    (run.retained_home_origin valid inventory lawful typed suspensions member active retained).resolve_left new
  exact State.external_cleanup_separation (run.suspensions valid inventory lawful typed suspensions) found home

/-- Cancellation's real scheduled root list cannot contain the retained
owner, even after arbitrary intervening source computation and host callbacks. -/
theorem Run.retained_cancel_separation {program : Kernel.Program} {host : Foreign.Model}
    {before current after : State} {trace : List Event} {registration : Foreign.Registration}
    {id : Identity} {context : Execution.Context} {roots : List Identity} {next : Task}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (suspensions : before.SuspensionsWellFormed) (run : Run program host before trace current)
    (initial : ∀ registration ∈ host.registrations before.hostState,
      registration.Valid program before.world (host.runtimes before.hostState))
    (member : registration ∈ host.registrations current.hostState) (active : registration.active = true)
    (retained : registration.retained = true) (cancel : EffectStep program current (some (.cancel id)) after)
    (cleanup : after.task = .cleanup context roots next) : registration.owner.root ∉ roots := by
  have separate := run.retained_cleanup_separation valid inventory lawful typed suspensions initial member active retained
  cases cancel with
  | cancel _ selected obligation _ _ =>
    cases cleanup
    exact separate.2.2 _ _ selected obligation.1

end Execution

namespace Foreign

open Execution

/-- Initial host entry, host continuation and callback return establish the
registry premise themselves. The theorem then follows all later execution,
including newly registered callbacks, instead of assuming post-source validity. -/
theorem Step.retained_run_cleanup_separation {program : Kernel.Program} {model : Model}
    {before middle after : State} {event : Option Event} {trace : List Event}
    {session : ForeignSession} {next : Code} {registration : Registration}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : model.Lawful program) (typed : Typing.WorldTyped program before.world)
    (suspensions : before.SuspensionsWellFormed) (step : Step program model before event middle)
    (handoff : middle.task = .foreign session next) (run : Execution.Run program model middle trace after)
    (member : registration ∈ model.registrations after.hostState) (active : registration.active = true)
    (retained : registration.retained = true) :
    (∀ activation scope kept roots, ScopeRoots after.world activation scope kept roots → registration.owner.root ∉ roots) ∧
    (∀ activation kept roots, ActivationRoots after.world activation kept roots → registration.owner.root ∉ roots) ∧
    ∀ id suspension, after.resumptions.get id = some suspension → suspension.active = true →
      registration.owner.root ∉ suspension.roots := by
  obtain ⟨same,_,_,_,_,registry⟩ := step.ready valid inventory lawful typed session next handoff
  apply run.retained_cleanup_separation valid inventory lawful (step.worldTyped valid inventory lawful typed)
    (step.suspensions lawful typed.1 suspensions) ?_ member active retained
  intro registration member
  simpa only [same] using registry.2 registration (by simpa only [same] using member)

/-- Normal foreign return uses the actual protected-result transfer's full
registry preservation. Later source execution requires only the exterior-home
projection, so legitimate unique lending and owning consumption stay allowed. -/
theorem Step.returned_retained_run_cleanup_separation {program : Kernel.Program} {model : Model}
    {before middle after : State} {event : Option Event} {trace : List Event}
    {root : Identity} {context : Execution.Context} {next : Code} {registration : Registration}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : model.Lawful program) (typed : Typing.WorldTyped program before.world)
    (suspensions : before.SuspensionsWellFormed) (step : Step program model before event middle)
    (handoff : middle.task = .retire root (.run context next)) (run : Execution.Run program model middle trace after)
    (member : registration ∈ model.registrations after.hostState) (active : registration.active = true)
    (retained : registration.retained = true) :
    (∀ activation scope kept roots, ScopeRoots after.world activation scope kept roots → registration.owner.root ∉ roots) ∧
    (∀ activation kept roots, ActivationRoots after.world activation kept roots → registration.owner.root ∉ roots) ∧
    ∀ id suspension, after.resumptions.get id = some suspension → suspension.active = true →
      registration.owner.root ∉ suspension.roots :=
  run.retained_cleanup_separation valid inventory lawful (step.worldTyped valid inventory lawful typed)
    (step.suspensions lawful typed.1 suspensions) (step.result_registrations lawful typed handoff).2 member active retained

end Foreign

namespace Contracts

/-- Canonical admitted invocation consumes the new-record origin result.
Pre-existing registry records still require their own initial storage evidence;
the invocation's historical-authority check alone does not supply it. -/
theorem InitialInvocation.run_new_retained_cleanup_separation {program : Kernel.Program} {host : Foreign.Model}
    {function : Function} {inputs : List InvocationInput} {start finish : Execution.State}
    {trace : List Execution.Event} {registration : Foreign.Registration}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (initial : InitialInvocation program host function inputs start)
    (run : Execution.Run program host start trace finish) (new : registration ∉ host.registrations start.hostState)
    (member : registration ∈ host.registrations finish.hostState) (active : registration.active = true)
    (retained : registration.retained = true) :
    (∀ activation scope kept roots, ScopeRoots finish.world activation scope kept roots → registration.owner.root ∉ roots) ∧
    (∀ activation kept roots, ActivationRoots finish.world activation kept roots → registration.owner.root ∉ roots) ∧
    ∀ id suspension, finish.resumptions.get id = some suspension → suspension.active = true →
      registration.owner.root ∉ suspension.roots :=
  run.new_retained_cleanup_separation valid inventory lawful initial.1.1 initial.suspensions new member active retained

end Contracts
end Glorious.Language
