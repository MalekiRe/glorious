import GloriousLanguage.MemoryPreservation
import GloriousLanguage.ReceiverPreservation

/-! Typed host interaction, including source callback re-entry. The external
model supplies mutation and protocol evidence, never the preservation result. -/
namespace Glorious.Language.Foreign

open Kernel Execution Memory

theorem replace_disjoint {before after : Value} {path observed : List Nat} {replacement : Option Value}
    (written : before.replace path replacement = some after)
    (outside : ¬ ∃ suffix, observed = path ++ suffix) (reverse : ¬ ∃ suffix, path = observed ++ suffix) :
    after.atPath observed = before.atPath observed := by
  induction path generalizing before after observed with
  | nil => exact False.elim (outside ⟨observed,rfl⟩)
  | cons index path ih =>
    cases observed with
    | nil => exact False.elim (reverse ⟨index :: path,rfl⟩)
    | cons other observed =>
      rcases Value.replace_cons_shape written with ⟨field,found,⟨rfl,rfl⟩ | ⟨child,changed,rfl,replaced,rfl⟩⟩
      · have different : index ≠ other := by
          intro same
          subst other
          exact outside ⟨observed,rfl⟩
        simp [Value.atPath,Value.withFields,Value.fields,List.getElem?_set_ne different]
      · by_cases same : index = other
        · subst other
          have bound := List.getElem?_eq_some_iff.mp found |>.1
          change ((before.fields.set index (some changed))[index]?.join >>= fun child => child.atPath observed) = _
          rw [List.getElem?_set_self bound]
          simp only [Value.atPath,found,Option.join_some]
          exact ih replaced
            (fun ⟨suffix,equal⟩ => outside ⟨suffix,by simp [equal]⟩)
            (fun ⟨suffix,equal⟩ => reverse ⟨suffix,by simp [equal]⟩)
        · simp [Value.atPath,Value.withFields,Value.fields,List.getElem?_set_ne same]

/-- Full value framing, including capture fields rather than only their
headers. It is consumed by registered-owner handoff preservation below. -/
theorem write_disjoint {before after : World} {address observed : Address} {value : Option Value}
    (written : before.write address value = some after) (outside : ¬ address.Overlaps observed) :
    after.read observed = before.read observed := by
  have update := World.write_value_update written
  unfold World.write at written
  cases selected : before.root address with
  | none => simp [selected] at written
  | some root =>
    obtain ⟨found,live,generation⟩ := World.root_found selected
    simp only [selected] at written
    dsimp at written
    by_cases sameRoot : observed.root = address.root
    · by_cases sameGeneration : observed.generation = address.generation
      · have pathOutside : ¬ ∃ suffix, observed.fields = address.fields ++ suffix :=
          fun included => outside ((show address.Prefix observed from ⟨sameRoot.symm,sameGeneration.symm,included⟩).overlaps)
        have reverse : ¬ ∃ suffix, address.fields = observed.fields ++ suffix :=
          fun included => outside ((show observed.Prefix address from ⟨sameRoot,sameGeneration,included⟩).overlaps.symm)
        split at written
        next empty =>
          have fields : address.fields = [] := by simpa using empty
          exact False.elim (pathOutside ⟨observed.fields,by simp [fields]⟩)
        next =>
          cases resident : root.value with
          | none => simp [resident] at written
          | some tree =>
            simp only [resident] at written
            dsimp at written
            cases replaced : tree.replace address.fields value with
            | none => simp [replaced] at written
            | some changed =>
              simp only [replaced] at written
              dsimp at written
              cases (Option.some.inj written).symm
              have observedGeneration : root.generation = observed.generation := generation.trans sameGeneration.symm
              simpa [World.read,World.root,Table.get_set,sameRoot,found,live,observedGeneration,resident]
                using replace_disjoint replaced pathOutside reverse
      · rcases update with ⟨changedRoot,_,changedFound,equal⟩
        have same := Option.some.inj (changedFound.symm.trans found)
        subst changedRoot
        subst after
        have different : root.generation ≠ observed.generation := by omega
        simp [World.read,World.root,sameRoot,Table.get_set,found,live,different]
    · rcases update with ⟨_,_,_,equal⟩
      subst after
      simp [World.read,World.root,Table.get_set_other _ _ _ _ sameRoot]

theorem Registration.Valid.transfer {program : Kernel.Program} {before after : World}
    {runtimes : List Identity} {registration : Registration} {authority : Authority} {source destination : Address}
    (valid : registration.Valid program before runtimes)
    (transferred : Transfers program.declarations before authority source destination after)
    (sourceSeparate : ¬ source.Overlaps registration.owner) (destinationSeparate : ¬ destination.Overlaps registration.owner) :
    registration.Valid program after runtimes := by
  intro active
  obtain ⟨⟨value,stored,initialized,head⟩,function,runtime,bound,synchronous,retained⟩ := valid active
  have read : after.read registration.owner = before.read registration.owner := by
    cases transferred with
    | move _ _ _ _ _ _ clear install =>
      exact (write_disjoint install destinationSeparate).trans (write_disjoint clear sourceSeparate)
  refine ⟨⟨value,read.trans stored,initialized,head⟩,function,runtime,bound,?_,?_⟩
  · intro sync
    have regions := congrArg World.liveRegions transferred.rest
    simpa only [regions] using synchronous sync
  · intro kept
    obtain ⟨root,domain,selected,home⟩ := retained kept
    obtain ⟨changed,found,location⟩ := World.root_transport transferred.locations selected
    have sameHome : changed.home = root.home := by simpa [Root.location] using congrArg Root.home location
    exact ⟨changed,domain,found,by simpa only [sameHome] using home⟩

theorem Mutation.worldTyped {program : Kernel.Program} {before after : World}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before) (changed : Mutation program before after) :
    Typing.WorldTyped program after := by
  cases changed with
  | allocate allocated => exact allocated.worldTyped typed
  | scalar stored => exact stored.worldTyped valid inventory typed
  | unit stored => exact stored.worldTyped valid inventory typed
  | pointer bound origin stored => exact stored.worldTyped valid inventory typed bound origin
  | aggregate inputs head constructed => exact constructed.aggregate_worldTyped valid inventory typed inputs head
  | acquire acquired => exact acquired.worldTyped valid inventory typed
  | borrow borrowed => exact borrowed.worldTyped valid inventory typed
  | allocateBuffer allocated => exact allocated.worldTyped valid inventory typed
  | reallocateBuffer reallocated => exact reallocated.worldTyped valid inventory typed
  | releaseBuffer released => exact released.worldTyped typed
  | rawRead read => exact read.worldTyped valid inventory typed
  | rawWrite written => exact written.worldTyped valid inventory typed
  | rawBorrow borrowed => exact borrowed.worldTyped valid inventory typed
  | bulkMove moved => exact moved.worldTyped valid inventory typed
  | retire retired => exact retired.worldTyped typed
  | endLoan ended => exact ended.worldTyped typed

theorem Mutations.worldTyped {program : Kernel.Program} {before after : World}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before) (changed : Mutations program before after) :
    Typing.WorldTyped program after := by
  induction changed with
  | refl => exact typed
  | cons first _ ih => exact ih (first.worldTyped valid inventory typed)

theorem Model.Lawful.host_worldTyped {program : Kernel.Program} {model : Model}
    {session : ForeignSession} {imported : Import} {contract : Contract} {before after : World}
    {observation next : List Nat} {action : HostAction}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : model.Lawful program) (typed : Typing.WorldTyped program before)
    (selected : Selected program model session.call imported contract) (active : contract.session before session)
    (step : model.step session.call.binding.declaration before session observation after action next) :
    Typing.WorldTyped program after :=
  (lawful.step session imported contract before observation after action next selected typed.1 active step).1.worldTyped
    valid inventory typed

/-- All foreign transitions preserve full resident typing and storage
well-formedness; callback receiver consumption and return handoff are ordinary
language ownership transitions, not an exemption for external code. -/
theorem Step.worldTyped {program : Kernel.Program} {model : Model} {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : model.Lawful program) (typed : Typing.WorldTyped program before.world)
    (step : Step program model before event after) : Typing.WorldTyped program after.world := by
  cases step with
  | enter _ _ protectedWorld _ _ _ => exact protectedWorld.worldTyped valid inventory typed
  | host _ _ selected active step => exact lawful.host_worldTyped valid inventory typed selected active step
  | result _ _ selected active step _ transferred =>
    exact transferred.worldTyped valid inventory (lawful.host_worldTyped valid inventory typed selected active step)
  | callback _ _ selected active step _ _ _ _ _ _ _ _ lent _ _ consumed =>
    exact consumed.worldTyped (lent.worldTyped valid inventory (lawful.host_worldTyped valid inventory typed selected active step))
  | callbackResult _ _ _ _ _ protectedWorld retired ended _ _ =>
    exact ended.worldTyped (retired.worldTyped (protectedWorld.worldTyped valid inventory typed))
  | fault _ _ selected active step => exact lawful.host_worldTyped valid inventory typed selected active step

/-- The invariant needed by every host step is established when that phase is
entered or resumed. Original preconditions need not be incorrectly re-applied
after operands have legitimately been consumed. -/
def Ready (program : Kernel.Program) (model : Model) (state : State) : Prop :=
  ∀ session next, state.task = .foreign session next →
    state.hostState = session.state ∧ ∃ imported contract, Selected program model session.call imported contract ∧
      contract.session state.world session ∧ RegistrationsValid program model state.world session.state

theorem Step.ready {program : Kernel.Program} {model : Model} {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : model.Lawful program) (typed : Typing.WorldTyped program before.world)
    (step : Step program model before event after) : Ready program model after := by
  intro session next task
  cases step with
  | enter _ selected protectedWorld callTyped precondition start =>
    cases task
    have law := lawful.start _ _ _ _ _ _ selected
      (protectedWorld.worldTyped valid inventory typed).1 callTyped precondition start
    exact ⟨rfl,_,_,selected,law.1,law.2.1⟩
  | host _ _ selected active step =>
    cases task
    have law := lawful.step _ _ _ _ _ _ _ _ selected typed.1 active step
    exact ⟨rfl,_,_,selected,law.2.2.2.2.1 rfl,law.2.2.2.1⟩
  | callbackResult _ _ selected _ _ protectedWorld retired ended postcondition returned =>
    cases task
    have law := lawful.callbackReturned _ _ _ _ _ _ _ _ selected
      (ended.worldTyped (retired.worldTyped (protectedWorld.worldTyped valid inventory typed))).1 postcondition returned
    exact ⟨rfl,_,_,selected,law.1,law.2.1⟩
  | result => cases task
  | callback => cases task
  | fault => cases task

/-- The actual normal-return transfer preserves every active registration,
not just the model's pre-handoff world. An owning callback must first be
unregistered before its storage can itself be handed back to source code. -/
theorem Step.result_registrations {program : Kernel.Program} {model : Model}
    {before after : State} {event : Option Event} {root : Identity} {context : Execution.Context} {next : Code}
    (lawful : model.Lawful program) (typed : Typing.WorldTyped program before.world)
    (step : Step program model before event after) (task : after.task = .retire root (.run context next)) :
    RegistrationsValid program model after.world after.hostState := by
  cases step with
  | result _ _ selected active host separated transferred =>
    have registry := (lawful.step _ _ _ _ _ _ _ _ selected typed.1 active host).2.2.2.1
    refine ⟨registry.1,?_⟩
    intro registration member active
    have separate := separated registration member active
    exact (registry.2 registration member).transfer transferred separate.1 separate.2 active
  | enter => cases task
  | host => cases task
  | callback => cases task
  | callbackResult => cases task
  | fault => cases task

/-- A retained registration's actual owner cannot be selected for implicit
source scope cleanup. Retention is storage ownership, not an unrelated list
of allegedly live captures. Explicit unregister/release remains contractual. -/
theorem Registration.Valid.not_scope_cleanup {program : Kernel.Program} {world : World}
    {runtimes : List Identity} {registration : Registration} {activation scope : Identity} {kept roots : List Identity}
    (valid : registration.Valid program world runtimes) (active : registration.active = true)
    (retained : registration.retained = true) (cleanup : ScopeRoots world activation scope kept roots) :
    registration.owner.root ∉ roots := by
  obtain ⟨_,_,_,_,_,lifetime⟩ := valid active
  obtain ⟨root,domain,selected,home⟩ := lifetime retained
  intro member
  obtain ⟨other,found,_,owned,_⟩ := (cleanup.2 registration.owner.root).mp member
  have same : root = other := Option.some.inj ((World.root_found selected).1.symm.trans found)
  subst other
  rcases home with home | home <;> simp [OwnedByScope,home] at owned

theorem Registration.Valid.not_activation_cleanup {program : Kernel.Program} {world : World}
    {runtimes : List Identity} {registration : Registration} {activation : Identity} {kept roots : List Identity}
    (valid : registration.Valid program world runtimes) (active : registration.active = true)
    (retained : registration.retained = true) (cleanup : ActivationRoots world activation kept roots) :
    registration.owner.root ∉ roots := by
  obtain ⟨_,_,_,_,_,lifetime⟩ := valid active
  obtain ⟨root,domain,selected,home⟩ := lifetime retained
  intro member
  obtain ⟨other,found,_,owned,_⟩ := (cleanup.2 registration.owner.root).mp member
  have same : root = other := Option.some.inj ((World.root_found selected).1.symm.trans found)
  subst other
  rcases home with home | home <;> simp [OwnedByActivation,home] at owned

/-- The actual resumed/continued host phase consumes the retention invariant
at its cleanup boundary, rather than merely recording it on a side table. -/
theorem Step.retained_outside_cleanup {program : Kernel.Program} {model : Model}
    {before after : State} {event : Option Event} {session : ForeignSession} {next : Code}
    {registration : Registration} {activation : Identity} {kept roots : List Identity}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : model.Lawful program) (typed : Typing.WorldTyped program before.world)
    (step : Step program model before event after) (task : after.task = .foreign session next)
    (registered : registration ∈ model.registrations after.hostState) (active : registration.active = true)
    (retained : registration.retained = true) (cleanup : ActivationRoots after.world activation kept roots) :
    registration.owner.root ∉ roots := by
  obtain ⟨same,_,_,_,_,registry⟩ := step.ready valid inventory lawful typed session next task
  rw [same] at registered
  exact (registry.2 registration registered).not_activation_cleanup active retained cleanup

theorem Step.returned_retained_outside_cleanup {program : Kernel.Program} {model : Model}
    {before after : State} {event : Option Event} {root : Identity} {context : Execution.Context} {next : Code}
    {registration : Registration} {activation : Identity} {kept roots : List Identity}
    (lawful : model.Lawful program) (typed : Typing.WorldTyped program before.world)
    (step : Step program model before event after) (task : after.task = .retire root (.run context next))
    (registered : registration ∈ model.registrations after.hostState) (active : registration.active = true)
    (retained : registration.retained = true) (cleanup : ActivationRoots after.world activation kept roots) :
    registration.owner.root ∉ roots :=
  ((step.result_registrations lawful typed task).2 registration registered).not_activation_cleanup active retained cleanup

end Glorious.Language.Foreign
