import GloriousLanguage.PrivateLocalPreservation
import GloriousLanguage.ActivationPreservation

/-! Proof invariants of the actual control stack above a saved hook guard.
Returning to the caller is allowed only after the inner prefix is exhausted;
an activation frame's caller is not mistaken for its cleanup owner. -/
namespace Glorious.Language.Execution

open _root_.Glorious.Language.Kernel

theorem Context.bind_avoids_root {context : Context} {localSlot : Local} {address : Address}
    {authority : Authority} {id : Identity} (outside : id ∉ context.rootSupport)
    (separate : address.root ≠ id) : id ∉ (context.bind localSlot address authority).rootSupport := by
  simp only [Context.rootSupport,List.mem_append,not_or] at outside ⊢
  refine ⟨?_,outside.2⟩
  intro member
  obtain ⟨binding,present,same⟩ := List.mem_map.mp member
  simp only [Context.bind,List.mem_cons,List.mem_filter] at present
  rcases present with rfl | ⟨present,_⟩
  · exact separate same
  · exact outside.1 (List.mem_map.mpr ⟨binding,present,same⟩)

theorem Context.bindResource_avoids_root {context : Context} {identity : Identity} {place : ResolvedPlace}
    {id : Identity} (outside : id ∉ context.rootSupport) (separate : place.address.root ≠ id) :
    id ∉ (context.bindResource identity place).rootSupport := by
  simp only [Context.rootSupport,List.mem_append,not_or] at outside ⊢
  refine ⟨?_,outside.2⟩
  intro member
  obtain ⟨binding,present,same⟩ := List.mem_map.mp member
  simp only [Context.bindResource,List.mem_cons,List.mem_filter] at present
  rcases present with rfl | ⟨present,_⟩
  · exact separate same
  · exact outside.1 (List.mem_map.mpr ⟨binding,present,same⟩)


theorem Context.resolves_avoids_root {context : Context} {world : World} {place : Place}
    {address : Address} {authority : Authority} {id : Identity}
    (outside : id ∉ context.rootSupport) (safe : CanEndStorage world id)
    (resolved : ResolvesPlace world context.environment place address authority) : address.root ≠ id :=
  resolved.avoids_root (Context.bindings_avoid_root outside) safe

theorem Context.install_avoids_root {context : Context} {bindings : Environment} {id : Identity}
    (outside : id ∉ context.rootSupport) (fresh : ∀ binding ∈ bindings, binding.address.root ≠ id) :
    id ∉ ({ context with environment := context.environment.install bindings }).rootSupport := by
  simp only [Context.rootSupport,List.mem_append,not_or] at outside ⊢
  refine ⟨?_,outside.2⟩
  intro member
  obtain ⟨binding,present,same⟩ := List.mem_map.mp member
  simp only [Environment.install,List.mem_append,List.mem_filter] at present
  rcases present with present | ⟨present,_⟩
  · exact fresh binding present same
  · exact outside.1 (List.mem_map.mpr ⟨binding,present,same⟩)

theorem Context.inheritResources_avoids_root {source receiver : Context} {id : Identity}
    (sourceOutside : id ∉ source.rootSupport) (receiverOutside : id ∉ receiver.rootSupport) :
    id ∉ (receiver.inheritResources source).rootSupport := by
  apply Context.install_avoids_root (context := receiver) receiverOutside
  intro binding member
  exact Context.bindings_avoid_root sourceOutside binding (List.mem_filter.mp member).1

theorem ReturnsResources.private_context {program : Kernel.Program} {source receiver returned : Context}
    {before after : World} {result : Address} {id : Identity} {root : Root}
    (returnedResources : ReturnsResources program source receiver before result returned after)
    (well : before.WellFormed) (slot : before.PrivateSlot id root)
    (sourceOutside : id ∉ source.rootSupport) (receiverOutside : id ∉ receiver.rootSupport) :
    id ∉ returned.rootSupport := by
  cases returnedResources with
  | localReturn _ => exact Context.inheritResources_avoids_root sourceOutside receiverOutside
  | invocationReturn _ resolved _ bound _ =>
    have bindingsOutside := (BindsInputsAttemptFor.private_slot bound well slot
      (resolved.avoids_root (Context.bindings_avoid_root sourceOutside) slot.safe)).2
    apply Context.install_avoids_root receiverOutside
    intro binding member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    exact bindingsOutside original present


theorem ResolvedOperands.avoids_root {world : World} {environment : Environment}
    {places : List Place} {operands : List ResolvedPlace} {id : Identity}
    (resolved : ResolvedOperands world environment places operands)
    (outside : ∀ binding ∈ environment, binding.address.root ≠ id)
    (safe : CanEndStorage world id) : id ∉ operands.map (fun place => place.address.root) := by
  induction resolved with
  | nil => simp
  | cons first _ ih =>
    simp only [List.map_cons,List.mem_cons,not_or]
    exact ⟨Ne.symm (first.1.avoids_root outside safe),ih⟩

theorem ArgumentInputs.avoids_root {world : World} {context : Context} {index : Nat}
    {formals : List Local} {places : List Place} {inputs : List InvocationInput} {id : Identity}
    (prepared : ArgumentInputs world context index formals places inputs)
    (outside : id ∉ context.rootSupport) (safe : CanEndStorage world id) :
    id ∉ inputs.flatMap InvocationInput.rootSupport := by
  induction prepared with
  | nil => simp
  | cons resolved _ _ ih =>
    simp only [List.flatMap_cons,InvocationInput.rootSupport,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false,not_or]
    exact ⟨Ne.symm (Context.resolves_avoids_root outside safe resolved),ih⟩

theorem _root_.Glorious.Language.Kernel.PatternPlan.avoids_root {program : Language.Program} {world : World}
    {address : Address} {authority : Authority} {access : Access} {pattern : Pattern}
    {actions : PatternActions} {id : Identity}
    (planned : PatternPlan program world address authority access pattern actions)
    (safe : CanEndStorage world id) (outside : id ≠ address.root) :
    id ∉ (ScheduledPattern actions).flatMap PatternAction.rootSupport := by
  refine PatternPlan.rec
    (motive_1 := fun address _ _ _ actions _ => id ≠ address.root →
      id ∉ (ScheduledPattern actions).flatMap PatternAction.rootSupport)
    (motive_2 := fun address _ _ _ _ actions _ => id ≠ address.root →
      id ∉ (ScheduledPattern actions).flatMap PatternAction.rootSupport)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ planned outside
  all_goals intros
  all_goals simp_all [ScheduledPattern,PatternAction.rootSupport,Address.child]
  case refine_9 =>
    rename_i found _ live _ _ _ _ ih bound
    have nested := ih (Ne.symm (safe.1 _ _ found live))
    exact nested

/-- An executable context stays outside the caller activation. A pending
yield may name that caller only when no inner frame remains. Operation routing
is checked at the actual invocation boundary, not forbidden by this invariant. -/
def Task.PrivateActivation (owner : Identity) (returning : Bool) : Task → Prop
  | .run context _ | .atom context _ _ _ | .apply context _ _ | .enter context _ _ _
  | .pattern context _ _ | .perform context _ _ _ | .resume context _ _ _
  | .primitive context _ _ _ _ _ => context.activation ≠ owner
  | .yield context _ => returning = true ∨ context.activation ≠ owner
  | .destroy context _ _ next | .destroyFields context _ _ _ next
  | .cleanup context _ next | .cancel context _ next =>
      context.activation ≠ owner ∧ next.PrivateActivation owner returning
  | .finishShell _ _ next | .retire _ next | .closeRegion _ next | .closeLoan _ next
  | .releaseLoan _ next | .transfer _ _ _ next => next.PrivateActivation owner returning
  | .finishClause handler _ _ _ => owner ∉ handler.activationSupport
  | .foreign session _ | .foreignCallbackReturned session _ _ _ => session.call.context.activation ≠ owner
  | .leave _ _ _ => False
  | .stopped _ _ | .fatal _ => True

def Frame.PrivateActivation (owner : Identity) (returning : Bool) : Frame → Prop
  | .binding context _ _ | .scope context _ _ | .label context _ _ _
  | .resumed context | .tailResume context _ => context.activation ≠ owner
  | .activation caller activeOwner _ => activeOwner ≠ owner ∧ (returning = true ∨ caller.activation ≠ owner)
  | .handler installed _ => owner ∉ installed.activationSupport
  | .serviced installed _ clause _ | .completion installed _ clause =>
      clause.activation ≠ owner ∧ owner ∉ installed.activationSupport
  | .hook context _ _ _ _ next => context.activation ≠ owner ∧ next.PrivateActivation owner returning
  | .hostCallback session _ _ _ _ => session.call.context.activation ≠ owner
  | .foreign _ => True

def PrivateFrames (owner : Identity) : List Frame → Prop
  | [] => True
  | frame :: rest => frame.PrivateActivation owner rest.isEmpty ∧ PrivateFrames owner rest

def PrivateControl (id owner : Identity) (inner : List Frame) (task : Task) : Prop :=
  id ∉ task.rootSupport ∧ id ∉ inner.flatMap Frame.rootSupport ∧
    task.PrivateActivation owner inner.isEmpty ∧ PrivateFrames owner inner

theorem Frame.PrivateActivation.not_owns_temporary {frame : Frame} {owner scope : Identity}
    {returning : Bool} (privateOwner : frame.PrivateActivation owner returning) :
    ¬ FrameOwnsHome frame (.temporary owner scope) := by
  cases frame <;>
    simp_all [Frame.PrivateActivation,FrameOwnsHome,HomeOwnedByActivation,HomeOwnedByScope,
      InstalledHandler.activationSupport,ne_comm]

theorem PrivateFrames.member {owner : Identity} {frames : List Frame} {frame : Frame}
    (privateOwners : PrivateFrames owner frames) (member : frame ∈ frames) :
    ∃ returning, frame.PrivateActivation owner returning := by
  induction frames with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨rest.isEmpty,privateOwners.1⟩
      · exact ih privateOwners.2 member

theorem PrivateFrames.append_right {owner : Identity} {first last : List Frame}
    (privateOwners : PrivateFrames owner (first ++ last)) : PrivateFrames owner last := by
  induction first with
  | nil => exact privateOwners
  | cons _ _ ih => exact ih privateOwners.2

theorem PrivateControl.binding_outside {id owner : Identity} {inner rest : List Frame} {task : Task}
    {caller context : Context} {address handle destination : Address} {authority : Authority} {loan : Identity}
    {next : Task} {body : Code} {outer : List Frame}
    (control : PrivateControl id owner inner task)
    (frames : inner ++ .hook caller address authority handle loan next :: outer = .binding context destination body :: rest) :
    destination.root ≠ id := by
  cases inner with
  | nil => cases frames
  | cons frame inner =>
    cases List.cons.inj frames |>.1
    have outside := control.2.1
    simp only [List.flatMap_cons,Frame.rootSupport,List.mem_append,List.mem_cons,List.not_mem_nil,
      or_false,not_or] at outside
    exact Ne.symm outside.1.2

theorem RetireAddresses.avoids_root {addresses : List Address} {next : Task} {id : Identity}
    (outside : ∀ address ∈ addresses, address.root ≠ id) (continued : id ∉ next.rootSupport) :
    id ∉ (addresses.foldr (fun address nextTask => .retire address.root nextTask) next).rootSupport := by
  induction addresses with
  | nil => exact continued
  | cons address rest ih =>
    exact fun member => (List.mem_cons.mp member).elim
      (fun same => outside address List.mem_cons_self same.symm)
      (ih (fun address member => outside address (List.mem_cons_of_mem _ member)))

@[simp] theorem RetireAddresses.private_activation (addresses : List Address) (next : Task)
    (owner : Identity) (returning : Bool) :
    (addresses.foldr (fun address nextTask => .retire address.root nextTask) next).PrivateActivation owner returning =
      next.PrivateActivation owner returning := by
  induction addresses with
  | nil => rfl
  | cons _ _ ih => exact ih

@[simp] theorem CloseRegions.private_activation (regions : List Identity) (next : Task)
    (owner : Identity) (returning : Bool) :
    (CloseRegions regions next).PrivateActivation owner returning = next.PrivateActivation owner returning := by
  unfold CloseRegions
  induction regions.eraseDups with
  | nil => rfl
  | cons _ _ ih => exact ih

@[simp] theorem ReleaseLoans.private_activation (loans : List Identity) (next : Task)
    (owner : Identity) (returning : Bool) :
    (ReleaseLoans loans next).PrivateActivation owner returning = next.PrivateActivation owner returning := by
  unfold ReleaseLoans
  induction loans.eraseDups with
  | nil => rfl
  | cons _ _ ih => exact ih

@[simp] theorem ReleaseCustodyLoans.private_activation (world : World) (custody : ClaimCustody) (next : Task)
    (owner : Identity) (returning : Bool) :
    (ReleaseCustodyLoans world custody next).PrivateActivation owner returning = next.PrivateActivation owner returning :=
  ReleaseLoans.private_activation _ next owner returning


theorem _root_.Glorious.Language.Kernel.ScopeRoots.avoids_private {world : World}
    {activation scope owner savedScope id : Identity} {root : Root} {kept roots : List Identity}
    (selected : ScopeRoots world activation scope kept roots) (slot : world.PrivateSlot id root)
    (home : root.home = .temporary owner savedScope) (outside : activation ≠ owner) : id ∉ roots := by
  intro member
  obtain ⟨actual,found,_,owned,_⟩ := (selected.2 id).mp member
  have same := Option.some.inj (found.symm.trans slot.found)
  subst actual
  simp [OwnedByScope,HomeOwnedByScope,home] at owned
  exact outside owned.1.symm

theorem _root_.Glorious.Language.Kernel.ActivationRoots.avoids_private {world : World}
    {activation owner savedScope id : Identity} {root : Root} {kept roots : List Identity}
    (selected : ActivationRoots world activation kept roots) (slot : world.PrivateSlot id root)
    (home : root.home = .temporary owner savedScope) (outside : activation ≠ owner) : id ∉ roots := by
  intro member
  obtain ⟨actual,found,_,owned,_⟩ := (selected.2 id).mp member
  have same := Option.some.inj (found.symm.trans slot.found)
  subst actual
  simp [OwnedByActivation,HomeOwnedByActivation,home] at owned
  exact outside owned.symm

theorem AtomStep.private_control {program : Kernel.Program} {before after : State} {event : Option Event}
    {id owner : Identity} {root : Root} {inner : List Frame}
    (step : AtomStep program before event after) (well : before.world.WellFormed)
    (slot : before.world.PrivateSlot id root) (control : PrivateControl id owner inner before.task) :
    PrivateControl id owner inner after.task := by
  cases step
  all_goals simp_all only [PrivateControl,Task.rootSupport,RetireAddresses.private_activation,
    Task.PrivateActivation,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or,
    not_false_eq_true,true_and,and_true]
  all_goals try exact control.2.2.1
  case closure captured _ _ created =>
    exact ⟨RetireAddresses.avoids_root (captured.private_slot well slot).2 control.1.1,control.2.2.1⟩
  case primitive resolved _ =>
    exact ⟨resolved.avoids_root (Context.bindings_avoid_root control.1.1) slot.safe,control.2.2.1⟩

end Glorious.Language.Execution
