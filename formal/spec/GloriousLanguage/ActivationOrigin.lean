import GloriousLanguage.Machine
import GloriousLanguage.ControlSupport

/-! Historical activation provenance of actual homes and executable control.
Freshness applies to every allocated identity, not merely the next activation:
entry and snapshot copying advance the same counter consumed by cleanup. -/
namespace Glorious.Language

def Home.ActivationsBelow (home : Home) (limit : Identity) : Prop :=
  ∀ activation, Kernel.HomeOwnedByActivation home activation → activation < limit

theorem Home.ActivationsBelow.mono {home : Home} {first last : Identity}
    (bounded : home.ActivationsBelow first) (limit : first ≤ last) : home.ActivationsBelow last :=
  fun activation owned => Nat.lt_of_lt_of_le (bounded activation owned) limit

@[simp] theorem Home.localSlot_activationsBelow {activation scope limit : Identity} :
    (Home.localSlot activation scope).ActivationsBelow limit ↔ activation < limit := by
  simp [ActivationsBelow,Kernel.HomeOwnedByActivation]

@[simp] theorem Home.temporary_activationsBelow {activation scope limit : Identity} :
    (Home.temporary activation scope).ActivationsBelow limit ↔ activation < limit := by
  simp [ActivationsBelow,Kernel.HomeOwnedByActivation]

@[simp] theorem Home.allocation_activationsBelow (domain limit : Identity) :
    (Home.allocation domain).ActivationsBelow limit := by
  simp [ActivationsBelow,Kernel.HomeOwnedByActivation]

@[simp] theorem Home.external_activationsBelow (domain limit : Identity) :
    (Home.external domain).ActivationsBelow limit := by
  simp [ActivationsBelow,Kernel.HomeOwnedByActivation]

@[simp] theorem Home.suspended_activationsBelow (id limit : Identity) :
    (Home.suspended id).ActivationsBelow limit := by
  simp [ActivationsBelow,Kernel.HomeOwnedByActivation]

def World.ActivationsBelow (world : World) (limit : Identity) : Prop :=
  ∀ id root, world.roots.get id = some root → root.home.ActivationsBelow limit

theorem World.ActivationsBelow.mono {world : World} {first last : Identity}
    (bounded : world.ActivationsBelow first) (limit : first ≤ last) : world.ActivationsBelow last :=
  fun id root found => (bounded id root found).mono limit

theorem World.ActivationsBelow.no_future_home {world : World} {limit activation id : Identity} {root : Root}
    (bounded : world.ActivationsBelow limit) (future : limit ≤ activation)
    (found : world.roots.get id = some root) : ¬ Kernel.OwnedByActivation root activation :=
  fun owned => Nat.not_lt_of_ge future (bounded id root found activation owned)

namespace Execution

open Kernel

def InstalledHandler.activationSupport (handler : InstalledHandler) : List Identity :=
  [handler.environment.activation,handler.computation.activation,handler.outer.activation]

def Task.activationSupport : Task → List Identity
  | .run context _ | .atom context _ _ _ | .yield context _ | .apply context _ _
  | .enter context _ _ _ | .pattern context _ _ | .perform context _ _ _
  | .resume context _ _ _ | .leave context _ _ | .primitive context _ _ _ _ _ => [context.activation]
  | .destroy context _ _ next | .destroyFields context _ _ _ next
  | .cleanup context _ next | .cancel context _ next => context.activation :: next.activationSupport
  | .finishShell _ _ next | .retire _ next | .closeRegion _ next | .closeLoan _ next
  | .releaseLoan _ next | .transfer _ _ _ next => next.activationSupport
  | .finishClause handler _ _ _ => handler.activationSupport
  | .foreign session _ | .foreignCallbackReturned session _ _ _ => [session.call.context.activation]
  | .stopped _ | .fatal _ => []

def Frame.activationSupport : Frame → List Identity
  | .binding context _ _ | .scope context _ _ | .label context _ _ _
  | .resumed context | .tailResume context _ => [context.activation]
  | .activation caller owner _ => [caller.activation,owner]
  | .handler installed _ => installed.activationSupport
  | .serviced installed _ clause _ | .completion installed _ clause =>
      clause.activation :: installed.activationSupport
  | .hook context _ _ _ _ next => context.activation :: next.activationSupport
  | .foreign _ => []
  | .hostCallback session _ _ _ _ => [session.call.context.activation]

def Suspension.controlActivationSupport (suspension : Suspension) : List Identity :=
  suspension.context.activation :: suspension.handler.activationSupport ++ suspension.frames.flatMap Frame.activationSupport

/-- Every historical home and retained context is older than the next identity.
Ended roots and inactive suspensions retain provenance, not access permission. -/
structure State.ActivationsWellFormed (state : State) : Prop where
  homes : state.world.ActivationsBelow state.nextActivation
  task : RootSupport.Below state.task.activationSupport state.nextActivation
  frames : RootSupport.Below (state.frames.flatMap Frame.activationSupport) state.nextActivation
  saved : ∀ id suspension, state.resumptions.get id = some suspension →
    RootSupport.Below suspension.controlActivationSupport state.nextActivation

theorem State.ActivationsWellFormed.no_future_home {state : State} (valid : state.ActivationsWellFormed)
    {activation rootId : Identity} {root : Root} (future : state.nextActivation ≤ activation)
    (found : state.world.roots.get rootId = some root) : ¬ OwnedByActivation root activation :=
  valid.homes.no_future_home future found

/-- Cleanup's existing home-ownership relation only claims activations that
occur in the actual owning frame, including explicit activation-frame owners. -/
theorem FrameOwnsHome.activation_mem {frame : Frame} {home : Home} {activation : Identity}
    (owns : FrameOwnsHome frame home) (homeOwner : HomeOwnedByActivation home activation) :
    activation ∈ frame.activationSupport := by
  rcases homeOwner with ⟨scope,rfl⟩ | ⟨scope,rfl⟩
  all_goals cases frame <;> simp_all [FrameOwnsHome,Frame.activationSupport,InstalledHandler.activationSupport,
    HomeOwnedByActivation,HomeOwnedByScope] <;> grind

theorem CapturedHome.activation_mem {handler : InstalledHandler} {frames : List Frame}
    {home : Home} {activation : Identity}
    (captured : CapturedHome handler frames home) (owns : HomeOwnedByActivation home activation) :
    activation ∈ handler.activationSupport ++ frames.flatMap Frame.activationSupport := by
  rcases captured with scopeOwned | ⟨frame,member,owned⟩
  · apply List.mem_append_left
    rcases owns with ⟨scope,rfl⟩ | ⟨scope,rfl⟩
    all_goals simp_all [InstalledHandler.activationSupport,HomeOwnedByScope]
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨frame,member,owned.activation_mem owns⟩)

theorem Suspension.CaptureOrigin.homes_activationsBelow {suspension : Suspension} {limit : Identity}
    (origin : suspension.CaptureOrigin)
    (bounded : RootSupport.Below suspension.controlActivationSupport limit)
    {root : Identity} {home : Home} (found : suspension.homes.get root = some home) :
    home.ActivationsBelow limit := by
  intro activation owns
  exact bounded activation (List.mem_cons_of_mem _ ((origin.ownedHomes root home found).activation_mem owns))

end Execution
end Glorious.Language
