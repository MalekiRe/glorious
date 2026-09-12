import GloriousLanguage.ActivationForeignOrigin

/-! The actual machine preserves historical activation provenance. Entry,
handler clauses and copied snapshots share one monotonically advancing supply;
saved control keeps its immutable original contexts through replay accounting. -/
namespace Glorious.Language.Execution

theorem Step.activation_frontier {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event} (step : Step program host before event after) :
    before.nextActivation ≤ after.nextActivation := by
  rcases step with localStep | atom | effect | branch | primitive | foreign
  · exact localStep.activation_frontier
  · exact atom.activation_frontier
  · exact effect.activation_frontier
  · exact branch.activation_frontier
  · exact primitive.activation_frontier
  · exact foreign.activation_frontier

theorem Run.activation_frontier {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} (run : Run program host before trace after) :
    before.nextActivation ≤ after.nextActivation := by
  induction run with
  | refl => exact Nat.le_refl _
  | silent step _ ih | visible step _ ih => exact Nat.le_trans step.activation_frontier ih

theorem Step.saved_activation_origin {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event} (valid : before.ActivationsWellFormed)
    (step : Step program host before event after) :
    ∀ id suspension, after.resumptions.get id = some suspension →
      RootSupport.Below suspension.controlActivationSupport after.nextActivation := by
  have frontier := step.activation_frontier
  apply step.resumption_change.saved_property (fun _ _ _ _ bounded => bounded)
    (fun id suspension found => (valid.saved id suspension found).mono frontier)
  intro id equal
  rcases step with localStep | atom | effect | branch | primitive | foreign
  · cases localStep <;> cases equal
  · cases atom <;> simp_all <;> split at equal <;> (try split at equal) <;> contradiction
  · rw [equal] at effect
    obtain ⟨suspension,found,bounded⟩ := effect.created_activation_origin valid
    exact ⟨suspension,found,bounded.mono frontier⟩
  · cases branch <;> cases equal
  · cases primitive <;> cases equal
  · cases foreign <;> cases equal

theorem Step.activationsWellFormed {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event}
    (lawful : host.Lawful program) (well : before.world.WellFormed)
    (suspensions : before.SuspensionsWellFormed) (valid : before.ActivationsWellFormed)
    (step : Step program host before event after) : after.ActivationsWellFormed := by
  have support : after.world.ActivationsBelow after.nextActivation ∧
      RootSupport.Below after.task.activationSupport after.nextActivation ∧
      RootSupport.Below (after.frames.flatMap Frame.activationSupport) after.nextActivation := by
    rcases step with localStep | atom | effect | branch | primitive | foreign
    · exact ⟨localStep.homes_activationsBelow valid.homes valid.task valid.frames,
        localStep.activation_support valid.task valid.frames⟩
    · exact ⟨atom.homes_activationsBelow valid.homes valid.task,
        atom.activation_support valid.task valid.frames⟩
    · exact ⟨effect.homes_activationsBelow well suspensions valid,effect.activation_support valid⟩
    · exact ⟨branch.homes_activationsBelow valid.homes valid.task valid.frames,
        branch.activation_support valid.task valid.frames⟩
    · exact ⟨primitive.homes_activationsBelow valid.homes,
        primitive.activation_support valid.task valid.frames⟩
    · exact ⟨foreign.homes_activationsBelow lawful well valid.homes valid.task valid.frames,
        foreign.activation_support valid.task valid.frames⟩
  exact ⟨support.1,support.2.1,support.2.2,step.saved_activation_origin valid⟩

end Glorious.Language.Execution
