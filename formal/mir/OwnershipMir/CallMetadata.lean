import OwnershipMir.CallSafety

namespace OwnershipMir

theorem State.declared_without_temp {n : Nat} {declarations : Declarations} {signature : Signature}
    {state : State n} (valid : state.Declared declarations signature) :
    (State.mk state.slots none).Declared declarations signature :=
  ⟨valid.1, by intro tree impossible; cases impossible⟩

theorem Safe.declared_step {n : Nat} {α : Type} {signature : Signature} {declarations : Declarations}
    {rule : Context n → α → Context n → Prop} {exec : α → State n → Option (State n)}
    {final : Context n} {before after : Configuration n α} (safe : Safe signature rule final before)
    (preserves : ∀ {before after op state next}, rule before op after → state.Typed signature before →
      state.Declared declarations signature → exec op state = some next → next.Declared declarations signature)
    (valid : before.state.Declared declarations signature) (step : Step exec before after) :
    after.state.Declared declarations signature := by
  obtain ⟨current, typed, checked⟩ := safe
  cases step with
  | act executed => cases checked with | act head tail => exact preserves head typed valid executed
  | branch => exact valid
  | loop => exact valid

namespace Calls

/-- One declaration environment validates the active region and every retained
caller. This invariant follows actual residents, including holes and registers. -/
def Configuration.Declared {n : Nat} (declarations : Declarations) (signature : Signature)
    (config : Configuration n) : Prop :=
  config.state.Declared declarations signature ∧
    ∀ frame ∈ config.stack, frame.state.Declared declarations signature

theorem argument_declared {n : Nat} {declarations : Declarations} {signature : Signature} {value : Value}
    (valid : Layout.Declared declarations (value.layout (Atom.kind signature))) :
    (State.mk (argumentSlots value) none : State (n + 1)).Declared declarations signature := by
  refine ⟨?_, by intro tree impossible; cases impossible⟩
  intro i
  refine Fin.cases ?_ (fun _ => ?_) i
  · intro tree same; cases same; exact valid
  · intro tree impossible; cases impossible

theorem Instruction.Checked.preserves_declarations {n : Nat} {program : Program n} {module : Module}
    {signature : Signature} {before after : Context (n + 1)} {instruction : Instruction n}
    (checked : Instruction.Checked program module before instruction after) {state next : State (n + 1)}
    (typed : state.Typed signature before) (valid : state.Declared program.declarations signature)
    (executed : instruction.exec state = some next) : next.Declared program.declarations signature := by
  cases checked with
  | operation checked => exact checked.preserves_declarations typed valid executed
  | call => cases executed

theorem Safe.declared_step {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    {before after : Configuration n} (safe : Safe program signature final before)
    (valid : before.Declared program.declarations signature) (step : Transition program before after) :
    after.Declared program.declarations signature := by
  cases step with
  | operation step =>
    cases safe with
    | body typed checked retained =>
      exact ⟨OwnershipMir.Safe.declared_step ⟨_, typed, checked⟩ (fun checked typed valid executed => checked.preserves_declarations typed valid executed) valid.1 step, valid.2⟩
  | @enter identity destination next cleanup state stack function argument resolved resident =>
    refine ⟨argument_declared (valid.1.2 argument resident), ?_⟩
    intro frame member
    rcases List.mem_cons.mp member with same | member
    · subst frame; exact State.declared_without_temp valid.1
    · exact valid.2 frame member
  | @handoff cleanup state frame stack slots installed =>
    cases safe with
    | body typed checked retained =>
      cases checked
      cases retained with
      | cons resident returned put next outer release =>
        have caller := valid.2 frame (by simp)
        have transferred := put.preserves_declarations (state := ⟨frame.slots, state.temp⟩)
          ⟨resident, typed.2.trans returned⟩ ⟨caller.1, valid.1.2⟩ installed
        refine ⟨State.declared_without_temp valid.1, ?_⟩
        intro other member
        rcases List.mem_cons.mp member with same | member
        · subst other; exact transferred
        · exact valid.2 other (List.mem_cons_of_mem _ member)
  | clean step =>
    cases safe with
    | cleaning typed checked retained =>
      exact ⟨OwnershipMir.Safe.declared_step ⟨_, typed, checked⟩ (fun checked typed valid executed => checked.preserves_declarations typed valid executed) valid.1 step, valid.2⟩
  | @retire frame stack =>
    exact ⟨valid.2 frame (by simp), fun other member => valid.2 other (List.mem_cons_of_mem _ member)⟩

theorem Safe.declared_run {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    (functions : program.Checked) {before after : Configuration n} (safe : Safe program signature final before)
    (valid : before.Declared program.declarations signature) (run : Run (Transition program) before after) :
    after.Declared program.declarations signature := by
  induction run with
  | refl => exact valid
  | step head tail ih => exact ih (safe.preservation functions head) (safe.declared_step valid head)

end Calls
end OwnershipMir
