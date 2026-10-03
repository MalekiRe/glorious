import OwnershipMir.SourceCalls
import OwnershipMir.Simulation

namespace OwnershipMir.SourceCalls

theorem operations_exec {n : Nat} (ops : List (Op (n + 1))) (state : State (n + 1)) :
    Block.exec Calls.Instruction.exec (ops.map Calls.Instruction.operation) state =
      Block.exec Op.exec ops state := by
  induction ops generalizing state with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.map_cons, Block.exec, Calls.Instruction.exec]
    rw [funext ih]

theorem Instruction.block_nonempty {n : Nat} (instruction : Instruction n) : instruction.block ≠ [] := by
  cases instruction with
  | command cmd => simpa [Instruction.block] using cmd.block_nonempty
  | call => simp [Instruction.block]
  | result => simp [Instruction.block]

theorem Instruction.exec_eq {n : Nat} (instruction : Instruction n) (state : State (n + 1)) :
    instruction.exec state = Block.exec Calls.Instruction.exec instruction.block state := by
  cases instruction with
  | command cmd => simp [Instruction.exec, Instruction.block, operations_exec, Command.exec_eq]
  | call => simp [Instruction.exec, Instruction.block, Block.exec, Calls.Instruction.exec]
  | result value => simp [Instruction.exec, Instruction.block, Block.exec, Calls.Instruction.exec, acquire_eq]

theorem lower_step {n : Nat} {before after : OwnershipMir.Configuration (n + 1) (Instruction n)}
    (step : Step Instruction.exec before after) :
    ∃ middle, Step Calls.Instruction.exec ⟨lower before.code, before.state⟩ middle ∧
      Run (Step Calls.Instruction.exec) middle ⟨lower after.code, after.state⟩ := by
  cases step with
  | @act instruction next state after executed =>
    exact Block.exec_positive instruction.block instruction.block_nonempty
      (by rwa [Instruction.exec_eq] at executed) (lower next)
  | @branch guard yes no state choice observed =>
    cases choice <;> exact ⟨_, .branch observed, .refl _⟩
  | @loop guard body next state choice observed =>
    cases choice
    · exact ⟨_, .loop observed, .refl _⟩
    · refine ⟨_, .loop observed, ?_⟩
      simpa [lower_append, lower] using (Run.refl (next := Step Calls.Instruction.exec)
        (OwnershipMir.Configuration.mk (lower (body.append (.loop guard body next))) state))

private theorem body_run {n : Nat} {program : Calls.Program n}
    {before after : OwnershipMir.Configuration (n + 1) (Calls.Instruction n)}
    (run : Run (Step Calls.Instruction.exec) before after)
    (cleanup : Code (n + 1) (Op (n + 1))) (stack : List (Calls.Frame n)) :
    Run (Calls.Transition program) ⟨.body before.code cleanup, before.state, stack⟩
      ⟨.body after.code cleanup, after.state, stack⟩ := by
  induction run with
  | refl => exact .refl _
  | step head tail ih => exact .step (.operation head) ih

/-- Argument preparation is a real target step before call entry. Callee
execution, protected handoff, source cleanup, and retirement all remain visible. -/
theorem Transition.lower {n : Nat} {program : Program n} {before after : Configuration n}
    (step : Transition program before after) :
    ∃ middle, Calls.Transition program.lower before.lower middle ∧
      Run (Calls.Transition program.lower) middle after.lower := by
  cases step with
  | operation step =>
    obtain ⟨middle, head, tail⟩ := lower_step step
    exact ⟨_, .operation head, body_run tail _ _⟩
  | enter resolved acquired resident =>
    exact ⟨_, .operation (.act (by rwa [acquire_eq] at acquired)),
      .step (.enter (Program.selected resolved) resident) (.refl _)⟩
  | handoff installed => exact ⟨_, .handoff installed, .refl _⟩
  | clean step =>
    obtain ⟨middle, head, tail⟩ := OwnershipMir.lower_step step
    exact ⟨_, .clean head, Calls.Run.cleaning tail _⟩
  | retire => exact ⟨_, .retire, .refl _⟩

theorem Run.lower {n : Nat} {program : Program n} {before after : Configuration n}
    (run : Run (Transition program) before after) :
    Run (Calls.Transition program.lower) before.lower after.lower :=
  PositiveSimulation.run (source := Transition program) Transition.lower run

theorem Transition.not_terminal {n : Nat} {program : Program n} {before after : Configuration n}
    (step : Transition program before after) : ¬ before.Terminal := by
  intro terminal
  obtain ⟨middle, head, _⟩ := step.lower
  exact head.not_terminal (before.terminal_lower.mpr terminal)

theorem Transition.deterministic {n : Nat} {program : Program n} {before first second : Configuration n}
    (left : Transition program before first) (right : Transition program before second) : first = second := by
  cases left with
  | operation left =>
    cases right with
    | operation right => cases left.deterministic right; rfl
    | enter => cases left with | act executed => cases executed
    | handoff => exact False.elim (left.not_halt rfl)
  | enter resolved acquired resident =>
    cases right with
    | operation right => cases right with | act executed => cases executed
    | enter selected moved live =>
      cases Option.some.inj (resolved.symm.trans selected)
      cases Option.some.inj (acquired.symm.trans moved)
      cases Option.some.inj (resident.symm.trans live)
      rfl
  | handoff installed =>
    cases right with
    | operation right => exact False.elim (right.not_halt rfl)
    | handoff other => cases Option.some.inj (installed.symm.trans other); rfl
  | clean left =>
    cases right with
    | clean right => cases left.deterministic right; rfl
    | retire => exact False.elim (left.not_halt rfl)
  | retire =>
    cases right with
    | clean right => exact False.elim (right.not_halt rfl)
    | retire => rfl

end OwnershipMir.SourceCalls
