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
    (run : Run (Step Calls.Instruction.exec) before after) (store : Store (n + 1) Atom) (active : Nat)
    (live : store.region active = some before.state.slots) (register : store.temp = before.state.temp)
    (cleanup : Code (n + 1) (Op (n + 1))) (stack : List (Calls.Frame n)) :
    Run (Calls.Transition program) ⟨.body before.code cleanup, store, active, stack⟩
      ⟨.body after.code cleanup, store.replace active after.state.slots after.state.temp, active, stack⟩ := by
  induction run generalizing store with
  | @refl start =>
    have same : store.replace active start.state.slots start.state.temp = store := by
      rw [← register]; exact Store.replace_self live
    rw [same]; exact .refl _
  | @step before middle after head tail ih =>
    have first : Calls.Transition program ⟨.body before.code cleanup, store, active, stack⟩
        ⟨.body middle.code cleanup, store.replace active middle.state.slots middle.state.temp, active, stack⟩ :=
      .operation live (by simpa [register] using head)
    have rest := ih (store.replace active middle.state.slots middle.state.temp)
      (Store.replace_same (Store.region_bound live) _ _) rfl
    simpa only [Store.replace_replace] using Run.step first rest


/-- Argument preparation is a real target step before call entry. Callee
execution, protected handoff, source cleanup, and retirement all remain visible. -/
theorem Transition.lower {n : Nat} {program : Program n} {before after : Configuration n}
    (step : Transition program before after) :
    ∃ middle, Calls.Transition program.lower before.lower middle ∧
      Run (Calls.Transition program.lower) middle after.lower := by
  cases step with
  | operation live step =>
    obtain ⟨middle, head, tail⟩ := lower_step step
    refine ⟨_, .operation live head, ?_⟩
    simpa only [Configuration.lower, Control.lower, Store.replace_replace] using body_run tail _ _ (Store.replace_same (Store.region_bound live) _ _) rfl _ _
  | @enter identity argument destination next cleanup store active slots prepared stack function value live resolved acquired resident =>
    refine ⟨_, .operation live (.act (by rwa [acquire_eq] at acquired)), .step ?_ (.refl _)⟩
    simpa only [Configuration.lower, Control.lower, Frame.lower, List.map_cons, Store.replace, List.length_set,
      Block.emit, Function.lower, Function.cleanup, Calls.Function.cleanup, Function.cleanupContext, Calls.Function.cleanupContext] using
      (Calls.Transition.enter (store := store.replace active prepared.slots prepared.temp) (active := active)
        (next := SourceCalls.lower next) (cleanup := OwnershipMir.lower cleanup) (destination := destination)
        (stack := stack.map Frame.lower) (Program.selected resolved) resident)
  | handoff live installed => exact ⟨_, .handoff live installed, .refl _⟩
  | clean live step =>
    obtain ⟨middle, head, tail⟩ := OwnershipMir.lower_step step
    refine ⟨_, .clean live head, ?_⟩
    simpa only [Configuration.lower, Control.lower, Store.replace_replace] using Calls.Run.cleaning tail _ _ (Store.replace_same (Store.region_bound live) _ _) rfl _
  | retire empty register => exact ⟨_, .retire empty register, .refl _⟩


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
  | operation found left =>
    cases right with
    | operation live right => cases Option.some.inj (found.symm.trans live); cases left.deterministic right; rfl
    | enter live => cases Option.some.inj (found.symm.trans live); cases left with | act executed => cases executed
    | handoff => exact False.elim (left.not_halt rfl)
  | enter found resolved acquired resident =>
    cases right with
    | operation live right => cases Option.some.inj (found.symm.trans live); cases right with | act executed => cases executed
    | enter live selected moved stored =>
      cases Option.some.inj (found.symm.trans live)
      cases Option.some.inj (resolved.symm.trans selected)
      cases Option.some.inj (acquired.symm.trans moved)
      cases Option.some.inj (resident.symm.trans stored)
      rfl
  | handoff found installed =>
    cases right with
    | operation live right => exact False.elim (right.not_halt rfl)
    | handoff live other => cases Option.some.inj (found.symm.trans live); cases Option.some.inj (installed.symm.trans other); rfl
  | clean found left =>
    cases right with
    | clean live right => cases Option.some.inj (found.symm.trans live); cases left.deterministic right; rfl
    | retire => exact False.elim (left.not_halt rfl)
  | retire =>
    cases right with
    | clean live right => exact False.elim (right.not_halt rfl)
    | retire => rfl


end OwnershipMir.SourceCalls
