import OwnershipMir.CallShells

namespace OwnershipMir.Calls

/-- Appending retained caller regions changes no local lookup or instruction.
This is storage embedding for activations, not another execution semantics. -/
def Configuration.retain {n : Nat} (config : Configuration n) (callers : List (Frame n)) : Configuration n :=
  {config with stack := config.stack ++ callers}

theorem Transition.retain {n : Nat} {program : Program n} {before after : Configuration n}
    (step : Transition program before after) (callers : List (Frame n)) :
    Transition program (before.retain callers) (after.retain callers) := by
  cases step with
  | operation step => exact .operation step
  | enter resolved resident => exact .enter resolved resident
  | handoff installed => exact .handoff installed
  | clean step => exact .clean step
  | retire => exact .retire

theorem Run.retain {n : Nat} {program : Program n} {before after : Configuration n}
    (run : Run (Transition program) before after) (callers : List (Frame n)) :
    Run (Transition program) (before.retain callers) (after.retain callers) := by
  induction run with
  | refl => exact .refl _
  | step head tail ih => exact .step (head.retain callers) ih

theorem Diverges.retain {n : Nat} {program : Program n} {start : Configuration n}
    (infinite : Diverges (Transition program) start) (callers : List (Frame n)) : Diverges (Transition program) (start.retain callers) := by
  obtain ⟨trace, initial, steps⟩ := infinite
  exact ⟨fun i => (trace i).retain callers, congrArg (·.retain callers) initial, fun i => (steps i).retain callers⟩

theorem Safe.terminal_typed {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    {config : Configuration n} (safe : Safe program signature final config) (terminal : config.Terminal) :
    config.state.Typed signature final := by
  obtain ⟨cleanup, halted, empty⟩ := terminal
  cases safe with
  | body typed checked retained =>
    cases halted
    cases empty
    cases retained
    cases checked
    exact typed
  | cleaning => cases halted

/-- An actual returning callee composes with entry, caller result installation,
complete ordered cleanup, and resumption. Return is a theorem about a supplied
execution, never an assumption in Program.Checked or progress. -/
theorem Function.call_return {n : Nat} {program : Program n} {signature : Signature} {function : Function n}
    (functions : program.Checked) {identity : Nat} (selected : program identity = some function)
    {caller : State (n + 1)} {before after : Context (n + 1)}
    (callerTyped : caller.Typed signature before) {destination : Place (n + 1)}
    (checked : Instruction.Checked program before (.call identity destination) after)
    {argument : Value} (resident : caller.temp = some argument) {returned : State (n + 1)}
    (bodyRun : Run (Transition program) (function.start argument) ⟨.body .halt function.cleanup, returned, []⟩)
    (next : Body n) (cleanup : Code (n + 1) (Op (n + 1))) (stack : List (Frame n)) :
    ∃ slots,
      Run (Transition program) ⟨.body (.act (.call identity destination) next) cleanup, caller, stack⟩
        ⟨.body next cleanup, ⟨slots, none⟩, stack⟩ ∧
      (State.mk slots none).Typed signature after ∧
      (∀ slot, slot ≠ destination.root → slots slot = caller.slots slot) := by
  cases checked with
  | call resolved argumentType put =>
    cases Option.some.inj (selected.symm.trans resolved)
    have classified : argument.kind signature = function.input := by
      simpa [resident] using callerTyped.2.trans argumentType
    have returnedTyped := ((Function.start_safe functions selected classified).execution functions bodyRun).terminal_typed
      ⟨function.cleanup, rfl, rfl⟩
    let frame : Frame n := ⟨caller.slots, next, cleanup, destination⟩
    obtain ⟨result, installed, typed, _⟩ := put.sound (state := ⟨caller.slots, returned.temp⟩)
      ⟨callerTyped.1, returnedTyped.2⟩
    have empty : result.temp = none := by
      cases put
      exact Option.map_eq_none_iff.mp typed.2
    cases result with
    | mk slots temp =>
      cases empty
      have releaseTyped : (State.mk returned.slots none).Typed signature function.cleanupContext :=
        ⟨returnedTyped.1, rfl⟩
      have release := Function.cleanup_returns (program := program) (functions identity function selected).2.1
        releaseTyped ({frame with slots := slots}) stack
      refine ⟨slots, .step (.enter selected resident) ((Run.retain bodyRun (frame :: stack)).trans (.step (.handoff installed) release)), typed, ?_⟩
      exact handoff_frame returned frame installed

/-- Recursive divergence propagates through actual call entry with all caller
regions retained. A call is never collapsed into a terminating instruction. -/
theorem Function.call_diverges {n : Nat} {program : Program n} {function : Function n}
    {identity : Nat} (selected : program identity = some function) {caller : State (n + 1)}
    {argument : Value} (resident : caller.temp = some argument)
    (infinite : Diverges (Transition program) (function.start argument)) (destination : Place (n + 1))
    (next : Body n) (cleanup : Code (n + 1) (Op (n + 1))) (stack : List (Frame n)) :
    Diverges (Transition program) ⟨.body (.act (.call identity destination) next) cleanup, caller, stack⟩ := by
  have entry : Run (Transition program) ⟨.body (.act (.call identity destination) next) cleanup, caller, stack⟩
      ((function.start argument).retain (⟨caller.slots, next, cleanup, destination⟩ :: stack)) :=
    .step (.enter selected resident) (.refl _)
  exact (entry.diverges_iff Transition.deterministic).mpr (Diverges.retain infinite _)

/-- Ready source-facing signature shapes imply actual initialized residents,
not merely initialized static annotations. -/
theorem Function.return_initialized {n : Nat} {program : Program n} {signature : Signature} {function : Function n}
    (functions : program.Checked) {identity : Nat} (selected : program identity = some function)
    {argument : Value} (typed : argument.kind signature = function.input) {after : Configuration n}
    (run : Run (Transition program) (function.start argument) after) (terminal : after.Terminal) :
    ∃ value, after.state.temp = some value ∧ value.kind signature = function.output ∧ value.ready := by
  have returned := ((Function.start_safe functions selected typed).execution functions run).terminal_typed terminal
  obtain ⟨value, stored, classified⟩ := Option.map_eq_some_iff.mp returned.2
  have ready : (value.kind signature).ready := classified.symm ▸ (functions identity function selected).2.2.2
  exact ⟨value, stored, classified, by simpa [Value.kind] using ready⟩

end OwnershipMir.Calls
