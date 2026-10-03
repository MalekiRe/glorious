import OwnershipMir.CallShells

namespace OwnershipMir.Calls
variable {module : Module}

/-- Retain control frames, never copies of resident storage. -/
def Configuration.retain {n : Nat} (config : Configuration n) (callers : List (Frame n)) : Configuration n :=
  {config with stack := config.stack ++ callers}

theorem Transition.retain {n : Nat} {program : Program n} {before after : Configuration n}
    (step : Transition program before after) (callers : List (Frame n)) :
    Transition program (before.retain callers) (after.retain callers) := by
  cases step with
  | operation live step => exact .operation live step
  | enter resolved resident => exact .enter resolved resident
  | handoff live installed => exact .handoff live installed
  | clean live step => exact .clean live step
  | retire empty register => exact .retire empty register

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
    ∃ slots, config.store.region config.active = some slots ∧ (State.mk slots config.store.temp).Typed signature final := by
  obtain ⟨cleanup, halted, empty⟩ := terminal
  cases safe with
  | body live typed checked retained =>
    cases halted; cases empty; cases retained; cases checked
    exact ⟨_, live, typed⟩
  | cleaning => cases halted

/-- The lower bound describes which existing regions this call can update. -/
def Configuration.Within {n : Nat} (bound : Nat) (config : Configuration n) : Prop :=
  bound ≤ config.active ∧ ∀ frame ∈ config.stack, bound ≤ frame.region

theorem Safe.within_step {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    {before after : Configuration n} (safe : Safe program signature final before) {bound : Nat}
    (within : before.Within bound) (step : Transition program before after) :
    after.Within bound ∧ ∀ r, r < bound → after.store.region r = before.store.region r := by
  cases step with
  | operation live step => exact ⟨within, fun r below => Store.replace_other _ _ _ _ _ (by have h := within.1; dsimp at h; omega)⟩
  | enter selected resident =>
    cases safe with
    | body live typed checked retained =>
      have allocated := Store.region_bound live
      have activeBound := within.1
      dsimp at activeBound
      refine ⟨⟨by dsimp; omega, ?_⟩, ?_⟩
      · intro frame member
        rcases List.mem_cons.mp member with same | old
        · subst frame; exact within.1
        · exact within.2 frame old
      · intro r below; exact Store.allocate_old (by omega) _
  | handoff live installed =>
    exact ⟨within, fun r below => Store.replace_other _ _ _ _ _ (by have := within.2 _ (List.mem_cons_self); omega)⟩
  | clean live step => exact ⟨within, fun r below => Store.replace_other _ _ _ _ _ (by have h := within.1; dsimp at h; omega)⟩
  | retire empty register =>
    refine ⟨⟨within.2 _ (List.mem_cons_self), fun frame member => within.2 frame (List.mem_cons_of_mem _ member)⟩, ?_⟩
    exact fun r below => Store.retire_other _ _ _ (by have h := within.1; dsimp at h; omega)

theorem Safe.within_run {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    (functions : program.Checked) {before after : Configuration n} (safe : Safe program signature final before)
    {bound : Nat} (within : before.Within bound) (run : Run (Transition program) before after) :
    after.Within bound ∧ ∀ r, r < bound → after.store.region r = before.store.region r := by
  induction run with
  | refl => exact ⟨within, fun _ _ => rfl⟩
  | step head tail ih =>
    obtain ⟨middle, first⟩ := safe.within_step within head
    obtain ⟨last, rest⟩ := ih (safe.preservation functions head) middle
    exact ⟨last, fun r below => (rest r below).trans (first r below)⟩

/-- Callee execution occurs in the actual ambient store, not a fresh snapshot.
Only control frames are appended when composing the supplied returning run. -/
theorem Function.call_return {n : Nat} {program : Program n} {signature : Signature} {function : Function n}
    (functions : program.Checked) {identity : Nat} (selected : program identity = some function)
    (caller : Store (n + 1) Atom) (active : Nat) {callerSlots : Region (n + 1) Atom}
    (live : caller.region active = some callerSlots) {before after : Context (n + 1)}
    (callerTyped : (State.mk callerSlots caller.temp).Typed signature before) {destination : Place (n + 1)}
    (checked : Instruction.Checked program module before (.call identity destination) after)
    {argument : Value} (resident : caller.temp = some argument) (returned : Store (n + 1) Atom) (returnedActive : Nat)
    (bodyRun : Run (Transition program)
      ⟨.body function.body function.cleanup, caller.allocate (argumentSlots argument), caller.regions.length, []⟩
      ⟨.body .halt function.cleanup, returned, returnedActive, []⟩)
    (next : Body n) (cleanup : Code (n + 1) (Op (n + 1))) (stack : List (Frame n)) :
    ∃ slots, Run (Transition program)
      ⟨.body (.act (.call identity destination) next) cleanup, caller, active, stack⟩
      ⟨.body next cleanup, (returned.replace active slots none).retire returnedActive, active, stack⟩ ∧
      (State.mk slots none).Typed signature after ∧
      (∀ slot, slot ≠ destination.root → slots slot = callerSlots slot) := by
  cases checked with
  | call resolved argumentType put =>
    cases Option.some.inj (selected.symm.trans resolved)
    have classified : Value.kind signature argument = function.input := by simpa [resident] using callerTyped.2.trans argumentType
    have safe : Safe program signature function.exit
        ⟨.body function.body function.cleanup, caller.allocate (argumentSlots argument), caller.regions.length, []⟩ :=
      .body (Store.allocate_fresh _ _) (argument_typed classified) (functions identity function selected).1 .nil
    obtain ⟨returnedSlots, returnedLive, returnedTyped⟩ := (safe.execution functions bodyRun).terminal_typed ⟨_, rfl, rfl⟩
    have lower : active < caller.regions.length := Store.region_bound live
    obtain ⟨within, outside⟩ := safe.within_run functions ⟨Nat.le_refl _, by intro frame impossible; cases impossible⟩ bodyRun
    have callerLive : returned.region active = some callerSlots :=
      (outside active lower).trans ((Store.allocate_old lower _).trans live)
    have different : returnedActive ≠ active := by have h := within.1; dsimp at h; omega
    let frame : Frame n := ⟨active, next, cleanup, destination⟩
    obtain ⟨result, installed, typed, _⟩ := put.sound (state := ⟨callerSlots, returned.temp⟩) ⟨callerTyped.1, returnedTyped.2⟩
    have empty : result.temp = none := by cases put; exact Option.map_eq_none_iff.mp typed.2
    cases result with
    | mk slots temp =>
      cases empty
      have releaseTyped : (State.mk returnedSlots none).Typed signature function.cleanupContext := ⟨returnedTyped.1, rfl⟩
      have kept : (returned.replace active slots none).region returnedActive = some returnedSlots :=
        (Store.replace_other _ _ _ _ _ different).trans returnedLive
      have release := Function.cleanup_returns (program := program) (functions identity function selected).2.1
        (returned.replace active slots none) returnedActive kept releaseTyped frame stack
      refine ⟨slots, .step (.enter selected resident)
        ((Run.retain bodyRun (frame :: stack)).trans (.step (.handoff callerLive installed) release)), typed, ?_⟩
      exact handoff_frame frame installed

theorem Function.call_diverges {n : Nat} {program : Program n} {function : Function n}
    {identity : Nat} (selected : program identity = some function) (caller : Store (n + 1) Atom) (active : Nat)
    {argument : Value} (resident : caller.temp = some argument)
    (infinite : Diverges (Transition program)
      ⟨.body function.body function.cleanup, caller.allocate (argumentSlots argument), caller.regions.length, []⟩)
    (destination : Place (n + 1)) (next : Body n) (cleanup : Code (n + 1) (Op (n + 1))) (stack : List (Frame n)) :
    Diverges (Transition program) ⟨.body (.act (.call identity destination) next) cleanup, caller, active, stack⟩ := by
  have entry : Run (Transition program) ⟨.body (.act (.call identity destination) next) cleanup, caller, active, stack⟩
      ((Configuration.mk (.body function.body function.cleanup) (caller.allocate (argumentSlots argument)) caller.regions.length []).retain
        (⟨active, next, cleanup, destination⟩ :: stack)) := .step (.enter selected resident) (.refl _)
  exact (entry.diverges_iff Transition.deterministic).mpr (Diverges.retain infinite _)

theorem Function.return_initialized {n : Nat} {program : Program n} {signature : Signature} {function : Function n}
    (functions : program.Checked) {identity : Nat} (selected : program identity = some function)
    {argument : Value} (typed : argument.kind signature = function.input) {after : Configuration n}
    (run : Run (Transition program) (function.start argument) after) (terminal : after.Terminal) :
    ∃ value, after.store.temp = some value ∧ Value.kind signature value = function.output ∧ value.ready := by
  obtain ⟨_, _, returned⟩ := ((Function.start_safe functions selected typed).execution functions run).terminal_typed terminal
  obtain ⟨value, stored, classified⟩ := Option.map_eq_some_iff.mp returned.2
  have ready : (value.kind signature).ready := classified.symm ▸ (functions identity function selected).2.2.2.1
  exact ⟨value, stored, classified, by simpa [Value.kind] using ready⟩

end OwnershipMir.Calls
