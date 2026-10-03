import OwnershipMir.SourceCallLowering

namespace OwnershipMir.SourceCalls
variable {module : Module} {authority : Authority}

private theorem operations_ready {n : Nat} {program : Calls.Program n} {signature : Signature}
    {before final : Context (n + 1)} (ops : List (Op (n + 1))) {next : Calls.Body n}
    (checked : Code.Checked (Calls.Instruction.Checked program module) before
      (Block.emit (ops.map Calls.Instruction.operation) next) final)
    {state : State (n + 1)} (typed : state.Typed signature before) :
    ∃ result, Block.exec Op.exec ops state = some result := by
  obtain ⟨result, middle, executed, _, _⟩ := Block.checked_prefix
    (exec := Calls.Instruction.exec) (ops.map Calls.Instruction.operation) checked typed (by
      intro instruction member input output head resident realized
      obtain ⟨op, _, rfl⟩ := List.mem_map.mp member
      cases head with
      | operation checked =>
        obtain ⟨next, executed, finalTyped, _⟩ := checked.sound realized
        exact ⟨next, executed, finalTyped⟩)
  exact ⟨result, by rwa [operations_exec] at executed⟩

private theorem command_progress {n : Nat} {signature : Signature} {final : Context n}
    {code : Code n (Command n)} {state : State n}
    (safe : OwnershipMir.Safe signature (Op.Checked authority) final ⟨OwnershipMir.lower code, state⟩) :
    code = .halt ∨ ∃ next, Step Command.exec ⟨code, state⟩ next := by
  obtain ⟨before, typed, checked⟩ := safe
  cases code with
  | halt => exact Or.inl rfl
  | act cmd next =>
    obtain ⟨result, middle, executed, _, _⟩ := Block.checked_prefix
      (exec := Op.exec) cmd.block checked typed (by
        intro op _ input output head resident realized
        obtain ⟨next, executed, finalTyped, _⟩ := head.sound realized
        exact ⟨next, executed, finalTyped⟩)
    exact Or.inr ⟨_, .act (by rwa [Command.exec_eq])⟩
  | branch guard yes no =>
    cases checked with
    | branch scalar left right =>
      obtain ⟨choice, observed⟩ := observe_ready typed scalar
      exact Or.inr ⟨_, .branch observed⟩
  | loop guard body next =>
    cases checked with
    | loop scalar body tail =>
      obtain ⟨choice, observed⟩ := observe_ready typed scalar
      exact Or.inr ⟨_, .loop observed⟩

/-- The existing target invariant is pulled back to source boundaries. Its
preservation comes from actual finite simulation. Progress below is derived
from checked finite prefixes; it is not a field of this invariant. -/
def Safe {n : Nat} (program : Program n) (signature : Signature) (final : Context (n + 1))
    (config : Configuration n) : Prop := Calls.Safe program.lower signature final config.lower

theorem Safe.preservation {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    (functions : program.Checked) {before after : Configuration n} (safe : Safe program signature final before)
    (step : Transition program before after) : Safe program signature final after := by
  obtain ⟨middle, head, tail⟩ := step.lower
  exact safe.execution functions.lower (.step head tail)

theorem Safe.progress {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    {config : Configuration n} (safe : Safe program signature final config) :
    config.Terminal ∨ ∃ next, Transition program config next := by
  cases config with
  | mk control store active stack =>
    cases control with
    | body code cleanup =>
      change Calls.Safe program.lower signature final
        ⟨.body (lower code) (OwnershipMir.lower cleanup), store, active, stack.map Frame.lower⟩ at safe
      cases code with
      | halt =>
        cases stack with
        | nil => exact Or.inl ⟨cleanup, rfl, rfl⟩
        | cons frame stack =>
          rcases safe.progress with ⟨_, _, impossible⟩ | ⟨next, step⟩
          · cases impossible
          · cases step with
            | operation live step => exact False.elim (step.not_halt rfl)
            | handoff live installed => exact Or.inr ⟨_, .handoff live installed⟩
      | act instruction next =>
        cases safe with
        | body live typed checked retained =>
          cases instruction with
          | command cmd =>
            obtain ⟨result, executed⟩ := operations_ready cmd.block checked typed
            exact Or.inr ⟨_, .operation live (.act (by simpa [Instruction.exec, Command.exec_eq] using executed))⟩
          | result value =>
            cases checked with
            | act head tail =>
              cases head with
              | operation move =>
                obtain ⟨result, executed⟩ := move.progress typed
                exact Or.inr ⟨_, .operation live (.act (by simpa [Instruction.exec, acquire_eq] using executed))⟩
          | call identity argument destination =>
            cases checked with
            | act head tail =>
              cases head with
              | operation move =>
                obtain ⟨prepared, executed⟩ := move.progress typed
                have realized := (move.executed typed executed).1
                cases tail with
                | act head tail =>
                  cases head with
                  | call resolved argumentType result =>
                    obtain ⟨function, selected, rfl⟩ := Option.map_eq_some_iff.mp resolved
                    obtain ⟨value, resident, _⟩ := Option.map_eq_some_iff.mp (realized.2.trans argumentType)
                    exact Or.inr ⟨_, .enter live selected (by rwa [acquire_eq]) resident⟩
      | branch guard yes no =>
        cases safe with
        | body live typed checked retained =>
          cases checked with
          | branch scalar left right =>
            obtain ⟨choice, observed⟩ := observe_ready typed scalar
            exact Or.inr ⟨_, .operation live (.branch observed)⟩
      | loop guard body next =>
        cases safe with
        | body live typed checked retained =>
          cases checked with
          | loop scalar body tail =>
            obtain ⟨choice, observed⟩ := observe_ready typed scalar
            exact Or.inr ⟨_, .operation live (.loop observed)⟩
    | cleaning code =>
      change Calls.Safe program.lower signature final
        ⟨.cleaning (OwnershipMir.lower code), store, active, stack.map Frame.lower⟩ at safe
      cases safe with
      | cleaning live typed checked retained =>
        rcases command_progress ⟨_, typed, checked⟩ with halted | ⟨next, step⟩
        · subst code
          cases checked
          have empty := Calls.typed_empty typed
          have slotsEmpty := congrArg State.slots empty
          have tempEmpty := congrArg State.temp empty
          cases stack with
          | nil => cases retained
          | cons frame stack => exact Or.inr ⟨_, .retire (live.trans (congrArg some slotsEmpty)) tempEmpty⟩
        · cases next with
          | mk next after => exact Or.inr ⟨_, .clean live step⟩

theorem Function.start_safe {n : Nat} {program : Program n} {signature : Signature} {function : Function n}
    (functions : program.Checked) {identity : Nat} (selected : program identity = some function)
    {argument : Value} (typed : argument.kind signature = function.input) :
    Safe program signature function.exit (function.start argument) :=
  Calls.Function.start_safe functions.lower (Program.selected selected) typed

/-- Exact terminal endpoint reflection, including returned value, remaining
outer storage, and empty retained stack. Intermediate target states need not
be source configurations. -/
theorem terminal_reflection {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    (functions : program.Checked) {start : Configuration n} (safe : Safe program signature final start)
    {result : Calls.Configuration n} (run : Run (Calls.Transition program.lower) start.lower result)
    (terminal : result.Terminal) :
    ∃ sourceResult, Run (Transition program) start sourceResult ∧ sourceResult.Terminal ∧ sourceResult.lower = result := by
  exact PositiveSimulation.terminal_reflection
    (source := Transition program) (target := Calls.Transition program.lower)
    (P := Safe program signature final)
    (fun safe step => safe.preservation functions step) (fun _ safe => safe.progress)
    Transition.lower Calls.Transition.deterministic
    (fun config => config.terminal_lower.symm) (fun terminal _ step => step.not_terminal terminal)
    safe run terminal

theorem diverges_iff {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    (functions : program.Checked) {start : Configuration n} (safe : Safe program signature final start) :
    Diverges (Transition program) start ↔ Diverges (Calls.Transition program.lower) start.lower := by
  exact PositiveSimulation.diverges_iff
    (source := Transition program) (target := Calls.Transition program.lower)
    (P := Safe program signature final)
    (fun safe step => safe.preservation functions step) (fun _ safe => safe.progress)
    Transition.lower Calls.Transition.deterministic Transition.deterministic
    (fun config => config.terminal_lower.symm) (fun terminal _ step => step.not_terminal terminal)
    safe (fun _ reached => (Calls.Safe.execution functions.lower safe reached).progress)

/-- Source body checking, not checked MIR bodies or prepared runtime packs,
is the public premise for safety of every physical target prefix. -/
theorem compiled_program_safety {n : Nat} {program : Program n} {signature : Signature} {function : Function n}
    (functions : program.Checked) {identity : Nat} (selected : program identity = some function)
    {argument : Value} (typed : argument.kind signature = function.input)
    (unique : (function.start argument).lower.Unique) {after : Calls.Configuration n}
    (run : Run (Calls.Transition program.lower) (function.start argument).lower after) :
    Calls.Safe program.lower signature function.exit after ∧ after.Unique ∧
      Calls.Preserves signature (function.start argument).lower after ∧
      (after.Terminal ∨ ∃ next, Calls.Transition program.lower after next) ∧
      after.linearShells ≤ (function.start argument).lower.linearShells ∧
      after.Declared program.declarations signature ∧
      ∃ amount, Calls.ShellTrace program.lower (function.start argument).lower after amount ∧
        after.shells + amount = (function.start argument).lower.shells :=
  Calls.program_safety functions.lower (Program.selected selected) typed unique run

/-- Source prefixes inherit the same resident ownership facts, because lowering
changes control only. Source progress is supplied by the boundary proof above. -/
theorem program_safety {n : Nat} {program : Program n} {signature : Signature} {function : Function n}
    (functions : program.Checked) {identity : Nat} (selected : program identity = some function)
    {argument : Value} (typed : argument.kind signature = function.input)
    (unique : (function.start argument).lower.Unique) {after : Configuration n}
    (run : Run (Transition program) (function.start argument) after) :
    Safe program signature function.exit after ∧ after.lower.Unique ∧
      Calls.Preserves signature (function.start argument).lower after.lower ∧
      (after.Terminal ∨ ∃ next, Transition program after next) ∧ after.lower.Declared program.declarations signature := by
  obtain ⟨safe, distinct, conserved, _, _, declared, _⟩ := compiled_program_safety functions selected typed unique (Run.lower run)
  exact ⟨safe, distinct, conserved, Safe.progress safe, declared⟩

/-- Every actual terminal target execution corresponds to a source execution
with the exact lowered endpoint, not just the same result type. -/
theorem compiled_return_iff {n : Nat} {program : Program n} {signature : Signature} {function : Function n}
    (functions : program.Checked) {identity : Nat} (selected : program identity = some function)
    {argument : Value} (typed : argument.kind signature = function.input)
    {result : Calls.Configuration n} (terminal : result.Terminal) :
    Run (Calls.Transition program.lower) (function.start argument).lower result ↔
      ∃ sourceResult, Run (Transition program) (function.start argument) sourceResult ∧
        sourceResult.Terminal ∧ sourceResult.lower = result := by
  constructor
  · intro run
    exact terminal_reflection functions (Function.start_safe functions selected typed) run terminal
  · rintro ⟨sourceResult, run, _, rfl⟩
    exact Run.lower run

theorem compiled_diverges_iff {n : Nat} {program : Program n} {signature : Signature} {function : Function n}
    (functions : program.Checked) {identity : Nat} (selected : program identity = some function)
    {argument : Value} (typed : argument.kind signature = function.input) :
    Diverges (Transition program) (function.start argument) ↔
      Diverges (Calls.Transition program.lower) (function.start argument).lower :=
  diverges_iff functions (Function.start_safe functions selected typed)

theorem Function.return_initialized {n : Nat} {program : Program n} {signature : Signature} {function : Function n}
    (functions : program.Checked) {identity : Nat} (selected : program identity = some function)
    {argument : Value} (typed : argument.kind signature = function.input) {after : Configuration n}
    (run : Run (Transition program) (function.start argument) after) (terminal : after.Terminal) :
    ∃ value, after.store.temp = some value ∧ Value.kind signature value = function.output ∧ value.ready :=
  Calls.Function.return_initialized functions.lower (Program.selected selected) typed
    (Run.lower run) (after.terminal_lower.mpr terminal)

/-- Source and MIR retirement share the physical store and its derived lifetime
proof; lowering cannot substitute a copied caller store or a different loan
interpretation at this boundary. -/
theorem retirement_borrow_safe {n : Nat} {program : Program n} {signature : Signature}
    {store : Store (n + 1) Atom} {active : Nat} (frame : Frame n) (stack : List (Frame n))
    (valid : store.BorrowInvariant signature) (empty : store.region active = some (fun _ => none))
    (register : store.temp = none) :
    ∃ after, Transition program ⟨.cleaning .halt, store, active, frame :: stack⟩ after ∧
      Calls.Transition program.lower (Configuration.lower ⟨.cleaning .halt, store, active, frame :: stack⟩) after.lower ∧
      after.store.BorrowInvariant signature ∧ after.active = frame.region ∧ after.stack = stack ∧
      (∀ via mode address, after.store.Permitted via mode address ↔ store.Permitted via mode address) := by
  refine ⟨⟨.body frame.next frame.cleanup, store.retire active, frame.region, stack⟩,
    .retire empty register, ?_, valid.retire_empty empty, rfl, rfl, store.retire_empty_permissions empty⟩
  exact Calls.Transition.retire empty register


end OwnershipMir.SourceCalls
