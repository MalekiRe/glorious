import OwnershipMir.SourceCallLowering

namespace OwnershipMir

theorem Op.OwnerPermitted.transport {n : Nat} {before after : Store n Atom} {region : Nat} {op : Op n}
    (preserved : ∀ mode address, before.Permitted none mode address → after.Permitted none mode address)
    (permission : op.OwnerPermitted before region) : op.OwnerPermitted after region := by
  cases op with
  | take place mode => exact preserved _ _ permission
  | put place => exact preserved _ _ permission
  | copy place => exact preserved _ _ permission
  | drop => trivial

/-- All permissions are stated in the entry store. Each real effect transports
those for pending instructions; pending post-state permission is not assumed.
This rule is for ordinary blocks, which do not create fresh loans. -/
theorem Block.borrow_progress {n : Nat} {authority : Authority} {signature : Signature}
    {ops : List (Op n)} {before after : Context n} {store : Store n Atom} {region : Nat} {slots : Region n Atom}
    (checked : Code.Checked (Op.Checked authority) before (sequence ops) after)
    (typed : (State.mk slots store.temp).Typed signature before) (live : store.region region = some slots)
    (valid : store.BorrowInvariant signature) (permissions : ∀ op ∈ ops, op.OwnerPermitted store region) :
    ∃ result, Block.exec Op.exec ops ⟨slots, store.temp⟩ = some result ∧ result.Typed signature after ∧
      (store.replace region result.slots result.temp).BorrowInvariant signature ∧
      ∀ mode address, store.Permitted none mode address →
        (store.replace region result.slots result.temp).Permitted none mode address := by
  induction ops generalizing before store slots with
  | nil =>
    cases checked
    refine ⟨⟨slots, store.temp⟩, rfl, typed, ?_, ?_⟩
    · simpa only [Store.replace_self live] using valid
    · intro mode address allowed; simpa only [Store.replace_self live] using allowed
  | cons op rest ih =>
    cases checked with
    | act head tail =>
      obtain ⟨middle, executed, realized, preserved, framed⟩ :=
        head.borrow_progress typed live valid (permissions op (List.mem_cons_self))
      have nextLive := Store.replace_same (Store.region_bound live) middle.slots middle.temp
      obtain ⟨result, completed, resultTyped, resultValid, resultPermissions⟩ :=
        ih tail realized nextLive preserved (fun pending member =>
          (permissions pending (List.mem_cons_of_mem op member)).transport framed)
      change Block.exec Op.exec rest middle = some result at completed
      refine ⟨result, ?_, resultTyped, ?_, ?_⟩
      · simpa only [Block.exec, executed, Option.bind_some] using completed
      · simpa only [Store.replace_replace] using resultValid
      · intro mode address allowed
        simpa only [Store.replace_replace] using resultPermissions mode address (framed mode address allowed)

def Command.OwnerPermitted {n : Nat} (store : Store n Atom) (region : Nat) : Command n → Prop
  | .move _ source target =>
      store.Permitted none .unique ⟨region, source.root, source.path⟩ ∧
      store.Permitted none .unique ⟨region, target.root, target.path⟩
  | .copy source target =>
      store.Permitted none .shared ⟨region, source.root, source.path⟩ ∧
      store.Permitted none .unique ⟨region, target.root, target.path⟩
  | .dispose source => store.Permitted none .unique ⟨region, source.root, source.path⟩

theorem Command.OwnerPermitted.block {n : Nat} {store : Store n Atom} {region : Nat} {command : Command n}
    (permission : command.OwnerPermitted store region) : ∀ op ∈ command.block, op.OwnerPermitted store region := by
  cases command <;> simpa [Command.block, Op.OwnerPermitted, Command.OwnerPermitted] using permission

/-- Source command permission is sufficient for ordered physical progress,
including same-aggregate transfers. The source destination is not resolved or
assumed ready before the real source-clear transition. -/
theorem Command.Checked.borrow_progress {n : Nat} {authority : Authority} {signature : Signature}
    {command : Command n} {before after : Context n} {store : Store n Atom} {region : Nat} {slots : Region n Atom}
    (checked : Command.Checked authority before command after)
    (typed : (State.mk slots store.temp).Typed signature before) (live : store.region region = some slots)
    (valid : store.BorrowInvariant signature) (permission : command.OwnerPermitted store region) :
    ∃ result, command.exec ⟨slots, store.temp⟩ = some result ∧ result.Typed signature after ∧
      (store.replace region result.slots result.temp).BorrowInvariant signature ∧
      ∀ mode address, store.Permitted none mode address →
        (store.replace region result.slots result.temp).Permitted none mode address := by
  have compiled := checked.lower (.halt)
  obtain ⟨result, executed, realized, preserved, permissions⟩ :=
    Block.borrow_progress compiled typed live valid permission.block
  exact ⟨result, (command.exec_eq _).trans executed, realized, preserved, permissions⟩

/-- Every actual internal prefix preserves borrowing, including the transfer
register between extraction and installation. This is not only an endpoint
simulation theorem. -/
theorem Block.borrow_prefix {n : Nat} {authority : Authority} {signature : Signature}
    {ops : List (Op n)} {before after : Context n} {store : Store n Atom} {region : Nat} {slots : Region n Atom}
    (checked : Code.Checked (Op.Checked authority) before (sequence ops) after)
    (typed : (State.mk slots store.temp).Typed signature before) (live : store.region region = some slots)
    (valid : store.BorrowInvariant signature) (permissions : ∀ op ∈ ops, op.OwnerPermitted store region)
    {result : Configuration n (Op n)}
    (run : Run (Step Op.exec) ⟨sequence ops, ⟨slots, store.temp⟩⟩ result) :
    (store.replace region result.state.slots result.state.temp).BorrowInvariant signature := by
  induction ops generalizing before store slots with
  | nil =>
    cases run with
    | refl => simpa only [Store.replace_self live] using valid
    | step head tail => cases head
  | cons op rest ih =>
    cases run with
    | refl => simpa only [Store.replace_self live] using valid
    | step head runTail =>
      cases head with
      | act executed =>
        cases checked with
        | act admitted checkedTail =>
          obtain ⟨effect, realized, legal⟩ := admitted.effect typed executed
          obtain ⟨preserved, framed⟩ := effect.borrow_preservation legal.conservationAllowed
            (permissions op List.mem_cons_self) live valid
          have remaining := ih checkedTail realized (Store.replace_same (Store.region_bound live) _ _) preserved
            (fun pending member => (permissions pending (List.mem_cons_of_mem op member)).transport framed) runTail
          simpa only [Store.replace_replace] using remaining

theorem Command.Checked.borrow_prefix {n : Nat} {authority : Authority} {signature : Signature}
    {command : Command n} {before after : Context n} {store : Store n Atom} {region : Nat} {slots : Region n Atom}
    (checked : Command.Checked authority before command after)
    (typed : (State.mk slots store.temp).Typed signature before) (live : store.region region = some slots)
    (valid : store.BorrowInvariant signature) (permission : command.OwnerPermitted store region)
    {result : Configuration n (Op n)}
    (run : Run (Step Op.exec) ⟨sequence command.block, ⟨slots, store.temp⟩⟩ result) :
    (store.replace region result.state.slots result.state.temp).BorrowInvariant signature :=
  Block.borrow_prefix (checked.lower .halt) typed live valid permission.block run



end OwnershipMir


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


/-- Source atomic command progress and its positive MIR execution share the
same physical endpoint. Permission evidence concerns the source entry store;
it is transported through the actual internal block by borrow_progress. -/
theorem command_borrow_progress {n : Nat} {program : Program n} {signature : Signature}
    {store : Store (n + 1) Atom} {active : Nat} {slots : Region (n + 1) Atom} {stack : List (Frame n)}
    {command : Command (n + 1)} {next : Body n} {cleanup : Code (n + 1) (Command (n + 1))}
    {before after : Context (n + 1)}
    (checked : Command.Checked authority before command after)
    (typed : (State.mk slots store.temp).Typed signature before) (live : store.region active = some slots)
    (valid : store.BorrowInvariant signature) (permission : command.OwnerPermitted store active) :
    ∃ result, Transition program ⟨.body (.act (.command command) next) cleanup, store, active, stack⟩ result ∧
      result.store.BorrowInvariant signature ∧
      ∃ middle, Calls.Transition program.lower
        (Configuration.lower ⟨.body (.act (.command command) next) cleanup, store, active, stack⟩) middle ∧
        Run (Calls.Transition program.lower) middle result.lower := by
  obtain ⟨result, executed, _, preserved, _⟩ := checked.borrow_progress typed live valid permission
  have step : Transition program ⟨.body (.act (.command command) next) cleanup, store, active, stack⟩
      ⟨.body next cleanup, store.replace active result.slots result.temp, active, stack⟩ :=
    .operation live (.act executed)
  exact ⟨_, step, preserved, step.lower⟩

theorem cleanup_command_borrow_progress {n : Nat} {program : Program n} {signature : Signature}
    {store : Store (n + 1) Atom} {active : Nat} {slots : Region (n + 1) Atom} {stack : List (Frame n)}
    {command : Command (n + 1)} {next : Code (n + 1) (Command (n + 1))} {before after : Context (n + 1)}
    (checked : Command.Checked authority before command after)
    (typed : (State.mk slots store.temp).Typed signature before) (live : store.region active = some slots)
    (valid : store.BorrowInvariant signature) (permission : command.OwnerPermitted store active) :
    ∃ result, Transition program ⟨.cleaning (.act command next), store, active, stack⟩ result ∧
      result.store.BorrowInvariant signature ∧
      ∃ middle, Calls.Transition program.lower
        (Configuration.lower ⟨.cleaning (.act command next), store, active, stack⟩) middle ∧
        Run (Calls.Transition program.lower) middle result.lower := by
  obtain ⟨result, executed, _, preserved, _⟩ := checked.borrow_progress typed live valid permission
  have step : Transition program ⟨.cleaning (.act command next), store, active, stack⟩
      ⟨.cleaning next, store.replace active result.slots result.temp, active, stack⟩ :=
    .clean live (.act executed)
  exact ⟨_, step, preserved, step.lower⟩


/-- Arguments and results share the actual acquisition contract. Reference
readiness and mode permissions are before-state obligations on the selected
resident; the returned obligations are derived through the physical move. -/
theorem AcquireChecked.borrow_progress {n : Nat} {signature : Signature}
    {store : Store n Atom} {region : Nat} {slots : Region n Atom} {before after : Context n} {place : Place n}
    (checked : AcquireChecked authority before place after)
    (typed : (State.mk slots store.temp).Typed signature before) (live : store.region region = some slots)
    (valid : store.BorrowInvariant signature) (permission : (Op.take place .whole).OwnerPermitted store region)
    (references : ∀ lens value, place.find slots = some lens → lens.selected = some value → Value.ReferencesReady store value) :
    ∃ result value, acquire place ⟨slots, store.temp⟩ = some result ∧ result.temp = some value ∧
      result.Typed signature after ∧ value.ready ∧
      (store.replace region result.slots result.temp).BorrowInvariant signature ∧
      Value.ReferencesReady (store.replace region result.slots result.temp) value := by
  obtain ⟨result, effect, realized, legal⟩ := checked.transfer.realize typed
  have executed := effect.exec
  have preserved := (effect.borrow_preservation legal.conservationAllowed permission live valid).1
  cases effect with
  | @take _ _ _ lens value moved found selected extracted empty =>
    cases Option.some.inj extracted
    have operation : (Op.take place .whole).Effect ⟨slots, store.temp⟩
        ⟨place.write slots lens none, some value⟩ := .take found selected rfl empty
    refine ⟨_, value, (acquire_eq _ _).trans executed, rfl, realized, ?_, preserved, ?_⟩
    · have ready := checked.initialized (Value.kind signature value) realized.2.symm
      simpa only [Value.kind, Tree.ready_map] using ready
    · intro identity mode target member
      have admitted := references lens value found selected identity mode target member
      obtain ⟨whole, stored, inside⟩ := focus_contains found selected member
      have handle : store.HasHandle identity :=
        ⟨mode, target, Or.inr ⟨region, slots, place.root, whole, live, stored, inside⟩⟩
      refine ⟨operation.preserves_loanReady permission live admitted.1 (Store.hasHandle_active handle), ?_⟩
      intro loan origin
      apply operation.preserves_permission live (admitted.2 loan origin)
      intro id same
      cases Option.some.inj same
      exact ⟨mode, target, Or.inl ⟨value, rfl, member⟩⟩

/-- Actual result acquisition preserves the initialization and permissions of
returned references. Selection of permitted input/retained-owner origins and
declared outlives constraints remains a separate source-contract obligation. -/
theorem result_borrow_progress {n : Nat} {program : Program n} {signature : Signature}
    {store : Store (n + 1) Atom} {active : Nat} {slots : Region (n + 1) Atom} {stack : List (Frame n)}
    {place : Place (n + 1)} {next : Body n} {cleanup : Code (n + 1) (Command (n + 1))}
    {before after : Context (n + 1)}
    (checked : AcquireChecked authority before place after)
    (typed : (State.mk slots store.temp).Typed signature before) (live : store.region active = some slots)
    (valid : store.BorrowInvariant signature) (permission : (Op.take place .whole).OwnerPermitted store active)
    (references : ∀ lens value, place.find slots = some lens → lens.selected = some value → Value.ReferencesReady store value) :
    ∃ result value, Transition program ⟨.body (.act (.result place) next) cleanup, store, active, stack⟩ result ∧
      result.store.temp = some value ∧ value.ready ∧ Value.ReferencesReady result.store value ∧
      result.store.BorrowInvariant signature ∧
      ∃ middle, Calls.Transition program.lower
        (Configuration.lower ⟨.body (.act (.result place) next) cleanup, store, active, stack⟩) middle ∧
        Run (Calls.Transition program.lower) middle result.lower := by
  obtain ⟨result, value, executed, register, _, ready, preserved, admitted⟩ :=
    checked.borrow_progress typed live valid permission references
  have step : Transition program ⟨.body (.act (.result place) next) cleanup, store, active, stack⟩
      ⟨.body next cleanup, store.replace active result.slots result.temp, active, stack⟩ :=
    .operation live (.act executed)
  exact ⟨_, value, step, register, ready, admitted, preserved, step.lower⟩


/-- Source call entry consumes the same acquisition admission as source
results, then physically installs the argument in the fresh callee region.
Neither referent initialization nor callee reference permissions are assumed
after that transfer. -/
theorem argument_borrow_progress {n : Nat} {program : Program n} {signature : Signature}
    {store : Store (n + 1) Atom} {active identity : Nat} {slots : Region (n + 1) Atom} {stack : List (Frame n)}
    {argument destination : Place (n + 1)} {next : Body n} {cleanup : Code (n + 1) (Command (n + 1))}
    {function : Function n} {before prepared : Context (n + 1)}
    (resolved : program identity = some function)
    (checked : AcquireChecked authority before argument prepared) (argumentType : prepared.temp = some function.input)
    (typed : (State.mk slots store.temp).Typed signature before) (live : store.region active = some slots)
    (valid : store.BorrowInvariant signature) (permission : (Op.take argument .whole).OwnerPermitted store active)
    (references : ∀ lens value, argument.find slots = some lens → lens.selected = some value → Value.ReferencesReady store value) :
    ∃ result value callee, Transition program ⟨.body (.act (.call identity argument destination) next) cleanup, store, active, stack⟩ result ∧
      result.store.region result.active = some callee ∧ callee 0 = some value ∧
      Value.kind signature value = function.input ∧ value.ready ∧ Value.ReferencesReady result.store value ∧
      result.store.BorrowInvariant signature ∧
      ∃ middle, Calls.Transition program.lower
        (Configuration.lower ⟨.body (.act (.call identity argument destination) next) cleanup, store, active, stack⟩) middle ∧
        Run (Calls.Transition program.lower) middle result.lower := by
  obtain ⟨preparedState, value, acquired, register, preparedTyped, ready, preserved, admitted⟩ :=
    checked.borrow_progress typed live valid permission references
  have classified : Value.kind signature value = function.input := by
    simpa only [register, Option.map_some, argumentType, Option.some.injEq] using preparedTyped.2
  let staged := store.replace active preparedState.slots preparedState.temp
  have stagedRegister : staged.temp = some value := register
  have entered := Calls.enter_borrow_invariant preserved stagedRegister
  have fresh : (staged.allocate (Calls.argumentSlots value)).region store.regions.length =
      some (Calls.argumentSlots value) := by
    have located := Store.allocate_fresh staged (Calls.argumentSlots value)
    simpa only [staged, Store.replace, List.length_set] using located
  have step := Transition.enter (program := program) (destination := destination) (next := next)
    (cleanup := cleanup) (stack := stack) live resolved acquired register
  refine ⟨_, value, Calls.argumentSlots value, step, fresh, rfl, classified, ready, ?_, entered.1, step.lower⟩
  intro id mode target member
  have source := admitted id mode target member
  refine ⟨source.1.allocate _, ?_⟩
  intro loan origin
  exact (entered.2 (some id) mode loan.referent).mpr (source.2 loan origin)


end OwnershipMir.SourceCalls
