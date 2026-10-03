import OwnershipMir.CallBoundary

namespace OwnershipMir.SourceCalls
variable {module : Module}

/-- The argument pack and result are explicit owned places. Calls force a move;
copying a duplicable argument uses the existing source copy command beforehand.
Function identities, field paths, and acquisition order are already resolved. -/
inductive Instruction (n : Nat) where
  | command (command : Command (n + 1))
  | call (identity : Nat) (argument destination : Place (n + 1))
  | result (value : Place (n + 1))

def acquire {n : Nat} (place : Place n) (state : State n) : Option (State n) := do
  match state.temp with
  | some _ => none
  | none =>
    let lens ← place.find state.slots
    let value ← lens.selected
    some ⟨place.write state.slots lens none, some value⟩

theorem acquire_eq {n : Nat} (place : Place n) (state : State n) :
    acquire place state = (Op.take place .whole).exec state := by
  cases empty : state.temp <;>
    simp [acquire, Op.exec, Extract.apply, empty]

def Instruction.exec {n : Nat} : Instruction n → State (n + 1) → Option (State (n + 1))
  | .command cmd, state => cmd.exec state
  | .call _ _ _, _ => none
  | .result value, state => acquire value state

abbrev Body (n : Nat) := Code (n + 1) (Instruction n)

structure Function (n : Nat) where
  input : Shape
  output : Shape
  body : Body n
  residual : Fin (n + 1) → Option Shape
  module : Module

structure Program (n : Nat) where
  declarations : Declarations
  functions : Nat → Option (Function n)

instance {n : Nat} : CoeFun (Program n) (fun _ => Nat → Option (Function n)) := ⟨Program.functions⟩

def Program.authority {n : Nat} (program : Program n) (module : Module) : Authority :=
  ⟨program.declarations, module⟩

def Function.entry {n : Nat} (function : Function n) : Context (n + 1) :=
  ⟨Calls.argumentSlots function.input, none⟩
def Function.exit {n : Nat} (function : Function n) : Context (n + 1) :=
  ⟨function.residual, some function.output⟩
def Function.cleanupContext {n : Nat} (function : Function n) : Context (n + 1) :=
  ⟨function.residual, none⟩
def Function.cleanup {n : Nat} (function : Function n) : Code (n + 1) (Command (n + 1)) :=
  sequence ((Calls.activationScope n).commands function.cleanupContext)

/-- Source whole-value transfer additionally requires initialization. Internal
MIR cleanup can move residual structures, but source arguments/results cannot. -/
structure AcquireChecked {n : Nat} (authority : Authority) (before : Context n) (place : Place n) (after : Context n) : Prop where
  transfer : Op.Checked authority before (.take place .whole) after
  access : place.Visible authority before.slots
  initialized : ∀ shape, after.temp = some shape → shape.ready

inductive Instruction.Checked {n : Nat} (program : Program n) (module : Module) :
    Context (n + 1) → Instruction n → Context (n + 1) → Prop where
  | command {before after command} (checked : Command.Checked (program.authority module) before command after) :
      Checked program module before (.command command) after
  | call {before prepared after identity argument destination function}
      (resolved : program identity = some function)
      (input : AcquireChecked (program.authority module) before argument prepared)
      (argumentType : prepared.temp = some function.input)
      (result : Op.Checked (program.authority module) ⟨prepared.slots, some function.output⟩ (.put destination) after)
      (access : destination.Visible (program.authority module) prepared.slots) :
      Checked program module before (.call identity argument destination) after
  | result {before after value} (checked : AcquireChecked (program.authority module) before value after) :
      Checked program module before (.result value) after

def Program.Checked {n : Nat} (program : Program n) : Prop :=
  ∀ identity function, program identity = some function →
    Code.Checked (Instruction.Checked program function.module) function.entry function.body function.exit ∧
    (Calls.activationScope n).Admitted (program.authority function.module) function.cleanupContext ∧
    function.input.ready ∧ function.output.ready ∧
    Layout.Declared program.declarations (function.input.layout id) ∧
    Layout.Declared program.declarations (function.output.layout id)

structure Frame (n : Nat) where
  slots : Fin (n + 1) → Option Value
  next : Body n
  cleanup : Code (n + 1) (Command (n + 1))
  destination : Place (n + 1)

def Frame.state {n : Nat} (frame : Frame n) : State (n + 1) := ⟨frame.slots, none⟩

inductive Control (n : Nat) where
  | body (code : Body n) (cleanup : Code (n + 1) (Command (n + 1)))
  | cleaning (code : Code (n + 1) (Command (n + 1)))

structure Configuration (n : Nat) where
  control : Control n
  state : State (n + 1)
  stack : List (Frame n)

/-- Independent source execution: call entry acquires an argument and suspends
the caller, without executing the callee atomically or assuming it returns. -/
inductive Transition {n : Nat} (program : Program n) : Configuration n → Configuration n → Prop where
  | operation {code cleanup state next after stack}
      (step : OwnershipMir.Step Instruction.exec ⟨code, state⟩ ⟨next, after⟩) :
      Transition program ⟨.body code cleanup, state, stack⟩ ⟨.body next cleanup, after, stack⟩
  | enter {identity argument destination next cleanup state prepared stack function value}
      (resolved : program identity = some function) (acquired : acquire argument state = some prepared)
      (resident : prepared.temp = some value) :
      Transition program ⟨.body (.act (.call identity argument destination) next) cleanup, state, stack⟩
        ⟨.body function.body function.cleanup, ⟨Calls.argumentSlots value, none⟩,
          ⟨prepared.slots, next, cleanup, destination⟩ :: stack⟩
  | handoff {cleanup state frame stack slots}
      (installed : (Op.put frame.destination).exec ⟨frame.slots, state.temp⟩ = some ⟨slots, none⟩) :
      Transition program ⟨.body .halt cleanup, state, frame :: stack⟩
        ⟨.cleaning cleanup, ⟨state.slots, none⟩, {frame with slots := slots} :: stack⟩
  | clean {code state next after stack}
      (step : OwnershipMir.Step Command.exec ⟨code, state⟩ ⟨next, after⟩) :
      Transition program ⟨.cleaning code, state, stack⟩ ⟨.cleaning next, after, stack⟩
  | retire {frame stack} :
      Transition program ⟨.cleaning .halt, Calls.emptyState n, frame :: stack⟩
        ⟨.body frame.next frame.cleanup, frame.state, stack⟩

def Configuration.Terminal {n : Nat} (config : Configuration n) : Prop :=
  ∃ cleanup, config.control = .body .halt cleanup ∧ config.stack = []

def Instruction.block {n : Nat} : Instruction n → List (Calls.Instruction n)
  | .command cmd => cmd.block.map Calls.Instruction.operation
  | .call identity argument destination => [.operation (.take argument .whole), .call identity destination]
  | .result value => [.operation (.take value .whole)]

def lower {n : Nat} : Body n → Calls.Body n
  | .halt => .halt
  | .act instruction next => Block.emit instruction.block (lower next)
  | .branch guard yes no => .branch guard (lower yes) (lower no)
  | .loop guard body next => .loop guard (lower body) (lower next)

def Function.lower {n : Nat} (function : Function n) : Calls.Function n :=
  ⟨function.input, function.output, SourceCalls.lower function.body, function.residual, function.module⟩
def Program.lower {n : Nat} (program : Program n) : Calls.Program n :=
  ⟨program.declarations, fun identity => (program identity).map Function.lower⟩

def Frame.lower {n : Nat} (frame : Frame n) : Calls.Frame n :=
  ⟨frame.slots, SourceCalls.lower frame.next, OwnershipMir.lower frame.cleanup, frame.destination⟩
def Control.lower {n : Nat} : Control n → Calls.Control n
  | .body code cleanup => .body (SourceCalls.lower code) (OwnershipMir.lower cleanup)
  | .cleaning code => .cleaning (OwnershipMir.lower code)
def Configuration.lower {n : Nat} (config : Configuration n) : Calls.Configuration n :=
  ⟨config.control.lower, config.state, config.stack.map Frame.lower⟩

def Function.start {n : Nat} (function : Function n) (argument : Value) : Configuration n :=
  ⟨.body function.body function.cleanup, ⟨Calls.argumentSlots argument, none⟩, []⟩

@[simp] theorem Function.start_lower {n : Nat} (function : Function n) (argument : Value) :
    (function.start argument).lower = function.lower.start argument := rfl

theorem Program.selected {n : Nat} {program : Program n} {identity : Nat} {function : Function n}
    (selected : program identity = some function) : program.lower identity = some function.lower := by
  change (program identity).map Function.lower = some function.lower
  simp [selected]

theorem lower_append {n : Nat} (first last : Body n) :
    lower (first.append last) = (lower first).append (lower last) := by
  induction first with
  | halt => rfl
  | act instruction next ih => simp [lower, Code.append, ih]
  | branch guard yes no yesIH noIH => simp [lower, Code.append, yesIH, noIH]
  | loop guard body next _ nextIH => simp [lower, Code.append, nextIH]

@[simp] theorem lower_halt {n : Nat} (source : Body n) : lower source = .halt ↔ source = .halt := by
  cases source with
  | halt => simp [lower]
  | act instruction next =>
    cases instruction with
    | command command => simp [lower, Instruction.block, command.block_nonempty]
    | call => simp [lower, Instruction.block]
    | result => simp [lower, Instruction.block]
  | branch => simp [lower]
  | loop => simp [lower]

@[simp] theorem Configuration.terminal_lower {n : Nat} (config : Configuration n) :
    config.lower.Terminal ↔ config.Terminal := by
  cases config with
  | mk control state stack =>
    cases control with
    | body code cleanup =>
      simp [Configuration.lower, Control.lower, Configuration.Terminal, Calls.Configuration.Terminal]
    | cleaning code =>
      simp [Configuration.lower, Control.lower, Configuration.Terminal, Calls.Configuration.Terminal]

private theorem operations_checked {n : Nat} {program : Calls.Program n}
    {before after final : Context (n + 1)} {ops : List (Op (n + 1))}
    (checked : Code.Checked (Op.Checked (program.authority module)) before (sequence ops) after) {next : Calls.Body n}
    (tail : Code.Checked (Calls.Instruction.Checked program module) after next final) :
    Code.Checked (Calls.Instruction.Checked program module) before
      (Block.emit (ops.map Calls.Instruction.operation) next) final := by
  induction ops generalizing before with
  | nil => cases checked; exact tail
  | cons op rest ih =>
    cases checked with
    | act head remaining => exact .act (.operation head) (ih remaining)

theorem Instruction.Checked.lower {n : Nat} {program : Program n}
    {before after final : Context (n + 1)} {instruction : Instruction n}
    (checked : Instruction.Checked program module before instruction after) {next : Calls.Body n}
    (tail : Code.Checked (Calls.Instruction.Checked program.lower module) after next final) :
    Code.Checked (Calls.Instruction.Checked program.lower module) before
      (Block.emit instruction.block next) final := by
  cases checked with
  | command checked => exact operations_checked (program := program.lower) (module := module) (checked.lower .halt) tail
  | call resolved input argumentType result access =>
    exact .act (.operation input.transfer) (.act (.call (Program.selected resolved) argumentType result) tail)
  | result checked => exact .act (.operation checked.transfer) tail

theorem lower_checked {n : Nat} {program : Program n} {before after : Context (n + 1)} {source : Body n}
    (checked : Code.Checked (Instruction.Checked program module) before source after) :
    Code.Checked (Calls.Instruction.Checked program.lower module) before (lower source) after := by
  induction checked with
  | halt => exact .halt
  | act head tail ih => exact head.lower ih
  | branch scalar left right leftIH rightIH => exact .branch scalar leftIH rightIH
  | loop scalar body tail bodyIH tailIH => exact .loop scalar bodyIH tailIH

theorem Program.Checked.lower {n : Nat} {program : Program n} (checked : program.Checked) : program.lower.Checked := by
  intro identity function selected
  obtain ⟨source, found, same⟩ := Option.map_eq_some_iff.mp selected
  subst function
  exact ⟨lower_checked (checked identity source found).1, (checked identity source found).2⟩

end OwnershipMir.SourceCalls
