import OwnershipMir.CleanupTrace

namespace OwnershipMir.Calls

/-- Calls are control operations, not atomic state transformers. Ordinary MIR
instructions and structured control retain their existing meanings. -/
inductive Instruction (n : Nat) where
  | operation (op : Op (n + 1))
  | call (function : Nat) (destination : Place (n + 1))

def Instruction.exec {n : Nat} : Instruction n → State (n + 1) → Option (State (n + 1))
  | .operation op, state => op.exec state
  | .call _ _, _ => none

abbrev Body (n : Nat) := Code (n + 1) (Instruction n)

def argumentSlots {α : Type} {n : Nat} (value : α) : Fin (n + 1) → Option α :=
  Fin.cases (some value) (fun _ => none)

def emptyState (n : Nat) : State (n + 1) := ⟨fun _ => none, none⟩
def emptyContext (n : Nat) : Context (n + 1) := ⟨fun _ => none, none⟩

/-- Every slot of a fresh activation belongs to that activation. The argument
pack is slot zero; remaining slots are in resolved lexical acquisition order.
No supplied subset can hide callee-owned roots from retirement. -/
def activationScope (n : Nat) : Scope (n + 1) :=
  ⟨List.finRange (n + 1), List.nodup_finRange _⟩

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
  ⟨argumentSlots function.input, none⟩
def Function.exit {n : Nat} (function : Function n) : Context (n + 1) :=
  ⟨function.residual, some function.output⟩
def Function.cleanupContext {n : Nat} (function : Function n) : Context (n + 1) :=
  ⟨function.residual, none⟩
def Function.cleanup {n : Nat} (function : Function n) : Code (n + 1) (Op (n + 1)) :=
  lower (sequence ((activationScope n).commands function.cleanupContext))

/-- A call uses a prepared argument tuple exactly once. The result contract is
checked at the caller's actual destination, not assumed to be installable. -/
inductive Instruction.Checked {n : Nat} (program : Program n) (module : Module) :
    Context (n + 1) → Instruction n → Context (n + 1) → Prop where
  | operation {before after op} (checked : Op.Checked (program.authority module) before op after) :
      Checked program module before (.operation op) after
  | call {before after identity destination function}
      (resolved : program identity = some function) (argument : before.temp = some function.input)
      (result : Op.Checked (program.authority module) ⟨before.slots, some function.output⟩ (.put destination) after) :
      Checked program module before (.call identity destination) after

/-- Recursive bodies are checked against declarations, not their executions.
There is no assumed termination, successful return, or future cleanup run. -/
def Program.Checked {n : Nat} (program : Program n) : Prop :=
  ∀ identity function, program identity = some function →
    Code.Checked (Instruction.Checked program function.module) function.entry function.body function.exit ∧
    (activationScope n).Admitted (program.authority function.module) function.cleanupContext ∧
    function.input.ready ∧ function.output.ready ∧
    Layout.Declared program.declarations (function.input.layout id) ∧
    Layout.Declared program.declarations (function.output.layout id)

/-- Suspended callers have no transfer register: its argument has moved into
the fresh activation. Protected return values are installed in these slots. -/
structure Frame (n : Nat) where
  slots : Fin (n + 1) → Option Value
  next : Body n
  cleanup : Code (n + 1) (Op (n + 1))
  destination : Place (n + 1)

def Frame.state {n : Nat} (frame : Frame n) : State (n + 1) := ⟨frame.slots, none⟩

inductive Control (n : Nat) where
  | body (code : Body n) (cleanup : Code (n + 1) (Op (n + 1)))
  | cleaning (code : Code (n + 1) (Op (n + 1)))

structure Configuration (n : Nat) where
  control : Control n
  state : State (n + 1)
  stack : List (Frame n)

/-- Fresh region creation is structural; allocation and physical addresses are
outside this semantic slice. Each stack occurrence is a separate storage region. -/
inductive Transition {n : Nat} (program : Program n) : Configuration n → Configuration n → Prop where
  | operation {code cleanup state next after stack}
      (step : OwnershipMir.Step Instruction.exec ⟨code, state⟩ ⟨next, after⟩) :
      Transition program ⟨.body code cleanup, state, stack⟩ ⟨.body next cleanup, after, stack⟩
  | enter {identity destination next cleanup state stack function argument}
      (resolved : program identity = some function) (resident : state.temp = some argument) :
      Transition program ⟨.body (.act (.call identity destination) next) cleanup, state, stack⟩
        ⟨.body function.body function.cleanup, ⟨argumentSlots argument, none⟩,
          ⟨state.slots, next, cleanup, destination⟩ :: stack⟩
  | handoff {cleanup state frame stack slots}
      (installed : (Op.put frame.destination).exec ⟨frame.slots, state.temp⟩ = some ⟨slots, none⟩) :
      Transition program ⟨.body .halt cleanup, state, frame :: stack⟩
        ⟨.cleaning cleanup, ⟨state.slots, none⟩, {frame with slots := slots} :: stack⟩
  | clean {code state next after stack}
      (step : OwnershipMir.Step Op.exec ⟨code, state⟩ ⟨next, after⟩) :
      Transition program ⟨.cleaning code, state, stack⟩ ⟨.cleaning next, after, stack⟩
  | retire {frame stack} :
      Transition program ⟨.cleaning .halt, emptyState n, frame :: stack⟩
        ⟨.body frame.next frame.cleanup, frame.state, stack⟩


def Configuration.Terminal {n : Nat} (config : Configuration n) : Prop :=
  ∃ cleanup, config.control = .body .halt cleanup ∧ config.stack = []

/-- The suspended continuation records the callee's result and complete cleanup
obligations. Its runtime frame contains only actual storage and control. -/
inductive StackTyped {n : Nat} (program : Program n) (signature : Signature) :
    List (Frame n) → Context (n + 1) → Code (n + 1) (Op (n + 1)) → Context (n + 1) → Prop where
  | nil {final cleanup} : StackTyped program signature [] final cleanup final
  | cons {frame stack output cleanup final slots result after callerExit callerModule calleeModule}
      (resident : ∀ i, (frame.slots i).map (Value.kind signature) = slots i)
      (returned : output.temp = some result)
      (put : Op.Checked (program.authority callerModule) ⟨slots, some result⟩ (.put frame.destination) after)
      (next : Code.Checked (Instruction.Checked program callerModule) after frame.next callerExit)
      (outer : StackTyped program signature stack callerExit frame.cleanup final)
      (release : Code.Checked (Op.Checked (program.authority calleeModule)) ⟨output.slots, none⟩ cleanup (emptyContext n)) :
      StackTyped program signature (frame :: stack) output cleanup final

inductive ResumeTyped {n : Nat} (program : Program n) (signature : Signature) :
    List (Frame n) → Context (n + 1) → Prop where
  | cons {frame stack before output final module}
      (resident : frame.state.Typed signature before)
      (next : Code.Checked (Instruction.Checked program module) before frame.next output)
      (outer : StackTyped program signature stack output frame.cleanup final) :
      ResumeTyped program signature (frame :: stack) final

inductive Safe {n : Nat} (program : Program n) (signature : Signature) (final : Context (n + 1)) :
    Configuration n → Prop where
  | body {code cleanup state stack before output module} (typed : state.Typed signature before)
      (checked : Code.Checked (Instruction.Checked program module) before code output)
      (retained : StackTyped program signature stack output cleanup final) :
      Safe program signature final ⟨.body code cleanup, state, stack⟩
  | cleaning {code state stack before module} (typed : state.Typed signature before)
      (checked : Code.Checked (Op.Checked (program.authority module)) before code (emptyContext n))
      (retained : ResumeTyped program signature stack final) :
      Safe program signature final ⟨.cleaning code, state, stack⟩

end OwnershipMir.Calls
