import OwnershipMir.CleanupTrace
import OwnershipMir.Store

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

/-- Frames retain control and a region identity, never copies of resident storage. -/
structure Frame (n : Nat) where
  region : Nat
  next : Body n
  cleanup : Code (n + 1) (Op (n + 1))
  destination : Place (n + 1)

inductive Control (n : Nat) where
  | body (code : Body n) (cleanup : Code (n + 1) (Op (n + 1)))
  | cleaning (code : Code (n + 1) (Op (n + 1)))

structure Configuration (n : Nat) where
  control : Control n
  store : Store (n + 1) Atom
  active : Nat
  stack : List (Frame n)

/-- All local execution and cross-frame result installation update the same
store. Empty retirement invalidates its region identity rather than reusing it. -/
inductive Transition {n : Nat} (program : Program n) : Configuration n → Configuration n → Prop where
  | operation {code cleanup store active slots next after stack}
      (live : store.region active = some slots)
      (step : OwnershipMir.Step Instruction.exec ⟨code, ⟨slots, store.temp⟩⟩ ⟨next, after⟩) :
      Transition program ⟨.body code cleanup, store, active, stack⟩
        ⟨.body next cleanup, store.replace active after.slots after.temp, active, stack⟩
  | enter {identity destination next cleanup store active stack function argument}
      (resolved : program identity = some function) (resident : store.temp = some argument) :
      Transition program ⟨.body (.act (.call identity destination) next) cleanup, store, active, stack⟩
        ⟨.body function.body function.cleanup, store.allocate (argumentSlots argument), store.regions.length,
          ⟨active, next, cleanup, destination⟩ :: stack⟩
  | handoff {cleanup store active frame stack caller slots}
      (live : store.region frame.region = some caller)
      (installed : (Op.put frame.destination).exec ⟨caller, store.temp⟩ = some ⟨slots, none⟩) :
      Transition program ⟨.body .halt cleanup, store, active, frame :: stack⟩
        ⟨.cleaning cleanup, store.replace frame.region slots none, active, frame :: stack⟩
  | clean {code store active slots next after stack}
      (live : store.region active = some slots)
      (step : OwnershipMir.Step Op.exec ⟨code, ⟨slots, store.temp⟩⟩ ⟨next, after⟩) :
      Transition program ⟨.cleaning code, store, active, stack⟩
        ⟨.cleaning next, store.replace active after.slots after.temp, active, stack⟩
  | retire {store active frame stack}
      (empty : store.region active = some (fun _ => none)) (register : store.temp = none) :
      Transition program ⟨.cleaning .halt, store, active, frame :: stack⟩
        ⟨.body frame.next frame.cleanup, store.retire active, frame.region, stack⟩

def Configuration.Terminal {n : Nat} (config : Configuration n) : Prop :=
  ∃ cleanup, config.control = .body .halt cleanup ∧ config.stack = []

/-- Retained regions are older than the active region. Typing refers to the
actual store cells, not to saved snapshots of a caller's values. -/
inductive StackTyped {n : Nat} (program : Program n) (signature : Signature)
    (store : Store (n + 1) Atom) : Nat → List (Frame n) → Context (n + 1) →
      Code (n + 1) (Op (n + 1)) → Context (n + 1) → Prop where
  | nil {ceiling final cleanup} : StackTyped program signature store ceiling [] final cleanup final
  | cons {ceiling frame stack output cleanup final slots actual result after callerExit callerModule calleeModule}
      (older : frame.region < ceiling) (live : store.region frame.region = some actual)
      (resident : ∀ i, (actual i).map (Value.kind signature) = slots i)
      (returned : output.temp = some result)
      (put : Op.Checked (program.authority callerModule) ⟨slots, some result⟩ (.put frame.destination) after)
      (next : Code.Checked (Instruction.Checked program callerModule) after frame.next callerExit)
      (outer : StackTyped program signature store frame.region stack callerExit frame.cleanup final)
      (release : Code.Checked (Op.Checked (program.authority calleeModule)) ⟨output.slots, none⟩ cleanup (emptyContext n)) :
      StackTyped program signature store ceiling (frame :: stack) output cleanup final

inductive ResumeTyped {n : Nat} (program : Program n) (signature : Signature)
    (store : Store (n + 1) Atom) (ceiling : Nat) : List (Frame n) → Context (n + 1) → Prop where
  | cons {frame stack before output final module actual}
      (older : frame.region < ceiling) (live : store.region frame.region = some actual)
      (resident : (State.mk actual none).Typed signature before)
      (next : Code.Checked (Instruction.Checked program module) before frame.next output)
      (outer : StackTyped program signature store frame.region stack output frame.cleanup final) :
      ResumeTyped program signature store ceiling (frame :: stack) final

inductive Safe {n : Nat} (program : Program n) (signature : Signature) (final : Context (n + 1)) :
    Configuration n → Prop where
  | body {code cleanup store active slots stack before output module}
      (live : store.region active = some slots) (typed : (State.mk slots store.temp).Typed signature before)
      (checked : Code.Checked (Instruction.Checked program module) before code output)
      (retained : StackTyped program signature store active stack output cleanup final) :
      Safe program signature final ⟨.body code cleanup, store, active, stack⟩
  | cleaning {code store active slots stack before module}
      (live : store.region active = some slots) (typed : (State.mk slots store.temp).Typed signature before)
      (checked : Code.Checked (Op.Checked (program.authority module)) before code (emptyContext n))
      (retained : ResumeTyped program signature store active stack final) :
      Safe program signature final ⟨.cleaning code, store, active, stack⟩

end OwnershipMir.Calls
