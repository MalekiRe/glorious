import OwnershipMir.CallCleanup
import OwnershipMir.CallMetadata

namespace OwnershipMir.Calls
variable {module : Module} {authority : Authority}

def bodyShellDebit {n : Nat} (code : Body n) (state : State (n + 1)) : Nat :=
  match code with
  | .act (.operation op) _ => op.shellDebit state
  | _ => 0

def Configuration.shellDebit {n : Nat} (config : Configuration n) : Nat :=
  match config.control with
  | .body code _ => bodyShellDebit code config.state
  | .cleaning code => OwnershipMir.Configuration.shellDebit ⟨code, config.state⟩

def Configuration.shells {n : Nat} (config : Configuration n) : Nat :=
  config.mass (fun _ => 0) (fun shell => if shell.restriction = .exact then 1 else 0)

def Configuration.linearShells {n : Nat} (config : Configuration n) : Nat :=
  config.mass (fun _ => 0) (fun shell => if shell.restriction = .data then 0 else 1)

theorem local_shells {n : Nat} {program : Program n} {signature : Signature}
    {before output : Context (n + 1)} {code next : Body n} {state after : State (n + 1)}
    (typed : state.Typed signature before)
    (checked : Code.Checked (Instruction.Checked program module) before code output)
    (step : OwnershipMir.Step Instruction.exec ⟨code, state⟩ ⟨next, after⟩) :
    after.linearShells ≤ state.linearShells ∧ after.shells + bodyShellDebit code state = state.shells := by
  cases step with
  | act executed =>
    cases checked with
    | act head tail =>
      cases head with
      | operation checked => exact ⟨checked.linear_shells typed executed, checked.shell_balance typed executed⟩
      | call => cases executed
  | branch => exact ⟨Nat.le_refl _, Nat.add_zero _⟩
  | loop => exact ⟨Nat.le_refl _, Nat.add_zero _⟩

theorem Safe.shell_step {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    {before after : Configuration n} (safe : Safe program signature final before)
    (step : Transition program before after) :
    after.linearShells ≤ before.linearShells ∧ after.shells + before.shellDebit = before.shells := by
  cases step with
  | @operation code cleanup state next after stack step =>
    cases safe with
    | body typed checked retained =>
      obtain ⟨bounded, balance⟩ := local_shells typed checked step
      constructor
      · exact Nat.add_le_add_right bounded _
      · change after.shells + stackMass _ _ stack + bodyShellDebit code state = state.shells + stackMass _ _ stack
        omega
  | @enter identity destination next cleanup state stack function argument resolved resident =>
    have same := enter_mass state stack next cleanup destination argument resident
    exact ⟨Nat.le_of_eq (same _ _), by simpa only [Configuration.shellDebit, bodyShellDebit, Nat.add_zero, Configuration.shells, Configuration.mass] using same (fun _ => 0) (fun s => if s.restriction = .exact then 1 else 0)⟩
  | @handoff cleanup state frame stack slots installed =>
    have same := handoff_mass state frame stack installed
    exact ⟨Nat.le_of_eq (same _ _), by simpa only [Configuration.shellDebit, bodyShellDebit, Nat.add_zero, Configuration.shells, Configuration.mass] using same (fun _ => 0) (fun s => if s.restriction = .exact then 1 else 0)⟩
  | @clean code state next after stack step =>
    cases safe with
    | cleaning typed checked retained =>
      have start : OwnershipMir.Safe signature (Op.Checked _) _ ⟨code, state⟩ := ⟨_, typed, checked⟩
      have bounded := start.linear_shells_step step
      have balance := start.shell_step step
      change after.shells + OwnershipMir.Configuration.shellDebit ⟨code, state⟩ = state.shells at balance
      constructor
      · exact Nat.add_le_add_right bounded _
      · change after.shells + stackMass _ _ stack + OwnershipMir.Configuration.shellDebit ⟨code, state⟩ =
          state.shells + stackMass _ _ stack
        omega
  | retire =>
    simp [Configuration.linearShells, Configuration.shells, Configuration.mass, stackMass, empty_mass,
      Configuration.shellDebit, OwnershipMir.Configuration.shellDebit]

/-- A trace interpretation of real transitions, not runtime bookkeeping. -/
inductive ShellTrace {n : Nat} (program : Program n) : Configuration n → Configuration n → Nat → Prop where
  | refl (config) : ShellTrace program config config 0
  | step {before middle after amount} (head : Transition program before middle)
      (tail : ShellTrace program middle after amount) : ShellTrace program before after (before.shellDebit + amount)

theorem Safe.shell_execution {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    (functions : program.Checked) {before after : Configuration n} (safe : Safe program signature final before)
    (run : Run (Transition program) before after) :
    after.linearShells ≤ before.linearShells ∧
      ∃ amount, ShellTrace program before after amount ∧ after.shells + amount = before.shells := by
  induction run with
  | refl => exact ⟨Nat.le_refl _, 0, .refl _, Nat.add_zero _⟩
  | step head tail ih =>
    obtain ⟨bounded, balance⟩ := safe.shell_step head
    obtain ⟨restBound, amount, trace, restBalance⟩ := ih (safe.preservation functions head)
    exact ⟨Nat.le_trans restBound bounded, _, .step head trace, by omega⟩

/-- The outer activation is an explicit caller boundary. Its final state keeps
its declared output context; called activations must retire completely. -/
def Function.start {n : Nat} (function : Function n) (argument : Value) : Configuration n :=
  ⟨.body function.body function.cleanup, ⟨argumentSlots argument, none⟩, []⟩

theorem Function.start_safe {n : Nat} {program : Program n} {signature : Signature} {function : Function n}
    (functions : program.Checked) {identity : Nat} (selected : program identity = some function)
    {argument : Value} (typed : argument.kind signature = function.input) :
    Safe program signature function.exit (function.start argument) :=
  .body (argument_typed typed) (functions identity function selected).1 .nil
theorem Function.start_declared {n : Nat} {program : Program n} {signature : Signature} {function : Function n}
    (functions : program.Checked) {identity : Nat} (selected : program identity = some function)
    {argument : Value} (typed : argument.kind signature = function.input) :
    (function.start argument).Declared program.declarations signature := by
  have valid : Layout.Declared program.declarations (argument.layout (Atom.kind signature)) := by
    simpa [← typed, Value.kind, Tree.layout_map] using (functions identity function selected).2.2.2.2.1
  exact ⟨argument_declared valid, by intro frame impossible; cases impossible⟩


/-- General entry-to-arbitrary-prefix safety, including recursive calls,
intermediate transfers, protected returns, and every cleanup instruction. -/
theorem program_safety {n : Nat} {program : Program n} {signature : Signature} {function : Function n}
    (functions : program.Checked) {identity : Nat} (selected : program identity = some function)
    {argument : Value} (typed : argument.kind signature = function.input)
    (unique : (function.start argument).Unique) {after : Configuration n}
    (run : Run (Transition program) (function.start argument) after) :
    Safe program signature function.exit after ∧ after.Unique ∧ Preserves signature (function.start argument) after ∧
      (after.Terminal ∨ ∃ next, Transition program after next) ∧
      after.linearShells ≤ (function.start argument).linearShells ∧
      after.Declared program.declarations signature ∧
      ∃ amount, ShellTrace program (function.start argument) after amount ∧
        after.shells + amount = (function.start argument).shells := by
  have safe := Function.start_safe functions selected typed
  obtain ⟨preserved, distinct, conserved, progress⟩ := ownership_safety functions safe unique run
  obtain ⟨bounded, amount, trace, balanced⟩ := safe.shell_execution functions run
  exact ⟨preserved, distinct, conserved, progress, bounded,
    safe.declared_run functions (Function.start_declared functions selected typed) run, amount, trace, balanced⟩

end OwnershipMir.Calls
