import Glorious.Driver

/-!
# Command line

`glorious run FILE` runs a program on the bytecode machine.
`glorious check FILE` runs it on both machines and reports whether they agree.
-/

open Glorious

/-- Run a machine until it stops, counting steps. -/
partial def runToEnd {σ : Type} (step : σ → Step σ Value) (s : σ) (steps : Nat := 0) :
    Step σ Value × Nat :=
  match step s with
  | .next s' => runToEnd step s' (steps + 1)
  | r => (r, steps + 1)

def usage : String :=
  "usage: glorious run FILE\n       glorious check FILE"

def load (path : String) : IO (Except String Compiled) := do
  let src ← IO.FS.readFile path
  pure (compileSource src)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["run", path] =>
    match ← load path with
    | .error e =>
      IO.eprintln s!"{path}: {e}"
      pure 1
    | .ok c =>
      let bytecode := compile c.core
      let (outcome, _) := runToEnd (Bytecode.step bytecode) (Bytecode.init bytecode)
      IO.println (showOutcome c.ctorNames outcome)
      pure (match outcome with
        | .halt _ => 0
        | _ => 2)
  | ["check", path] =>
    match ← load path with
    | .error e =>
      IO.eprintln s!"{path}: {e}"
      pure 1
    | .ok c =>
      let bytecode := compile c.core
      let (onCore, coreSteps) := runToEnd (Core.step c.core) (Core.init c.core)
      let (onVm, vmSteps) := runToEnd (Bytecode.step bytecode) (Bytecode.init bytecode)
      let a := showOutcome c.ctorNames onCore
      let b := showOutcome c.ctorNames onVm
      IO.println s!"core:     {a}  ({coreSteps} steps)"
      IO.println s!"bytecode: {b}  ({vmSteps} steps)"
      if a == b then pure 0
      else
        IO.eprintln "the two machines disagree"
        pure 3
  | _ =>
    IO.eprintln usage
    pure 64
