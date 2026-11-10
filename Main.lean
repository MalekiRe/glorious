import Glorious.Driver
import Glorious.Cases
import Glorious.Bytecode.Encode

/-!
# Command line

* `glorious run FILE [INPUT...]` runs a program on the bytecode machine, printing
  what it writes as it writes it. The integers after the file are its input.
* `glorious check FILE [INPUT...]` runs it on both machines and reports whether
  they agree.
* `glorious build FILE OUT` compiles it to a bytecode file for the Rust VM.
* `glorious selftest [VM]` runs the test programs on the Core machine and the
  Lean bytecode machine, and on the Rust VM if its path is given.
-/

open Glorious

/-- Run a machine until it stops, counting steps. -/
partial def runToEnd {σ : Type} (step : σ → Step σ Result) (s : σ) (steps : Nat := 0) :
    Step σ Result × Nat :=
  match step s with
  | .next s' => runToEnd step s' (steps + 1)
  | r => (r, steps + 1)

/-- Run the bytecode machine, printing each value as soon as it is written. -/
partial def runStreaming (names : Array String) (bytecode : Bytecode.Program)
    (c : Bytecode.Config) (printed : Nat) : IO (Step Bytecode.Config Result) := do
  let out := c.world.output
  for v in out.drop printed do
    IO.println (showValue names v)
  match Bytecode.stepIO bytecode c with
  | .next c' => runStreaming names bytecode c' out.length
  | r => pure r

def usage : String :=
  "usage: glorious run FILE [INPUT...]\n       glorious check FILE [INPUT...]\n" ++
  "       glorious build FILE OUT\n       glorious selftest [VM]"

def writeBytecode (c : Compiled) (out : System.FilePath) : IO Unit :=
  IO.FS.writeBinFile out
    ⟨(Bytecode.Encode.file c.ctorNames.toList (compile c.core)).toArray⟩

/-- Run every test program on the Lean machines, and on the Rust VM if given. -/
def selftest (vm : Option String) : IO UInt32 := do
  let mut failures := 0
  let mut ran := 0
  let tmp : System.FilePath := (← IO.getEnv "TMPDIR").getD "/tmp"
  let file := tmp / s!"glorious-selftest-{← IO.monoMsNow}.glbc"
  for c in cases do
    ran := ran + 1
    let got := evalSource c.src c.input
    if got != c.expect then
      failures := failures + 1
      IO.eprintln s!"lean machines: expected\n{c.expect}\ngot\n{got}\nfor\n{c.src}\n"
    if let some vm := vm then
      match compileSource c.src with
      | .error _ => pure ()
      | .ok compiled =>
        writeBytecode compiled file
        let out ← IO.Process.output
          { cmd := vm, args := #[file.toString] ++ (c.input.map toString).toArray }
        let got := if out.exitCode == 0 then out.stdout else "went wrong\n"
        if got != c.expect ++ "\n" then
          failures := failures + 1
          IO.eprintln s!"rust vm: expected\n{c.expect}\ngot\n{got}\n{out.stderr}for\n{c.src}\n"
  if vm.isSome then IO.FS.removeFile file
  let machines := if vm.isSome then "Core, Lean bytecode and Rust VM" else "Core and Lean bytecode"
  IO.println s!"{ran} programs on {machines}: {failures} failures"
  pure (if failures == 0 then 0 else 1)

def parseInput (args : List String) : Except String (List Int) :=
  args.mapM fun a =>
    match a.toInt? with
    | some n => pure n
    | none => throw s!"input `{a}` is not an integer"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["selftest"] => selftest none
  | ["selftest", vm] => selftest (some vm)
  | ["build", path, out] =>
    match compileSource (← IO.FS.readFile path) with
    | .ok c =>
      writeBytecode c out
      pure 0
    | .error e =>
      IO.eprintln s!"{path}: {e}"
      pure 1
  | command :: path :: rest =>
    let input ← match parseInput rest with
      | .ok input => pure input
      | .error e =>
        IO.eprintln e
        return 64
    let c ← match compileSource (← IO.FS.readFile path) with
      | .ok c => pure c
      | .error e =>
        IO.eprintln s!"{path}: {e}"
        return 1
    let bytecode := compile c.core
    if command == "run" then
      match ← runStreaming c.ctorNames bytecode (Bytecode.initIO bytecode input) 0 with
      | .halt r =>
        IO.println (showValue c.ctorNames r.value)
        pure 0
      | _ =>
        IO.eprintln "the program went wrong"
        pure 2
    else if command == "check" then
      let (onCore, coreSteps) := runToEnd (Core.stepIO c.core) (Core.initIO c.core input)
      let (onVm, vmSteps) := runToEnd (Bytecode.stepIO bytecode) (Bytecode.initIO bytecode input)
      let a := showOutcome c.ctorNames onCore
      let b := showOutcome c.ctorNames onVm
      IO.println s!"core ({coreSteps} steps):\n{a}"
      IO.println s!"bytecode ({vmSteps} steps):\n{b}"
      if a == b then pure 0
      else
        IO.eprintln "the two machines disagree"
        pure 3
    else
      IO.eprintln usage
      pure 64
  | _ =>
    IO.eprintln usage
    pure 64
