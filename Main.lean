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
* `glorious certify FILE` compiles it and says what the typing of its Core
  shows: that it is well typed, and whether it also follows the ownership rules
  and the region rules, which the proofs need to say that no resumption is used
  twice and that no mutable variable is used after its block has ended. Every
  command that compiles a program does this check; this one only reports it.
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

/-- The configuration at which a Core program has no next step. -/
partial def stuckAt (p : Core.Program) (cfg : Core.Config) : Core.Config :=
  match Core.stepIO p cfg with
  | .next cfg' => stuckAt p cfg'
  | _ => cfg

def usage : String :=
  "usage: glorious run FILE [INPUT...]\n       glorious check FILE [INPUT...]\n" ++
  "       glorious build FILE OUT\n       glorious certify FILE\n" ++
  "       glorious selftest [VM]"

def writeBytecode (c : Compiled) (out : System.FilePath) : IO Unit :=
  IO.FS.writeBinFile out
    ⟨((Bytecode.Encode.file c.ctorNames.toList (compile c.core)).map Nat.toUInt8).toArray⟩

/-- The expectation at the top of an example file: an optional `// input: ...`
line, then `// expect:` followed by one comment line per line of output. -/
def parseExpectation (src : String) : Option (List Int × String) := Id.run do
  let mut input : List Int := []
  let mut expect : Array String := #[]
  let mut found := false
  for line in src.splitOn "\n" do
    if !line.startsWith "//" then break
    if line.startsWith "// input:" then
      input := ((line.drop 9).toString.splitOn " ").filterMap String.toInt?
    else if line.startsWith "// expect:" then
      found := true
    else if found then
      expect := expect.push (line.drop 3).toString
  if found then some (input, "\n".intercalate expect.toList) else none

/-- The example programs that state what they must print. -/
def exampleCases (dir : System.FilePath) : IO (List Case) := do
  if !(← dir.pathExists) then return []
  let entries := (← dir.readDir).qsort (fun a b => a.fileName < b.fileName)
  let mut out : Array Case := #[]
  for entry in entries do
    if entry.fileName.endsWith ".glorious" then
      let src ← IO.FS.readFile entry.path
      if let some (input, expect) := parseExpectation src then
        out := out.push ⟨src, input, expect⟩
  pure out.toList

/-- Run every test program and every example on the Lean machines, and on the
Rust VM if its path is given. -/
def selftest (vm : Option String) : IO UInt32 := do
  let mut failures := 0
  let mut ran := 0
  let tmp : System.FilePath := (← IO.getEnv "TMPDIR").getD "/tmp"
  let file := tmp / s!"glorious-selftest-{← IO.monoMsNow}.glbc"
  let examples ← exampleCases "examples"
  for c in cases ++ examples do
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
  IO.println s!"{ran} programs ({examples.length} examples) on {machines}: {failures} failures"
  pure (if failures == 0 then 0 else 1)

def parseInput (args : List String) : Except String (List Int) :=
  args.mapM fun a =>
    match a.toInt? with
    | some n => pure n
    | none => throw s!"input `{a}` is not an integer"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["certify", path] =>
    match compileSource (← IO.FS.readFile path) with
    | .ok c =>
      let n := (c.cert.map (·.sigs.length)).getD 0
      let owned := (c.cert.map (·.strict)).getD false
      let regions := (c.cert.map (·.regions)).getD false
      let how := if owned then "well typed and well owned" else "well typed, not shown well owned,"
      let borrows := if regions then "its references shown never to outlive their variables"
        else "its references not shown to stay within their variables' blocks"
      IO.println s!"{path}: {how} in Core, {borrows}, with {n} function signatures"
      pure 0
    | .error e =>
      IO.eprintln s!"{path}: {e}"
      pure 1
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
        -- The bytecode went wrong, so the Core program does too: find where and say why.
        IO.eprintln s!"the program went wrong: {explainStuck c (stuckAt c.core (Core.initIO c.core input))}"
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
