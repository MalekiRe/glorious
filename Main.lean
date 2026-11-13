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
  twice and that no mutable variable or label is used after its block has ended.
  With both, the program can go wrong only by arithmetic overflow. It also says
  how many borrows are scopes of their own in Core under the rules for borrows:
  of those the proofs say that what is lent is used only through the borrow.
  It lists every borrow that is not one; with `--strict` it fails if there is
  any.
  Every command that compiles a program does this check; this one only reports
  it.
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
  "       glorious build FILE OUT\n       glorious certify [--strict] FILE\n" ++
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

/-- The texts of the modules of the program at `path` that are files of their
own, each with its path as a module. The module `child` of a module whose
modules are in the directory `D` is the file `D/child/child.glorious`, and its
own modules are in `D/child`. -/
partial def moduleFiles (path : System.FilePath) : IO (List (List String × String)) := do
  let root := path.parent.getD "."
  let rec load (here : List String) (src : String) : IO (List (List String × String)) := do
    let named ← match Syntax.fileModules src with
      | .ok named => pure named
      | .error _ => pure []
    let mut out : List (List String × String) := []
    for rel in named do
      let whole := here ++ rel
      let name := whole.getLast!
      let dir := whole.foldl (fun (dir : System.FilePath) (seg : String) => dir / seg) root
      let file := dir / s!"{name}.glorious"
      if ← file.pathExists then
        let text ← IO.FS.readFile file
        out := out ++ [(whole, text)] ++ (← load whole text)
    pure out
  load [] (← IO.FS.readFile path)

/-- Compile the program at `path`, with the modules it has in other files. -/
def compileFile (path : String) : IO (Except String Compiled) := do
  pure (compileSource (← IO.FS.readFile path) true (← moduleFiles path))

/-- The example programs that state what they must print. -/
def exampleCases (dir : System.FilePath) :
    IO (List (Case × List (List String × String))) := do
  if !(← dir.pathExists) then return []
  let entries := (← dir.readDir).qsort (fun a b => a.fileName < b.fileName)
  let mut out : Array (Case × List (List String × String)) := #[]
  for entry in entries do
    if entry.fileName.endsWith ".glorious" then
      let src ← IO.FS.readFile entry.path
      if let some (input, expect) := parseExpectation src then
        out := out.push (⟨src, input, expect⟩, ← moduleFiles entry.path)
  pure out.toList

/-- Run every test program and every example on the Lean machines, and on the
Rust VM if its path is given. -/
def selftest (vm : Option String) : IO UInt32 := do
  let mut failures := 0
  let mut ran := 0
  let tmp : System.FilePath := (← IO.getEnv "TMPDIR").getD "/tmp"
  let file := tmp / s!"glorious-selftest-{← IO.monoMsNow}.glbc"
  let examples ← exampleCases "examples"
  for (c, files) in cases.map (·, []) ++ examples do
    ran := ran + 1
    let got := evalSource c.src c.input (files := files)
    if got != c.expect then
      failures := failures + 1
      IO.eprintln s!"lean machines: expected\n{c.expect}\ngot\n{got}\nfor\n{c.src}\n"
    if let some vm := vm then
      match compileSource c.src true files with
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

/-- Say what the typing of a program's Core shows. With `strict`, fail if some
borrow is not covered by the proof about borrows. -/
def certify (path : String) (strict : Bool) : IO UInt32 := do
  match ← compileFile path with
  | .ok c =>
    let n := (c.cert.map (·.sigs.length)).getD 0
    let owned := (c.cert.map (·.strict)).getD false
    let regions := (c.cert.map (·.regions)).getD false
    let how := if owned then "well typed and well owned" else "well typed, not shown well owned,"
    let borrows :=
      if regions then "its mutable variables and labels shown never to be used after their blocks end"
      else "its mutable variables and labels not shown to stay within their blocks"
    let loans := (c.cert.map (·.loans)).getD false
    let lent :=
      if !loans then "the rules for borrows not shown to hold"
      else if c.lent == 0 then "no borrow made a scope of its own"
      else s!"{c.lent} borrows shown to be the only way to what they borrow while they last"
    IO.println s!"{path}: {how} in Core, {borrows}, {lent}, with {n} function signatures"
    for b in c.plain do
      IO.println s!"{path}:{b.show} is not shown exclusive in Core"
    if strict && !c.plain.isEmpty then
      IO.eprintln s!"{path}: {c.plain.length} borrows are kept exclusive only by the check of the source text"
      pure 1
    else pure 0
  | .error e =>
    IO.eprintln s!"{path}: {e}"
    pure 1

/-- For each file: what Core shows of the program, then what it writes and
gives, or why it does not compile. For trying programs quickly. -/
def probe (paths : List String) : IO UInt32 := do
  for path in paths do
    let src ← IO.FS.readFile path
    let files ← moduleFiles path
    match compileSource src true files with
    | .error e => IO.println s!"error: {e}"
    | .ok c =>
      let cert := c.cert
      let shown := s!"strict={(cert.map (·.strict)).getD false} regions={(cert.map (·.regions)).getD false} loans={(cert.map (·.loans)).getD false} scopes={c.lent} plain={c.plain.length}"
      IO.println s!"{shown} => {evalSource src [] 200000 files}"
    IO.println "--"
  pure 0

/-- Why a program's Core is not shown to follow every rule: what stops the
certificate with all of them asked for. -/
def why (path : String) : IO UInt32 := do
  let src ← IO.FS.readFile path
  let files ← moduleFiles path
  let .ok (prelude, items) := parseProgram src files | IO.println "parse failed"; return 1
  let .ok resolved := Syntax.Modules.resolve prelude items | IO.println "resolve failed"; return 1
  let .ok all := Syntax.expandAliases resolved.items | IO.println "aliases failed"; return 1
  let all := Syntax.fillDefaults all
  let .ok blocks := Check.checkProgram all resolved.info | IO.println "check failed"; return 1
  let all := Elab.eraseLifetimes all
  let (all, blocks) := Elab.untrait blocks all
  let .ok all := Elab.unfield blocks all | IO.println "unfield failed"; return 1
  let all := Elab.reachable ("main" :: blocks.coercions.map (·.2)) all
  for lends in [1, 0] do
    let .ok out := Elab.elabProgram all (some blocks) (fun _ => lends) | IO.println "elab failed"; return 1
    match Infer.certify all out.program true out.envSizes true true with
    | .ok cert =>
      if Typing.checkProgram cert out.program then IO.println s!"lends={lends}: accepted"
      else IO.println s!"lends={lends}: rejected: {Infer.rejected cert out.program}"
    | .error e => IO.println s!"lends={lends}: no certificate: {e}"
  pure 0

/-- How many of the test programs compile, and of those how many are shown
to follow each set of Core's rules. -/
def survey : IO UInt32 := do
  let examples ← exampleCases "examples"
  let mut compiled := 0
  let mut strict := 0
  let mut regions := 0
  let mut loans := 0
  let mut all := 0
  let mut scopes := 0
  let mut plain := 0
  let mut withPlain := 0
  let mut weak : List String := []
  for (c, files) in cases.map (·, []) ++ examples do
    if let .ok out := compileSource c.src true files then
      compiled := compiled + 1
      let has := fun (f : Typing.Cert → Bool) => (out.cert.map f).getD false
      if has (·.strict) then strict := strict + 1
      if has (·.regions) then regions := regions + 1
      if has (·.loans) then loans := loans + 1
      if has (·.strict) && has (·.regions) && has (·.loans) then all := all + 1
      else weak := weak ++ [s!"strict={has (·.strict)} regions={has (·.regions)} loans={has (·.loans)}: {c.src}"]
      scopes := scopes + out.lent
      plain := plain + out.plain.length
      unless out.plain.isEmpty do withPlain := withPlain + 1
  IO.println s!"{compiled} compile; {strict} well owned; {regions} with regions; {loans} with loans; {all} with all three"
  IO.println s!"{scopes} borrows are scopes of their own; {plain} are not, in {withPlain} programs"
  for w in weak do IO.println s!"--\n{w}"
  pure 0

/-- How long each stage of compiling a program takes, in milliseconds. -/
def stages (path : String) : IO UInt32 := do
  let src ← IO.FS.readFile path
  let files ← moduleFiles path
  let mut last ← IO.monoMsNow
  let lap := fun (what : String) (last : Nat) => do
    let now ← IO.monoMsNow
    IO.println s!"{what}: {now - last} ms"
    pure now
  let .ok (prelude, items) := parseProgram src files | IO.println "parse failed"; return 1
  IO.println s!"{prelude.length + items.length} items"
  last ← lap "parse" last
  let .ok resolved := Syntax.Modules.resolve prelude items | IO.println "resolve failed"; return 1
  IO.println s!"{resolved.items.length} resolved"
  last ← lap "resolve" last
  let .ok all := Syntax.expandAliases resolved.items | IO.println "aliases failed"; return 1
  let all := Syntax.fillDefaults all
  IO.println s!"{all.length} filled"
  last ← lap "aliases, defaults" last
  let .ok blocks := Check.checkProgram all resolved.info | IO.println "check failed"; return 1
  IO.println s!"{blocks.given.length} given"
  last ← lap "check" last
  let all := Elab.eraseLifetimes all
  let (all, blocks) := Elab.untrait blocks all
  let .ok all := Elab.unfield blocks all | IO.println "unfield failed"; return 1
  let all := Elab.reachable ("main" :: blocks.coercions.map (·.2)) all
  IO.println s!"{all.length} plain"
  last ← lap "untrait, unfield, reach" last
  let .ok out := Elab.elabProgram all (some blocks) | IO.println "elab failed"; return 1
  IO.println s!"{out.program.fns.length} functions"
  last ← lap "elaborate" last
  match Infer.certify all out.program true out.envSizes true true with
  | .ok cert =>
    last ← lap "infer certificate" last
    IO.println s!"{Typing.checkProgram cert out.program}"
    last ← lap "check certificate" last
  | .error e => IO.println s!"certify: {e}"
  let bytecode := compile out.program
  IO.println s!"{bytecode.fns.length} compiled"
  _ ← lap "compile" last
  pure 0

def parseInput (args : List String) : Except String (List Int) :=
  args.mapM fun a =>
    match a.toInt? with
    | some n => pure n
    | none => throw s!"input `{a}` is not an integer"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["certify", path] => certify path false
  | ["certify", "--strict", path] => certify path true
  | "probe" :: paths => probe paths
  | ["stages", path] => stages path
  | ["survey"] => survey
  | ["why", path] => why path
  | ["selftest"] => selftest none
  | ["selftest", vm] => selftest (some vm)
  | ["build", path, out] =>
    match ← compileFile path with
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
    let c ← match ← compileFile path with
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
