import Glorious.Driver
import Glorious.Cases
import Glorious.Checks
import Glorious.Bytecode.Encode

/-!
# Command line

* `glorious run FILE [INPUT...]` runs a program on the bytecode machine, printing
  what it writes as it writes it. The integers after the file are its input.
* `glorious check FILE [INPUT...]` runs it on both machines and reports whether
  they agree.
* `glorious build FILE OUT` compiles it to a bytecode file for the Rust VM.
* `glorious exe FILE OUT` writes an executable of the program's own with no
  other tool: the VM with the program at its end, compiled to x86-64 when it
  starts. Needs the VM built.
* `glorious native FILE OUT` builds it as a program of its own: bytecode, a
  body for each function made by LLVM, and the runtime. Needs `clang`, and the
  VM built (`cargo build --release` in `vm`).
* `glorious cases DIR` writes every test program, with its bytecode where it
  compiles, for what runs them from outside.
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
  Lean bytecode machine, and on the Rust VM if its path is given; then what
  `Glorious/Checks.lean` asks; then says how many of the programs compile and
  what Core shows of them. The programs are gone through side by side, on as
  many cores as there are.
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

/-- How many locals each function starts with, its arguments and what its
closure captured, and one more; zero where the certificate does not say.
What runs the bytecode does not need this: it is for what rewrites it. -/
def startLocals (c : Compiled) : List Nat :=
  (List.range c.core.fns.length).map fun i =>
    match c.cert.bind fun cert => cert.sigs.find? (·.fn == i) with
    | some entry => entry.sig.params.length + entry.sig.caps.length + 1
    | none => 0

/-- The bytes of a compiled program's bytecode file. -/
def bytecodeBytes (c : Compiled) : ByteArray :=
  ⟨((Bytecode.Encode.file c.ctorNames.toList (compile c.core)
    ++ Bytecode.Encode.list Bytecode.Encode.nat (startLocals c)).map Nat.toUInt8).toArray⟩

def writeBytecode (c : Compiled) (out : System.FilePath) : IO Unit :=
  IO.FS.writeBinFile out (bytecodeBytes c)

/-- What the commands that go through every test program ask of one: all of
it found by compiling the program once. -/
structure Outcome where
  /-- What the Lean machines give, or why the program does not compile; empty
  where they were not asked. -/
  lean : String := ""
  /-- Why it does not compile. -/
  error : Option String := none
  /-- Its bytecode file. -/
  bytes : Option ByteArray := none
  /-- What the typing of its Core shows. -/
  certified : Bool := false
  strict : Bool := false
  regions : Bool := false
  loans : Bool := false
  /-- The borrows that are scopes of their own, and those that are not. -/
  lent : Nat := 0
  plain : Nat := 0

/-- Compile a test program, and with `run` run it on the Lean machines. -/
def outcome (run : Bool) (c : Case) (files : List (List String × String)) : Outcome :=
  match compileSource c.src true files with
  | .error e => { lean := s!"error: {e}", error := some e }
  | .ok compiled =>
    let has := fun (f : Typing.Cert → Bool) => (compiled.cert.map f).getD false
    { lean := if run then evalCompiled compiled c.input else ""
      bytes := some (bytecodeBytes compiled)
      certified := compiled.cert.isSome
      strict := has (·.strict), regions := has (·.regions), loans := has (·.loans)
      lent := compiled.lent, plain := compiled.plain.length }

/-- What every program starts from, the prelude and the library checked,
found before the programs are gone through side by side: each would find it
again for itself otherwise. -/
def warm : IO Unit := do
  let ok := fun (t : Thunk (Except String (Nat × Check.St))) =>
    Task.spawn fun _ => match t.get with
      | .ok _ => true
      | .error _ => false
  for t in [ok checkedPrelude, ok checkedStd, ok checkedPreludeDrop, ok checkedStdDrop] do
    let _ ← IO.wait t

/-- The same thing found for each of a list, side by side: the runtime runs
as many at a time as the machine has cores. -/
def sideBySide {α β : Type} (xs : List α) (f : α → β) : IO (Array β) := do
  let tasks := xs.toArray.map fun x => Task.spawn fun _ => f x
  tasks.mapM fun t => IO.wait t

/-- The same, saying how long each took, in milliseconds: for finding what
is slow. -/
def sideBySideTimed {α β : Type} [Inhabited β] (xs : List α) (f : α → β) : IO (Array (β × Nat)) := do
  let tasks ← xs.toArray.mapM fun x => IO.asTask do
    let before ← IO.monoMsNow
    let y := f x
    let after ← IO.monoMsNow
    pure (y, after - before)
  tasks.mapM fun t => do
    match ← IO.wait t with
    | .ok r => pure r
    | .error _ => pure (default, 0)

/-- How many programs the Rust VM is run on at a time. -/
def vmJobs : IO Nat := do
  pure (((← IO.getEnv "GLORIOUS_JOBS").bind String.toNat?).getD 16)

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
Rust VM if its path is given. Each is compiled once; the programs are gone
through side by side, and what failed is said in the order they are in. Then
how many compile, and how many are shown to follow each set of Core's rules. -/
def selftest (vm : Option String) : IO UInt32 := do
  let tmp : System.FilePath := (← IO.getEnv "TMPDIR").getD "/tmp"
  let stamp ← IO.monoMsNow
  let examples ← exampleCases "examples"
  let all := (cases.map (·, [])) ++ examples
  -- `GLORIOUS_TIMES`: how long each part of this takes.
  let times := (← IO.getEnv "GLORIOUS_TIMES").isSome
  let started ← IO.monoMsNow
  let lap := fun (what : String) => do
    if times then IO.eprintln s!"{what}: at {(← IO.monoMsNow) - started} ms"
  -- The checks are started with the programs, and looked at after them.
  let asked := Checks.all.toArray.map fun (_, check) => Task.spawn fun _ => check ()
  warm
  lap "the prelude and library checked"
  let found ← sideBySide all fun (c, files) => outcome true c files
  lap "programs compiled and run on the Lean machines"
  -- What is unsafe runs on the Rust VM alone, and the proved machines say so.
  let foreign ← if vm.isSome then sideBySide foreignCases fun c => outcome false c [] else pure #[]
  let mut failures : Array (Nat × String) := #[]
  for ((c, _), i) in all.zipIdx do
    let got := (found[i]?.map (·.lean)).getD ""
    if got != c.expect then
      failures := failures.push (2 * i, s!"lean machines: expected\n{c.expect}\ngot\n{got}\nfor\n{c.src}\n")
  for (c, i) in foreignCases.zipIdx do
    match foreign[i]? with
    | some o =>
      if let some e := o.error then
        failures := failures.push (2 * (all.length + i), s!"foreign: {e}\nfor\n{c.src}\n")
      else if o.certified then
        failures := failures.push (2 * (all.length + i),
          s!"foreign: a program that calls a foreign function has a certificate\nfor\n{c.src}\n")
    | none => pure ()
  if let some vm := vm then
    -- Each program's bytecode, what it is given, what it should give, and
    -- whether going wrong counts as `went wrong` or shows as it is.
    let runs : Array (Nat × ByteArray × Case × Bool) :=
      (all.zipIdx.filterMap fun ((c, _), i) =>
        (found[i]?.bind (·.bytes)).map fun bytes => (2 * i + 1, bytes, c, true)).toArray
      ++ (foreignCases.zipIdx.filterMap fun (c, i) =>
        (foreign[i]?.bind (·.bytes)).map fun bytes => (2 * (all.length + i) + 1, bytes, c, false)).toArray
    -- All are started by one process that holds little: one started from
    -- here for each program waits for this one's memory to be copied, a
    -- hundredth of a second each time and one at a time.
    let jobs ← vmJobs
    let dir := tmp / s!"glorious-selftest-{stamp}"
    IO.FS.createDirAll dir
    let vmPath ← IO.FS.realPath vm
    for ((_, bytes, c, _), k) in runs.toList.zipIdx do
      IO.FS.writeBinFile (dir / s!"{k}.gbc") bytes
      let given := " ".intercalate (c.input.map toString)
      IO.FS.writeFile (dir / s!"{k}.sh")
        s!"\"$VM\" {k}.gbc {given} > {k}.out 2> {k}.err\necho $? > {k}.rc\n"
    let ran ← IO.Process.output
      { cmd := "sh", env := #[("VM", some vmPath.toString)]
        args := #["-c", s!"cd '{dir}' && ls | grep '[.]sh$' | xargs -P {jobs} -n 1 sh"] }
    if ran.exitCode != 0 then
      failures := failures.push (0, s!"rust vm: the programs could not be run: {ran.stderr}\n")
    for ((at_, _, c, plain), k) in runs.toList.zipIdx do
      let out ← IO.FS.readFile (dir / s!"{k}.out")
      let code := (← IO.FS.readFile (dir / s!"{k}.rc")).trimAscii.toString
      let got := if plain && code != "0" then "went wrong\n" else out
      if got != c.expect ++ "\n" then
        let err ← IO.FS.readFile (dir / s!"{k}.err")
        failures := failures.push (at_, s!"rust vm: expected\n{c.expect}\ngot\n{got}\n{err}for\n{c.src}\n")
    IO.FS.removeDirAll dir
  lap "programs run on the Rust VM"
  -- What else is asked of the front end: see `Glorious/Checks.lean`.
  let held ← asked.mapM fun t => IO.wait t
  lap "checks"
  for ((n, _), i) in Checks.all.zipIdx do
    unless held[i]?.getD false do
      failures := failures.push (2 * (all.length + foreignCases.length) + n,
        s!"check {n} of `Glorious/Checks.lean` does not hold\n")
  for (_, said) in failures.qsort (fun a b => a.1 < b.1) do
    IO.eprintln said
  let ran := all.length + (if vm.isSome then foreignCases.length else 0)
  let machines := if vm.isSome then "Core, Lean bytecode and Rust VM" else "Core and Lean bytecode"
  IO.println s!"{ran} programs ({examples.length} examples) on {machines}, and {Checks.all.length} checks: {failures.size} failures"
  let count := fun (f : Outcome → Bool) => (found.filter f).size
  let scopes := found.foldl (fun n o => n + o.lent) 0
  let plain := found.foldl (fun n o => n + o.plain) 0
  IO.println s!"{count (·.bytes.isSome)} compile; {count (·.strict)} well owned; {count (·.regions)} with regions; {count (·.loans)} with loans; {count fun o => o.strict && o.regions && o.loans} with all three"
  IO.println s!"{scopes} borrows are scopes of their own; {plain} are not, in {count (·.plain > 0)} programs"
  pure (if failures.isEmpty then 0 else 1)

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
  let mut read : List (String × List (List String × String)) := []
  for path in paths do
    read := read ++ [(← IO.FS.readFile path, ← moduleFiles path)]
  -- (Each finds what it starts from as it needs it: the prelude alone is
  -- quick to check, and a few programs do not need all four kinds.)
  let said ← sideBySide read fun (src, files) =>
    match compileSource src true files with
    | .error e => s!"error: {e}"
    | .ok (c : Compiled) =>
      let has := fun (f : Typing.Cert → Bool) => (c.cert.map f).getD false
      let shown := s!"strict={has (·.strict)} regions={has (·.regions)} loans={has (·.loans)} scopes={c.lent} plain={c.plain.length}"
      s!"{shown} => {evalCompiled c [] 200000}"
  for s in said do
    IO.println s
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
  let written := all
  let all := Elab.eraseLifetimes all
  let (all, blocks) := Elab.untrait blocks all
  let .ok all := Elab.unfield blocks all | IO.println "unfield failed"; return 1
  let all := Elab.reachable ("main" :: blocks.coercions.map (·.2)) all
  let declared := Elab.withDeclared written all
  for lends in [1, 0] do
    let .ok out := Elab.elabProgram all (some blocks) (fun _ => lends) | IO.println "elab failed"; return 1
    match Infer.certify declared out.program true out.envSizes true true true with
    | .ok cert =>
      if Typing.checkProgram cert out.program then IO.println s!"lends={lends}: accepted"
      else
        IO.println s!"lends={lends}: rejected: {Infer.rejected cert out.program}"
        for e in cert.sigs do
          if let some F := out.program.fns[e.fn]? then
            unless Typing.checkFn cert e F do
              IO.println s!"  {out.fnNames[e.fn]?.getD ""} (function {e.fn}): {Infer.showSig e.sig}"
              for hs in e.hints do
                for h in hs do
                  IO.println (match h with
                    | .ty σ => s!"    : {Infer.showCoreTy σ}"
                    | .clo σ θ => s!"    closure {Infer.showCoreTy σ} at [{", ".intercalate (θ.map Infer.showRgn)}]"
                    | .handler _ _ _ _ => "    handler"
                    | .rgns rs => s!"    call at [{", ".intercalate (rs.map Infer.showRgn)}]")
    | .error e => IO.println s!"lends={lends}: no certificate: {e}"
  pure 0

/-- How many of the test programs compile, and of those how many are shown
to follow each set of Core's rules. -/
def survey : IO UInt32 := do
  let examples ← exampleCases "examples"
  let all := (cases.map (·, [])) ++ examples
  let before ← IO.monoMsNow
  warm
  -- `GLORIOUS_TIMES`: the programs that take longest to compile, instead.
  if (← IO.getEnv "GLORIOUS_TIMES").isSome then
    let warmed ← IO.monoMsNow
    let timed ← sideBySideTimed all fun (c, files) => (outcome false c files).bytes.isSome
    let done ← IO.monoMsNow
    IO.println s!"warm {warmed - before} ms; programs {done - warmed} ms; sum {timed.foldl (fun n r => n + r.2) 0} ms"
    let slow := ((all.zip timed.toList).toArray.qsort fun a b => a.2.2 > b.2.2).toList.take 25
    for ((c, _), (_, ms)) in slow do
      IO.println s!"{ms} ms: {((c.src.take 110).toString.replace "\n" " ")}"
    return 0
  let found ← sideBySide all fun (c, files) => outcome false c files
  let count := fun (f : Outcome → Bool) => (found.filter f).size
  let scopes := found.foldl (fun n o => n + o.lent) 0
  let plain := found.foldl (fun n o => n + o.plain) 0
  IO.println s!"{count (·.bytes.isSome)} compile; {count (·.strict)} well owned; {count (·.regions)} with regions; {count (·.loans)} with loans; {count fun o => o.strict && o.regions && o.loans} with all three"
  IO.println s!"{scopes} borrows are scopes of their own; {plain} are not, in {count (·.plain > 0)} programs"
  for ((c, _), i) in all.zipIdx do
    if let some o := found[i]? then
      if o.bytes.isSome && !(o.strict && o.regions && o.loans) then
        IO.println s!"--\nstrict={o.strict} regions={o.regions} loans={o.loans}: {c.src}"
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
  let all0 := all
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
  -- One try of the search for borrows that are scopes of their own: every
  -- place lent, then certified as it is and with ranked callables.
  let declared := Elab.withDeclared all0 all
  if let .ok lentOut := Elab.elabProgram all (some blocks) (fun _ => 1) then
    IO.println s!"{lentOut.sites} places a borrow could be a scope, {lentOut.lent} made one"
    last ← lap "elaborate, every place lent" last
    for ranked in [false, true] do
      match Infer.certify declared lentOut.program true lentOut.envSizes true true ranked with
      | .ok cert =>
        last ← lap s!"certify lent (ranked {ranked})" last
        IO.println s!"{Typing.checkProgram cert lentOut.program}"
        last ← lap "check that certificate" last
      | .error e =>
        IO.println s!"certify lent: {(e.take 80).toString}"
        last ← lap s!"certify lent (ranked {ranked}), refused" last
  match Infer.certify all out.program true out.envSizes true true with
  | .ok cert =>
    last ← lap "infer certificate" last
    IO.println s!"{Typing.checkProgram cert out.program}"
    last ← lap "check certificate" last
  | .error e => IO.println s!"certify: {e}"
  let bytecode := compile out.program
  IO.println s!"{bytecode.fns.length} compiled"
  last ← lap "compile" last
  -- And as the other commands do it: from the library already checked,
  -- with the search for which borrows can be scopes of their own.
  warm
  last ← lap "the prelude and library, checked for every kind of program" last
  let drops := hasDrop items
  let first := if drops then checkedStdDrop.get else checkedStd.get
  if let .ok (count, first) := first then
    match Check.checkAfter first (all0.drop count) resolved.info with
    | .ok b => IO.println s!"{b.given.length} given"
    | .error e => IO.println s!"checkAfter: {e}"
    last ← lap "check, after the library" last
  match compileSource src true files with
  | .ok c =>
    IO.println s!"{c.lent} borrows are scopes, {c.plain.length} are not"
    last ← lap "compileSource, after that" last
    IO.println s!"{(evalCompiled c).length} characters of result"
    _ ← lap "both Lean machines" last
  | .error e => IO.println s!"compileSource: {e}"
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
  | ["sigs", path] =>
    match ← compileFile path with
    | .ok c =>
      match c.cert with
      | some cert =>
        IO.println s!"strict={cert.strict} regions={cert.regions} loans={cert.loans}"
        for e in cert.sigs do
          IO.println s!"{c.fnNames[e.fn]?.getD ""} ({e.fn}): {Infer.showSig e.sig}"
        pure 0
      | none =>
        IO.println "no certificate"
        pure 1
    | .error e =>
      IO.eprintln s!"{path}: {e}"
      pure 1
  | ["native", path, out] =>
    -- A program of its own: the bytecode, a body for every function made by
    -- LLVM, and the runtime, linked. The VM and its library are looked for
    -- in `GLORIOUS_VM_DIR`, or where the repository builds them.
    match ← compileFile path with
    | .ok c => do
      let dir ← match ← IO.getEnv "GLORIOUS_VM_DIR" with
        | some d => pure (System.FilePath.mk d)
        | none => do
          let exe ← IO.appPath
          let root := (((exe.parent.bind (·.parent)).bind (·.parent)).bind (·.parent)).getD "."
          pure (root / "vm" / "target" / "release")
      let gbc := out ++ ".gbc"
      writeBytecode c gbc
      let ir ← IO.Process.output
        { cmd := (dir / "glorious-vm").toString, args := #["--emit-llvm", gbc] }
      if ir.exitCode != 0 then
        IO.eprintln s!"glorious-vm: {ir.stderr}"
        return 1
      IO.FS.writeFile (out ++ ".ll") ir.stdout
      let cc ← IO.Process.output
        { cmd := "clang",
          args := #["-O2", "-Wno-override-module", out ++ ".ll",
            (dir / "libglorious_vm.a").toString, "-o", out, "-lpthread", "-ldl", "-lm"] }
      if cc.exitCode != 0 then
        IO.eprintln s!"clang: {cc.stderr}"
        return 1
      pure 0
    | .error e =>
      IO.eprintln s!"{path}: {e}"
      pure 1
  | ["exe", path, out] =>
    -- An executable of the program's own with no other tool: the VM with
    -- the program at its end, compiled to machine code when it starts.
    match ← compileFile path with
    | .ok c => do
      let dir ← match ← IO.getEnv "GLORIOUS_VM_DIR" with
        | some d => pure (System.FilePath.mk d)
        | none => do
          let exe ← IO.appPath
          let root := (((exe.parent.bind (·.parent)).bind (·.parent)).bind (·.parent)).getD "."
          pure (root / "vm" / "target" / "release")
      let gbc := out ++ ".gbc"
      writeBytecode c gbc
      let made ← IO.Process.output
        { cmd := (dir / "glorious-vm").toString, args := #["--bundle", gbc, out] }
      IO.FS.removeFile gbc
      if made.exitCode != 0 then
        IO.eprintln s!"glorious-vm: {made.stderr}"
        return 1
      pure 0
    | .error e =>
      IO.eprintln s!"{path}: {e}"
      pure 1
  | ["cases", dir] => do
    -- Every test program as files, for what runs them from outside: the
    -- bytecode where the program compiles, what it is given, what it gives.
    IO.FS.createDirAll dir
    let all := Glorious.cases ++ Glorious.foreignCases
    warm
    let found ← sideBySide all fun c => outcome false c []
    let mut n := 0
    let mut built := 0
    for (c, i) in all.zipIdx do
      n := n + 1
      let stem := s!"{dir}/{n}"
      IO.FS.writeFile s!"{stem}.glorious" c.src
      IO.FS.writeFile s!"{stem}.in" (" ".intercalate (c.input.map toString))
      IO.FS.writeFile s!"{stem}.out" c.expect
      if let some bytes := found[i]?.bind (·.bytes) then
        IO.FS.writeBinFile s!"{stem}.gbc" bytes
        built := built + 1
    IO.println s!"{n} programs, {built} built, in {dir}"
    pure 0
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
