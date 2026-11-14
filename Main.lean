module

public import Glorious.Driver
public import Glorious.Cases
public import Glorious.Checks
public import Glorious.Bytecode.Encode

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

public section

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
  "       glorious watch FILE [INPUT...]   (compile and run again on every change)\n" ++
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
  deriving Inhabited

/-- Compile a test program, and with `run` run it on the Lean machines. -/
def outcome (run : Bool) (c : Case) (files : List (List String × String)) (few : Bool := false) :
    Outcome :=
  match compileSource c.src true files few with
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

/-- Where what the last compile of the program at `path` found for each place
is kept: in the user's cache, under a name made from the path. -/
def placesFile (path : String) : IO System.FilePath := do
  let whole ← IO.FS.realPath path
  let home := (← IO.getEnv "HOME").getD "/tmp"
  let base := match ← IO.getEnv "XDG_CACHE_HOME" with
    | some dir => System.FilePath.mk dir
    | none => System.FilePath.mk home / ".cache"
  pure (base / "glorious" / "places" / s!"{(hash whole.toString).toNat}")

/-- What the last compile found for each place: a line for each, its number in
its function, how it was elaborated and the function's name. -/
def readPlaces (file : System.FilePath) : IO (List ((String × Nat) × Nat)) := do
  unless ← file.pathExists do return []
  let lines := (← IO.FS.readFile file).splitOn "\n"
  pure <| lines.filterMap fun line =>
    match line.splitOn "\t" with
    | k :: v :: rest => do
      pure ((("\t".intercalate rest), ← k.toNat?), ← v.toNat?)
    | _ => none

/-- Compile the program at `path`, with the modules it has in other files.
What the last compile of it found for each place where a borrow can be a scope
of its own is where this one starts; and what this one finds is kept for the
next (`GLORIOUS_FRESH` set: not read). -/
def compileFile (path : String) : IO (Except String Compiled) := do
  let file ← placesFile path
  let known ← if (← IO.getEnv "GLORIOUS_FRESH").isSome then pure [] else readPlaces file
  let result := compileSource (← IO.FS.readFile path) true (← moduleFiles path) (few := true) known
  if let .ok c := result then
    try
      if let some dir := file.parent then IO.FS.createDirAll dir
      IO.FS.writeFile file ("\n".intercalate (c.places.map fun ((owner, k), v) => s!"{k}\t{v}\t{owner}"))
    catch _ => pure ()
  pure result

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
  let examples := (← exampleCases "examples") ++ (← exampleCases "covey")
  -- (The programs that take the Lean machines too long come last, and are
  -- run on the Rust VM alone.)
  let quick := (cases.map (·, [])) ++ examples
  let all := quick ++ longCases.map (·, [])
  -- `GLORIOUS_TIMES`: how long each part of this takes.
  let times := (← IO.getEnv "GLORIOUS_TIMES").isSome
  let started ← IO.monoMsNow
  let lap := fun (what : String) => do
    if times then IO.eprintln s!"{what}: at {(← IO.monoMsNow) - started} ms"
  -- The checks are started with the programs, and looked at after them.
  let asked := Checks.all.toArray.map fun (_, check) => Task.spawn fun _ => check ()
  warm
  lap "the prelude and library checked"
  let found ← if times then do
      let timed ← sideBySideTimed all.zipIdx fun ((c, files), i) =>
        -- (An example is compiled as the command compiles a file.)
        outcome (i < quick.length) c files (cases.length ≤ i && i < quick.length)
      let slow := ((all.zip timed.toList).toArray.qsort fun a b => a.2.2 > b.2.2).toList.take 8
      for ((c, _), (_, ms)) in slow do
        IO.eprintln s!"{ms} ms: {((c.src.take 100).toString.replace "\n" " ")}"
      pure (timed.map (·.1))
    else sideBySide all.zipIdx fun ((c, files), i) =>
        -- (An example is compiled as the command compiles a file.)
        outcome (i < quick.length) c files (cases.length ≤ i && i < quick.length)
  lap "programs compiled and run on the Lean machines"
  -- What is unsafe runs on the Rust VM alone, and the proved machines say so.
  let foreign ← if vm.isSome then sideBySide foreignCases fun c => outcome false c [] else pure #[]
  let mut failures : Array (Nat × String) := #[]
  for ((c, _), i) in all.zipIdx do
    let got := (found[i]?.map (·.lean)).getD ""
    if i < quick.length then
      if got != c.expect then
        failures := failures.push (2 * i, s!"lean machines: expected\n{c.expect}\ngot\n{got}\nfor\n{c.src}\n")
    else if let some e := found[i]?.bind (·.error) then
      failures := failures.push (2 * i, s!"does not compile: {e}\nfor\n{c.src}\n")
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
  let .ok (all, blocks) := lowered blocks written all | IO.println "lowering failed"; return 1
  let all := Elab.reachable ("main" :: blocks.coercions.map (·.2)) all
  let declared := Elab.withDeclared written all
  -- (`GLORIOUS_LENDS=2,0,1`: how each place is tried, in place of all at once.)
  let asked := ((← IO.getEnv "GLORIOUS_LENDS").map fun s => (s.splitOn ",").map String.toNat!)
  for lends in [1, 0] do
    let sites := fun (i : Nat) => match asked with
      | some ms => if lends == 0 then 0 else ms[i]?.getD 0
      | none => lends
    let .ok out := Elab.elabProgram all (some blocks) sites | IO.println "elab failed"; return 1
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
  let examples := (← exampleCases "examples") ++ (← exampleCases "covey")
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

/-! A Core program written out, for reading what the elaborator made. -/

def showAtom : Atom → String
  | .var i => s!"v{i}"
  | .int n => s!"{n}"

def showAtoms (as : List Atom) : String := ", ".intercalate (as.map showAtom)

def showRhs : Rhs → String
  | .atom a => showAtom a
  | .prim _ args => s!"prim({showAtoms args})"
  | .construct tag args => s!"#{tag}({showAtoms args})"
  | .place pl => s!"v{pl.var}.{pl.path}"
  | .closure fn caps => s!"fn{fn}[{showAtoms caps}]"
  | .rebind a fn => s!"rebind({showAtom a}, fn{fn})"

partial def showTm (n : Nat) : Core.Tm → String
  | .ret a => s!"ret {showAtom a}"
  | .let_ rhs body => s!"let v{n} = {showRhs rhs}\n" ++ showTm (n + 1) body
  | .call f args body => s!"let v{n} = {showAtom f}({showAtoms args})\n" ++ showTm (n + 1) body
  | .tail f args => s!"tail {showAtom f}({showAtoms args})"
  | .handle _ _ caps thunk body =>
    s!"let v{n} = handle {showAtom thunk} [{showAtoms caps}]\n" ++ showTm (n + 1) body
  | .handleTail _ _ caps thunk => s!"handle {showAtom thunk} [{showAtoms caps}]"
  | .raise op args => s!"raise op{op}({showAtoms args})"
  | .perform op args body => s!"let v{n} = perform op{op}({showAtoms args})\n" ++ showTm (n + 1) body
  | .label thunk body => s!"let v{n} = label {showAtom thunk}\n" ++ showTm (n + 1) body
  | .labelTail thunk => s!"label {showAtom thunk}"
  | .guard c thunk body => s!"let v{n} = guard {showAtom c} {showAtom thunk}\n" ++ showTm (n + 1) body
  | .guardTail c thunk => s!"guard {showAtom c} {showAtom thunk}"
  | .cancel k body => s!"let v{n} = cancel {showAtom k}\n" ++ showTm (n + 1) body
  | .cell init thunk body => s!"let v{n} = cell {showAtom init} in {showAtom thunk}\n" ++ showTm (n + 1) body
  | .cellTail init thunk => s!"cell {showAtom init} in {showAtom thunk}"
  | .lend u r thunk pre post body =>
    s!"let v{n} = lend{if u then " mut" else ""} {showAtom r} to {showAtom thunk}({showAtoms pre} | {showAtoms post})\n"
      ++ showTm (n + 1) body
  | .mem _ args body => s!"let v{n} = mem({showAtoms args})\n" ++ showTm (n + 1) body
  | .host id args body => s!"let v{n} = host{id}({showAtoms args})\n" ++ showTm (n + 1) body

def showCore (names : Array String) (p : Core.Program) : String := Id.run do
  let mut out := ""
  for (F, i) in p.fns.zipIdx do
    out := out ++ s!"fn{i} {names[i]?.getD ""}:\n"
    for c in F.clauses do
      out := out ++ s!"  clause ({c.pats.length} patterns)\n"
      let lines := (showTm 1000 c.body).splitOn "\n"
      for l in lines do
        out := out ++ s!"    {l}\n"
  out ++ "main:\n" ++ "\n".intercalate (((showTm 0 p.main).splitOn "\n").map ("  " ++ ·))

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
  let written := all
  let all := Elab.eraseLifetimes all
  let .ok (all, blocks) := lowered blocks written all | IO.println "lowering failed"; return 1
  let all := Elab.reachable ("main" :: blocks.coercions.map (·.2)) all
  IO.println s!"{all.length} plain"
  last ← lap "untrait, unfield, reach" last
  let .ok out := Elab.elabProgram all (some blocks) | IO.println "elab failed"; return 1
  IO.println s!"{out.program.fns.length} functions"
  last ← lap "elaborate" last
  if (← IO.getEnv "GLORIOUS_CORE").isSome then IO.println (showCore out.fnNames out.program)
  -- One try of the search for borrows that are scopes of their own: every
  -- place lent, then certified as it is and with ranked callables.
  let declared := Elab.withDeclared all0 all
  if let .ok lentOut := Elab.elabProgram all (some blocks) (fun _ => 1) then
    IO.println s!"{lentOut.sites} places a borrow could be a scope, {lentOut.lent} made one"
    last ← lap "elaborate, every place lent" last
    for (ranked, widen) in [(false, false), (true, false), (false, true), (true, true)] do
      match Infer.certify declared lentOut.program true lentOut.envSizes true true ranked widen with
      | .ok cert =>
        last ← lap s!"certify lent (ranked {ranked}, widen {widen})" last
        let ok := Typing.checkProgram cert lentOut.program
        IO.println s!"{ok}{if ok then "" else s!": {Infer.rejected cert lentOut.program}"}"
        last ← lap "check that certificate" last
      | .error e =>
        IO.println s!"certify lent: {(e.take 300).toString}"
        last ← lap s!"certify lent (ranked {ranked}, widen {widen}), refused" last
  match Infer.certify all out.program true out.envSizes true true with
  | .ok cert =>
    last ← lap "infer certificate" last
    IO.println s!"{Typing.checkProgram cert out.program}"
    last ← lap "check certificate" last
  | .error e => IO.println s!"certify: {e}"
  -- With references taken to be to one of several cells where they have to be.
  for ranked in [true, false] do
    match Infer.certify all out.program true out.envSizes true false ranked true with
    | .ok cert =>
      let ok := Typing.checkProgram cert out.program
      IO.println s!"certify one of several (ranked {ranked}): {ok}{if ok then "" else s!": {Infer.rejected cert out.program}"}"
      if (← IO.getEnv "GLORIOUS_CORE").isSome && !ok then
        for e in cert.sigs do
          if let some F := out.program.fns[e.fn]? then
            unless Typing.checkFn cert e F do
              IO.println s!"  fn{e.fn}: {Infer.showSig e.sig}"
              for hs in e.hints do
                IO.println s!"    hints: {hs.map fun h => match h with
                  | .ty σ => s!"ty {Infer.showCoreTy σ}"
                  | .clo σ θ => s!"clo {Infer.showCoreTy σ} at {θ.map Infer.showRgn}"
                  | .handler .. => "handler"
                  | .rgns rs => s!"rgns {rs.map Infer.showRgn}"}"
    | .error e => IO.println s!"certify one of several (ranked {ranked}): {e}"
  let bytecode := compile out.program
  IO.println s!"{bytecode.fns.length} compiled"
  last ← lap "compile" last
  -- The search for which borrows can be scopes of their own, a step at a
  -- time: every place at once, each place alone, those that passed alone
  -- together.
  if let .ok lentOut := Elab.elabProgram all (some blocks) (fun _ => 1) then
    let try_ := fun (sites : Nat → Nat) =>
      match Elab.elabProgram all (some blocks) sites with
      | .ok o =>
        [false, true].any fun ranked =>
          match Infer.certify declared o.program true o.envSizes true true ranked with
          | .ok cert => o.lent != 0 && Typing.checkProgram cert o.program
          | .error _ => false
      | .error _ => false
    IO.println s!"every place at once: {try_ (fun _ => 1)}"
    last ← lap "every place at once" last
    let mut alone : Array Nat := #[]
    for i in [0:lentOut.sites] do
      let before ← IO.monoMsNow
      let mode := if try_ (fun j => if j == i then 1 else 0) then 1
        else if try_ (fun j => if j == i then 2 else 0) then 2 else 0
      alone := alone.push mode
      IO.println s!"  place {i} alone: {mode} ({(← IO.monoMsNow) - before} ms)"
    last ← lap "each place alone, one after another" last
    let asked := (List.range lentOut.sites).map fun i => Task.spawn fun _ =>
      if try_ (fun j => if j == i then 1 else 0) then 1
      else if try_ (fun j => if j == i then 2 else 0) then 2 else 0
    let again ← asked.mapM fun t => IO.wait t
    IO.println s!"side by side: the same answers: {again.toArray == alone}"
    last ← lap "each place alone, side by side" last
    IO.println s!"those that passed alone, together: {try_ (fun j => alone[j]?.getD 0)}"
    last ← lap "those together" last
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

/-- Compile the program at `path` again whenever its text or a module of it
changes, and run it. What does not change between compiles is kept: the
prelude and the whole library, checked once; and what the last compile found
of where borrows can be scopes of their own. -/
partial def watch (path : String) (input : List Int) : IO UInt32 := do
  let file ← placesFile path
  let mut known ← readPlaces file
  let mut last : List String := []
  repeat
    let texts ← try
        let src ← IO.FS.readFile path
        let files ← moduleFiles path
        pure (some (src, files))
      catch _ => pure none
    if let some (src, files) := texts then
      let now := src :: files.map (·.2)
      if now != last then
        last := now
        let start ← IO.monoMsNow
        match compileSource src true files (few := false) known with
        | .error e => IO.eprintln s!"{path}: {e}"
        | .ok c =>
          known := c.places
          try
            if let some dir := file.parent then IO.FS.createDirAll dir
            IO.FS.writeFile file ("\n".intercalate (c.places.map fun ((owner, k), v) => s!"{k}\t{v}\t{owner}"))
          catch _ => pure ()
          let compiled ← IO.monoMsNow
          IO.println s!"-- compiled in {compiled - start} ms"
          let bytecode := compile c.core
          match ← runStreaming c.ctorNames bytecode (Bytecode.initIO bytecode input) 0 with
          | .halt r => IO.println (showValue c.ctorNames r.value)
          | _ => IO.eprintln s!"the program went wrong: {explainStuck c (stuckAt c.core (Core.initIO c.core input))}"
        (← IO.getStdout).flush
    IO.sleep 100
  pure 0

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
    let all := Glorious.cases ++ Glorious.foreignCases ++ Glorious.longCases
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
  | "watch" :: path :: rest =>
    match parseInput rest with
    | .ok input => watch path input
    | .error e =>
      IO.eprintln e
      pure 64
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
