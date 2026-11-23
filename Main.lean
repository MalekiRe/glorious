module

public import Glorious.Driver
public import Glorious.Target
public import Glorious.Store
public import Std.Async.TCP
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
* `glorious serve` compiles for the other commands, keeping what it can
  between compiles; `run`, `certify` and `build` ask it where it runs.
* `glorious watch FILE [INPUT...]` compiles and runs it again on every change.
* `glorious exe FILE OUT` writes an executable of the program's own with no
  other tool: the VM with the program at its end, loaded and compiled to
  x86-64 ahead of time (its code is given addresses when it starts). Needs
  the VM built.
* `glorious native FILE OUT` builds it as a program of its own: bytecode, a
  body for each function made by LLVM, and the runtime, linked with wild where
  it is installed. Needs `clang`, and the VM built (`cargo build --release` in
  `vm`).
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

@[noinline] unsafe def sameOutputImpl (a b : List Value) : Bool := ptrEq a b

/-- Is this the very output seen before (so nothing was written since)?
Answered `false` where it cannot be told, and then what is new is looked for. -/
@[implemented_by sameOutputImpl] def sameOutput (a b : List Value) : Bool := let _ := (a, b); false

/-- Run the bytecode machine, printing each value as soon as it is written.
(The output is walked only where the step wrote some: most write none.) -/
partial def runStreaming (names : Array String) (bytecode : Bytecode.Program)
    (c : Bytecode.Config) (printed : Nat) (seen : List Value := []) : IO (Step Bytecode.Config Result) := do
  let out := c.world.output
  let printed ← if sameOutput out seen then pure printed else do
    for v in out.drop printed do
      IO.println (showValue names v)
    pure out.length
  match Bytecode.stepIO bytecode c with
  | .next c' => runStreaming names bytecode c' printed out
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
  -- (Each function's first signature, found once: not looked for among
  -- them all for each function.)
  let first : Std.HashMap Nat Nat := match c.cert with
    | some cert => cert.sigs.foldl (init := {}) fun m entry =>
      m.insertIfNew entry.fn (entry.sig.params.length + entry.sig.caps.length + 1)
    | none => {}
  (List.range c.core.fns.size).map fun i => first.getD i 0

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
  /-- Run on the Core machine: the cleanups installed, those started, and those
  left in resumptions never taken (`Core.cleanup_accounting`). -/
  cleanups : Option (Nat × Nat × Nat) := none
  /-- What the compile found for each place, and the way its certificate
  was found: what a later compile is given to try first. -/
  places : List ((String × Nat) × Nat) := []
  deriving Inhabited

/-- Compile a test program, and with `run` run it on the Lean machines. -/
def outcome (run : Bool) (c : Case) (files : List (List String × String)) (few : Bool := false)
    (known : List ((String × Nat) × Nat) := []) : Outcome :=
  match compileSource c.src true files few (known := known) with
  | .error e => { lean := s!"error: {e}", error := some e }
  | .ok compiled =>
    let has := fun (f : Typing.Cert → Bool) => (compiled.cert.map f).getD false
    -- (An example, a program as long as it needs, is given more steps on
    -- bytecode.)
    { lean := if run then evalCompiled compiled c.input (vmScale := if few then 200 else 20) else ""
      bytes := some (bytecodeBytes compiled)
      certified := compiled.cert.isSome
      strict := has (·.strict), regions := has (·.regions), loans := has (·.loans)
      lent := compiled.lent, plain := compiled.plain.length
      cleanups := if run then cleanupsOf compiled.core c.input else none
      places := compiled.places }

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

/-- What was found of each, put back in the order of the list: `order` is
the list's entries with their places, in the order they were gone through. -/
def placed {α β : Type} [Inhabited β] (order : List (α × Nat)) (found : Array β) (n : Nat) : Array β :=
  (order.zip found.toList).foldl (fun acc ((_, i), b) => acc.set! i b) (Array.replicate n default)

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
is kept: in its build directory. -/
def placesFile (path : String) : IO System.FilePath := do
  pure ((← Target.dirOf path) / "places")

/-- Keep what a compile found for each place. -/
def writePlaces (file : System.FilePath) (places : List ((String × Nat) × Nat)) : IO Unit := do
  try
    if let some dir := file.parent then IO.FS.createDirAll dir
    IO.FS.writeFile file ("\n".intercalate (places.map fun ((owner, k), v) => s!"{k}\t{v}\t{owner}"))
  catch _ => pure ()

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



instance : Nonempty Syntax.Fixities := ⟨{}⟩

/-- What certificate inference made is kept in this many files, by its keys
(`shardOf`): each written on a thread of its own, and only those something
was made anew in. One file took longer to write than all else kept. -/
def inferShards : Nat := 8

def shardOf (k : UInt64) : Nat := (k % inferShards.toUInt64).toNat

/-- What compiles are writing to keep, waited for before the process ends. -/
initialize keeping : IO.Ref (Array (Task (Except IO.Error Unit))) ← IO.mkRef #[]

/-- Write what is kept on a thread of its own: what was compiled is used, and
run, while it is written. -/
def keep (act : IO Unit) : IO Unit := do
  let t ← IO.asTask act
  keeping.modify (·.push t)

/-- Entries by key, kept as `inferShards` files `name.i` by `shardOf`: each
written on a thread of its own, only where an entry not `kept` falls to it,
pointing into what was read; the first `most` of each. -/
def saveShards {α : Type} (dir : System.FilePath) (name key : String) (entries : List (UInt64 × α))
    (kept : UInt64 → Bool) (most : Nat := 1 <<< 30) : IO Unit := do
  for i in [0:inferShards] do
    let mine := entries.filter (shardOf ·.1 == i)
    if mine.any (!kept ·.1) then
      keep <| Trace.timedIO s!"save: {name}" (Store.save (dir / s!"{name}.{i}") key (mine.take most) (chain := 64))

/-- What `saveShards` kept, all of it. -/
def loadShards {α : Type} (dir : System.FilePath) (name key : String) : IO (List (UInt64 × α)) := do
  let mut all : List (UInt64 × α) := []
  for i in [0:inferShards] do
    if let some part ← Store.load (α := List (UInt64 × α)) (dir / s!"{name}.{i}") key then
      all := part ++ all
  pure all

/-- Compile the program at `path`, with the modules it has in other files.
What the last compile of it found for each place where a borrow can be a scope
of its own is where this one starts; and what this one finds is kept for the
next, with the certificate it found: one that the proved checker accepts for
the program now is used, and no other looked for (`GLORIOUS_FRESH` set:
neither is read). -/
def compileFile (path : String) (checkKept : Check.Kept := []) (search : Bool := true) :
    IO (Except String Compiled) := do
  let file ← placesFile path
  let known ← if (← IO.getEnv "GLORIOUS_FRESH").isSome then pure [] else readPlaces file
  -- (Which way of finding a certificate passed last time, kept by any
  -- compile, where the places say none.)
  let known ← if (← IO.getEnv "GLORIOUS_FRESH").isSome || (List.lookup ("%way", 0) known).isSome then pure known
    else match ← Store.load (α := Nat) ((← Target.dirOf path) / "way") "way" with
      | some k => pure ((("%way", 0), k) :: known)
      | none => pure known
  let dir ← Target.dirOf path
  let kept ← if (← IO.getEnv "GLORIOUS_FRESH").isSome then pure [] else
    pure ((← Target.readCert dir).toList)
  -- (And what any program kept of the library's modules, checked first.)
  let library ← Target.libraryDir
  let libraryKept ← if (← IO.getEnv "GLORIOUS_FRESH").isSome then pure []
    else pure ((← Store.load (α := Check.Kept) (library / "units") "units").getD [])
  let checkKept := checkKept ++ libraryKept
  -- (What certificate inference made the last time, by function and signature.)
  let memo ← if (← IO.getEnv "GLORIOUS_FRESH").isSome then pure {} else do
    let mut m : Infer.Memo := {}
    for i in [0:inferShards] do
      if let some part ← Store.load (α := Infer.Memo) (dir / s!"infer.{i}") "infer" then
        m := if m.inst.isEmpty && m.schemes.isEmpty && m.faces.isEmpty then part else
          { inst := part.inst.fold (·.insert) m.inst, schemes := part.schemes.fold (·.insert) m.schemes
            faces := part.faces.fold (·.insert) m.faces }
    pure m
  -- (The prelude and library as checked, by an earlier process of this
  -- compiler, for any program.)
  let firsts ← if (← IO.getEnv "GLORIOUS_FRESH").isSome then pure [] else
    [(true, false), (true, true), (false, false), (false, true)].filterMapM fun (std, drop) => do
      pure (((← Store.load (α := List (Nat × Check.St)) (library / s!"first-{std}-{drop}") "first").bind
        (·.head?)).map ((std, drop), ·))
  -- (The prelude as any earlier process of this compiler parsed it.)
  let preludeKept ← if (← IO.getEnv "GLORIOUS_FRESH").isSome then pure none else
    Store.load (α := List Syntax.Item × Syntax.Fixities) (library / "prelude") "prelude"
  -- (Modules' items as an earlier compile parsed them.)
  let parsedKept : Parsed ← if (← IO.getEnv "GLORIOUS_FRESH").isSome then pure {} else
    pure (Std.HashMap.ofList ((← Store.load (α := List (UInt64 × List Syntax.Item)) (dir / "parsed") "parsed").getD []))
  let texts : Texts ← if (← IO.getEnv "GLORIOUS_FRESH").isSome then pure {} else
    pure (Std.HashMap.ofList ((← Store.load (α := List (UInt64 × TextRead)) (dir / "texts") "texts").getD []))
  -- (What each of the program's own groups added, as the last compile of it
  -- checked them.)
  -- (Each in a file of its own: a compile writes only those it made anew.)
  -- (All in one kept file, read as one region: each group is a place in
  -- it, not a file of its own to open.)
  let groupsKeptList : List (UInt64 × Check.KeptGroup) ← if (← IO.getEnv "GLORIOUS_FRESH").isSome then pure [] else
    loadShards dir "groups.kept" "groups"
  let groupsKept : Check.Deltas := groupsKeptList.foldl (fun m (k, d) => m.insertIfNew k (Thunk.pure (some d))) {}
  -- (And each module's items as resolution made them.)
  let unitsKept : Syntax.Modules.UnitsKept ← if (← IO.getEnv "GLORIOUS_FRESH").isSome then pure {} else
    pure (Std.HashMap.ofList ((← Store.load (α := List (UInt64 × List Syntax.Flat.FItem × Syntax.Modules.UnitMade))
      (dir / "resolved") "resolved").getD []))
  -- (And what the front end's passes made of each item.)
  let frontKept : Std.HashMap UInt64 (List Syntax.Flat.FItem) ← if (← IO.getEnv "GLORIOUS_FRESH").isSome then pure {} else
    pure (Std.HashMap.ofList (← loadShards (α := List Syntax.Flat.FItem) dir "front" "front"))
  -- (And each function as lowered.)
  let lowerKept : Elab.LowerMemo ← if (← IO.getEnv "GLORIOUS_FRESH").isSome then pure {} else
    pure ((← Store.load (α := Elab.LowerMemo) (dir / "lower") "lower").getD {})
  -- (And each function as elaborated.)
  let elabKept : Elab.ElabMemo ← if (← IO.getEnv "GLORIOUS_FRESH").isSome then pure {} else
    pure ((← Store.load (α := Elab.ElabMemo) (dir / "elab") "elab").getD {})
  -- (And each group of the program's own text's items, as parsed.)
  let itemsKept : Syntax.ItemsKept ← if (← IO.getEnv "GLORIOUS_FRESH").isSome then pure {} else
    pure ((← Store.load (α := Syntax.ItemsKept) (dir / "items") "items").getD {})
  let text ← IO.FS.readFile path
  let files ← moduleFiles path
  let result ← Trace.timedIO "compile" (IO.lazyPure fun _ =>
    compileSource text true files (few := true) known kept checkKept search memo firsts parsedKept preludeKept texts
      (groupsKept := some groupsKept) (unitsKept := some unitsKept) (frontKept := some frontKept)
      (itemsKept := some itemsKept) (elabKept := some elabKept) (lowerKept := some lowerKept))
  if let .ok c := result then keep <| Trace.timedIO "save what is kept" do
    -- (What a compile that did not look for each place found is not kept
    -- for one that does.)
    if search then
      writePlaces file c.places
      if let some cert := c.cert then Target.writeCert dir cert
    -- (The program's own unit's state is not kept: a compile of the same
    -- texts takes the program built, and one of others checks it anew.
    -- The states before it are kept with the library, for any program.)
    if preludeKept.isNone then
      if let .ok parsed := readPrelude.get then Store.save (library / "prelude") "prelude" parsed
    -- (Saved again only where something was parsed anew.)
    unless c.parsedMade.all (parsedKept.contains ·.1) do Trace.timedIO "save: parsed" (Store.save (dir / "parsed") "parsed" c.parsedMade)
    unless c.textsMade.all (texts.contains ·.1) do Trace.timedIO "save: texts" (Store.save (dir / "texts") "texts" c.textsMade (chain := 64))
    -- (Saved again only where something was made anew, pointing into what
    -- was read.)
    -- (The large ones each on a thread of its own, beside the others.)
    -- (In `inferShards` files, each written on a thread of its own, and
    -- only where something of it was made anew.)
    for i in [0:inferShards] do
      let made : Infer.Made :=
        { inst := c.inferMade.inst.filter (shardOf ·.1 == i), schemes := c.inferMade.schemes.filter (shardOf ·.1 == i)
          faces := c.inferMade.faces.filter (shardOf ·.1 == i) }
      let inferNew := made.inst.any (fun (k, sig, _) => !((memo.inst.get? k).getD []).any (·.1 == sig))
        || made.schemes.any (fun (k, _) => !memo.schemes.contains k)
        || made.faces.any (fun (k, _) => !memo.faces.contains k)
      if inferNew then keep <| Trace.timedIO "save: infer" (Store.save (dir / s!"infer.{i}") "infer" (Infer.toMemo made) (chain := 64))
    if let some ((std, drop), first) := c.firstMade then
      Store.save (library / s!"first-{std}-{drop}") "first" [first]
    -- (The library's modules, and the program's modules that are files, as
    -- this compile checked them, with those kept before, newest first and
    -- no more than 96.)
    let newKeys := c.libraryKept.map (·.1)
    unless c.libraryKept.isEmpty || newKeys.all (fun k => libraryKept.any (·.1 == k)) do
      Store.save (library / "units") "units"
        ((c.libraryKept ++ libraryKept.filter fun (k, _) => !newKeys.contains k).take 96)
    if let some k := List.lookup ("%way", 0) c.places then Store.save (dir / "way") "way" k
    -- (Saved again only where something was made anew; pointing into what
    -- was read, up to 64 files, then all written again.)
    saveShards dir "front" "front" c.frontMade.toList (frontKept.contains ·)
    if c.lowerMade.size != lowerKept.size
        || c.lowerMade.fold (fun b n k => b || ((lowerKept[n]?).map (·.key)) != some k.key) false then
      keep <| Trace.timedIO "save: lower" (Store.save (dir / "lower") "lower" c.lowerMade (chain := 64))
    if c.elabMade.size != elabKept.size
        || c.elabMade.fold (fun b n k => b || ((elabKept[n]?).map (·.key)) != some k.key) false then
      keep <| Trace.timedIO "save: elab" (Store.save (dir / "elab") "elab" c.elabMade (chain := 64))
    if c.itemsMade.fold (fun b i (_, h, _, _) => b || ((itemsKept[i]?).map (·.2.1)) != some h) false then
      keep <| Trace.timedIO "save: items" (Store.save (dir / "items") "items" c.itemsMade (chain := 64))
    -- (Not where the only unit made anew is the one the program's `main` is
    -- in: the text being edited, resolved again the next time it changes,
    -- which is each time; the others' are what a next compile finds.)
    let isMain := fun (items : List Syntax.Flat.FItem) => items.any fun
      | .fn "main" .. => true
      | _ => false
    let anew := c.unitsMade.filter fun (k, _) => !unitsKept.contains k
    unless anew.isEmpty || anew.all (fun (_, items, _) => isMain items) do
      keep <| Trace.timedIO "save: resolved" (Store.save (dir / "resolved") "resolved" c.unitsMade (chain := 64))
    -- (Saved again only where a group was checked anew, pointing into what
    -- was read. Those of earlier versions of the program are kept, for an
    -- edit taken back: up to 4096, this compile's first.)
    let made : Std.HashSet UInt64 := c.groupsMade.foldl (fun s (k, _) => s.insert k) {}
    let older := groupsKeptList.filter fun (k, _) => !made.contains k
    saveShards dir "groups.kept" "groups" (c.groupsMade.toList ++ older) (groupsKept.contains ·)
      (most := 4096 / inferShards)
    -- (`GLORIOUS_CORE`: the Core that was compiled, with what destroys what.)
    if (← IO.getEnv "GLORIOUS_CORE").isSome then
      IO.eprintln (showCore c.fnNames c.core)
      IO.eprintln s!"drops: {c.core.drops}"
  pure result

/-- The program at `path` built: what the last compile kept in the build
directory, if it was made from the same texts by the same compiler, and
otherwise compiled and kept (`GLORIOUS_FRESH` set: compiled whatever is kept). -/
def buildFile (path : String) (checkKept : Option (IO.Ref (List (String × Check.Kept))) := none)
    (search : Bool := true) : IO (Except String Target.Built) := do
  let dir ← Target.dirOf path
  let key ← Target.keyOf (← IO.FS.readFile path) (← moduleFiles path)
  if (← IO.getEnv "GLORIOUS_FRESH").isNone then
    if let some b ← Trace.timedIO "read the program" (Target.read dir key) then
      -- (One built without looking for each place serves what does not
      -- ask for that.)
      if b.searched || !search then return .ok b
  let kept ← match checkKept with
    | some ref => pure (((← ref.get).lookup path).getD [])
    | none => pure []
  match ← compileFile path kept search with
  | .error e => pure (.error e)
  | .ok c =>
    if let some ref := checkKept then
      ref.modify fun ks => (path, c.checkKept) :: ks.filter (·.1 != path)
    let b := Trace.timed "bytecode" fun _ => Target.Built.of c (startLocals c) search
    -- (Written while it runs.)
    keep <| Trace.timedIO "write the program" (Target.write dir key b)
    pure (.ok b)

/-! ## The compile server

`glorious serve` keeps one process for compiling: what any compile finds
once and for all (the prelude checked, the library's texts read) is found
once, and later what it keeps of each program. Where one runs, `run`,
`certify` and `build` ask it for the program built, and run or report on
what it gives as they would on their own; where none runs, or one of another
compiler, they build it themselves. -/

/-- Where a running server says it is: its port and the compiler it is. -/
def serverFile : IO System.FilePath := do
  let home := (← IO.getEnv "HOME").getD "/tmp"
  let base := match ← IO.getEnv "XDG_CACHE_HOME" with
    | some dir => System.FilePath.mk dir
    | none => System.FilePath.mk home / ".cache"
  pure (base / "glorious" / "server")

/-- This compiler: its file, by size and time. -/
def compilerIdentity : IO String := do
  let exe ← IO.appPath
  let info ← exe.metadata
  pure s!"{exe} {info.byteSize} {info.modified.sec}.{info.modified.nsec}"

def loopback (port : UInt16) : Std.Net.SocketAddress :=
  .v4 ⟨Std.Net.IPv4Addr.ofParts 127 0 0 1, port⟩

/-- A message: its length in eight bytes, then it. -/
def frame (payload : ByteArray) : ByteArray := Id.run do
  let n := payload.size
  let mut out := ByteArray.empty
  for k in [0:8] do
    out := out.push ((n >>> (8 * (7 - k))) % 256).toUInt8
  pure (out ++ payload)

/-- Read one message. -/
partial def receive (c : Std.Async.TCP.Socket.Client) : IO (Option ByteArray) := do
  let rec fill (have_ : ByteArray) (want : Nat) : IO (Option ByteArray) := do
    if have_.size ≥ want then return some have_
    match ← (c.recv? 65536).block with
    | some more => fill (have_ ++ more) want
    | none => return none
  let some head ← fill ByteArray.empty 8 | return none
  let n := (List.range 8).foldl (fun acc k => acc * 256 + (head.get! k).toNat) 0
  let some whole ← fill head (8 + n) | return none
  pure (some (whole.extract 8 (8 + n)))

def bytesOf (bs : List Nat) : ByteArray := ⟨(bs.map Nat.toUInt8).toArray⟩

/-- Serve compiles until killed. -/
partial def serve : IO UInt32 := do
  let server ← Std.Async.TCP.Socket.Server.mk
  server.bind (loopback 0)
  server.listen 16
  let port := (← server.getSockName).port
  let file ← serverFile
  if let some dir := file.parent then IO.FS.createDirAll dir
  IO.FS.writeFile file s!"{port}\n{← compilerIdentity}"
  IO.println s!"glorious: serving compiles on port {port}"
  (← IO.getStdout).flush
  -- (What the checker kept of each program, for its next compile.)
  let kept ← IO.mkRef ([] : List (String × Check.Kept))
  repeat
    let client ← server.accept.block
    try
      let some request ← receive client | continue
      let reply : ByteArray ← match String.fromUTF8? request with
        | none => pure (frame (bytesOf [1] ++ "an unreadable request".toUTF8))
        | some path =>
          match ← buildFile path (some kept) with
          | .ok b => pure (frame (bytesOf ([0] ++ Target.encode "" b)))
          | .error e => pure (frame (bytesOf [1] ++ e.toUTF8))
      (client.send reply).block
      client.shutdown.block
    catch e => IO.eprintln s!"glorious serve: {e}"
  pure 0

/-- The program at `path` built by the running server, if one of this
compiler runs; none if none does or it cannot be reached. -/
def buildByServer (path : String) : IO (Option (Except String Target.Built)) := do
  if (← IO.getEnv "GLORIOUS_FRESH").isSome || (← IO.getEnv "GLORIOUS_TARGET").isSome then return none
  let file ← serverFile
  unless ← file.pathExists do return none
  let lines := (← IO.FS.readFile file).splitOn "\n"
  let some port := (lines.headD "").toNat? | return none
  unless (lines.drop 1).headD "" == (← compilerIdentity) do return none
  try
    let client ← Std.Async.TCP.Socket.Client.mk
    (client.connect (loopback port.toUInt16)).block
    let whole ← IO.FS.realPath path
    (client.send (frame whole.toString.toUTF8)).block
    let some reply ← receive client | return none
    let bytes := reply.toList.map (·.toNat)
    match bytes with
    | 0 :: rest => pure ((Target.decode "" rest).map Except.ok)
    | 1 :: rest => pure (some (.error ((String.fromUTF8? (bytesOf rest)).getD "the server's error is unreadable")))
    | _ => pure none
  catch _ => pure none

/-- The bytes of a built program's bytecode file. -/
def builtBytes (b : Target.Built) : ByteArray :=
  ⟨((Bytecode.Encode.file b.ctorNames.toList b.bytecode
    ++ Bytecode.Encode.list Bytecode.Encode.nat b.startLocals).map Nat.toUInt8).toArray⟩

/-- The program at `path` built: by the running server if there is one, and
otherwise here. -/
def buildAsked (path : String) (search : Bool := true) : IO (Except String Target.Built) := do
  match ← buildByServer path with
  | some result => pure result
  | none => buildFile path (search := search)

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

/-- Does what a program gave match what it should: the same, or, of one
said to be refused (`error containing: ..`), an error that says that. -/
def expectMatches (expect got : String) : Bool :=
  if expect.startsWith "error containing: " then
    got.startsWith "error: " && (got.splitOn (expect.drop "error containing: ".length).toString).length > 1
  else got == expect

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
  -- (`GLORIOUS_ONLY=text`: only the programs whose source has the text in
  -- it, for trying a change on those first; `GLORIOUS_ONLY=examples`: the
  -- examples alone; `GLORIOUS_ONLY=cases`: the test programs alone.)
  let only := (← IO.getEnv "GLORIOUS_ONLY").getD ""
  let keep := fun (c : Case) => only.isEmpty || only == "examples" || only == "cases" || (c.src.splitOn only).length > 1
  let cases := if only == "examples" then [] else cases.filter keep
  let examples := if only == "cases" then [] else examples.filter (keep ·.1)
  let longCases := if only.isEmpty then longCases else longCases.filter keep
  let quick := (cases.map (·, [])) ++ examples
  let all := quick ++ longCases.map (·, [])
  -- `GLORIOUS_TIMES`: how long each part of this takes.
  let times := (← IO.getEnv "GLORIOUS_TIMES").isSome
  let started ← IO.monoMsNow
  let lap := fun (what : String) => do
    if times then IO.eprintln s!"{what}: at {(← IO.monoMsNow) - started} ms"
  -- The checks are started with the programs, and looked at after them.
  -- (Not where only some programs are asked for, `GLORIOUS_ONLY=text`.)
  let checksAsked := only.isEmpty || only == "examples" || only == "cases"
  let asked := if checksAsked then Checks.all.toArray.map fun (_, check) => Task.spawn fun _ => check () else #[]
  warm
  lap "the prelude and library checked"
  -- (What the last run found of each program's places and the way its
  -- certificate was found, by its text: tried first, as a compile of the
  -- command tries what the last compile of the file found. Only where to
  -- look first: a certificate is checked as any other.)
  let knownFile := (← Target.libraryDir) / "selftest-known"
  let knownBefore : Std.HashMap UInt64 (List ((String × Nat) × Nat)) ←
    if (← IO.getEnv "GLORIOUS_FRESH").isSome then pure {}
    else pure (Std.HashMap.ofList ((← Store.load (α := List (UInt64 × List ((String × Nat) × Nat))) knownFile "known").getD []))
  -- (The examples first, and the long ones among them: the others, which
  -- are quick, fill in around them.)
  let order := (all.zipIdx.filter fun (_, i) => cases.length ≤ i) ++ (all.zipIdx.filter fun (_, i) => i < cases.length)
  let run := fun (((c, files), i) : (Case × List (List String × String)) × Nat) =>
    -- (An example is compiled as the command compiles a file.)
    outcome (i < quick.length) c files (cases.length ≤ i && i < quick.length)
      (known := knownBefore.getD (hash c.src) [])
  let found ← if times then do
      let timed ← sideBySideTimed order run
      let slow := ((order.zip timed.toList).toArray.qsort fun a b => a.2.2 > b.2.2).toList.take 8
      for (((c, _), _), (_, ms)) in slow do
        IO.eprintln s!"{ms} ms: {((c.src.take 100).toString.replace "\n" " ")}"
      pure (placed order (timed.map (·.1)) all.length)
    else do pure (placed order (← sideBySide order run) all.length)
  lap "programs compiled and run on the Lean machines"
  Store.save knownFile "known" ((all.zip found.toList).filterMap fun ((c, _), o) =>
    if o.places.isEmpty then none else some (hash c.src, o.places))
  -- What is unsafe runs on the Rust VM alone, and the proved machines say so.
  let foreign ← if vm.isSome then sideBySide foreignCases fun c => outcome false c [] else pure #[]
  let mut failures : Array (Nat × String) := #[]
  for ((c, _), i) in all.zipIdx do
    let got := (found[i]?.map (·.lean)).getD ""
    if i < quick.length then
      if !expectMatches c.expect got then
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
    unless !checksAsked || held[i]?.getD false do
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
  let installs := count fun o => match o.cleanups with
    | some (n, _, _) => decide (n > 0)
    | none => false
  let lost := count fun o => match o.cleanups with
    | some (_, _, h) => decide (h > 0)
    | none => false
  IO.println s!"{installs} programs install cleanups on the Core machine; {lost} leave one in a resumption never taken"
  pure (if failures.isEmpty then 0 else 1)

/-- Say what the typing of a program's Core shows. With `strict`, fail if some
borrow is not covered by the proof about borrows. -/
def certify (path : String) (strict : Bool) : IO UInt32 := do
  match ← buildAsked path with
  | .ok c =>
    let n := c.sigs
    let owned := c.strict
    let regions := c.regions
    let how := if owned then "well typed and well owned" else "well typed, not shown well owned,"
    let borrows :=
      if regions then "its mutable variables and labels shown never to be used after their blocks end"
      else "its mutable variables and labels not shown to stay within their blocks"
    let loans := c.loans
    let lent :=
      if !loans then "the rules for borrows not shown to hold"
      else if c.lent == 0 then "no borrow made a scope of its own"
      else s!"{c.lent} borrows shown to be the only way to what they borrow while they last"
    IO.println s!"{path}: {how} in Core, {borrows}, {lent}, with {n} function signatures"
    for b in c.plain do
      IO.println s!"{path}:{b} is not shown exclusive in Core"
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

/-- Why a program's Core is not shown to follow every rule: what stops the
certificate with all of them asked for. -/
def why (path : String) : IO UInt32 := do
  let src ← IO.FS.readFile path
  let files ← moduleFiles path
  let .ok (prelude, items, _, _, _) := parseProgram src files | IO.println "parse failed"; return 1
  let .ok resolved := Syntax.Modules.resolve (Syntax.Flat.promoteItems (Syntax.Flat.ofItems prelude)).1 (Syntax.Flat.promoteItems (Syntax.Flat.ofItems items)).1 | IO.println "resolve failed"; return 1
  let .ok (all, _) := Syntax.Flat.expandAliases resolved.items | IO.println "aliases failed"; return 1
  let all := (Syntax.Flat.fillDefaults all).1
  -- (With what destroys values written, where the program has something to
  -- destroy, as a compile has it.)
  let drops := hasDrop items || hasText src "defer"
  let blocks ← match Check.checkProgram all resolved.info drops with
    | .ok blocks => pure blocks
    | .error e => IO.println s!"check failed: {e}"; return 1
  let written := Elab.declaredOf all
  let all := Elab.eraseLifetimes all
  let .ok (all, blocks) := lowered blocks written all | IO.println "lowering failed"; return 1
  let declared := Elab.withDeclared written (Elab.declaredOf all)
  -- (`GLORIOUS_LENDS=2,0,1`: how each place is tried, in place of all at once.)
  let asked := ((← IO.getEnv "GLORIOUS_LENDS").map fun s => (s.splitOn ",").map String.toNat!)
  for lends in [1, 0] do
    let sites := fun (i : Nat) => match asked with
      | some ms => if lends == 0 then 0 else ms[i]?.getD 0
      | none => lends
    let out ← match Elab.elabProgram all (some blocks) sites with
      | .ok out => pure out
      | .error e => IO.println s!"elab failed: {e}"; return 1
    if lends == 1 && (← IO.getEnv "GLORIOUS_CORE").isSome then
      IO.println (showCore out.fnNames out.program)
      IO.println s!"places: {out.siteOwners.toList.zipIdx.map fun (o, i) => s!"{i}:{o}"}"
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

/-- The signature of each function a program writes, as the checker found it
(name, type parameters, parameters, result, effects, asks), and each trait's
functions as declared; with `library`, the prelude's and library's too. -/
def signatures (path : String) (library : Bool) : IO UInt32 := do
  match compileSource (← IO.FS.readFile path) true (← moduleFiles path) (search := false) (lenient := true) with
    | .ok c =>
      let st := c.checkKept.foldl (fun (best : Option Check.St) (_, s) =>
        match best with
        | some b => if s.fns.size > b.fns.size then some s else some b
        | none => some s) none
      match st with
      | some st =>
        for (name, w) in Check.writtenSignatures st library do
          match w with
          | .ok w =>
            IO.println s!"{name} ¦ {", ".intercalate w.generics} ¦ {" ;; ".intercalate w.params} ¦ {w.ret} ¦ {w.effects} ¦ {" ;; ".intercalate w.asks}"
          | .error e => IO.println s!"{name} ¦ ERROR ¦ {e}"
        for r in st.refusals do
          IO.println s!"REFUSED ¦ {r}"
        for (name, w) in Check.writtenMethods st do
          match w with
          | .ok w =>
            IO.println s!"TRAIT {name} ¦ {", ".intercalate w.generics} ¦ {" ;; ".intercalate w.params} ¦ {w.ret} ¦ {w.effects} ¦ "
          | .error e => IO.println s!"TRAIT {name} ¦ ERROR ¦ {e}"
        pure 0
      | none => IO.eprintln "nothing was checked"; pure 1
    | .error e =>
      IO.eprintln s!"{path}: {e}"
      pure 1

/-- How long each stage of compiling a program takes, in milliseconds. -/
def stages (path : String) : IO UInt32 := do
  let src ← IO.FS.readFile path
  let files ← moduleFiles path
  let mut last ← IO.monoMsNow
  let lap := fun (what : String) (last : Nat) => do
    let now ← IO.monoMsNow
    IO.println s!"{what}: {now - last} ms"
    pure now
  let .ok (prelude, items, _, _, _) := parseProgram src files | IO.println "parse failed"; return 1
  IO.println s!"{prelude.length + items.length} items"
  last ← lap "parse" last
  let .ok resolved := Syntax.Modules.resolve (Syntax.Flat.promoteItems (Syntax.Flat.ofItems prelude)).1 (Syntax.Flat.promoteItems (Syntax.Flat.ofItems items)).1 | IO.println "resolve failed"; return 1
  IO.println s!"{resolved.items.length} resolved"
  last ← lap "resolve" last
  let .ok (all, _) := Syntax.Flat.expandAliases resolved.items | IO.println "aliases failed"; return 1
  let all := (Syntax.Flat.fillDefaults all).1
  let all0 := all
  IO.println s!"{all.length} filled"
  last ← lap "aliases, defaults" last
  -- (With what destroys values written, where the program has something to
  -- destroy, as a compile has it.)
  let drops := hasDrop items || hasText src "defer"
  let blocks ← match Check.checkProgram all resolved.info drops with
    | .ok blocks => pure blocks
    | .error e => IO.println s!"check failed: {e}"; return 1
  IO.println s!"{blocks.given.size} given"
  last ← lap "check" last
  let written := Elab.declaredOf all
  let all := Elab.eraseLifetimes all
  let .ok (all, blocks) := lowered blocks written all | IO.println "lowering failed"; return 1
  IO.println s!"{all.length} plain"
  last ← lap "untrait, unfield, reach" last
  let .ok out := Elab.elabProgram all (some blocks) | IO.println "elab failed"; return 1
  IO.println s!"{out.program.fns.size} functions"
  last ← lap "elaborate" last
  if (← IO.getEnv "GLORIOUS_CORE").isSome then IO.println (showCore out.fnNames out.program)
  -- One try of the search for borrows that are scopes of their own: every
  -- place lent, then certified as it is and with ranked callables.
  let declared := Elab.withDeclared (Elab.declaredOf all0) (Elab.declaredOf all)
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
  match Infer.certify (Elab.declaredOf all) out.program true out.envSizes true true with
  | .ok cert =>
    last ← lap "infer certificate" last
    IO.println s!"{Typing.checkProgram cert out.program}"
    last ← lap "check certificate" last
  | .error e => IO.println s!"certify: {e}"
  -- With references taken to be to one of several cells where they have to be.
  for ranked in [true, false] do
    match Infer.certify (Elab.declaredOf all) out.program true out.envSizes true false ranked true with
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
  IO.println s!"{bytecode.fns.size} compiled"
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
    | .ok b => IO.println s!"{b.given.size} given"
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
changes, and run it, each compile as `compileFile` makes one: from what the
build directory keeps. -/
partial def watch (path : String) (input : List Int) : IO UInt32 := do
  let mut last : List String := []
  let mut kept : Check.Kept := []
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
        match ← compileFile path kept (search := false) with
        | .error e => IO.eprintln s!"{path}: {e}"
        | .ok c =>
          kept := c.checkKept
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
  let code ← Trace.timedIO "glorious" (command args)
  -- (What a compile keeps is written while the program it made runs.)
  -- (Until none is left: one may start others.)
  let mut waited := 0
  while waited < (← keeping.get).size do
    let t := (← keeping.get)[waited]!
    let _ ← IO.wait t
    waited := waited + 1
  Trace.report
  -- (Ended here, not by returning: the ways of finding a certificate not
  -- taken, each on a thread of its own, would be waited for to the end.)
  (← IO.getStdout).flush
  (← IO.getStderr).flush
  IO.Process.exit code.toUInt8
where
  command (args : List String) : IO UInt32 := do
  match args with
  | ["certify", path] => certify path false
  | ["certify", "--strict", path] => certify path true
  | "probe" :: paths => probe paths
  | ["stages", path] => stages path
  | ["survey"] => survey
  | ["why", path] => why path
  -- (How many cleanups the Core machine installed, started, and left in a
  -- resumption never taken, running the program: `Core.cleanup_accounting`.)
  | ["cleanups", path] => do
    match cleanups (← IO.FS.readFile path) with
    | some (installed, started, held) =>
      IO.println s!"{installed} installed, {started} started, {held} left in resumptions never taken"
      pure 0
    | none => IO.println "does not compile, or does not finish"; pure 1
  -- (The signature of each function the program writes, as the checker
  -- found it: name, type parameters, parameters, result, effects, asks.)
  | ["signatures", path] => signatures path false
  | ["signatures", "--library", path] => signatures path true
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
    match ← compileFile path (search := false) with
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
      -- Linked with wild where it is installed (much faster than the
      -- system's linker), else with clang's own.
      let wild ← try
          let w ← IO.Process.output { cmd := "sh", args := #["-c", "command -v wild"] }
          pure (if w.exitCode == 0 && !w.stdout.trimAscii.isEmpty then
            #[s!"--ld-path={w.stdout.trimAscii}"] else #[])
        catch _ => pure #[]
      let cc ← IO.Process.output
        { cmd := "clang",
          args := #["-O2", "-Wno-override-module"] ++ wild ++ #[out ++ ".ll",
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
    -- the program at its end, loaded and compiled to machine code by it.
    match ← compileFile path (search := false) with
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
    match ← buildAsked path (search := false) with
    | .ok b =>
      IO.FS.writeBinFile out (builtBytes b)
      pure 0
    | .error e =>
      IO.eprintln s!"{path}: {e}"
      pure 1
  | ["serve"] => serve
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
    if command == "run" then
      -- (Running needs the program, not how much of it is shown: the places
      -- where a borrow can be a scope of its own are not looked for.)
      let b ← match ← buildAsked path (search := false) with
        | .ok b => pure b
        | .error e =>
          IO.eprintln s!"{path}: {e}"
          return 1
      match ← Trace.timedIO "run" (runStreaming b.ctorNames b.bytecode (Bytecode.initIO b.bytecode input) 0) with
      | .halt r =>
        -- (A `main` that gives nothing, `fn main() { .. }`, shows nothing.)
        let shown := showValue b.ctorNames r.value
        unless shown == "()" do IO.println shown
        return 0
      | _ =>
        -- The bytecode went wrong, so the Core program does too: find where
        -- and say why (the Core program made again, where it was kept).
        match ← compileFile path with
        | .ok c =>
          IO.eprintln s!"the program went wrong: {explainStuck c (stuckAt c.core (Core.initIO c.core input))}"
        | .error e => IO.eprintln s!"the program went wrong; compiled again: {e}"
        return 2
    let c ← match ← compileFile path (search := false) with
      | .ok c => pure c
      | .error e =>
        IO.eprintln s!"{path}: {e}"
        return 1
    let bytecode := compile c.core
    if command == "check" then
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
