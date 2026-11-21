module

public import Lean.CompactedRegion

/-!
# What a compile keeps, as Lean keeps it

A value the compiler made, its checker's state or an elaborated function, is
written to a file as Lean writes its own `.olean` files: the objects as they
are in memory, laid out in one region. Reading it back maps the file and is
done; nothing is decoded. Objects read so are never freed.

The objects' layout is this compiler's: a file is read only by the compiler
that wrote it (`identity`), and only at the type it was written at, which
the caller says by the name of the file. A value with a closure in it cannot
be kept.
-/

@[expose] public section

namespace Glorious.Store

/-- Which compiler wrote a file: its own file, by size and the time it was
written. -/
def identity : IO String := do
  let exe ← IO.appPath
  let info ← exe.metadata
  pure s!"{exe} {info.byteSize} {info.modified.sec}.{info.modified.nsec}"

/-- What is kept: the compiler that wrote it, what it was made from, and it. -/
structure Kept (α : Type) where
  compiler : String
  key : String
  value : α

/-- The regions read so far in this process, by their files: what a region
saved after them may point into, and what one read after them may. -/
initialize loaded : IO.Ref (Array (String × Lean.CompactedRegion)) ← IO.mkRef #[]

/-- The regions of these files, in order, each read (once) with those before
it: a file saved pointing into others is read after them. -/
unsafe def regionsOf (files : List System.FilePath) : IO (Array Lean.CompactedRegion) := do
  let mut regions := #[]
  for f in files do
    match (← loaded.get).find? (·.1 == f.toString) with
    | some (_, r) => regions := regions.push r
    | none =>
      let ((_ : Unit), r) ← Lean.CompactedRegion.read (α := Unit) f regions
      loaded.modify (·.push (f.toString, r))
      regions := regions.push r
  pure regions

unsafe def saveUnsafe {α : Type} (file : System.FilePath) (value : Kept α)
    (deps : List System.FilePath) : IO Unit := do
  let regions ← regionsOf deps
  -- (Each file its own place to be read at: two read in one process are not
  -- moved for each other.)
  let _ ← Lean.CompactedRegion.save file (.mkSimple s!"glorious.{file.fileName.getD ""}") value regions none
  pure ()

unsafe def loadUnsafe {α : Type} [Nonempty α] (file : System.FilePath) (deps : List System.FilePath) :
    IO (Kept α) := do
  let regions ← regionsOf deps
  let (value, r) ← Lean.CompactedRegion.read (α := Kept α) file regions
  loaded.modify (·.push (file.toString, r))
  pure value

@[implemented_by saveUnsafe]
opaque saveRaw {α : Type} (file : System.FilePath) (value : Kept α) (deps : List System.FilePath) : IO Unit

@[implemented_by loadUnsafe]
opaque loadRaw {α : Type} [Nonempty α] (file : System.FilePath) (deps : List System.FilePath) : IO (Kept α)

/-- What marks a file that names the files a value is in: those it points
into, and its own, last. -/
def headMark : String := "glorious: kept in"

/-- The files `file` names, if it is such a file. -/
def headOf (file : System.FilePath) : IO (List System.FilePath) := do
  unless ← file.pathExists do return []
  try
    let text ← IO.FS.readFile file
    match text.splitOn "\n" |>.filter (!·.isEmpty) with
    | mark :: names =>
      if mark != headMark then return []
      pure (names.map fun (n : String) => (file.parent.getD ".") / n)
    | [] => pure []
  catch _ => pure []

/-- Keep a value made from `key`, written first to a file of its own and then
put in place, so that what is read is never half written. (A directory that
cannot be written is let be.) With `chain` more than zero, what it has of
what was kept in `file` before is not written again but pointed into, the
files it is in kept beside it, up to `chain` of them; then all is written
again. A file once written is never written again, only taken away when no
file of `file` points into it. -/
def save {α : Type} (file : System.FilePath) (key : String) (value : α) (chain : Nat := 0) : IO Unit := do
  try
    let some dir := file.parent | return
    IO.FS.createDirAll dir
    let now ← IO.monoNanosNow
    if chain == 0 then
      let fresh := file.addExtension s!"{now}"
      saveRaw fresh { compiler := ← identity, key, value } []
      IO.FS.rename fresh file
      return
    let before ← headOf file
    -- (Only regions this process read, as this compiler: one it did not,
    -- of another compiler or not read at all, is not pointed into, and
    -- all is written again.)
    let read := (← loaded.get).map (·.1)
    let deps := if before.length ≤ chain && before.all (read.contains ·.toString) then before else []
    let name := s!"{file.fileName.getD "kept"}.{now}.region"
    saveRaw (dir / name) { compiler := ← identity, key, value } deps
    let files := deps ++ [dir / name]
    let head := file.addExtension s!"{now}"
    IO.FS.writeFile head (headMark ++ "\n" ++ "\n".intercalate (files.map fun f => f.fileName.getD ""))
    IO.FS.rename head file
    -- (What no longer is pointed into: taken away.)
    let own := files.map (·.fileName.getD "")
    for entry in ← dir.readDir do
      if entry.fileName.startsWith s!"{file.fileName.getD "kept"}." && entry.fileName.endsWith ".region"
          && !own.contains entry.fileName then
        discard <| (IO.FS.removeFile entry.path).toBaseIO
  catch _ => pure ()

/-- What was kept in `file`, if this compiler wrote it from `key`. -/
def load {α : Type} [Nonempty α] (file : System.FilePath) (key : String) : IO (Option α) := do
  unless ← file.pathExists do return none
  try
    -- (The compiler and the key are read before the value is touched: a
    -- `Kept` is laid out alike whatever it holds, and a region another
    -- compiler wrote may not be laid out as this one reads it.)
    let files ← headOf file
    let kept : Kept α ← match files.getLast? with
      | some own => loadRaw own files.dropLast
      | none => loadRaw file []
    unless kept.compiler == (← identity) && kept.key == key do return none
    pure (some kept.value)
  catch _ => pure none

unsafe def loadLaterUnsafe {α : Type} [Nonempty α] (file : System.FilePath) (key : String) : Thunk (Option α) :=
  Thunk.mk fun _ => match unsafeBaseIO ((load (α := α) file key).toBaseIO) with
    | .ok v => v
    | .error _ => none

/-- What was kept in `file`, read when it is first asked: of many kept, a
compile reads only those it asks. -/
@[implemented_by loadLaterUnsafe]
opaque loadLater {α : Type} [Nonempty α] (file : System.FilePath) (key : String) : Thunk (Option α)

end Glorious.Store
