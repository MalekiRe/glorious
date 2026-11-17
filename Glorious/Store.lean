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

unsafe def saveUnsafe {α : Type} (file : System.FilePath) (value : Kept α) : IO Unit := do
  let _ ← Lean.CompactedRegion.save file `glorious value #[] none
  pure ()

unsafe def loadUnsafe {α : Type} [Nonempty α] (file : System.FilePath) : IO (Kept α) := do
  let (value, _) ← Lean.CompactedRegion.read (α := Kept α) file #[]
  pure value

@[implemented_by saveUnsafe]
opaque saveRaw {α : Type} (file : System.FilePath) (value : Kept α) : IO Unit

@[implemented_by loadUnsafe]
opaque loadRaw {α : Type} [Nonempty α] (file : System.FilePath) : IO (Kept α)

/-- Keep a value made from `key`, written first to a file of its own and then
put in place, so that what is read is never half written. (A directory that
cannot be written is let be.) -/
def save {α : Type} (file : System.FilePath) (key : String) (value : α) : IO Unit := do
  try
    if let some dir := file.parent then IO.FS.createDirAll dir
    let fresh := file.addExtension s!"{← IO.monoNanosNow}"
    saveRaw fresh { compiler := ← identity, key, value }
    IO.FS.rename fresh file
  catch _ => pure ()

/-- What was kept in `file`, if this compiler wrote it from `key`. -/
def load {α : Type} [Nonempty α] (file : System.FilePath) (key : String) : IO (Option α) := do
  unless ← file.pathExists do return none
  try
    -- (The compiler and the key are read before the value is touched: a
    -- `Kept` is laid out alike whatever it holds, and a region another
    -- compiler wrote may not be laid out as this one reads it.)
    let kept : Kept α ← loadRaw file
    unless kept.compiler == (← identity) && kept.key == key do return none
    pure (some kept.value)
  catch _ => pure none

end Glorious.Store
