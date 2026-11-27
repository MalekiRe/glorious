module

public import Glorious.Driver
public import Glorious.Bytecode.Encode
public import Glorious.Store

/-!
# The target directory: what a compile keeps for the next

A program's build directory holds what its last compile made, keyed by
everything it was made from: the program's texts, its modules' texts and the
compiler itself. Where none of that has changed, the next compile is the
reading of one file.

What is kept of a compile (`Built`) is what the commands that run a program
need: the bytecode, the constructor names values are printed with, and the
local slots each function starts with.

Nothing here is trusted beyond the compiler that wrote it: the key names the
compiler's own file, by its size and the time it was written, so a file
written by another compiler is not read.
-/

@[expose] public section

namespace Glorious.Target

/-- What a compile made, as the commands use it. -/
structure Built where
  bytecode : Bytecode.Program
  ctorNames : Array String
  /-- The local slots each function needs, for the Rust VM's bytecode file. -/
  startLocals : List Nat

/-- What a compile keeps of a program it compiled. -/
def Built.of (c : Compiled) (startLocals : List Nat) : Built :=
  { bytecode := compile c.core, ctorNames := c.ctorNames, startLocals }

/-! ## Where it is kept -/

/-- The compiler's directory in the user's cache. -/
def cacheDir : IO System.FilePath := do
  let home := (← IO.getEnv "HOME").getD "/tmp"
  let base := ((← IO.getEnv "XDG_CACHE_HOME").map System.FilePath.mk).getD (System.FilePath.mk home / ".cache")
  pure (base / "glorious")

/-- The build directory of the program whose first module is at `path`:
`GLORIOUS_TARGET` if set, and otherwise one in the user's cache, named from
the path. -/
def dirOf (path : String) : IO System.FilePath := do
  let whole ← IO.FS.realPath path
  match ← IO.getEnv "GLORIOUS_TARGET" with
  | some dir => pure (System.FilePath.mk dir)
  | none => pure ((← cacheDir) / "build" / s!"{(hash whole.toString).toNat}")

/-- Where what is kept for every program is: the prelude and the library as
checked, in the user's cache. -/
def libraryDir : IO System.FilePath := do
  pure ((← cacheDir) / "library")

/-- What a compile is made from, written down: the compiler's file, by size
and time, and every text, each with its module's path and its length. -/
def keyOf (src : String) (files : List (List String × String)) : IO String := do
  let exe ← IO.appPath
  let info ← exe.metadata
  let texts := ([], src) :: files
  let hashed := texts.foldl (fun h (path, text) =>
    mixHash h (mixHash (hash ("::".intercalate path)) (mixHash (hash text) (hash text.length)))) 7
  pure s!"{exe} {info.byteSize} {info.modified.sec}.{info.modified.nsec} {texts.length} {hashed}"

deriving instance Nonempty for Bytecode.Program
deriving instance Nonempty for Built

/-- What the last compile kept, if it was made from `key`. -/
def read (dir : System.FilePath) (key : String) : IO (Option Built) :=
  Store.load (dir / "program") key

/-- Keep what a compile made. -/
def write (dir : System.FilePath) (key : String) (b : Built) : IO Unit :=
  Store.save (dir / "program") key b

end Glorious.Target
