module

public import Glorious.Driver
public import Glorious.Bytecode.Encode
public import Glorious.Bytecode.Decode

/-!
# The target directory: what a compile keeps for the next

A program's build directory holds what its last compile made, keyed by
everything it was made from: the program's texts, its modules' texts and the
compiler itself. Where none of that has changed, the next compile is the
reading of one file.

What is kept of a compile (`Built`) is what the commands that run or report
on a program need: the bytecode, the constructor names values are printed
with, what Core's typing showed, which borrows are not scopes of their own,
and how each place where a borrow can be a scope of its own was made, which
a later compile of a changed program starts from.

Nothing here is trusted beyond the compiler that wrote it: the key names the
compiler's own file, by its size and the time it was written, so a file
written by another compiler is not read.
-/

@[expose] public section

namespace Glorious.Target

open Bytecode.Encode (Bytes)

/-- What a compile made, as the commands use it. -/
structure Built where
  bytecode : Bytecode.Program
  ctorNames : Array String
  /-- The local slots each function needs, for the Rust VM's bytecode file. -/
  startLocals : List Nat
  /-- How many function signatures the certificate has, and which of Core's
  sets of rules it shows: none if the program has no certificate. -/
  sigs : Nat
  certified : Bool
  strict : Bool
  regions : Bool
  loans : Bool
  /-- How many borrows are scopes of their own, and the others, as written. -/
  lent : Nat
  plain : List String
  /-- How each place was made, for a later compile (`Compiled.places`). -/
  places : List ((String × Nat) × Nat)

/-- What a compile keeps of a program it compiled. -/
def Built.of (c : Compiled) (startLocals : List Nat) : Built :=
  let has := fun (f : Typing.Cert → Bool) => (c.cert.map f).getD false
  { bytecode := compile c.core, ctorNames := c.ctorNames, startLocals
    sigs := (c.cert.map (·.sigs.length)).getD 0, certified := c.cert.isSome
    strict := has (·.strict), regions := has (·.regions), loans := has (·.loans)
    lent := c.lent, plain := c.plain.map (·.show), places := c.places }

/-! ## Writing and reading -/

namespace Enc
def bool (b : Bool) : Bytes := [if b then 1 else 0]
def place : (String × Nat) × Nat → Bytes
  | ((owner, k), v) => Bytecode.Encode.string owner ++ Bytecode.Encode.nat k ++ Bytecode.Encode.nat v
end Enc

namespace Dec
def bool : Bytes → Option (Bool × Bytes)
  | b :: rest => some (b == 1, rest)
  | [] => none

def string (bs : Bytes) : Option (String × Bytes) := do
  let (codes, rest) ← Bytecode.Decode.list (fun
    | b :: rest => some (b, rest)
    | [] => none) bs
  let text ← String.fromUTF8? ⟨(codes.map Nat.toUInt8).toArray⟩
  pure (text, rest)

def place (bs : Bytes) : Option (((String × Nat) × Nat) × Bytes) := do
  let (owner, bs) ← string bs
  let (k, bs) ← Bytecode.Decode.nat bs
  let (v, bs) ← Bytecode.Decode.nat bs
  pure (((owner, k), v), bs)
end Dec

/-- The magic `GLBO` and the format's version. -/
def magic : Bytes := [0x47, 0x4C, 0x42, 0x4F, 1]

/-- A built program as bytes, after the key it was made from. -/
def encode (key : String) (b : Built) : Bytes :=
  magic ++ Bytecode.Encode.string key
    ++ Bytecode.Encode.list Bytecode.Encode.string b.ctorNames.toList
    ++ Bytecode.Encode.list Bytecode.Encode.nat b.startLocals
    ++ Bytecode.Encode.nat b.sigs ++ Enc.bool b.certified ++ Enc.bool b.strict
    ++ Enc.bool b.regions ++ Enc.bool b.loans ++ Bytecode.Encode.nat b.lent
    ++ Bytecode.Encode.list Bytecode.Encode.string b.plain
    ++ Bytecode.Encode.list Enc.place b.places
    ++ Bytecode.Encode.program b.bytecode

/-- A built program from bytes, if they are one and were made from `key`. -/
def decode (key : String) (bs : Bytes) : Option Built := do
  guard (bs.take magic.length == magic)
  let bs := bs.drop magic.length
  let (written, bs) ← Dec.string bs
  guard (written == key)
  let (ctorNames, bs) ← Bytecode.Decode.list Dec.string bs
  let (startLocals, bs) ← Bytecode.Decode.list Bytecode.Decode.nat bs
  let (sigs, bs) ← Bytecode.Decode.nat bs
  let (certified, bs) ← Dec.bool bs
  let (strict, bs) ← Dec.bool bs
  let (regions, bs) ← Dec.bool bs
  let (loans, bs) ← Dec.bool bs
  let (lent, bs) ← Bytecode.Decode.nat bs
  let (plain, bs) ← Bytecode.Decode.list Dec.string bs
  let (places, bs) ← Bytecode.Decode.list Dec.place bs
  let bytecode ← Bytecode.Decode.program bs
  pure { bytecode, ctorNames := ctorNames.toArray, startLocals, sigs, certified, strict, regions
         loans, lent, plain, places }

/-! ## Where it is kept -/

/-- The build directory of the program whose first module is at `path`:
`GLORIOUS_TARGET` if set, and otherwise one in the user's cache, named from
the path. -/
def dirOf (path : String) : IO System.FilePath := do
  let whole ← IO.FS.realPath path
  match ← IO.getEnv "GLORIOUS_TARGET" with
  | some dir => pure (System.FilePath.mk dir)
  | none =>
    let home := (← IO.getEnv "HOME").getD "/tmp"
    let base := match ← IO.getEnv "XDG_CACHE_HOME" with
      | some dir => System.FilePath.mk dir
      | none => System.FilePath.mk home / ".cache"
    pure (base / "glorious" / "build" / s!"{(hash whole.toString).toNat}")

/-- What a compile is made from, written down: the compiler's file, by size
and time, and every text, each with its module's path and its length. -/
def keyOf (src : String) (files : List (List String × String)) : IO String := do
  let exe ← IO.appPath
  let info ← exe.metadata
  let texts := ([], src) :: files
  let hashed := texts.foldl (fun h (path, text) =>
    mixHash h (mixHash (hash ("::".intercalate path)) (mixHash (hash text) (hash text.length)))) 7
  pure s!"{exe} {info.byteSize} {info.modified.sec}.{info.modified.nsec} {texts.length} {hashed}"

/-- What the last compile kept, if it was made from `key`. -/
def read (dir : System.FilePath) (key : String) : IO (Option Built) := do
  let file := dir / "program"
  unless ← file.pathExists do return none
  let bytes ← IO.FS.readBinFile file
  pure (decode key (bytes.toList.map (·.toNat)))

/-- Keep what a compile made. (A directory that cannot be written is let be.) -/
def write (dir : System.FilePath) (key : String) (b : Built) : IO Unit := do
  try
    IO.FS.createDirAll dir
    IO.FS.writeBinFile (dir / "program") ⟨((encode key b).map Nat.toUInt8).toArray⟩
  catch _ => pure ()

end Glorious.Target
