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

/-! ## A certificate

Kept so that a later compile whose Core is the same need not look for one: the
proved checker checks it against the program as any certificate is, so one
that does not fit is not used. -/

namespace Enc
open Bytecode.Encode (nat list) in
partial def rgn : Typing.Rgn → Bytes
  | .var i => [0] ++ nat i
  | .bound k => [1] ++ nat k
  | .cell a => [2] ++ nat a
  | .lab l => [3] ++ nat l
  | .loan b => [4] ++ nat b
  | .wr r => [5] ++ rgn r
  | .or a b => [6] ++ rgn a ++ rgn b

def option {α : Type} (item : α → Bytes) : Option α → Bytes
  | none => [0]
  | some a => [1] ++ item a

open Bytecode.Encode (nat list) in
partial def ty : Typing.Ty → Bytes
  | .int => [0]
  | .tuple fs => [1] ++ list ty fs
  | .data n args => [2] ++ nat n ++ list ty args
  | .fn rgns ps r eff once env acc =>
    [3] ++ nat rgns ++ list ty ps ++ ty r ++ list (fun (o, args) => nat o ++ list ty args) eff
      ++ bool once ++ option (list ty) env ++ list rgn acc
  | .ref ρ t => [4] ++ rgn ρ ++ ty t
  | .never => [5]

open Bytecode.Encode (nat list) in
def row (r : Typing.Row) : Bytes := list (fun (o, args) => nat o ++ list ty args) r

open Bytecode.Encode (nat list) in
def sig (s : Typing.FnSig) : Bytes :=
  list ty s.caps ++ list ty s.params ++ ty s.ret ++ row s.eff ++ nat s.crgns ++ nat s.rgns
    ++ list rgn s.acc

open Bytecode.Encode (nat list) in
def hint : Typing.Hint → Bytes
  | .ty σ => [0] ++ ty σ
  | .clo σ θ => [1] ++ ty σ ++ list rgn θ
  | .handler ρ H Φ θs => [2] ++ ty ρ ++ row H ++ list rgn Φ ++ list (list rgn) θs
  | .rgns rs => [3] ++ list rgn rs

open Bytecode.Encode (nat list) in
def cert (c : Typing.Cert) : Bytes :=
  list (fun (e : Typing.SigEntry) => nat e.fn ++ sig e.sig ++ list (list hint) e.hints) c.sigs
    ++ list (fun (d : Typing.DataInst) =>
        nat d.name ++ list ty d.args ++ list (fun (k, fs) => nat k ++ list ty fs) d.ctors ++ bool d.dup) c.datas
    ++ list (fun (o : Typing.OpInst) =>
        nat o.op ++ list ty o.args ++ list ty o.payload ++ option ty o.result) c.ops
    ++ ty c.mainTy ++ list hint c.mainHints ++ bool c.strict ++ bool c.regions ++ bool c.loans
end Enc

namespace Dec
open Bytecode.Decode (nat list)

def option {α : Type} (item : Bytes → Option (α × Bytes)) : Bytes → Option (Option α × Bytes)
  | 0 :: rest => some (none, rest)
  | 1 :: rest => (item rest).map fun (a, rest) => (some a, rest)
  | _ => none

partial def rgn : Bytes → Option (Typing.Rgn × Bytes)
  | 0 :: bs => (nat bs).map fun (i, bs) => (.var i, bs)
  | 1 :: bs => (nat bs).map fun (i, bs) => (.bound i, bs)
  | 2 :: bs => (nat bs).map fun (i, bs) => (.cell i, bs)
  | 3 :: bs => (nat bs).map fun (i, bs) => (.lab i, bs)
  | 4 :: bs => (nat bs).map fun (i, bs) => (.loan i, bs)
  | 5 :: bs => (rgn bs).map fun (r, bs) => (.wr r, bs)
  | 6 :: bs => do
    let (a, bs) ← rgn bs
    let (b, bs) ← rgn bs
    pure (.or a b, bs)
  | _ => none

partial def ty : Bytes → Option (Typing.Ty × Bytes)
  | 0 :: bs => some (.int, bs)
  | 1 :: bs => (list ty bs).map fun (fs, bs) => (.tuple fs, bs)
  | 2 :: bs => do
    let (n, bs) ← nat bs
    let (args, bs) ← list ty bs
    pure (.data n args, bs)
  | 3 :: bs => do
    let (rgns, bs) ← nat bs
    let (ps, bs) ← list ty bs
    let (r, bs) ← ty bs
    let (eff, bs) ← list (fun bs => do
      let (o, bs) ← nat bs
      let (args, bs) ← list ty bs
      pure ((o, args), bs)) bs
    let (once, bs) ← bool bs
    let (env, bs) ← option (list ty) bs
    let (acc, bs) ← list rgn bs
    pure (.fn rgns ps r eff once env acc, bs)
  | 4 :: bs => do
    let (ρ, bs) ← rgn bs
    let (t, bs) ← ty bs
    pure (.ref ρ t, bs)
  | 5 :: bs => some (.never, bs)
  | _ => none

def row (bs : Bytes) : Option (Typing.Row × Bytes) :=
  list (fun bs => do
    let (o, bs) ← nat bs
    let (args, bs) ← list ty bs
    pure ((o, args), bs)) bs

def sig (bs : Bytes) : Option (Typing.FnSig × Bytes) := do
  let (caps, bs) ← list ty bs
  let (params, bs) ← list ty bs
  let (ret, bs) ← ty bs
  let (eff, bs) ← row bs
  let (crgns, bs) ← nat bs
  let (rgns, bs) ← nat bs
  let (acc, bs) ← list rgn bs
  pure (⟨caps, params, ret, eff, crgns, rgns, acc⟩, bs)

def hint : Bytes → Option (Typing.Hint × Bytes)
  | 0 :: bs => (ty bs).map fun (σ, bs) => (.ty σ, bs)
  | 1 :: bs => do
    let (σ, bs) ← ty bs
    let (θ, bs) ← list rgn bs
    pure (.clo σ θ, bs)
  | 2 :: bs => do
    let (ρ, bs) ← ty bs
    let (H, bs) ← row bs
    let (Φ, bs) ← list rgn bs
    let (θs, bs) ← list (list rgn) bs
    pure (.handler ρ H Φ θs, bs)
  | 3 :: bs => (list rgn bs).map fun (rs, bs) => (.rgns rs, bs)
  | _ => none

def cert (bs : Bytes) : Option (Typing.Cert × Bytes) := do
  let (sigs, bs) ← list (fun bs => do
    let (fn, bs) ← nat bs
    let (s, bs) ← sig bs
    let (hints, bs) ← list (list hint) bs
    pure (({ fn, sig := s, hints } : Typing.SigEntry), bs)) bs
  let (datas, bs) ← list (fun bs => do
    let (name, bs) ← nat bs
    let (args, bs) ← list ty bs
    let (ctors, bs) ← list (fun bs => do
      let (k, bs) ← nat bs
      let (fs, bs) ← list ty bs
      pure ((k, fs), bs)) bs
    let (dup, bs) ← bool bs
    pure (({ name, args, ctors, dup } : Typing.DataInst), bs)) bs
  let (ops, bs) ← list (fun bs => do
    let (op, bs) ← nat bs
    let (args, bs) ← list ty bs
    let (payload, bs) ← list ty bs
    let (result, bs) ← option ty bs
    pure (({ op, args, payload, result } : Typing.OpInst), bs)) bs
  let (mainTy, bs) ← ty bs
  let (mainHints, bs) ← list hint bs
  let (strict, bs) ← bool bs
  let (regions, bs) ← bool bs
  let (loans, bs) ← bool bs
  pure ({ sigs, datas, ops, mainTy, mainHints, strict, regions, loans }, bs)
end Dec

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

/-- The certificate the last compile found, if one was kept. -/
def readCert (dir : System.FilePath) : IO (Option Typing.Cert) := do
  let file := dir / "certificate"
  unless ← file.pathExists do return none
  let bytes ← IO.FS.readBinFile file
  pure ((Dec.cert (bytes.toList.map (·.toNat))).map (·.1))

/-- Keep a certificate. -/
def writeCert (dir : System.FilePath) (c : Typing.Cert) : IO Unit := do
  try
    IO.FS.createDirAll dir
    IO.FS.writeBinFile (dir / "certificate") ⟨((Enc.cert c).map Nat.toUInt8).toArray⟩
  catch _ => pure ()

/-- Keep what a compile made. (A directory that cannot be written is let be.) -/
def write (dir : System.FilePath) (key : String) (b : Built) : IO Unit := do
  try
    IO.FS.createDirAll dir
    IO.FS.writeBinFile (dir / "program") ⟨((encode key b).map Nat.toUInt8).toArray⟩
  catch _ => pure ()

end Glorious.Target
