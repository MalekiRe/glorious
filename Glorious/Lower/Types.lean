module

public import Glorious.Core.Ast

/-!
# Core's types, as the typed lowering reads them

Each function at each signature it is used at, with the type of each of its
`let`s, and the declared types and operations those use: what `Typer` finds
and `Lower.Typed` reads.
-/

@[expose] public section

namespace Glorious.Lower

open Core

/-- A type of Core. -/
inductive Ty where
  | int
  /-- A scalar of so many bits (`Syntax.scalars`' widths: with a sign if
  positive): held as a whole number, laid out in its own width. -/
  | scalar (bits : Int)
  | tuple (fields : List Ty)
  /-- A declared data type applied to its arguments. -/
  | data (name : Nat) (args : List Ty)
  /-- A callable: a function, a resumption or a label. `eff` lists the
  operations it may perform, each with the type arguments of its effect.
  `once` says that it may be called at most once. `env`, if given, says that
  it is a function that captured values of exactly these types: its
  environment, which another function written against the same environment
  can take over. -/
  | fn (params : List Ty) (ret : Ty) (eff : List (Nat × List Ty)) (once : Bool) (env : Option (List Ty))
  | ref (t : Ty)
  /-- The result of a call that does not return. No value has this type. -/
  | never
  deriving Inhabited, BEq, Hashable, Repr

def Ty.unit : Ty := .tuple []

/-- The operations something may perform, each with its effect's type
arguments. -/
abbrev Row := List (Nat × List Ty)

/-- A function's signature: what it is made with, given, gives and performs. -/
structure FnSig where
  caps : List Ty
  params : List Ty
  ret : Ty
  eff : Row
  deriving BEq, Hashable, Inhabited

/-- What the lowering is told rather than left to find. -/
inductive Hint where
  /-- The type of the value a `let` binds, a call that does not return
  gives, or a host operation past the first two gives. -/
  | ty (σ : Ty)
  /-- What a handler yields, and the operations it serves, in the handler's
  order, each with the type arguments of its effect. -/
  | handler (ρ : Ty) (H : Row)
  deriving BEq, Hashable, Inhabited

/-- One use of a declared data type: at these arguments, its constructors with
their field types. -/
structure DataInst where
  name : Nat
  args : List Ty
  ctors : List (Nat × List Ty)
  deriving BEq, Hashable

/-- An operation of an effect used at some type arguments: what it takes, and
what it is resumed with if it can be resumed. -/
structure OpInst where
  op : Nat
  args : List Ty
  payload : List Ty
  result : Option Ty
  deriving BEq, Hashable

/-- A function at a signature, with the hints of each of its clauses. -/
structure SigEntry where
  fn : Nat
  sig : FnSig
  hints : List (List Hint)

/-- Core's types: each function at each signature it is used at, the
declared types and operations those use, and `main`'s. -/
structure Types where
  sigs : Array SigEntry
  datas : List DataInst
  ops : List OpInst
  mainTy : Ty
  mainHints : List Hint
  /-- Where in `sigs` each function's signatures are (`Types.withIndex`). -/
  byFn : Array (List Nat) := #[]

/-- Each function's signatures, where they are in `sigs`. -/
def Types.withIndex (C : Types) : Types :=
  let n := C.sigs.foldl (fun m e => max m (e.fn + 1)) 0
  let byFn := (C.sigs.toList.zipIdx.foldr (fun (e, i) (acc : Array (List Nat)) =>
    acc.modify e.fn (i :: ·)) (Array.replicate n []))
  { C with byFn }

/-- The signatures of `fn`. -/
def Types.sigsOf (C : Types) (fn : Nat) : List SigEntry :=
  if C.byFn.isEmpty then C.sigs.toList.filter (·.fn == fn)
  else ((C.byFn[fn]?).getD []).filterMap fun i => C.sigs[i]?

/-- A declared type's constructors at these arguments. -/
def findData (ds : List DataInst) (name : Nat) (args : List Ty) : Option (List (Nat × List Ty)) :=
  (ds.find? fun d => d.name == name && d.args == args).map (·.ctors)

/-- An operation's payload and result at its effect's arguments. -/
def findOp (os : List OpInst) (op : Nat) (args : List Ty) : Option (List Ty × Option Ty) :=
  (os.find? fun o => o.op == op && o.args == args).map fun o => (o.payload, o.result)

/-- The fields of the `[T; N]` constructor `tag` builds, if it is that of these
arguments. -/
def fixedFields (tag : Nat) : List Ty → Option (List Ty)
  | [t, .data len []] =>
    if lenBase ≤ len && tag == fixedBase + (len - lenBase) then some (List.replicate (len - lenBase) t) else none
  | _ => none

/-- The field types of a constructor of a declared type, or of a `[T; N]`. -/
def Types.fields (C : Types) (tag name : Nat) (args : List Ty) : Option (List Ty) :=
  if name = fixedName then fixedFields tag args
  else (findData C.datas name args).bind (·.lookup tag)

/-- The field types of constructor `tag` at a type, if it is a constructor of
that type. -/
def ctorFieldsOf (C : Types) (tag : Nat) : Ty → Option (List Ty)
  | .tuple Fs => if tag = 0 then some Fs else none
  | .data name args => if tag = 0 then none else C.fields tag name args
  | _ => none

/-- The fields that can be read from a value of a type without testing which
constructor built it. -/
def fieldsOf (C : Types) : Ty → Option (List Ty)
  | .tuple Fs => some Fs
  | .data name args =>
    if name = fixedName then
      match args with
      | [_, .data len []] => fixedFields (fixedBase + (len - lenBase)) args
      | _ => none
    else
      match findData C.datas name args with
      | some ((_, Fs) :: rest) => if rest.all (fun c => c.2 == Fs) then some Fs else none
      | _ => none
  | _ => none

/-- The type of the place a path of fields reaches. -/
def placeTy (C : Types) : Ty → List Nat → Option Ty
  | τ, [] => some τ
  | τ, i :: path =>
    match fieldsOf C τ with
    | some Fs =>
      match Fs[i]? with
      | some σ => placeTy C σ path
      | none => none
    | none => none

/-- The type of a `[T; N]`'s elements, if this is the type of one. -/
def fixedElem : Ty → Option Ty
  | .data name [t, _] => if name = fixedName then some t else none
  | _ => none

mutual

/-- The types a pattern binds from a value of type `τ`. -/
def patTys (C : Types) : Pat → Ty → Option (List Ty)
  | .wild, _ => some []
  | .bind, τ => some [τ]
  | .int _, τ => match τ with
    | .int | .scalar _ => some []
    | _ => none
  | .ctor tag ps, T =>
    match ctorFieldsOf C tag T with
    | some Fs => patsTys C ps Fs
    | none => none

def patsTys (C : Types) : List Pat → List Ty → Option (List Ty)
  | [], [] => some []
  | p :: ps, τ :: τs =>
    match patTys C p τ, patsTys C ps τs with
    | some B, some Bs => some (B ++ Bs)
    | _, _ => none
  | [], _ :: _ => none
  | _ :: _, [] => none

end

/-- The signature of what destroys a closure of a function at `sig`: given
what the closure captured. -/
def dropSig (sig : FnSig) : FnSig := { caps := [], params := sig.caps, ret := .unit, eff := [] }

end Glorious.Lower
