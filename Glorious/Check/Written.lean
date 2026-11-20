module

public import Glorious.Check.Program

public section

namespace Glorious.Check

open Syntax

/-!
# A function's type, written as its signature

What the checker found of a function, written as the language writes a
signature: its type parameters, what it is given and gives, what it performs,
and what it asks of its type parameters. For writing the signatures of
functions written without them (`glorious signatures`).
-/

/-- A function's signature as written: its type parameters, each parameter's
type, its result, what it performs, and what it asks. -/
structure Written where
  generics : List String
  params : List String
  ret : String
  effects : String
  asks : List String

/-- How the type variables, rows and type parameters of one signature are
named. -/
structure Names where
  tys : List (Nat × String) := []
  rows : List (Nat × String) := []
  /-- Something the language cannot write was met. -/
  unwritable : Option String := none

private def letters : List String :=
  ["T", "U", "V", "W", "X", "Y", "Z", "A", "B", "C", "D", "F", "G", "H", "K", "L", "M", "N", "P", "Q", "R", "S"]

private def nextName (taken : List String) : String :=
  match letters.find? (!taken.contains ·) with
  | some l => l
  | none => s!"T{taken.length}"

/-- A declared type's name as a program writes it: the library's and the
prelude's by their last name, a program's by its whole path. -/
def typeName (n : String) : String :=
  let b := bareName n
  if b.startsWith "std::" || b.startsWith "core::" || b.startsWith "alloc::" || b.startsWith "prelude::" then
    Syntax.lastSegment b
  else b

mutual

/-- A type as the language writes it, naming each variable as it is met. -/
partial def writeTy (t : Ty) : StateT Names M String := do
  match ← (find t : M Ty) with
  | .var v =>
    match (← get).tys.lookup v with
    | some n => pure n
    | none =>
      let taken := ((← get).tys.map (·.2))
      let n := nextName taken
      modify fun s => { s with tys := s.tys ++ [(v, n)] }
      pure n
  | .con n [] =>
    if n.startsWith "'" then
      let p := bareName n
      unless ((← get).tys.map (·.2)).contains p do
        modify fun s => { s with tys := s.tys ++ [(0, p)] }
      pure p
    else if bareName n == Syntax.neverParam then pure "!"
    else if n.startsWith "%" then
      modify fun s => { s with unwritable := some n }
      pure "_"
    else pure (typeName n)
  | .con n [subject, .con tr targs, .con name gargs] =>
    if n == Syntax.projMark then
      -- (Of a trait with arguments, the subject is the type with them after
      -- it, as a tuple.)
      let arity := ((← (get : M St)).traitShape[tr]?).map (·.1) |>.getD 0
      let (self, targs) ← match ← (find subject : M Ty) with
        | .tuple (self :: rest) => pure (if arity > 0 && rest.length == arity then (self, rest) else (subject, targs))
        | _ => pure (subject, targs)
      let ta ← targs.mapM writeTy
      let ga ← gargs.mapM writeTy
      let trait := typeName tr
      let trait := if ta.isEmpty then trait else s!"{trait}<{", ".intercalate ta}>"
      let gat := if ga.isEmpty then "" else s!"<{", ".intercalate ga}>"
      pure s!"<{← writeTy self} as {trait}>::{name}{gat}"
    else
      let last := typeName n
      pure s!"{last}<{", ".intercalate (← [subject, .con tr targs, .con name gargs].mapM writeTy)}>"
  | .con n args =>
    let last := typeName n
    match last, args with
    | "Result", [ok, err] =>
      match ← (find err : M Ty) with
      | .tuple [] =>
        match ← (find ok : M Ty) with
        | .tuple [] => pure "Bool"
        | _ => pure s!"Option<{← writeTy ok}>"
      | _ => pure s!"Result<{← writeTy ok}, {← writeTy err}>"
    | "Array", [element] => pure s!"[{← writeTy element}]"
    | _, _ =>
      if n.startsWith "%" then
        modify fun s => { s with unwritable := some n }
      pure s!"{last}<{", ".intercalate (← args.mapM writeTy)}>"
  | .tuple [one] => pure s!"({← writeTy one},)"
  | .tuple args => pure s!"({", ".intercalate (← args.mapM writeTy)})"
  | .fn ps r effs tail _ =>
    let sig := s!"fn({", ".intercalate (← ps.mapM writeTy)}) -> {← writeTy r}"
    let e ← writeEffs effs tail
    pure (if e.isEmpty then sig else s!"{sig} / {e}")
  | .ref how t _ =>
    match ← (find how : M Ty) with
    -- (A lifetime given to a type: written so where none is named.)
    | .con "'" [] => pure "'_"
    | .con "&mut" [] => pure s!"&mut {← writeTy t}"
    | _ => pure s!"&{← writeTy t}"

/-- What a callable performs, `{Log, Ask<Int> | e}`, or nothing where it
performs nothing. -/
partial def writeEffs (effs : List (String × List Ty)) (tail : Option Nat) : StateT Names M String := do
  let named ← effs.mapM fun (e, args) => do
    let n := Syntax.lastSegment e
    if args.isEmpty then pure n else pure s!"{n}<{", ".intercalate (← args.mapM writeTy)}>"
  let row ← match tail with
    | some r =>
      let r ← (flattenRow ⟨[], some r⟩ : M Row)
      match r.tail with
      | some v =>
        match (← get).rows.lookup v with
        | some n => pure (some n)
        | none =>
          let count := (← get).rows.length
          let n := if count == 0 then "e" else s!"e{count}"
          modify fun s => { s with rows := s.rows ++ [(v, n)] }
          pure (some n)
      | none => pure none
    | none => pure none
  match named, row with
  | [], none => pure ""
  | _, none => pure ("{" ++ ", ".intercalate named ++ "}")
  | [], some r => pure ("{| " ++ r ++ "}")
  | _, some r => pure ("{" ++ ", ".intercalate named ++ " | " ++ r ++ "}")

end

/-- The signature of a function whose scheme is `s`, or why it cannot be
written. `named`: type variables named already, an implementation's type
parameters, which are not the function's own. -/
def writeSignature (s : Scheme) (named : List (Nat × String) := []) : M (Except String Written) := do
  let ty ← zonk s.ty
  let .fn ps r effs tail _ := ty | return .error "not a function"
  let act : StateT Names M (List String × String × String × List String) := do
    -- (What an implementation leaves to be found, and the function does not
    -- choose, by its projection: `<F as Trait<S>>::Out`.)
    for (tr, subject, name, v) in s.assocs do
      if let .var r ← (find v : M Ty) then
        unless (← get).tys.any (·.1 == r) do
          let shown ← match ← (find subject : M Ty) with
            | .tuple (self :: targs) =>
              pure s!"<{← writeTy self} as {typeName tr}<{", ".intercalate (← targs.mapM writeTy)}>>::{name}"
            | t => pure s!"<{← writeTy t} as {typeName tr}>::{name}"
          modify fun n => { n with tys := (r, shown) :: n.tys }
    let params ← ps.mapM writeTy
    let ret ← writeTy r
    -- (A row of effects of its own that nothing it is given performs is
    -- what its body performs: not written, and so nothing.)
    let rowsGiven := (← get).rows.map (·.1)
    let own ← match tail with
      | some v => do
        let row ← (flattenRow ⟨[], some v⟩ : M Row)
        pure (match row.tail with
          | some t => if rowsGiven.contains t then tail else none
          | none => none)
      | none => pure none
    let effects ← writeEffs effs own
    let facts ← ((s.dups.map (("%dup", ·))) ++ (s.drops.map (("%drop", ·))) ++ (s.stays.map (("%stay", ·))) ++ (s.quiets.map (("%quiet", ·)))).mapM fun (k, t, _) => do
      pure s!"{k} {← writeTy t}"
    let asks ← s.bounds.mapM fun (tr, t) => do
      match ← (find t : M Ty) with
      | .tuple (self :: targs) =>
        pure s!"{← writeTy self}: {typeName tr}<{", ".intercalate (← targs.mapM writeTy)}>"
      | _ => pure s!"{← writeTy t}: {typeName tr}"
    pure (params, ret, effects, asks ++ facts)
  -- (Each named variable by what it now stands for.)
  let named ← named.filterMapM fun (v, n) => do
    match ← find (.var v) with
    | .var r => pure (some (r, n))
    | _ => pure none
  let ((params, ret, effects, asks), names) ← act.run { tys := named }
  if let some what := names.unwritable then
    return .error s!"its type has `{what}` in it, which no program writes"
  let own := names.tys.filter fun (v, n) => !named.any (·.1 == v) && !n.startsWith "<"
  let generics := own.map (·.2) ++ names.rows.map fun (_, n) => s!"{n}: EffectRow"
  pure (.ok ⟨generics, params, ret, effects, asks⟩)

/-- A trait's function as declared, for an implementation to restate: `Self`
for the type it is for, `%P0`, `%P1`, .. for the trait's own parameters (the
implementation's arguments go there), `Self::Name` for what the trait leaves
to the implementation, and its own type parameters by name. -/
def writeMethod (ms : MethodSig) : M (Except String Written) := do
  let named : List (Nat × String) := [(ms.self, "Self")]
    ++ ms.tparams.zipIdx.map (fun (v, i) => (v, s!"%P{i}"))
    ++ ms.assocs.map (fun (n, v) => (v, s!"Self::{n}"))
    ++ ms.mparams.map (fun (n, v) => (v, n))
  let act : StateT Names M (List String × String × String) := do
    let params ← ms.params.mapM writeTy
    let ret ← writeTy ms.ret
    let effects ← writeEffs ms.row.effs ms.row.tail
    pure (params, ret, effects)
  let rows ← ms.rowAssocs.filterMapM fun (n, v) => do
    match (← flattenRow ⟨[], some v⟩).tail with
    | some r => pure (some (r, s!"Self::{n}"))
    | none => pure none
  let ((params, ret, effects), names) ← act.run { tys := named, rows }
  if let some what := names.unwritable then
    return .error s!"its type has `{what}` in it, which no program writes"
  let own := names.tys.filter fun (v, _) => !named.any (·.1 == v)
  -- (A type the trait leaves to implementations at types, `Got<'a>`, is
  -- not written here.)
  unless own.isEmpty do return .error "it has a type the trait leaves to implementations at types"
  pure (.ok ⟨ms.mparams.map (·.1), params, ret, effects, []⟩)

/-- Each trait's functions as declared (`writeMethod`), by `Trait::name`. -/
def writtenMethods (st : St) : List (String × Except String Written) :=
  st.methods.toList.filterMap fun (name, ms) =>
    match (writeMethod ms).run st with
    | .ok (w, _) => some (s!"{ms.trait}::{name}", w)
    | .error _ => none

/-- The signature of each function a state has checked, by its name, that is
not the library's or the prelude's: written, or why not. -/
def writtenSignatures (st : St) (library : Bool := false) : List (String × Except String Written) :=
  let names := st.fns.toList.filter fun (name, _) =>
    library || (!libraryOwner name && !(st.modules.homes.lookup name).any (· == "%prelude"))
  let sorted := names.mergeSort fun a b => a.1 ≤ b.1
  -- (A function an implementation gives: its type parameters are the
  -- implementation's, by their names.)
  let implParams : Std.HashMap String (List (Nat × String)) := st.impls.foldl (fun m im =>
    im.methods.foldl (fun m item => match item with
      | .fn f _ _ _ _ => m.insert (Syntax.implFnName im.trait im.head (Syntax.lastSegment f)) (im.pvars.map fun (p, v) => (v, p))
      | _ => m) m) {}
  sorted.filterMap fun (name, scheme) =>
    match (writeSignature scheme (implParams.getD name [])).run st with
    | .ok (w, _) => some (name, w)
    | .error _ => none

end Glorious.Check
