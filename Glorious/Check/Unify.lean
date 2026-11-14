module

public import Glorious.Check.Types

public section

namespace Glorious.Check

open Syntax

/-! ## Unification -/

def bindTy (id : Nat) (t : Ty) : M Unit := do
  if (freeTys (← zonk t)).contains id then
    throw "this would need a type that contains itself"
  modify fun s => { s with tys := s.tys.set! id (some t) }

def bindRow (id : Nat) (r : Row) : M Unit :=
  modify fun s => { s with rows := s.rows.set! id (some r) }

/-- Can two types never be the same, whatever what is still unknown in them
turns out to be? Two instances of an effect whose arguments are apart are two
effects (`Store<Int>`, `Store<Str>`); a function's own type parameters are
each apart from the other and from every type that is not a parameter. -/
partial def apart (a b : Ty) : M Bool := do
  match ← find a, ← find b with
  | .var _, _ => pure false
  | _, .var _ => pure false
  | .con n as, .con m bs =>
    if n != m || as.length != bs.length then pure true else anyApart as bs
  | .tuple as, .tuple bs => if as.length != bs.length then pure true else anyApart as bs
  | .fn ps r _ _ _, .fn qs s _ _ _ =>
    if ps.length != qs.length then pure true else anyApart (r :: ps) (s :: qs)
  | .ref _ x _, .ref _ y _ => apart x y
  | _, _ => pure true
where
  anyApart (as bs : List Ty) : M Bool := (as.zip bs).anyM fun (x, y) => apart x y

/-- Are the two written the same, as far as each is known? -/
partial def sameTy (a b : Ty) : M Bool := do
  match ← find a, ← find b with
  | .var i, .var j => pure (i == j)
  | .con n as, .con m bs => if n != m || as.length != bs.length then pure false else all as bs
  | .tuple as, .tuple bs => if as.length != bs.length then pure false else all as bs
  | .fn ps r _ _ _, .fn qs s _ _ _ =>
    if ps.length != qs.length then pure false else all (r :: ps) (s :: qs)
  | .ref _ x _, .ref _ y _ => sameTy x y
  | _, _ => pure false
where
  all (as bs : List Ty) : M Bool := (as.zip bs).allM fun (x, y) => sameTy x y

/-- The instance of an effect among those of a row that one named here is:
the one written the same; or, failing that, the one it could be. Where it
could be either of two that are themselves apart, which is meant has to be
said. None if every instance of the effect in the row is another. -/
def findInstance (effs : List (String × List Ty)) (e : String × List Ty) :
    M (Option (Nat × List Ty)) := do
  let named := (effs.zipIdx.filter fun ((n, args), _) => n == e.1 && args.length == e.2.length)
  let mut could : List (Nat × List Ty) := []
  for ((_, args), i) in named do
    if ← (args.zip e.2).allM fun (x, y) => sameTy x y then return some (i, args)
    unless ← (args.zip e.2).anyM fun (x, y) => apart x y do could := could ++ [(i, args)]
  match could with
  | [] => pure none
  | [one] => pure (some one)
  | first :: rest =>
    for (_, other) in rest do
      if ← (first.2.zip other).anyM fun (x, y) => apart x y then
        throw s!"which `{e.1}` is meant is not known here, and there are several: write the operation with its types, as in `operation<Type>(..)`"
    pure (some first)

mutual

partial def unify (a b : Ty) : M Unit := do
  let a ← find a
  let b ← find b
  match a, b with
  | .var i, .var j => if i == j then pure () else bindTy i b
  | .var i, _ => bindTy i b
  | _, .var j => bindTy j a
  | .con n as, .con m bs =>
    if n == m && as.length == bs.length then unifyAll as bs else mismatch a b
  | .tuple as, .tuple bs => if as.length == bs.length then unifyAll as bs else mismatch a b
  | .fn ps r e1 t1 c1, .fn qs s e2 t2 c2 =>
    if ps.length == qs.length then do
      unifyAll ps qs
      unify r s
      unifyRow ⟨e1, t1⟩ ⟨e2, t2⟩
      unifyCap c1 c2
    else mismatch a b
  | .ref h1 x c1, .ref h2 y c2 => do
    try unify h1 h2
    catch _ => mismatch a b
    unify x y
    unifyCap c1 c2
  | _, _ => mismatch a b

partial def mismatch (a b : Ty) : M Unit := do
  throw s!"`{showTy (← zonk a)}` is not `{showTy (← zonk b)}`"

partial def unifyAll (as bs : List Ty) : M Unit := do
  for (a, b) in as.zip bs do
    unify a b

/-- Unify two effect rows as sets of effects. -/
partial def unifyRow (r1 r2 : Row) : M Unit := do
  let r1 ← flattenRow r1
  let r2 ← flattenRow r2
  let e1 ← collapse r1.effs
  let e2 ← collapse r2.effs
  -- Each effect of the one with the instance of it the other has, if any.
  let mut taken : List Nat := []
  let mut only1 : List (String × List Ty) := []
  for (n, args) in e1 do
    let left := e2.zipIdx.filterMap fun (e, i) => if taken.contains i then none else some e
    match ← findInstance left (n, args) with
    | some (k, args') =>
      unifyAll args args'
      -- (`k` counts among those not yet taken.)
      let at_ := ((List.range e2.length).filter (!taken.contains ·))[k]?.getD k
      taken := at_ :: taken
    | none => only1 := only1 ++ [(n, args)]
  let only2 := e2.zipIdx.filterMap fun (e, i) => if taken.contains i then none else some e
  let unhandled := fun (e : String × List Ty) =>
    (throw s!"effect `{e.1}` is not handled here" : M Unit)
  match r1.tail, r2.tail with
  | none, none =>
    match only1 ++ only2 with
    | e :: _ => unhandled e
    | [] => pure ()
  | some i, none =>
    match only1 with
    | e :: _ => unhandled e
    | [] => bindRow i ⟨only2, none⟩
  | none, some j =>
    match only2 with
    | e :: _ => unhandled e
    | [] => bindRow j ⟨only1, none⟩
  | some i, some j =>
    if i == j then
      match only1 ++ only2 with
      | e :: _ => unhandled e
      | [] => pure ()
    else do
      let k ← freshRowVar
      bindRow i ⟨only2, some k⟩
      bindRow j ⟨only1, some k⟩

/-- A row names each instance of an effect once. -/
partial def collapse (effs : List (String × List Ty)) : M (List (String × List Ty)) := do
  let mut out : List (String × List Ty) := []
  for (n, args) in effs do
    let again ← out.anyM fun (m, args') =>
      if m == n && args.length == args'.length then (args.zip args').allM fun (x, y) => sameTy x y
      else pure false
    unless again do out := out ++ [(n, args)]
  pure out

end

/-- Unify, reporting a failure as a mismatch between what was expected and found. -/
def unifyAt (what : String) (expected actual : Ty) : M Unit := do
  try unify expected actual
  catch e =>
    let detail := if e.startsWith "effect" || e.startsWith "this would" || e.startsWith "lifetime"
      then s!" ({e})" else ""
    throw s!"{what}: expected `{showTy (← zonk expected)}`, found `{showTy (← zonk actual)}`{detail}"

/-! ## The effects of a callee

A callee may perform fewer effects than are permitted where it is called. Its
named effects are required of the caller at once. If the rest of its effects is
still unknown, the call is remembered, and at the end of the function each
unknown is given the most that every place it is called from permits. Making a
callee's effects equal to its caller's instead would wrongly tie together two
calls of one function value made under different handlers.
-/

/-- The named effects of a callee must be permitted where it is called. -/
def includeNamed (callee amb : Row) (what : String) : M Unit := do
  let c ← flattenRow callee
  for (e, args) in ← collapse c.effs do
    let a ← flattenRow amb
    try
      match ← findInstance a.effs (e, args) with
      | some (_, args') => unifyAll args args'
      | none => unifyRow amb ⟨[(e, args)], some (← freshRowVar)⟩
    catch err => throw s!"{what} cannot be called here: {err}"

/-- The callee's unknown remaining effects, unless they are the caller's own. -/
def openTail (callee amb : Row) : M (Option Nat) := do
  let c ← flattenRow callee
  let a ← flattenRow amb
  match c.tail with
  | none => pure none
  | some ρ => pure (if a.tail == some ρ then none else some ρ)

/-- The rows a function is given by whoever uses it: its row parameters. -/
def paramTails : M (List (Nat × String)) := do
  let mut out : List (Nat × String) := []
  for (_, rowParams) in (← get).rowChecks do
    for (e, carrier) in rowParams do
      if let .fn [] _ [] (some k) _ ← find carrier then
        let r ← flattenRow ⟨[], some k⟩
        if r.effs.isEmpty then
          if let some ρ := r.tail then out := (ρ, e) :: out
  pure out

/-- The rows of effects that are someone else's to say: a function's row
parameters, and those left to implementations not yet known, which is what a
trait says a type parameter performs. Each stays a row of its own, and is
not made the row of where it is performed: two of them performed in one
function are then two, and the function performs both. -/
def assocTails : M (List Nat) := do
  let mut out : List Nat := (← paramTails).map (·.1)
  for (_, _, _, a, _, _) in (← get).assocUses do
    if let .fn [] _ [] (some k) _ ← find a then
      let r ← flattenRow ⟨[], some k⟩
      if r.effs.isEmpty then
        if let some ρ := r.tail then out := ρ :: out
  pure out

def includeRow (callee amb : Row) (what : String) : M Unit := do
  includeNamed callee amb what
  if (← openTail callee amb).isSome then
    modify fun s => { s with rowIncl := s.rowIncl.push (callee, amb, s.pos ++ what) }

/--
Work through the remembered calls. Named effects are always passed on. With
`bind`, an unknown that `bind` accepts is then decided, newest first, since an
inner unknown should give way before an outer one: if every place it is called
from has the same remaining effects, it gets the named effects common to them
all; otherwise, and only when `final`, it is made equal to each in turn.
-/
partial def settleRows (bind : Option (Nat → Bool)) (final : Bool) : M Unit := do
  let pending := (← get).rowIncl
  modify fun s => { s with rowIncl := #[] }
  let mut left : Array (Row × Row × String × Nat) := #[]
  for (callee, amb, what) in pending do
    includeNamed callee amb what
    if let some ρ ← openTail callee amb then left := left.push (callee, amb, what, ρ)
  let restore : M Unit :=
    modify fun s => { s with rowIncl := left.map (fun (c, a, w, _) => (c, a, w)) ++ s.rowIncl }
  match bind with
  | none => restore
  | some ok =>
    let held ← assocTails
    let candidates := ((left.toList.map (·.2.2.2)).eraseDups.filter fun ρ =>
      ok ρ && !held.contains ρ).mergeSort (· ≥ ·)
    for ρ in candidates do
      let mine := left.toList.filter (·.2.2.2 == ρ)
      let ambs ← mine.mapM fun (_, amb, _, _) => flattenRow amb
      match ambs with
      | [] => pure ()
      | first :: _ =>
        if ambs.all (·.tail == first.tail) && first.tail != some ρ then
          let common ← (← collapse first.effs).filterM fun e =>
            ambs.allM fun a => do pure (← findInstance a.effs e).isSome
          modify fun s => { s with rows := s.rows.set! ρ (some ⟨common, first.tail⟩) }
          restore
          return ← settleRows bind final
        else if final then
          for (callee, amb, what, _) in mine do
            try unifyRow callee amb
            catch err => throw s!"{what} cannot be called here: {err}"
          restore
          return ← settleRows bind final
    restore

end Glorious.Check
