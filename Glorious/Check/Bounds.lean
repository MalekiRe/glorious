module

public import Glorious.Trace
public import Glorious.Check.Expr

public section

namespace Glorious.Check

open Syntax

/-! ## Programs -/

/-! ## Traits

A bound is a trait needed of a type. Where the type is made with a name, an
implementation meets it, on its conditions; where it is one the function is
generic in, the function is given the evidence, and so needs the bound of
whoever calls it. -/

/-- Whose a function's type parameters are. Its own; or, for functions that
call each other, the group's: a parameter two of them write with one name
is then one type to both, which is what lets one call the other with what
it was given. -/
def rigidOwner (decls : List FnDecl) (d : FnDecl) : String :=
  if d.impl.isSome then d.name else
  match decls.filter (·.impl.isNone) with
  | first :: _ :: _ => first.name
  | _ => d.name

/-- The number `Traits.solve` knows a type by, if it is one a function is
generic in: a type nothing has decided, or one of the function's own type
parameters. -/
def keyOf (t : Ty) : M (Option Nat) := do
  let numbered := fun (r : Rigid) => do
    let s ← get
    match s.rigidAt[r]? with
    | some i => pure (some (2 * i + 1))
    | none =>
      let i := s.rigidKeys.size
      modify fun s => { s with rigidKeys := s.rigidKeys.push r, rigidAt := s.rigidAt.insert r i }
      pure (some (2 * i + 1))
  match ← find t with
  | .var id => pure (some (2 * id))
  | .rigid r => numbered r
  -- (A lifetime's mark, `'`, as a type of its own.)
  | .con n [] => if n.startsWith "'" then numbered (.param n "") else pure none
  | _ => pure none

/-- The number a condition said in `owner` of a type made from type
parameters is known by, `'%condition:owner:key:type`, kept also under
`key:type` (`conditionKeys`). -/
def conditionKey (owner : String) (key : Syntax.TraitKey) (t : Ty) : M (Option Nat) := do
  let written ← keyTy t
  let r := Rigid.cond owner key written
  let known := (← get).rigidAt.contains r
  let k ← keyOf (.rigid r)
  unless known do
    if let some i := (← get).rigidAt[r]? then
      modify fun s => { s with conditionsAt := s.conditionsAt.alter (key, written) fun
        | some is => some (i :: is)
        | none => some [i] }
  pure k

partial def toSTy (t : Ty) : M Traits.STy := do
  let t ← find t
  match ← keyOf t with
  | some k => pure (.var k)
  | none =>
    match t with
    -- (What an `is` found is a tuple of it, `Elab`'s `.pack`.)
    | .con n args =>
      if (Syntax.packNames n).isSome then pure (.con s!"(tuple{args.length})" (← args.mapM toSTy))
      else pure (.con n (← args.mapM toSTy))
    | .tuple args => pure (.con s!"(tuple{args.length})" (← args.mapM toSTy))
    | .fn _ _ _ _ _ => pure (.con "(callable)" [])
    | .ref _ _ _ => pure (.con "(reference)" [])
    | .rigid r => pure (.con r.spelled [])
    | .var _ => pure (.var 0)

/-- The numbers under which a condition of an implementation on a type made
from its type parameters, `where (A, (B, ())): Fetch<W>`, is known in the
implementation's functions: one for each function it was said in. -/
def conditionKeys (key : Syntax.TraitKey) (t : Ty) : M (List Nat) := do
  let said := (key, ← keyTy (← zonk t))
  let found := (((← get).conditionsAt[said]?).getD []).reverse.map (2 * · + 1)
  if !found.isEmpty then return found
  -- (Of what a trait leaves to an implementation, not known here: the
  -- condition written of it, `where <H as Assoc>::Out: Act`.)
  let some p ← projectionOf t | return []
  let said := (key, ← keyTy p)
  pure ((((← get).conditionsAt[said]?).getD []).reverse.map (2 * · + 1))


/-- The conditions written of what a trait leaves to an implementation,
`where <H as Assoc>::Out: Act`, where `t` is that. -/
def projectedCondition (key : Syntax.TraitKey) (t : Ty) : M (List Nat) := do
  match ← find t with
  | .con n _ => if n == Syntax.projMark then conditionKeys key t else pure []
  | .var _ => if (← projectionOf t).isSome then conditionKeys key t else pure []
  | _ => pure []

/-- The type an implementation is for, as it writes it: `W<T>`, `(H, R)`. -/
def implShown (im : ImplDecl) : String :=
  if im.head.startsWith "(tuple" then s!"({", ".intercalate im.params})"
  else if im.params.isEmpty then im.head
  else s!"{im.head}<{", ".intercalate im.params}>"

/-- How often an implementation chosen for a type uses a value of each of its
type parameters, as its where says, `T: Use<[0, *]>`, at most once where it
says nothing: asked of what each is there. -/
def askUses (im : ImplDecl) (at_ : List (Nat × Ty)) (pos : String) : M Unit := do
  if im.trait == Syntax.destroyKey then return
  for (p, id) in im.pvars do
    if let some t := at_.lookup id then
      let (lower, upper) := (im.uses.lookup p).getD (0, some 1)
      if lower == 0 || upper.isNone then
        -- (Said as the implementation writes its type, which names the
        -- parameter: not the type here, which would be spelled each time.)
        let whose := s!"{pos}the implementation of `{im.trait.shown}` for `{implShown im}`"
        if lower == 0 then
          modify fun s => { s with drops := s.drops.push (t, s!"{whose} may leave a `{p}` unused") }
        if upper.isNone then
          modify fun s => { s with dups := s.dups.push (t, s!"{whose} may use a `{p}` more than once") }

/-- The bounds on types a function is generic in that a bound comes down to,
each with the number of its type. This is only to say what a function needs
and to explain a failure: the evidence itself is `Traits.solve`'s. -/
partial def leaves (pos : String) (trait : Syntax.TraitKey) (t : Ty) : M (List (Syntax.TraitKey × Nat × Ty)) := do
  let t ← find t
  -- (What a trait leaves to an implementation, not known here, of which a
  -- condition is written: that condition.)
  if let k :: _ ← projectedCondition trait t then return [(trait, k, t)]
  match ← keyOf t with
  | some k => pure [(trait, k, t)]
  | none =>
    let missing : M (List (Syntax.TraitKey × Nat × Ty)) := do
      throw s!"{pos}`{showTy (← zonk t)}` does not implement `{trait}`"
    -- (Its head's: a name, a tuple, a callable, a reference; of how a
    -- value is destroyed, one for every callable and every reference.)
    let head ← match t with
      | .fn .. => pure (if trait == Syntax.destroyKey then some ("(callable)", []) else t.head)
      | .ref .. => pure (if trait == Syntax.destroyKey then some ("(reference)", []) else t.head)
      | t => headFor trait.base t
    match head with
    | some (n, args) =>
      match (← get).kimpls.find trait n args.length with
      | some (i, I) =>
        if let some im := (← get).impls[i]? then askUses im (← implAt im args) pos
        let mut out : List (Syntax.TraitKey × Nat × Ty) := []
        for (tr', j) in I.context do
          out := out ++ (← leaves pos tr' (args[j]?.getD .unit))
        pure out
      | none => missing
    | none => missing

/-- `toDictE`, each dictionary object made once in a group's bounds: the same
one found for many calls (as `solveFitting` finds them) is the same value,
not a copy for each, in what the program is elaborated with and what is
kept of the checker. -/
partial def toDictEShared (impls : Array ImplDecl) (marker : String → Bool) (d : Traits.Dict) : M Elab.DictE := do
  if let some (_, e) := (← get).dictShared[addrOf d]? then return e
  let e ← match d with
    | .given k => pure (Elab.DictE.param k)
    | .impl i subs => do
      -- (Of a trait with no functions, every implementation is the same
      -- value, `()`: one, `Syntax.markerDict`, whatever its conditions are
      -- met by, which are not looked at.)
      if (impls[i]?.map fun im => marker (im.trait.base)).getD false then
        pure (Elab.DictE.impl Syntax.markerDict [])
      else
      let fn := (impls[i]?.map (·.dictFn)).getD ""
      let subs ← subs.mapM (toDictEShared impls marker)
      let key := (fn, subs.map addrOf)
      match (← get).dictByShape[key]? with
      | some e => pure e
      | none =>
        let e := Elab.DictE.impl fn subs
        modify fun s => { s with dictByShape := s.dictByShape.insert key e }
        pure e
  -- (What the implementation's type parameters are, where known: what its
  -- functions are written out at.)
  if let (.impl i _, some at_) := (d, (← get).fitParams[addrOf d]?) then
    if let some im := impls[i]? then
      unless (← get).dictTypes.contains (addrOf e) do
        -- (Those known whatever the function it is found in is given.)
        let written ← at_.filterMapM fun (k, t) => do
          let t ← zonk t
          if !(freeTys t).isEmpty || t.hasRigid then return none
          pure ((im.pvars.find? (·.2 == k)).bind fun (x, _) => t.writtenRigid.map (x, ·))
        unless written.isEmpty do
          modify fun s => { s with dictTypes := s.dictTypes.insert (addrOf e) written }
  modify fun s => { s with dictShared := s.dictShared.insert (addrOf d) (d, e) }
  pure e

partial def toDictE (impls : Array ImplDecl) : Traits.Dict → Elab.DictE
  | .given k => .param k
  | .impl i subs => .impl ((impls[i]?.map (·.dictFn)).getD "") (subs.map (toDictE impls))

instance : Inhabited Traits.STy := ⟨.var 0⟩

/-- A field's type as `Traits.solve` knows types, for finding how the field is
destroyed: a parameter of the declared type is known by its place among the
type's parameters. -/
partial def fieldSTy (tvars places : List Nat) : Ty → Traits.STy
  | .var id =>
    match (tvars.idxOf? id).bind (places[·]?) with
    | some j => .var j
    | none => .con "(reference)" []
  | .con n args => .con n (args.map (fieldSTy tvars places))
  | .tuple args => .con s!"(tuple{args.length})" (args.map (fieldSTy tvars places))
  | .fn _ _ _ _ _ => .con "(callable)" []
  | .ref _ _ _ => .con "(reference)" []
  | .rigid r => .con r.spelled []

/-- The types a value of this type directly holds. -/
def partsOf (t : Ty) : M (List Ty) := do
  match ← find t with
  | .tuple args => pure args
  | .con name args =>
    match (← get).types[name]? with
    | none => pure []
    | some decl =>
      decl.ctors.flatMapM fun c => do
        match (← get).ctors[c]? with
        | none => pure []
        | some sig => pure (sig.fieldsAt args)
  | _ => pure []

/-- Is there anything to do when a value of this type is destroyed: is it, or
does it hold, a value of a type with `Drop`? A type being asked about above
holds nothing more than was seen on the way. -/
partial def needsDestroying (seen : List String) (t : Ty) : M Bool := do
  match ← find t with
  | .tuple args => args.anyM (needsDestroying seen)
  | .fn _ _ _ _ cap =>
    -- A callable that holds something with a `drop` to run: giving it up
    -- runs them. And a resumption: giving it up runs the cleanups of the
    -- computation it suspended.
    let root ← findCap cap
    if (← edgesFrom root).any (fun (_, what) => match what with
        | .once => true
        | .must => true
        | _ => false) then return true
    -- (And in the program's own functions, one that holds a value of a type
    -- the function is generic in, which may have one: as what it holds is
    -- destroyed, `heldGeneric`.)
    if (← get).ownItems && !libraryOwner (← get).owner then
      for (_, what) in ← edgesFrom root do
        if let .ty held := what then
          if hasParam held then
            match ← find held with
            | .ref .. => pure ()
            | .fn .. => pure ()
            | _ => return true
    let before := (← get).seen
    modify fun s => { s with seen := {} }
    let held ← tyHasDrop [] t
    modify fun s => { s with seen := before }
    pure held.isSome
  | .con name args =>
    if (← get).kimpls.has (.of "Drop") name then return true
    let key ← spellTy (.con name args)
    if seen.contains key then return false
    (← partsOf (.con name args)).anyM (needsDestroying (key :: seen))
  | _ => pure false

/-- The name of the implementation a condition of another comes down to: the
trait itself, or the one chosen by fitting where there is a choice. -/
def subKey (trait : String) (ty : Ty) (args : List Ty) : M Syntax.TraitKey := do
  let several ← severalFor trait ((← headFor trait (← find ty)).map (·.1))
  if args.isEmpty && !several then pure (.of trait) else implKey trait ty args

/-- A condition's type and the trait's arguments with what traits leave to
implementations in them, `<H as Touches>::List`, found where it can be. -/
def unprojectedCondition (subject : Ty) (cargs : List Ty) : M (Ty × List Ty) := do
  let before := (← get).assocUses.size
  let subject ← unproject subject
  let cargs ← cargs.mapM unproject
  if (← get).assocUses.size != before then settleAssocsAll
  pure (subject, cargs)

/-- A type all known, as its number in the pool of such types (`St.tyIds`):
the same number for the same type, made of its head and its parts' numbers.
None where a part is not known yet. -/
partial def internTy (t : Ty) : M (Option Nat) := do
  if let some (_, n) := (← get).tyMemo[addrOf t]? then return some n
  let r ← internTyAt t
  if let some n := r then
    modify fun s => { s with tyMemo := s.tyMemo.insert (addrOf t) (t, n) }
  pure r
where
  internTyAt : Ty → M (Option Nat)
  | .con n args => do
    let some parts ← internAll args | return none
    poolId ("c" ++ n) parts
  | .tuple args => do
    let some parts ← internAll args | return none
    poolId "()" parts
  | .ref how inner cap => do
    let .con h [] ← find how | return none
    let some i ← internTy (← find inner) | return none
    poolId s!"&{h}'{← findCap cap}" [i]
  -- (A callable: what it takes and gives, what it performs, and what it
  -- holds, by the record of that.)
  | .fn ps r effs tail cap => do
    let some parts ← internAll ps | return none
    let some out ← internTy (← find r) | return none
    let row ← flattenRow ⟨effs, tail⟩
    let mut said : Array Nat := #[]
    for (e, as) in row.effs do
      let some ss ← internAll as | return none
      let some n ← poolId ("!" ++ e) ss | return none
      said := said.push n
    let rest := match row.tail with
      | some k => s!"|{k}"
      | none => ""
    poolId s!"fn'{← findCap cap}{rest}" (parts ++ [out] ++ said.toList)
  | _ => pure none
  internAll (ts : List Ty) : M (Option (List Nat)) := do
    let mut out := #[]
    for t in ts do
      let some s ← internTy (← find t) | return none
      out := out.push s
    pure (some out.toList)
  poolId (head : String) (parts : List Nat) : M (Option Nat) := do
    match (← get).tyIds[(head, parts)]? with
    | some n => pure (some n)
    | none =>
      let n := (← get).tyIdCount
      modify fun s => { s with tyIds := s.tyIds.insert (head, parts) n, tyIdCount := n + 1 }
      pure (some n)

/-- The type and arguments so numbered, where each can be. -/
def fitKey (ty : Ty) (args : List Ty) : M (Option (List Nat)) := internTy.internAll (ty :: args)

/-- A type's shape as far as destroying it goes: a part that nothing
decides, and that the function is not given how to destroy, holds nothing
to destroy. -/
def destroyShape (givens : Traits.Givens Syntax.TraitKey) : Traits.STy → Traits.STy
  | .var k => if givens.contains (Syntax.destroyKey, k) then .var k else .con "(reference)" []
  | .con n args => .con n (args.map (destroyShape givens))

mutual

/-- How a bound is met, where implementations are chosen by fitting types
(`St.patterned`): as `Traits.solve` finds it, but each condition of the
implementation found is looked for the same way, with the trait's arguments
and the type the implementation says. Not proved, as `Traits.solve` is: what
it finds is checked with the program's Core. -/
partial def solveFitting (givens : Traits.Givens Syntax.TraitKey) (fuel : Nat) (key : Syntax.TraitKey) (ty : Ty)
    (args : List Ty) : M (Option Traits.Dict) := do
  if fuel == 0 || key == Syntax.destroyKey then return ← solveFittingNow givens fuel key ty args
  -- (Found once in a group where the type is all known.)
  let some spelled ← fitKey ty args | solveFittingNow givens fuel key ty args
  let k := ((← get).owner, key, spelled, givens)
  if let some d := (← get).solvedFit[k]? then return d
  let d ← solveFittingNow givens fuel key ty args
  modify fun s => { s with solvedFit := s.solvedFit.insert k d }
  pure d

partial def solveFittingNow (givens : Traits.Givens Syntax.TraitKey) (fuel : Nat) (key : Syntax.TraitKey) (ty : Ty)
    (args : List Ty) : M (Option Traits.Dict) := do
  if fuel == 0 then return none
  let ty ← find ty
  if key == Syntax.destroyKey then
    -- How a value is destroyed: as before, by the type's shape alone.
    -- (Found once for each type in a group: the same dictionary object for
    -- each, so that it is written out once.)
    let sty := destroyShape givens (← toSTy ty)
    if let some d := (← get).destroyFit[(sty, givens)]? then return d
    let d := Traits.solveIx (← get).kimpls givens 100000 key sty
    modify fun s => { s with destroyFit := s.destroyFit.insert (sty, givens) d }
    return d
  for k in ← projectedCondition key ty do
    if let some g := Traits.findGiven key k givens then return some (.given g)
  if let some k ← keyOf ty then return (Traits.findGiven key k givens).map .given
  -- (What the function is given of a type made from its type parameters.)
  for k in ← conditionKeys key ty do
    if let some g := Traits.findGiven key k givens then return some (.given g)
  -- (A function that performs something is not one an implementation for
  -- functions is for: what is written of `Self` there performs nothing.)
  if let .fn _ _ effs tail _ := ty then
    try unifyRow ⟨effs, tail⟩ ⟨[], none⟩ catch _ => return none
  let some (h, hargs) ← headFor key.base ty | return none
  let some (i, _) := (← get).kimpls.find key h hargs.length | return none
  let some im := (← get).impls[i]? | return none
  let some at_ ← fitHead im hargs args | return none
  unless ← fitConditions im at_ hargs (← get).owner "" do return none
  let mut subs : List Traits.Dict := []
  for (tr, j) in im.context do
    let some arg := hargs[j]? | return none
    let some d ← solveFitting givens (fuel - 1) (← subKey tr arg []) arg []
      | return none
    subs := subs ++ [d]
  for (tr, cargs, subject) in im.extra do
    -- (A condition of a type a trait leaves to implementations,
    -- `<H as Touches>::List: Concat<..>`: of what that is here.)
    let (subject, cargs) ← unprojectedCondition (subst at_ [] [] subject) (cargs.map (subst at_ [] []))
    let some d ← solveFitting givens (fuel - 1) (← subKey tr subject cargs) subject cargs
      | return none
    subs := subs ++ [d]
  let d : Traits.Dict := .impl i subs
  modify fun s => { s with fitParams := s.fitParams.insert (addrOf d) at_ }
  pure (some d)

end

mutual

/-- `leaves`, where implementations are chosen by fitting types. -/
partial def leavesFitting (pos : String) (key : Syntax.TraitKey) (t : Ty) (args : List Ty) (owner : String := "")
    (via : List (String × Ty) := []) (asking : List ((Syntax.TraitKey × List Nat) × Ty) := []) : M (List (Syntax.TraitKey × Nat × Ty × List Ty)) := do
  if key == Syntax.destroyKey then
    -- (A type of nothing still to be found, and no type parameter: how it
    -- is destroyed asks nothing of anyone. What destroys it is found when
    -- the program is written, by its shape.)
    let z ← zonk t
    if (freeTys z).isEmpty && !z.hasRigid then return []
    return ← leavesFittingNow pos key t args owner via asking
  -- (Found once in a group where the type is all known; what is refused is
  -- said each time, with where it was asked. The same objects asked again,
  -- as the rest of a list is by each of its entries' implementations, are
  -- found by where they are, before they are spelled.)
  let t' ← find t
  let args' ← args.mapM find
  let at_ := (owner, key, addrOf t', args'.map addrOf)
  if let some (_, _, ls) := (← get).leavesAt[at_]? then return ls
  let some spelled ← fitKey t args | leavesFittingNow pos key t args owner via asking
  let k := (owner, key, spelled)
  if let some ls := (← get).leavesFit[k]? then
    modify fun s => { s with leavesAt := s.leavesAt.insert at_ (t', args', ls) }
    return ls
  -- (One asked again while it is being found: implementations whose
  -- conditions ask each other, which no answer ends.)
  let here := (key, spelled)
  if asking.any (·.1 == here) then
    let chain ← ((here, t) :: asking).reverse.mapM fun ((k, _), ty) => do pure s!"{k} of {showTy (← zonk ty)}"
    throw s!"{pos}`{key.shown}` of `{showTy (← zonk t)}` asks itself: its implementation's conditions come back to it ({" -> ".intercalate chain})"
  let ls ← leavesFittingNow pos key t args owner via ((here, t) :: asking)
  modify fun s => { s with leavesFit := s.leavesFit.insert k ls, leavesAt := s.leavesAt.insert at_ (t', args', ls) }
  pure ls

partial def leavesFittingNow (pos : String) (key : Syntax.TraitKey) (t : Ty) (args : List Ty) (owner : String := "")
    (via : List (String × Ty) := []) (asking : List ((Syntax.TraitKey × List Nat) × Ty) := []) : M (List (Syntax.TraitKey × Nat × Ty × List Ty)) := do
  let t ← find t
  -- (How a value is destroyed is found by the type's shape alone, as
  -- `solveFitting` finds it: no condition is left of what it finds.)
  if key == Syntax.destroyKey then
    if (← solveFitting [] 1 key t []).isSome then return []
    -- (Nor is it asked of a callable, which is given up whole, as it is
    -- not of a bound's own type.)
    if let .fn .. := t then return []
  if let k :: _ ← projectedCondition key t then return [(key, k, t, args)]
  if let some k ← keyOf t then return [(key, k, t, args)]
  -- (What the function is given of a type made from its type parameters:
  -- one made of none has none.)
  let t' ← zonk t
  if Ty.hasRigid t' then
    if let some i := (← get).rigidAt[Rigid.cond owner key (← keyTy t')]? then return [(key, 2 * i + 1, t, args)]
  -- (What it was asked for, where it is a condition of another: said only
  -- where it is refused.)
  let missing : M (List (Syntax.TraitKey × Nat × Ty × List Ty)) := do
    let mut ws : List String := []
    for (tr, ty) in via do ws := ws ++ [s!"`{tr}` of `{showTy (← zonk ty)}`"]
    let because := match ws with
      | [] => ""
      | ws => s!", which {", which ".intercalate (ws.map (· ++ " needs"))}"
    throw s!"{pos}`{showTy (← zonk t)}` does not implement `{key.shown}`{because}"
  if let .fn _ _ effs tail _ := t then
    try unifyRow ⟨effs, tail⟩ ⟨[], none⟩
    catch _ => throw s!"{pos}`{showTy (← zonk t)}` performs effects, and `{key.shown}` is implemented for functions that perform none"
  let some (h, hargs) ← headFor key.base t | missing
  let some (i, _) := (← get).kimpls.find key h hargs.length | missing
  let some im := (← get).impls[i]? | missing
  let some at_ ← fitHead im hargs args | missing
  unless ← fitConditions im at_ hargs owner pos do return ← missing
  askUses im at_ pos
  let mut out : List (Syntax.TraitKey × Nat × Ty × List Ty) := []
  let shown := key.shown
  let this := ((shown.takeWhile (· != '<')).toString, t)
  for (tr, j) in im.context do
    let arg := hargs[j]?.getD .unit
    out := out ++ (← leavesFitting pos (← subKey tr arg []) arg [] owner (this :: via) asking)
  for (tr, cargs, subject) in im.extra do
    let (subject, cargs) ← unprojectedCondition (subst at_ [] [] subject) (cargs.map (subst at_ [] []))
    out := out ++ (← leavesFitting pos (← subKey tr subject cargs) subject cargs owner (this :: via) asking)
  pure out

end

/-- A dot call of a trait's function, of a value whose type does not
implement the trait but has a function of the name of its own, or is a
reference to a value whose type implements it, found only once the
bounds are met: refused, asking for the function by its name or for
`(*r).name(..)` (what the call gives was typed as the trait's function's
when it was read). -/
def dotOwnInstead (call : Nat) (trait : Syntax.TraitKey) (ty : Ty) (said : String) : M Unit := do
  if let some alts := dotAltsOf (← get).modules call then
    if let some h ← headName 8 ty then
      if let some alt := alts.find? (·.startsWith (h ++ "::")) then
        -- (Found only once the call was read, and what it gives typed as
        -- the trait's function's: said where the call is.)
        throw s!"{said}: `{h}` has a function `{Syntax.lastSegment alt}` of its own, found only after the call was read: write `{bareName alt}(receiver, ..)`"
    if let .ref _ inner _ ← find ty then
      if let some h ← headName 8 inner then
        if (← get).kimpls.has (.of trait.base) h then
          -- (Found only once the call was read, and what it gives typed as
          -- the reference's: read through it where the call is.)
          throw s!"{said}: the receiver is a reference to a `{h}`, which has it, found only after the call was read: write `(*receiver).name(..)`"

/-- A dot call's receiver, a name whose type was not known where the call
is (`lateReceivers`), once the bounds of types whose heads are known have
decided what they do, `F: Runs<O>` of `O`: where it is a value that is
copied, and the function takes a reference to read it, given a copy of it,
borrowed (`Elab.receiverCopyNode`); one not copied refused, its type
asked for where it is bound, as Rust asks; else given as it is. -/
def checkLateReceivers : M Unit := do
  let rs := (← get).lateReceivers
  modify fun s => { s with lateReceivers := #[] }
  for (owner, call, given, wanted) in rs do
    match ← find given, ← find wanted with
    | .var _, _ | .ref .., _ => unify given wanted
    | _, .ref how _ _ =>
      let uniq := match ← find how with
        | .con "&mut" [] => true
        | _ => false
      -- (Of what is copied, borrowed to be read: a copy of it, borrowed,
      -- written where it is, `Elab.receiverCopyNode`. Else its type is
      -- what was wanted where the call is, as Rust asks.)
      modify fun s => { s with seen := {} }
      let copied := !uniq && (← tyHasDrop [] given).isNone && !(← tyOwnsOnce [] given)
      unless copied do
        throw "the receiver's type is not known where the call is, and the function borrows it: say its type where the receiver is bound (`let x: Type = ..`)"
      if let .ref _ inner _ ← find wanted then unify given inner
      -- (Written where it is in the body as read, and in the one the count
      -- of uses follows.)
      let write := fun (m : Std.HashMap String Flat.Body) => match m[owner]? with
        | some b => m.insert owner ((Elab.receiverCopyNode call b).getD b)
        | none => m
      modify fun s => { s with runFns := write s.runFns, decidedFns := write s.decidedFns }
    | _, _ => unify given wanted

/-- A bound as its trait's implementations for the type it now has are told
apart: one whose type was not known when the bounds were keyed, or that
waited, keyed as it would have been then, where its trait has several
implementations for that type's head. (One whose name says the trait's
arguments, `Get<Value>`, and that does not have them apart, is found by its
name.) -/
def rekey (b : Bound) : M Bound := do
  let several ← severalFor (b.trait.base) ((← headFor b.trait.base (← find b.ty)).map (·.1))
  if (← get).patterned && several && b.trait.nth == 0
      && (!b.args.isEmpty || b.trait.plain) then
    pure { b with trait := ← implKey (b.trait.base) b.ty b.args }
  else pure b

/-- One function of a group given its type, once the group's bounds are
met (`settleBounds`): with the traits at arguments its bounds name, the
conditions on types made from its implementation's parameters, and what
it is given, each with this function's added. -/
def settleScheme (decls : List FnDecl) (defs : List (String × Ty))
    (instSites : Array (String × Nat × String × String × List Ty)) (leafs : Array (Syntax.TraitKey × Nat × Ty))
    (heldIncl : List (Ty × Ty)) (d : FnDecl) (keyed : List (Syntax.TraitKey × Syntax.TraitKey × List Ty))
    (compound : List (String × Syntax.TraitKey × String × Ty)) (givensOf : List (String × Traits.Givens Syntax.TraitKey)) :
    M (List (Syntax.TraitKey × Syntax.TraitKey × List Ty) × List (String × Syntax.TraitKey × String × Ty)
      × List (String × Traits.Givens Syntax.TraitKey)) := do
  let mut keyed := keyed
  let mut compound := compound
  let mut givensOf := givensOf
  let t0 ← zonk ((defs.lookup d.name).getD .unit)
  let (t1, seen) ← openParams [] t0
  -- A type parameter the function's type does not mention is one of its
  -- parameters all the same: a call says it (`f<Read>()`), and what is
  -- written of it holds (`A: Access`).
  let mut unmentioned : List Nat := []
  let mut seen := seen
  if d.impl.isNone then
    -- (Not one said to be a callable or a label: that is its type, and
    -- the parameter's name is not in the function's type for that reason.)
    let intrinsic := d.bounds.filterMap fun b =>
      if ["Fn", "RunsIn", "Environment", "Use", "Label", "Returns"].contains b.trait then some b.subject else none
    for p in d.params do
      let key := Rigid.param p (rigidOwner decls d)
      if !p.startsWith "'" && !intrinsic.contains p && (seen.lookup key).isNone then
        let fresh ← freshTy
        if let .var id := fresh then unmentioned := unmentioned ++ [id]
        seen := seen ++ [(key, fresh)]
  -- What the body needs of a type parameter it wrote, to be let go or to
  -- be used more than once, it needs of the type the parameter is at each
  -- use: said of the parameter as the function's type has it.
  let before ← get
  let mut opened : Array (Array (Ty × String)) := #[]
  for needs in [before.dups, before.drops, before.stays] do
    let mut out : Array (Ty × String) := #[]
    for (need, why) in needs do
      let (need, seen') ← openParams seen (← zonk need)
      seen := seen'
      out := out.push (need, why)
    opened := opened.push out
  modify fun s =>
    { s with dups := opened.getD 0 #[], drops := opened.getD 1 #[], stays := opened.getD 2 #[] }
  -- What a function needs of what its caller gives is what its signature
  -- says, not what its body is found to do: `T: Use<[fewest, most]>` of a
  -- type parameter, and where nothing is said, one that it may let go but
  -- not use twice, as Rust's `T` is. A callable it is given, it may call
  -- any number of times and let go, as Rust's `Fn`: a callable type
  -- parameter said `Use<[.., 1]>` is called at most once. The body's needs
  -- are held to that; the function's type says that and no more.
  let mut said : Array (Ty × Bool × Bool) := #[]
  let quantityOf := fun (p : String) =>
    (d.bounds.find? fun b => b.trait == "Use" && b.subject == p).bind (·.quantity)
  let rowOrLife := fun (p : String) => p.startsWith "'" || (Syntax.rowParam p).isSome
  -- (An implementation's function: of the implementation's type
  -- parameters, what the implementation says, `impl<T> .. where T:
  -- Use<[0, *]>`, as of its own.)
  for p in genericParams d.params do
    if rowOrLife p then continue
    if let some param := seen.lookup (Rigid.param p (rigidOwner decls d)) then
      let written := quantityOf p
      let (lower, upper) := written.getD (0, some 1)
      -- (What is needed of a reference to a `T` is not needed of a `T`.)
      let mentions := fun (need : Ty) => show M Bool from match param with
        | .var id => tyHoldsVar [] id need
        | _ => pure false
      -- (A type parameter of none of what it is given: nothing of one is the
      -- function's to let go or to use twice, `fn empty<T>() -> [T]`.)
      let given ← match ← find t1 with
        | .fn ps _ _ _ _ => match param with
          | .var id => ps.anyM fun q => tyHoldsVar [] id q
          | _ => pure true
        | _ => pure true
      if written.isNone && !given then continue
      let nothing := s!"`{p}` says nothing of how often it is used, so"
      if lower ≥ 1 then
        if let some (_, why) ← (opened.getD 1 #[]).findM? fun (need, _) => mentions need then
          if written.isNone then
            throw (inFunction d.name s!"{nothing} a `{p}` has to be used, but {why}: write `{p}: Use<[0, 1]>` for one that can go unused")
          throw (inFunction d.name s!"`{p}: Use<[{lower}, ..]>` says a `{p}` has to be used, but {why}")
      if upper.isSome then
        let said_ := if written.isSome then s!"`{p}: Use<[.., 1]>` says" else nothing
        if let some (_, why) ← (opened.getD 0 #[]).findM? fun (need, _) => mentions need then
          let whereTo := match d.impl with
            | some (_, sig) => if sig.mparams.any (·.1 == p) then " in the trait's function" else ""
            | none => ""
          let hint := if written.isNone then s!": write `{p}: Use<[0, *]>`{whereTo} for one that can be used any number of times" else ""
          throw (inFunction d.name s!"{said_} a `{p}` is used at most once, but {why}{hint}")
      said := said.push (param, lower == 0, upper.isNone)
  -- (A callable it is given: as many times as it likes, or none, unless
  -- its type parameter says how often, `F: Use<[1, 1]>` for once.)
  let mut envNeeds : List ((Ty × String) × Bool) := []
  let mut saidStays : Array (Ty × String) := #[]
  let mut saidStatics : Array (Ty × String) := #[]
  let mut envStays : List (Ty × String) := []
  if let .fn ps _ _ _ _ ← find t1 then
      for ((q, annot), place) in (ps.zip d.annots).zipIdx do
        if let .fn _ _ _ _ cap ← find q then
          let named := match annot with
            | some (.name f []) => some f
            | _ => none
          -- (`F: 'static`: what it is given borrows nothing.)
          if named.any fun f => d.bounds.any fun b => b.subject == f && b.trait == "'static" then
            saidStatics := saidStatics.push (q, s!"`{named.getD "F"}: 'static` says it borrows nothing, as a thread's does, which runs after the block a borrow would be of may have ended: give it what it uses (`let m = mine;` in its block)")
          let written := named.bind quantityOf
          let (lower, upper) := written.getD (0, none)
          let root ← findCap cap
          let isIt := fun (need : Ty) => show M Bool from do
            match ← find need with
            | .fn _ _ _ _ c => pure ((← findCap c) == root)
            | _ => pure false
          let f := named.getD "the callable"
          -- (One that runs in an environment the function is given: as the
          -- environment's rules say. Given it whole, it is called at most
          -- once, and goes unused unless the environment is to be used and
          -- it alone runs in it; lent it, `&E`, any number of times.)
          if let some b := named.bind fun f => d.bounds.find? fun b => b.trait == "RunsIn" && b.subject == f then
            let (env, lent) := match b.args.head? with
              | some (.name e []) => (some e, false)
              | some (.ref _ (.name e []) _) => (some e, true)
              | _ => (none, true)
            let members := (d.bounds.filter fun o => o.trait == "RunsIn" && match o.args.head? with
              | some (.name e []) => some e == env
              | _ => false).length
            let must := env.any fun e => d.bounds.any fun o =>
              o.trait == "Use" && o.subject == e && (o.quantity.any fun (lower, _) => lower ≥ 1)
            -- (Or as its own `Use` says, `F: Use<[1, 1]>` of one always called
            -- or given on.)
            let (drops, dups) := match written with
              | some (lower, upper) => (lower == 0, upper.isNone)
              | none => (lent || !(must && members == 1), lent)
            if dups then envNeeds := envNeeds ++ [((q, s!"`{f}` may be called any number of times"), true)]
            if drops then envNeeds := envNeeds ++ [((q, s!"`{f}` runs in an environment, and may not be the one that runs"), false)]
            if named.any fun f => d.bounds.any fun b => b.trait == "Returns" && b.subject == f then
              envStays := envStays ++ [(q, "it is said to come back when called")]
            else if let some (_, why) ← (opened.getD 2 #[]).findM? fun (need, _) => isIt need then
              throw (inFunction d.name s!"{why}, and what it is given may jump to a label and not come back: write `{f}: Returns`")
            continue
          if lower ≥ 1 then
            if let some (_, why) ← (opened.getD 1 #[]).findM? fun (need, _) => isIt need then
              throw (inFunction d.name s!"`{f}: Use<[{lower}, ..]>` says it has to be called, but {why}")
          if upper.isSome then
            if let some (_, why) ← (opened.getD 0 #[]).findM? fun (need, _) => isIt need then
              throw (inFunction d.name s!"`{f}: Use<[.., 1]>` says it is called at most once, but {why}")
          said := said.push (q, lower == 0, upper.isNone)
          -- (One the function calls while it holds a value that has to be
          -- used has to come back: `F: Returns`. Any other may jump to a
          -- label it was made under.)
          let returns := named.any fun f => d.bounds.any fun b => b.trait == "Returns" && b.subject == f
          if returns then saidStays := saidStays.push (q, "it is said to come back when called")
          else if let some (_, why) ← (opened.getD 2 #[]).findM? fun (need, _) => isIt need then
            let hint := match named with
              | some f => s!"write `{f}: Returns`"
              | none => s!"say so of a type parameter for parameter {place + 1}, `F: Fn<..>, F: Returns`"
            throw (inFunction d.name s!"{why}, and what it is given may jump to a label and not come back: {hint}")
  let saidDrops := said.filterMap fun (param, drops, _) =>
    if drops then some (param, "its type parameter is said to be one that can go unused") else none
  let saidDups := said.filterMap fun (param, _, dups) =>
    if dups then some (param, "its type parameter is said to be one that can be used more than once") else none
  let envDups := (envNeeds.filter (·.2)).map (·.1)
  let envDrops := (envNeeds.filter (!·.2)).map (·.1)
  modify fun s =>
    { s with drops := saidDrops ++ envDrops.toArray, dups := saidDups ++ envDups.toArray
             stays := saidStays ++ envStays.toArray, statics := saidStatics }
  let scheme ← generalize t1 [] false
  modify fun s => { s with dups := before.dups, drops := before.drops, stays := before.stays, statics := before.statics }
  -- What a lifetime is said to hold of a type parameter, it holds of the
  -- type the parameter is at each use.
  let mut edges : Array (Nat × Captured) := #[]
  for (cap, what) in scheme.edges do
    match what with
    | .ty target => edges := edges.push (cap, .ty (← openParams seen target).1)
    | other => edges := edges.push (cap, other)
  let mut ranked : List (Nat × List (Nat × String)) := []
  for (cap, lifetimes) in (← get).ranked do
    let root ← findCap cap
    if scheme.cvars.contains root && !ranked.any (·.1 == root) then
      ranked := (root, ← lifetimes.mapM fun (q, name) => do pure (← findCap q, name)) :: ranked
  -- Which instance of an effect each operation of the function is about,
  -- as the function's type has its type parameters.
  let mut vector : Array Ty := #[]
  let mut table : Array (Nat × String × String × Nat × Nat) := #[]
  for (owner, id, kind, name, tys) in instSites do
    if owner == d.name then
      let mut whose : List Ty := []
      for ty in tys do
        let (ty, seen') ← openParams seen (← zonk ty)
        seen := seen'
        whose := whose ++ [ty]
      table := table.push (id, kind, name, vector.size, whose.length)
      vector := vector ++ whose.toArray
  unless table.isEmpty do
    modify fun s =>
      { s with siteTable := (d.name, table.toList) :: s.siteTable
               siteTypes := (d.name, vector.toList.map Ty.written) :: s.siteTypes }
  let scheme := { scheme with edges := edges.toList, ranked, sites := vector.toList
                              tvars := scheme.tvars ++ unmentioned }
  -- The type parameters as written, for a call that writes types for them.
  let written := (d.params.filter fun p => !p.startsWith "'").map fun p =>
    match seen.lookup (Rigid.param p (rigidOwner decls d)) with
    | some (.var id) => if scheme.tvars.contains id then some id else none
    | _ => none
  modify fun s => { s with typeParams := (d.name, written) :: s.typeParams
                           typeParamNames := (d.name, d.params.filter fun p => !p.startsWith "'") :: s.typeParamNames }
  -- A type parameter may be in the function's type only as what a trait's
  -- type is said to be, `X: Graph<Node = N>`: it is one of the function's
  -- all the same, and what is written of it holds.
  for (_, subject, _, a, owner, _) in (← get).assocUses do
    if owner == d.name then
      let (_, seen') ← openParams seen (← zonk subject)
      let (_, seen'') ← openParams seen' (← zonk a)
      seen := seen''
  let mine : List (Syntax.TraitKey × Nat × Ty) ← match d.impl with
    | some (im, _) =>
      -- (As it is now: another of its functions may have found more that
      -- it assumes.)
      let im := ((← implsOfHead (im.trait.base) im.head).find? (·.dictFn == im.dictFn)).getD im
      -- An implementation says what it assumes.
      let plain ← im.context.mapM fun (tr, j) => do
        let t := .rigid (.param ((im.params[j]?).getD "") d.name)
        pure (Syntax.TraitKey.of tr, ((← keyOf t).getD 0), t)
      -- Those kept apart: the trait at its arguments, of a type
      -- parameter, as this function names the implementation's.
      let own := im.pvars.map fun (p, id) => (id, Ty.rigid (.param p d.name))
      let apart ← im.extra.mapM fun (tr, cargs, subject) => do
        let t := subst own [] [] subject
        let key ← if cargs.isEmpty then pure (Syntax.TraitKey.of tr) else traitKey tr (cargs.map (subst own [] []))
        match ← keyOf t with
        | some k => pure (key, k, t)
        | none =>
          -- Of a type made from them, `(A, B): Apart`: whoever uses the
          -- implementation has to meet it. In here it is known by a
          -- number of its own, which a need of the trait of that very
          -- type is met by.
          let own ← conditionKey d.name key t
          pure (key, own.getD 0, t)
      for (key, _, t) in apart do
        if (← keyOf t).isNone then
          compound := (d.name, key, ← spellTy t, Ty.rigid (.cond d.name key (← keyTy t))) :: compound
      pure (plain ++ apart)
    | none =>
      let inferred := leafs.toList.filter fun (_, _, k) =>
        match k with
        | .var id => scheme.tvars.contains id
        | .rigid r => (seen.lookup r).isSome
        | _ => false
      -- How each type parameter it is given values of is destroyed: by
      -- its signature, whether or not its body lets one go, so that what
      -- the function asks of its callers is what its signature says.
      let mut inferred := inferred
      -- (A coercion is given nothing: what it lets go of a type it is
      -- generic in, or what what it calls does, is not destroyed.)
      if (← get).coercing.contains d.name then
        inferred := inferred.filter (·.1 != .of Syntax.destroyTrait)
      else if (← get).dropMode then
        -- (Last, in the order of the type parameters, whatever order the
        -- body asked them in: as the signature alone gives them.)
        let byBody := inferred.filter (·.1 == .of Syntax.destroyTrait)
        inferred := inferred.filter (·.1 != .of Syntax.destroyTrait)
        -- (Each one its type has, as Rust gives every type parameter how
        -- its values are dropped: what the body does with one is not
        -- asked.)
        for p in (genericParams d.params).filter (!isLifetime ·) do
          let t := Ty.rigid (.param p (rigidOwner decls d))
          if (seen.lookup (Rigid.param p (rigidOwner decls d))).isSome then
            let k := (← keyOf t).getD 0
            inferred := inferred ++ [(.of Syntax.destroyTrait, k, t)]
        -- (And of each type its signature says a trait leaves to an
        -- implementation, `<I as Iterator>::Item`: what the function is
        -- given values of as much as its type parameters.)
        for (_, _, _, a, owner, _) in (← get).assocUses do
          if owner == d.name then
            let t ← find a
            if let .var id := t then
              if scheme.tvars.contains id then
                let k := (← keyOf t).getD 0
                unless inferred.any (fun (tr, k', _) => tr == .of Syntax.destroyTrait && k' == k) do
                  inferred := inferred ++ [(.of Syntax.destroyTrait, k, t)]
        for b in byBody do
          unless inferred.any (fun (tr, k', _) => tr == .of Syntax.destroyTrait && k' == b.2.1) do
            inferred := inferred ++ [b]
      -- Where traits are written of the function's type parameters, they
      -- are all a type parameter has: what the body needs of one must be
      -- among them, or among the traits those need.
      let ordinary := d.bounds.filter fun b =>
        !["Fn", "RunsIn", "Environment", "Use", "Returns"].contains b.trait && !b.trait.startsWith "'"
      if ordinary.isEmpty then pure inferred
      else
        let mut written : List (Syntax.TraitKey × Nat × Ty) := []
        let mut fittedKeys : Array (Syntax.TraitKey × Nat) := #[]
        for (b, at_) in ordinary.zipIdx do
          -- (Said of a type made of the parameters, the type.)
          let ofType := (← get).writtenSubjects.findSome? fun (f, n, t) =>
            if f == d.name && n == b.subject then some t else none
          let t := ofType.getD (Ty.rigid (.param b.subject (rigidOwner decls d)))
          if ofType.isSome || (seen.lookup (Rigid.param b.subject (rigidOwner decls d))).isSome then
            let k := (← keyOf t).getD 0
            -- The trait at the arguments written, if it takes some: this
            -- bound's, where the trait is asked of the type more than
            -- once (`F: Family<Int>, F: Family<String>`).
            let nth := ((ordinary.take at_).filter fun o => o.subject == b.subject && o.trait == b.trait).length
            let theirs := (← get).writtenArgs.filterMap fun (f, subject, tr, args) =>
              if f == d.name && subject == b.subject && tr == b.trait then some args else none
            let args := (theirs[nth]?).getD (theirs.headD [])
            let key ← traitKey b.trait args
            unless args.isEmpty || keyed.any (·.1 == key) do keyed := (key, .of b.trait, args) :: keyed
            for tr in key :: (← supersOf (.of b.trait)) do
              unless written.any (fun w => w.1 == tr && w.2.1 == k) do
                written := written ++ [(tr, k, t)]
        let blankets := (← get).blanketTraits
        for (tr, k, t) in inferred do
          let named := match t with
            | .rigid r => some r.spelled
            | .con n [] => some n
            | _ => none
          if let some n := named then
            -- (How a type parameter is destroyed is never written.)
            unless tr == Syntax.destroyKey || written.any (fun w => w.1 == tr && w.2.1 == k) do
              -- (A trait every type has that has what is written of this
              -- one is had by it too: met where the function is used.)
              let had := fun (c : String) => written.any fun w => w.1.base == c && w.2.1 == k
              if blankets.any (fun (b, asked) => b == tr.base && asked.all had) then
                written := written ++ [(tr, k, t)]
              else
              -- A need of the trait at arguments nothing has decided yet is
              -- the written one's, where they fit (`T: Unlinks<?>` with
              -- `T: Unlinks<T>` written): as Rust takes a `where` bound.
              let mut fitted := false
              if let some (_, _, args) := keyed.find? (·.1 == tr) then
                for w in written do
                  if !fitted && w.1.base == tr.base && w.2.1 == k then
                    if let some (_, _, wargs) := keyed.find? (·.1 == w.1) then
                      if wargs.length == args.length then
                        let saved ← get
                        try
                          for (a, b) in args.zip wargs do unify a b
                          fitted := true
                        catch _ => set saved
              -- (Its dictionary is the written one's: the need is met by it,
              -- its key spelled again, `settleBounds`.)
              if fitted then fittedKeys := fittedKeys.push (tr, k)
              else
                throw (inFunction d.name s!"`{bareName n}` is not said to have `{tr}`: write `{bareName n}: {tr}`")
        pure (written ++ inferred.filter fun (tr, k, _) =>
          !written.any (fun w => w.1 == tr && w.2.1 == k) && !fittedKeys.contains (tr, k))
  -- As the function's type has them: a trait with arguments is asked of
  -- the type together with them, so that each use says them anew.
  let mut bounds : List (String × Ty) := []
  for (tr, _, k) in mine do
    let self ← match k with
      | .rigid r => pure ((seen.lookup r).getD k)
      | k => do pure (← openParams seen (← zonk k)).1
    match keyed.find? (·.1 == tr) with
    | some (_, base, args) =>
      let args ← args.mapM fun a => do pure (← openParams seen (← zonk a)).1
      bounds := bounds ++ [(base.spelled, Ty.tuple (self :: args))]
    | none => bounds := bounds ++ [(tr.spelled, self)]
  -- The types left to implementations that the function's type mentions.
  let mut assocs : List (String × Ty × String × Ty) := []
  for (tr, subject, name, a, owner, _) in (← get).assocUses do
    if owner == d.name then
      assocs := assocs ++ [(tr, (← openParams seen (← zonk subject)).1, name,
        (← openParams seen (← zonk a)).1)]
  -- A type left to an implementation that the function's type does not
  -- mention is still found anew at each use.
  let mut incls : List (Ty × Ty) := []
  for (callee, amb) in heldIncl do
    incls := incls ++ [((← openParams seen (← zonk callee)).1, (← openParams seen (← zonk amb)).1)]
  let carried := assocs.map (·.2.2.2) ++ incls.flatMap fun (c, a) => [c, a]
  let found := ((assocs.flatMap fun (_, subject, _, _) => freeTys subject) ++ carried.flatMap freeTys).eraseDups
  let scheme := { scheme with assocs, incls, tvars := (scheme.tvars ++ found).eraseDups,
                              rvars := (scheme.rvars ++ carried.flatMap freeRows).eraseDups }
  givensOf := (d.name, mine.map fun (tr, k, _) => (tr, k)) :: givensOf
  modify fun s =>
    { s with
      fns := s.fns.insert d.name { scheme with bounds := bounds }
      fnBounds := (d.name, mine.length) :: s.fnBounds }
  pure (keyed, compound, givensOf)

/-- Meet the bounds of the group just inferred, and give each of its functions
its type. A bound on a type the function is generic in becomes something the
function is given; every other is met by `Traits.solve`. -/
def settleBounds (decls : List FnDecl) (defs : List (String × Ty)) : M Unit := do
  modify fun s => { s with solvedFit := {}, leavesFit := {}, leavesAt := {}, tyIds := {}, tyIdCount := 0, tyMemo := {}, dictShared := {}, dictByShape := {}, destroyFit := {}, fitParams := {} }
  -- A name of which parts were read before its type was known, which is now:
  -- if the type has a `drop` of its own and the parts read can be used any
  -- number of times, the value stayed whole and is destroyed when its block
  -- is left. A part that has to be destroyed cannot be moved out of it.
  for (site, t, reads, pos) in (← get).lateKeeps do
    if let .con n _ ← find t then
      if (← get).kimpls.has (.of "Drop") n
          && site.owner != Syntax.implFnName "Drop" n "drop" then
        for (subject, idx) in reads do
          let plain ← match ← (try fieldType subject idx catch _ => pure none) with
            | some ft => do
              let ft ← zonk ft
              modify fun st => { st with seen := {} }
              pure ((freeTys ft).isEmpty && (freeCaps ft).isEmpty && !hasParam ft
                && !(← tyOwnsOnce [] ft) && (← tyHasDrop [] ft).isNone)
            | none => pure false
          unless plain do
            throw (inFunction site.owner s!"{pos}a field that has to be destroyed is moved out of a `{bareName n}`, which has a `drop` of its own to run: say the value's type where it is taken, so that this is seen there")
        modify fun st => { st with dropCands := st.dropCands.push (site, t, pos) }
  modify fun s => { s with lateKeeps := #[] }
  -- A callable that lets go of what it is given whatever its type, used at
  -- a type with something to destroy: nothing would.
  let mut later : Array (Ty × String) := #[]
  for (t, why) in (← get).quiets do
    let t ← zonk t
    if !(freeTys t).isEmpty then later := later.push (t, why)
    else if ← needsDestroying [] t then throw why
  modify fun s => { s with quiets := later }
  let mut pending := (← get).bounds
  let uses := (← get).groupUses
  let cands := (← get).dropCands
  let instSites := (← get).instSites
  modify fun s => { s with bounds := #[], groupUses := #[], dropCands := #[], instSites := #[] }
  -- A variable whose value's type has `Drop` needs the implementation, to run
  -- its function when the value is destroyed.
  -- A value that is let go is destroyed by its type's function, if its type
  -- is one that has something to destroy, or is not yet known: then the
  -- function it is let go in is given how.
  if (← get).dropMode then
    for (site, ty, pos) in cands do
      -- (A coercion is given nothing: what it lets go of a type it is
      -- generic in is not destroyed.)
      let ty ← zonk ty
      if (← get).coercing.contains site.owner && !(← needsDestroying [] ty) then continue
      -- (What a callable captures is destroyed by it only where its type is
      -- known to need that: a function is not asked how to destroy what
      -- its callables capture of a type it is generic in.)
      if let .capture _ := site.name then
        -- (Or of a type the program's own function is generic in, not a
        -- reference or a callable: the function is then given how to
        -- destroy it, and the callable captures that.)
        let generic := (← get).ownItems && hasParam ty && !libraryOwner site.owner
          && (match ← find ty with
            | .ref .. => false
            | .fn .. => false
            | _ => true)
        unless generic || ((freeTys ty).isEmpty && !hasParam ty && (← needsDestroying [] ty)) do continue
      -- A callable is destroyed by giving it up, which is done where nothing
      -- may be performed (a cleanup, or what destroys another callable); and
      -- giving one up is allowed only where what it performs could be.
      if let .fn _ _ effs _ _ ← find ty then
        if !effs.isEmpty && (← needsDestroying [] ty) then
          let name := site.name.var
          throw (inFunction site.owner s!"{pos}`{name}` is let go here, and giving it up destroys what it holds (a `drop` runs, or the cleanups of the computation it suspended); but it performs operations, and it can be given up only where they could be performed, which is not where it is let go. Call it, or give it up before with `cancel({name})`")
      if (← needsDestroying [] ty) || !(freeTys ty).isEmpty || hasParam ty then
        let id := 2000000000 + (← get).dropAsked
        modify fun s => { s with dropAsked := s.dropAsked + 1, dropSites := s.dropSites.push (site, id) }
        pending := pending.push ⟨.of Syntax.destroyTrait, ty, id, 0, site.owner, pos, []⟩
  -- What is gone through to reach each borrowed field, for the elaborator.
  let sites := (← get).fieldSites
  modify fun s => { s with fieldSites := #[] }
  for (id, viaRef, ty, path, chosen, owner, pos) in sites do
    -- (the way to the field is by number by now)
    let mut cur ← zonk ty
    let mut steps : Array (Option String × Nat) := #[]
    for (idx, said) in path.zip (chosen ++ path.map fun _ => none) do
      -- (Past a reference a field before holds, or what is reached through
      -- is a reference to one: the step is marked `*` for each, and taken
      -- from what the last points to.)
      let mut past := 0
      if !steps.isEmpty then
        for _ in [0:8] do
          if let .ref _ inner _ := cur then
            cur ← zonk inner
            past := past + 1
      let mark := fun (c : Option String) =>
        if past > 0 then some ("".pushn '*' past ++ c.getD "") else c
      match cur with
      | .tuple ts =>
        steps := steps.push (mark none, ts.length)
        cur := ts.getD idx .unit
      | .con n args =>
        let declared := (← get).types
        let ctor := match said with
          | some c => some c
          | none =>
            match declared[n]? with
            | some decl => match decl.ctors with
              | [c] => some c
              | _ => none
            | none => none
        let known := (← get).ctors
        match ctor.bind fun c => (known[c]?).map fun sig => (c, sig) with
        | some (c, sig) =>
          let fields := sig.fieldsAt args
          -- `#` marks one of several constructors: its fields are taken by
          -- matching, since which a value has cannot be read off it.
          let several := match declared[n]? with
            | some decl => decl.ctors.length != 1
            | none => true
          steps := steps.push (mark (some (if said.isSome && several then "#" ++ c else c)), fields.length)
          cur ← zonk (fields.getD idx .unit)
        | none =>
          throw (inFunction owner (pos ++ s!"a field of a `{showTy cur}` cannot be borrowed: it has more than one constructor"))
      | _ =>
        throw (inFunction owner (pos ++ "the type whose field is borrowed here is not known: say what it is"))
    modify fun s => { s with fieldTable := s.fieldTable.push (id, viaRef, path, steps.toList) }
  -- A row parameter is whatever whoever calls says it is: the function
  -- cannot have found it to hold an effect, or to be another's row.
  let rowChecks := (← get).rowChecks
  for (owner, rowParams) in rowChecks do
    let mut rowsSeen : List Nat := []
    for (e, carrier) in rowParams do
      match ← zonk carrier with
      | .fn _ _ [] (some k) _ =>
        if rowsSeen.contains k then
          throw (inFunction owner s!"the row `{e}` is taken to be the same as another row parameter: what the function does with them makes them one")
        rowsSeen := k :: rowsSeen
      | .fn _ _ effs _ _ =>
        throw (inFunction owner s!"the row `{e}` is whatever the caller chooses, and what is written needs it to hold {showEffs effs}")
      | _ => pure ()
  -- An implementation for another name of a type, `impl T for Option<A>`,
  -- is one for the type with some of its arguments fixed: a type it is asked
  -- of has those.
  let mut undecided : List Nat := []
  for round in [0, 1] do
    -- A trait asked of a type that nothing in the group decided, even
    -- once the implementations the others fit have said what they do,
    -- where one of the trait's implementations is the one to fall back
    -- on: the type is that implementation's, or another of the trait's
    -- that has every other trait asked of the type. (`[a, b]` is an array
    -- where nothing says it is one of exactly two.)
    if round == 1 then
      -- (First the arguments a decided type's one implementation gives its
      -- trait are those asked for, which may decide another type: an array
      -- of exactly two arrays says what the two are. As deep as written.)
      for _ in List.range 8 do
        for b in pending do
          let (self, wanted) ← subjectOfKey b.trait b.ty
          if wanted.isEmpty then continue
          let found ← match ← find self with
            | .con h args => pure (some (h, args))
            | _ => pure none
          if let some (h, args) := found then
            let mine ← implsOfHead (b.trait.base) h
            if let [im] := mine then
              let at_ ← implAt im args
              for (given, want) in im.targs.zip wanted do
                try unify want (← fixedAt at_ given) catch _ => pure ()
      for b in pending do
        let (self, _) ← subjectOfKey b.trait b.ty
        if let .var v ← find self then
          let mine ← implsOfBase (b.trait.base)
          let (first, others) := mine.partition fun im => im.pvars.any (·.1 == Syntax.fallbackMark)
          if first.isEmpty then continue
          -- (The other traits asked of the same type.)
          let mut asked : List String := []
          for other in pending do
            let (theirs, _) ← subjectOfKey other.trait other.ty
            if let .var w ← find theirs then
              if w == v && other.trait != Syntax.destroyKey
                  && other.trait.base != b.trait.base then
                asked := other.trait.base :: asked
          let byBase := (← get).implsByBase
          let impls := (← get).impls
          let fitsAll := fun (head : String) => asked.all fun tr =>
            (byBase.getD tr #[]).any fun i => (impls[i]?.map (·.head)) == some head
          match (first ++ others).find? (fun im => fitsAll im.head) with
          | some im => unify self (.con im.head (← im.params.mapM fun _ => freshTy))
          | none => pure ()
    for (b, at_) in pending.toList.zipIdx do
      -- (The second time, those whose type was not decided the first.)
      if round == 1 && !undecided.contains at_ then continue
      if round == 0 then
        if let .var _ ← find (← subjectOfKey b.trait b.ty).1 then undecided := at_ :: undecided
      let goal ← zonk b.ty
      let fitting := (← get).patterned
      let named ← match goal with
        | .con h args => pure (some (h, args))
        | .tuple _ => headFor b.trait.base goal
        | _ => pure (if fitting then goal.head else none)
      if let some (h, args) := named then
        -- (Where the type has several implementations of the trait, the one
        -- chosen makes the arguments fit when it is chosen.)
        let several ← severalFor (b.trait.base) (some h)
        for im in ← implsOfHead (b.trait.base) h do
          if im.trait == b.trait && !several then
            -- (The implementation's own type parameters are this type's
            -- arguments here, not what another use of it made them.)
            let at_ ← implAt im args
            for (j, want) in im.fixed do
              if let some got := args[j]? then
                let want ← fixedAt at_ want
                -- (A type made of the function's own type parameters may
                -- have the trait by what the function assumes, not by this.)
                if Ty.hasRigid got then
                  try unify want got catch _ => pure ()
                else
                try unify want got
                catch _ =>
                  let fits ← zonk want
                  let whole := match goal with
                    | .tuple _ => Ty.tuple (args.set j fits)
                    | _ => .con h (args.set j fits)
                  throw (inFunction b.owner
                    s!"{b.pos}`{b.trait}` is implemented for `{showTy whole}`, not for `{showTy goal}`")
            -- What the implementation's conditions say of a type left to
            -- another trait's implementations is asked of the arguments.
            for (j, asked, name, said) in im.equal do
              if let some subject := args[j]? then
                let use := (asked, subject, name, subst at_ [] [] said, b.owner, b.pos)
                modify fun s => { s with assocUses := s.assocUses.push use }
            for (whole, asked, name, said) in im.extraEqual do
              let use := (asked, subst at_ [] [] whole, name, subst at_ [] [] said, b.owner, b.pos)
              modify fun s => { s with assocUses := s.assocUses.push use }
  -- A trait with arguments is asked of a type together with them: from here
  -- on it is the trait at those arguments, asked of the type.
  timedM "bounds: settle" settleAssocs
  -- (What an implementation found only now performs is passed on.)
  settleRows (some fun _ => true) true
  let mut keyed : List (Syntax.TraitKey × Syntax.TraitKey × List Ty) := []
  let mut split : Array Bound := #[]
  for b in pending do
    let (self, args) ← subjectOfKey b.trait b.ty
    -- (Where a type has several implementations of the trait, which one
    -- is chosen by fitting, arguments or none.)
    let several ← do
      pure ((← get).patterned && (← severalFor b.trait.base ((← headFor b.trait.base (← find self)).map (·.1))))
    if args.isEmpty && !several then split := split.push b
    else
      let key ← try implKey b.trait.base self args
        catch e => throw (inFunction b.owner (b.pos ++ e))
      unless keyed.any (·.1 == key) do keyed := (key, b.trait, args) :: keyed
      split := split.push { b with trait := key, ty := self, args := args }
  pending := split
  -- (The numbers an implementation's conditions on types made from its type
  -- parameters are known by in its functions, before what those need is
  -- looked for.)
  for d in decls do
    if let some (im, _) := d.impl then
      let own := im.pvars.map fun (p, id) => (id, Ty.rigid (.param p d.name))
      for (tr, cargs, subject) in im.extra do
        let t := subst own [] [] subject
        if (← keyOf t).isNone then
          let key ← if cargs.isEmpty then pure (Syntax.TraitKey.of tr) else traitKey tr (cargs.map (subst own [] []))
          let _ ← conditionKey d.name key t
  -- What the group's functions need of the types they are generic in.
  let mut leafs : Array (Syntax.TraitKey × Nat × Ty) := #[]
  -- (Those of a type whose head is known first: what their implementations
  -- say may decide what the others are of, `F: Into<S>` the `S` of a block
  -- named in place of a function that needs `S: Col`.)
  let mut known : Array (Option Bound) := #[]
  let mut unknown : Array (Option Bound) := #[]
  for b in pending do
    match ← find b.ty with
    | .var _ => unknown := unknown.push b
    | _ => known := known.push b
  -- (Bounds of a receiver found to be read through its reference: of what
  -- it points to, `dotOwnInstead`.)
  for b in known ++ #[none] ++ unknown do
    -- (Between: what those of known types decided of receivers.)
    let some b := b | checkLateReceivers; continue
    let b ← rekey b
    -- (How to destroy a type that nothing decides is not asked for.)
    let patterned := (← get).patterned
    let leavesOf := fun (ty : Ty) => (if patterned && b.trait != Syntax.destroyKey then leavesFitting b.pos b.trait ty b.args b.owner
        else (·.map fun (tr, k, t) => (tr, k, t, [])) <$> leaves b.pos b.trait ty : M _)
    let ls ← try (timedM "bounds: leaves" (leavesOf b.ty)) catch e =>
      if b.trait == Syntax.destroyKey then pure [] else do
        dotOwnInstead b.call b.trait b.ty e
        throw (inFunction b.owner e)
    for (tr, k, t, args) in ls do
      -- (One at arguments, `S: Get<Value>` that a condition comes down to,
      -- is said with them in the function's type, as one written is.)
      unless args.isEmpty || keyed.any (·.1 == tr) do keyed := (tr, .of tr.base, args) :: keyed
      unless leafs.any (fun x => x.1 == tr && x.2.1 == k) do leafs := leafs.push (tr, k, t)
  -- What a type parameter's trait says it performs stays a row of its own:
  -- that it is among what a function performs goes with the function's type,
  -- and is seen to where the function is used.
  let mut heldIncl : List (Ty × Ty) := []
  unless decls.isEmpty do
    let held ← assocTails
    let given ← paramTails
    let mut rest : Array (Row × Row × String) := #[]
    for (callee, amb, what) in (← get).rowIncl do
      let c ← flattenRow callee
      if c.tail.any held.contains then
        let cap ← freshCap
        let a ← flattenRow amb
        -- Where it is performed has to be able to have it: a row written
        -- without it, or as another parameter's alone, cannot.
        -- (A row written closed is kept to where the function is used: it
        -- is then for types whose implementations perform nothing more,
        -- which is how `impl Iterator` for what wraps a generator says it.)
        if let some e := c.tail.bind fun ρ => given.lookup ρ then
          if a.tail.isNone || a.tail.any held.contains then
            throw s!"{what} performs the row `{e}`, which is whatever the caller chooses, and the row written here does not have it: write it after `|`, with any other after a comma"
        if a.tail.any held.contains then
          throw s!"{what} performs what the implementation for a type parameter says it does, and the row written here has another's alone: write each after `|`, as `| <A as Trait>::Effects, <B as Trait>::Effects`"
        heldIncl := heldIncl ++ [(Ty.func [] .unit c cap, Ty.func [] .unit a cap)]
      else rest := rest.push (callee, amb, what)
    modify fun s => { s with rowIncl := rest }
  modify fun s => { s with rowChecks := [] }
  let mut givensOf : List (String × Traits.Givens Syntax.TraitKey) := []
  -- Conditions of an implementation on a type made from its parameters,
  -- `(A, B): Apart`, by the function and the trait at its arguments: the
  -- type as written, and the number it is known by in the function.
  let mut compound : List (String × Syntax.TraitKey × String × Ty) := []
  for d in decls do
    let (k, c, g) ← settleScheme decls defs instSites leafs heldIncl d keyed compound givensOf
    keyed := k
    compound := c
    givensOf := g
  let impls := (← get).impls
  let kimpls := (← get).kimpls
  let methodless : Std.HashSet String := (← get).traits.foldl (init := {}) fun m (t, fns) =>
    if fns.isEmpty && t != Syntax.destroyTrait then m.insert t else m
  let marker := fun (t : String) => methodless.contains t
  let mut table : List (Nat × List Elab.DictE) := []
  let record := fun (table : List (Nat × List Elab.DictE)) (call : Nat) (d : Elab.DictE) =>
    match table.lookup call with
    | some ds => (call, ds ++ [d]) :: table.filter (·.1 != call)
    | none => (call, [d]) :: table
  -- (A bound of a type not all decided waits for the others: meeting them
  -- may decide it. In the last round, what is left is refused.)
  let mut waiting := pending.toList
  let mut round := 0
  -- (Rounds go on while one meets any: a type left to an implementation of
  -- a type left to another, as deep as it is written, is found one level a
  -- round. The last is the first that met none, or the hundredth.)
  let mut before := waiting.length + 1
  let mut last := false
  while !waiting.isEmpty do
   round := round + 1
   -- (Stuck: a trait's arguments not decided that are its type where a use
   -- does not say, `x + y` of `Add<R = Self>`, are that, and the rounds go
   -- on; if there are none, this is the last.)
   if !last && (waiting.length == before || round > 100) then
     let mut moved := false
     for b in waiting do
       if ← defaultTraitArgs b.trait b.ty b.args then moved := true
     if moved && round <= 100 then
       before := waiting.length + 1
       settleAssocsAll
     else last := true
   before := waiting.length
   -- (What the bounds met so far said a type left to an implementation is.)
   if round > 1 then timedM "bounds: rounds settle" settleAssocsAll
   let now := waiting
   waiting := []
   for b in now do
    let givens := (givensOf.lookup b.owner).getD []
    -- (A need at arguments decided since, by a written bound, `T: Unlinks<?>`
    -- with `T: Unlinks<T>` written: that bound's, its key spelled again.)
    let b ← if b.args.isEmpty || givens.any (·.1 == b.trait) then pure b else do
      match ← keyOf b.ty with
      | some k =>
        let again ← traitKey (b.trait.base) b.args
        pure (if givens.contains (again, k) then { b with trait := again } else b)
      | none => pure b
    let b ← timedM "bounds: rekey" (rekey b)
    -- What `Traits.coherent` asks of the assumptions.
    unless Traits.distinct givens do
      throw (inFunction b.owner s!"{b.pos}a bound is assumed twice; this is a compiler defect")
    -- How a value is destroyed: a part of its type that nothing decides, and
    -- the function is not given, has nothing to destroy.
    let sty ← if b.trait == Syntax.destroyKey then do pure (destroyShape givens (← toSTy b.ty))
      else toSTy b.ty
    -- (A need of the trait of a type the implementation said has it: met by
    -- what it said.)
    -- (Spelled only where it is asked: most are met before.)
    let saidOf : M (Option (String × Syntax.TraitKey × String × Ty)) := do
      if compound.isEmpty then return none
      let spelled ← spellTy b.ty
      pure (compound.find? fun (owner, key, ty, _) =>
        owner == b.owner && key.base == b.trait.base && ty == spelled)
    let solve := fun (trait : Syntax.TraitKey) (ty : Ty) (sty : Traits.STy) => do
      -- (As deep as a condition's conditions go: a list of sixteen, each
      -- apart from those after it, goes some hundreds deep.)
      if (← get).patterned && b.trait != Syntax.destroyKey then solveFitting givens 4000 trait ty b.args
      else
        -- (Of what a trait leaves to an implementation, not known here: the
        -- condition written of it.)
        let given ← (← projectedCondition trait ty).findSomeM? fun k => do
          pure ((Traits.findGiven trait k givens).map Traits.Dict.given)
        pure (given <|> Traits.solveIx kimpls givens 100000 trait sty)
    let solved ← match ← timedM "bounds: solve" (solve b.trait b.ty sty) with
      | some d => pure (some d)
      | none =>
        match ← saidOf with
        | some (_, key, _, cond) => solve key cond (← toSTy cond)
        | none => pure none
    match solved with
    | some d => table := record table b.call (← timedM "bounds: dict" (toDictEShared impls marker d))
    | none =>
      -- (How a value of a type nothing here decides is destroyed: as one
      -- with nothing to destroy, as a part nothing decides is. Its place
      -- among what the call is given is kept: the callee takes one there.)
      if b.trait == Syntax.destroyKey then
        -- (A callable's is its own, given where it is given up.)
        let callable ← match ← find b.ty with
          | .fn .. => pure true
          | _ => pure false
        unless callable do
          if let some d := Traits.solveIx kimpls givens 100000 b.trait (.con "(reference)" []) then
            table := record table b.call (← toDictEShared impls marker d)
        continue
      if !last && !(← zonk b.ty).ground then
        waiting := waiting ++ [b]
        continue
      -- (A dot call of a trait's function, of a value whose type does not
      -- implement the trait but has a function of the name of its own:
      -- refused, saying so.)
      dotOwnInstead b.call b.trait b.ty s!"{b.pos}`{b.trait}` is not implemented"
      for (tr, k, t) in ← leaves b.pos b.trait b.ty do
        unless givens.contains (tr, k) do
          let named := match t with
            | .rigid r => some r.spelled
            | .con n [] => some n
            | _ => none
          match named with
          | some n =>
            let hint := if (decls.find? (·.name == b.owner)).any (·.impl.isSome) then
              s!": add `where {bareName n}: {tr}` to the implementation" else ""
            throw (inFunction b.owner
              s!"{b.pos}`{bareName n}` is not known to implement `{tr}`{hint}")
          | _ =>
            throw (inFunction b.owner
              s!"{b.pos}`{tr}` is needed of a type that nothing here decides")
      let shownArgs ← b.args.mapM fun a => do pure (showTy (← zonk a))
      let at_ := if shownArgs.isEmpty then "" else s!" at {", ".intercalate shownArgs}"
      throw (inFunction b.owner s!"{b.pos}no implementation of `{b.trait}` was found for `{showTy (← zonk b.ty)}`{at_}; this is a compiler defect")
  -- A use of one of the group's functions inside the group passes on what the
  -- function it is in was given.
  for u in uses do
    let theirs := (givensOf.lookup u.callee).getD []
    unless theirs.isEmpty do
      if u.call == 0 then
        throw (inFunction u.owner s!"{u.pos}`{u.callee}` needs a trait of a type it is used at, so it is called where it is named: write a block that calls it")
      let mine := (givensOf.lookup u.owner).getD []
      for g in theirs do
        match mine.idxOf? g with
        | some i => table := record table u.call (.param i)
        | none =>
          throw (inFunction u.owner
            s!"{u.pos}`{u.callee}` needs `{g.1}` of a type that `{u.owner}` is not given")
  modify fun s => { s with dictTable := s.dictTable ++ table.toArray, solvedFit := {}, leavesFit := {} }

end Glorious.Check
