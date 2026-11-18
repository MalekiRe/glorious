module

public import Glorious.Trace
public import Glorious.Check.Expr

public section

namespace Glorious.Check

open Syntax

/-! ## Programs -/

structure FnDecl where
  name : String
  params : List String
  annots : List (Option TypeExpr)
  ret : Option TypeExpr
  clauses : List Clause
  /-- For a function an implementation gives: the implementation, and the
  trait's function it is. -/
  impl : Option (ImplDecl × MethodSig) := none
  /-- What is written of its type parameters. -/
  bounds : List Syntax.Bound := []

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
  match ← find t with
  | .var id => pure (some (2 * id))
  | .con n [] =>
    if n.startsWith "'" then
      let keys := (← get).rigidKeys
      match keys.entries.find? (·.2 == n) with
      | some (i, _) => pure (some (2 * i + 1))
      | none =>
        modify fun s => { s with rigidKeys := s.rigidKeys.push n }
        pure (some (2 * keys.size + 1))
    else pure none
  | _ => pure none

partial def toSTy (t : Ty) : M Traits.STy := do
  let t ← find t
  match ← keyOf t with
  | some k => pure (.var k)
  | none =>
    match t with
    | .con n args => pure (.con n (← args.mapM toSTy))
    | .tuple args => pure (.con s!"(tuple{args.length})" (← args.mapM toSTy))
    | .fn _ _ _ _ _ => pure (.con "(callable)" [])
    | .ref _ _ _ => pure (.con "(reference)" [])
    | .var _ => pure (.var 0)

/-- The bounds on types a function is generic in that a bound comes down to,
each with the number of its type. This is only to say what a function needs
and to explain a failure: the evidence itself is `Traits.solve`'s. -/
partial def leaves (pos trait : String) (t : Ty) : M (List (String × Nat × Ty)) := do
  let t ← find t
  match ← keyOf t with
  | some k => pure [(trait, k, t)]
  | none =>
    let missing : M (List (String × Nat × Ty)) := do
      throw s!"{pos}`{showTy (← zonk t)}` does not implement `{trait}`"
    match t with
    | .con n args =>
      match Traits.findImpl trait n args.length (← get).kimpls with
      | some (_, I) =>
        let mut out : List (String × Nat × Ty) := []
        for (tr', j) in I.context do
          out := out ++ (← leaves pos tr' (args[j]?.getD .unit))
        pure out
      | none => missing
    | .tuple args =>
      match Traits.findImpl trait s!"(tuple{args.length})" args.length (← get).kimpls with
      | some (_, I) =>
        let mut out : List (String × Nat × Ty) := []
        for (tr', j) in I.context do
          out := out ++ (← leaves pos tr' (args[j]?.getD .unit))
        pure out
      | none => missing
    -- (A callable, of which there is one implementation, for all.)
    | .fn .. =>
      match Traits.findImpl trait "(callable)" 0 (← get).kimpls with
      | some (_, I) => if I.context.isEmpty then pure [] else missing
      | none => missing
    | _ => missing

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

/-- The types a value of this type directly holds. -/
def partsOf (t : Ty) : M (List Ty) := do
  match ← find t with
  | .tuple args => pure args
  | .con name args =>
    match (← get).types.lookup name with
    | none => pure []
    | some decl =>
      decl.ctors.flatMapM fun c => do
        match (← get).ctors.lookup c with
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
    modify fun s => { s with seen := [] }
    let held ← tyHasDrop [] t
    modify fun s => { s with seen := before }
    pure held.isSome
  | .con name args =>
    if (← get).kimpls.any fun I => I.trait == "Drop" && I.head == name then return true
    let key ← spellTy (.con name args)
    if seen.contains key then return false
    (← partsOf (.con name args)).anyM (needsDestroying (key :: seen))
  | _ => pure false

/-- The name of the implementation a condition of another comes down to: the
trait itself, or the one chosen by fitting where there is a choice. -/
def subKey (trait : String) (ty : Ty) (args : List Ty) : M String := do
  let head := (← find ty).head.map (·.1)
  let several := ((← implsOfBase trait).filter fun im => some im.head == head).length > 1
  if args.isEmpty && !several then pure trait else implKey trait ty args

/-- The numbers under which a condition of an implementation on a type made
from its type parameters, `where (A, (B, ())): Fetch<W>`, is known in the
implementation's functions: one for each function it was said in. -/
def conditionKeys (key : String) (t : Ty) : M (List Nat) := do
  let suffix := s!":{key}:{← spellTy (← zonk t)}"
  pure (((← get).rigidKeys.entries.filter fun (_, n) =>
    n.startsWith "'%condition:" && n.endsWith suffix).map fun (i, _) => 2 * i + 1)

/-- How a bound is met, where implementations are chosen by fitting types
(`St.patterned`): as `Traits.solve` finds it, but each condition of the
implementation found is looked for the same way, with the trait's arguments
and the type the implementation says. Not proved, as `Traits.solve` is: what
it finds is checked with the program's Core. -/
partial def solveFitting (givens : Traits.Givens) (fuel : Nat) (key : String) (ty : Ty)
    (args : List Ty) : M (Option Traits.Dict) := do
  if fuel == 0 then return none
  let ty ← find ty
  if key == Syntax.destroyTrait then
    -- How a value is destroyed: as before, by the type's shape alone.
    let rec settle : Traits.STy → Traits.STy
      | .var k => if givens.contains (Syntax.destroyTrait, k) then .var k else .con "(reference)" []
      | .con n args => .con n (args.map settle)
    return Traits.solve (← get).kimpls givens 100000 key (settle (← toSTy ty))
  if let some k ← keyOf ty then return (Traits.findGiven key k givens).map .given
  -- (What the function is given of a type made from its type parameters.)
  for k in ← conditionKeys key ty do
    if let some g := Traits.findGiven key k givens then return some (.given g)
  -- (A function that performs something is not one an implementation for
  -- functions is for: what is written of `Self` there performs nothing.)
  if let .fn _ _ effs tail _ := ty then
    try unifyRow ⟨effs, tail⟩ ⟨[], none⟩ catch _ => return none
  let some (h, hargs) := ty.head | return none
  let some (i, _) := Traits.findImpl key h hargs.length (← get).kimpls | return none
  let some im := (← get).impls[i]? | return none
  let at_ ← implAt im hargs
  -- (The implementation's new variables are made what is asked, and not
  -- the other way: a type what the function is given is said of keeps its
  -- number.)
  for (j, want) in im.fixed do
    if let some got := hargs[j]? then
      try unify (← fixedAt at_ want) got catch _ => return none
  -- (Its type parameters that are only in the trait's arguments are what
  -- those are asked at.)
  for (want, got) in (im.targs.map (subst at_ [] [])).zip args do
    try unify want got catch _ => return none
  -- (What its conditions say a type left to another trait's implementations
  -- is: said of this use, which may be what decides a type parameter that
  -- is only in the conditions.)
  for (j, asked, name, said) in im.equal do
    if let some subject := hargs[j]? then
      if let some found ← assocAt asked subject name then
        try unify (subst at_ [] [] said) found catch _ => return none
  for (whole, asked, name, said) in im.extraEqual do
    match ← assocAt asked (subst at_ [] [] whole) name with
    | some found => try unify (subst at_ [] [] said) found catch _ => return none
    | none =>
      -- (Found once what it is asked of is known.)
      let use := (asked, subst at_ [] [] whole, name, subst at_ [] [] said, (← get).owner, "")
      modify fun s => { s with assocUses := s.assocUses.push use }
  -- (What those decide, before the conditions on what they decide.)
  unless im.equal.isEmpty && im.extraEqual.isEmpty do settleAssocsAll
  let mut subs : List Traits.Dict := []
  for (tr, j) in im.context do
    let some arg := hargs[j]? | return none
    let some d ← solveFitting givens (fuel - 1) (← subKey tr arg []) arg []
      | return none
    subs := subs ++ [d]
  for (tr, cargs, subject) in im.extra do
    let subject := subst at_ [] [] subject
    let cargs := cargs.map (subst at_ [] [])
    let some d ← solveFitting givens (fuel - 1) (← subKey tr subject cargs) subject cargs
      | return none
    subs := subs ++ [d]
  pure (some (.impl i subs))

/-- `leaves`, where implementations are chosen by fitting types. -/
partial def leavesFitting (pos key : String) (t : Ty) (args : List Ty) (owner : String := "")
    (via : List String := []) : M (List (String × Nat × Ty × List Ty)) := do
  let t ← find t
  -- (How a value is destroyed is found by the type's shape alone, as
  -- `solveFitting` finds it: no condition is left of what it finds.)
  if key == Syntax.destroyTrait then
    if (← solveFitting [] 1 key t []).isSome then return []
    -- (Nor is it asked of a callable, which is given up whole, as it is
    -- not of a bound's own type.)
    if let .fn .. := t then return []
  if let some k ← keyOf t then return [(key, k, t, args)]
  -- (What the function is given of a type made from its type parameters.)
  let said := s!"'%condition:{owner}:{key}:{← spellTy (← zonk t)}"
  if let some (i, _) := (← get).rigidKeys.entries.find? (·.2 == said) then return [(key, 2 * i + 1, t, args)]
  -- (What it was asked for, where it is a condition of another.)
  let because := match via with
    | [] => ""
    | ws => s!", which {", which ".intercalate (ws.map (· ++ " needs"))}"
  let missing : M (List (String × Nat × Ty × List Ty)) := do
    throw s!"{pos}`{showTy (← zonk t)}` does not implement `{Syntax.traitShown key}`{because}"
  if let .fn _ _ effs tail _ := t then
    try unifyRow ⟨effs, tail⟩ ⟨[], none⟩
    catch _ => throw s!"{pos}`{showTy (← zonk t)}` performs effects, and `{Syntax.traitShown key}` is implemented for functions that perform none"
  let some (h, hargs) := t.head | missing
  let some (i, _) := Traits.findImpl key h hargs.length (← get).kimpls | missing
  let some im := (← get).impls[i]? | missing
  let at_ ← implAt im hargs
  for (j, want) in im.fixed do
    if let some got := hargs[j]? then
      try unify (← fixedAt at_ want) got catch _ => return ← missing
  for (want, got) in (im.targs.map (subst at_ [] [])).zip args do
    try unify want got catch _ => return ← missing
  for (j, asked, name, said) in im.equal do
    if let some subject := hargs[j]? then
      if let some found ← assocAt asked subject name then
        try unify (subst at_ [] [] said) found catch _ => return ← missing
  for (whole, asked, name, said) in im.extraEqual do
    match ← assocAt asked (subst at_ [] [] whole) name with
    | some found => try unify (subst at_ [] [] said) found catch _ => return ← missing
    | none =>
      -- (Found once what it is asked of is known.)
      let use := (asked, subst at_ [] [] whole, name, subst at_ [] [] said, owner, pos)
      modify fun s => { s with assocUses := s.assocUses.push use }
  -- (What those decide, before the conditions on what they decide.)
  unless im.equal.isEmpty && im.extraEqual.isEmpty do settleAssocsAll
  let mut out : List (String × Nat × Ty × List Ty) := []
  let shown := Syntax.traitShown key
  let this := s!"`{(shown.takeWhile (· != '<')).toString}` of `{showTy (← zonk t)}`"
  for (tr, j) in im.context do
    let arg := hargs[j]?.getD .unit
    out := out ++ (← leavesFitting pos (← subKey tr arg []) arg [] owner (this :: via))
  for (tr, cargs, subject) in im.extra do
    let subject := subst at_ [] [] subject
    let cargs := cargs.map (subst at_ [] [])
    out := out ++ (← leavesFitting pos (← subKey tr subject cargs) subject cargs owner (this :: via))
  pure out

/-- A dot call of a trait's function, of a value whose type does not
implement the trait but has a function of the name of its own: that one,
and the program read again (`Syntax.dotOwnMark`). -/
def dotOwnInstead (call : Nat) (ty : Ty) (said : String) : M Unit := do
  if let some alts := (← get).modules.dotAlts.lookup call then
    let rec head (fuel : Nat) (t : Ty) : M (Option String) := do
      match fuel, ← find t with
      | fuel + 1, .ref _ inner _ => head fuel inner
      | _, .con n _ => pure (some n)
      | _, _ => pure none
    if let some h ← head 8 ty then
      if let some alt := alts.find? (·.startsWith (h ++ "::")) then
        throw (Syntax.dotOwnMark call alt ++ said)

/-- A bound as its trait's implementations for the type it now has are told
apart: one whose type was not known when the bounds were keyed, or that
waited, keyed as it would have been then, where its trait has several
implementations for that type's head. (One whose name says the trait's
arguments, `Get<Value>`, and that does not have them apart, is found by its
name.) -/
def rekey (b : Bound) : M Bound := do
  let head := (← find b.ty).head.map (·.1)
  let several := ((← implsOfBase (Syntax.traitBase b.trait)).filter fun im => some im.head == head).length > 1
  if (← get).patterned && several && !b.trait.any (· == '#')
      && (!b.args.isEmpty || b.trait == Syntax.traitBase b.trait) then
    pure { b with trait := ← implKey (Syntax.traitBase b.trait) b.ty b.args }
  else pure b

/-- A type with the named type parameters it is made of, `'P@f`, the
variables `back` says. -/
partial def unrigidTy (back : List (String × Nat)) : Ty → Ty
  | .con n [] => match back.lookup n with
    | some id => .var id
    | none => .con n []
  | .con n as => .con n (as.map (unrigidTy back))
  | .tuple ts => .tuple (ts.map (unrigidTy back))
  | .fn ps r effs tail cap =>
    .fn (ps.map (unrigidTy back)) (unrigidTy back r) (effs.map fun (e, as) => (e, as.map (unrigidTy back))) tail cap
  | .ref how t cap => .ref how (unrigidTy back t) cap
  | t => t

/-- Meet the bounds of the group just inferred, and give each of its functions
its type. A bound on a type the function is generic in becomes something the
function is given; every other is met by `Traits.solve`. -/
def settleBounds (decls : List FnDecl) (defs : List (String × Ty)) : M Unit := do
  -- A name of which parts were read before its type was known, which is now:
  -- if the type has a `drop` of its own and the parts read can be used any
  -- number of times, the value stayed whole and is destroyed when its block
  -- is left. A part that has to be destroyed cannot be moved out of it.
  for (site, t, reads, pos) in (← get).lateKeeps do
    if let .con n _ ← find t then
      if (← get).kimpls.any (fun I => I.trait == "Drop" && I.head == n)
          && site.owner != Syntax.implFnName "Drop" n "drop" then
        for (subject, idx) in reads do
          let plain ← match ← (try fieldType subject idx catch _ => pure none) with
            | some ft => do
              let ft ← zonk ft
              modify fun st => { st with seen := [] }
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
  modify fun s => { s with bounds := #[], groupUses := #[], dropCands := #[], firstSaid := none, instSites := #[] }
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
      if (Syntax.captureSiteOf site.name).isSome then
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
          let name := (Syntax.captureSiteOf site.name).getD ((Syntax.letSiteOf site.name).getD site.name)
          throw (inFunction site.owner s!"{pos}`{name}` is let go here, and giving it up destroys what it holds (a `drop` runs, or the cleanups of the computation it suspended); but it performs operations, and it can be given up only where they could be performed, which is not where it is let go. Call it, or give it up before with `cancel({name})`")
      if (← needsDestroying [] ty) || !(freeTys ty).isEmpty || hasParam ty then
        let id := 2000000000 + (← get).dropAsked
        modify fun s => { s with dropAsked := s.dropAsked + 1, dropSites := s.dropSites.push (site, id) }
        pending := pending.push ⟨Syntax.destroyTrait, ty, id, 0, site.owner, pos, []⟩
  -- What is gone through to reach each borrowed field, for the elaborator.
  let sites := (← get).fieldSites
  modify fun s => { s with fieldSites := #[] }
  for (id, viaRef, ty, path, chosen, owner, pos) in sites do
    -- (the way to the field is by number by now)
    let mut cur ← zonk ty
    let mut steps : Array (Option String × Nat) := #[]
    for (idx, said) in path.zip (chosen ++ path.map fun _ => none) do
      -- (Past a reference a field before holds: the step is marked `*`,
      -- and taken from what the reference points to.)
      let past := match cur with
        | .ref .. => !steps.isEmpty
        | _ => false
      if past then
        if let .ref _ inner _ := cur then cur ← zonk inner
      let mark := fun (c : Option String) => if past then some ("*" ++ c.getD "") else c
      match cur with
      | .tuple ts =>
        steps := steps.push (mark none, ts.length)
        cur := ts.getD idx .unit
      | .con n args =>
        let declared := (← get).types
        let ctor := match said with
          | some c => some c
          | none =>
            match declared.lookup n with
            | some decl => match decl.ctors with
              | [c] => some c
              | _ => none
            | none => none
        let known := (← get).ctors
        match ctor.bind fun c => (known.lookup c).map fun sig => (c, sig) with
        | some (c, sig) =>
          let fields := sig.fieldsAt args
          -- `#` marks one of several constructors: its fields are taken by
          -- matching, since which a value has cannot be read off it.
          let several := match declared.lookup n with
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
          let (self, wanted) ← subjectOf b.trait b.ty
          if wanted.isEmpty then continue
          let found ← match ← find self with
            | .con h args => pure (some (h, args))
            | _ => pure none
          if let some (h, args) := found then
            let mine := (← implsOfBase (Syntax.traitBase b.trait)).filter fun im => im.head == h
            if let [im] := mine then
              let at_ ← implAt im args
              for (given, want) in im.targs.zip wanted do
                try unify want (← fixedAt at_ given) catch _ => pure ()
      for b in pending do
        let (self, _) ← subjectOf b.trait b.ty
        if let .var v ← find self then
          let mine ← implsOfBase (Syntax.traitBase b.trait)
          let (first, others) := mine.partition fun im => im.pvars.any (·.1 == Syntax.fallbackMark)
          if first.isEmpty then continue
          -- (The other traits asked of the same type.)
          let mut asked : List String := []
          for other in pending do
            let (theirs, _) ← subjectOf other.trait other.ty
            if let .var w ← find theirs then
              if w == v && other.trait != Syntax.destroyTrait
                  && Syntax.traitBase other.trait != Syntax.traitBase b.trait then
                asked := Syntax.traitBase other.trait :: asked
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
        if let .var _ ← find (← subjectOf b.trait b.ty).1 then undecided := at_ :: undecided
      let goal ← zonk b.ty
      let fitting := (← get).patterned
      let named := match goal with
        | .con h args => some (h, args)
        | .tuple parts => some (s!"(tuple{parts.length})", parts)
        | _ => if fitting then goal.head else none
      if let some (h, args) := named then
        -- (Where the type has several implementations of the trait, the one
        -- chosen makes the arguments fit when it is chosen.)
        let several := ((← implsOfBase (Syntax.traitBase b.trait)).filter fun im =>
          im.head == h).length > 1
        for im in (← get).impls do
          if im.trait == b.trait && im.head == h && !several then
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
  settleAssocs
  -- (What an implementation found only now performs is passed on.)
  settleRows (some fun _ => true) true
  let mut keyed : List (String × String × List Ty) := []
  let mut split : Array Bound := #[]
  for b in pending do
    let (self, args) ← subjectOf b.trait b.ty
    -- (Where a type has several implementations of the trait, which one
    -- is chosen by fitting, arguments or none.)
    let several ← do
      let head := (← find self).head.map (·.1)
      pure ((← get).patterned && ((← implsOfBase b.trait).filter fun im =>
        some im.head == head).length > 1)
    if args.isEmpty && !several then split := split.push b
    else
      let key ← try implKey b.trait self args
        catch e => throw (inFunction b.owner (b.pos ++ e))
      unless keyed.any (·.1 == key) do keyed := (key, b.trait, args) :: keyed
      split := split.push { b with trait := key, ty := self, args := args }
  pending := split
  -- (The numbers an implementation's conditions on types made from its type
  -- parameters are known by in its functions, before what those need is
  -- looked for.)
  for d in decls do
    if let some (im, _) := d.impl then
      let own := im.pvars.map fun (p, id) => (id, Ty.con s!"'{p}@{d.name}" [])
      for (tr, cargs, subject) in im.extra do
        let t := subst own [] [] subject
        if (← keyOf t).isNone then
          let key ← if cargs.isEmpty then pure tr else traitKey tr (cargs.map (subst own [] []))
          let _ ← keyOf (Ty.con s!"'%condition:{d.name}:{key}:{← spellTy t}" [])
  -- What the group's functions need of the types they are generic in.
  let mut leafs : Array (String × Nat × Ty) := #[]
  -- (Those of a type whose head is known first: what their implementations
  -- say may decide what the others are of, `F: Into<S>` the `S` of a block
  -- named in place of a function that needs `S: Col`.)
  let mut known : Array Bound := #[]
  let mut unknown : Array Bound := #[]
  for b in pending do
    match ← find b.ty with
    | .var _ => unknown := unknown.push b
    | _ => known := known.push b
  for b in known ++ unknown do
    let b ← rekey b
    -- (How to destroy a type that nothing decides is not asked for.)
    let ls ← try (if (← get).patterned && b.trait != Syntax.destroyTrait then leavesFitting b.pos b.trait b.ty b.args b.owner
        else (·.map fun (tr, k, t) => (tr, k, t, [])) <$> leaves b.pos b.trait b.ty) catch e =>
      if b.trait == Syntax.destroyTrait then pure [] else do
        dotOwnInstead b.call b.ty e
        throw (inFunction b.owner e)
    for (tr, k, t, args) in ls do
      -- (One at arguments, `S: Get<Value>` that a condition comes down to,
      -- is said with them in the function's type, as one written is.)
      unless args.isEmpty || keyed.any (·.1 == tr) do keyed := (tr, Syntax.traitBase tr, args) :: keyed
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
  let mut givensOf : List (String × List (String × Nat)) := []
  -- Conditions of an implementation on a type made from its parameters,
  -- `(A, B): Apart`, by the function and the trait at its arguments: the
  -- type as written, and the number it is known by in the function.
  let mut compound : List (String × String × String × Ty) := []
  for d in decls do
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
        if ["Fn", "RunsIn", "Environment", "Use", "Label"].contains b.trait then some b.subject else none
      for p in d.params do
        let key := s!"'{p}@{rigidOwner decls d}"
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
    -- `T: Use<[fewest, most]>`: what is said of a type parameter is all the
    -- body may need of it, and is what a caller has to give.
    let mut said : Array (Ty × Bool × Bool) := #[]
    for b in d.bounds do
      if b.trait == "Use" then
        if let (some (lower, upper), some param) := (b.quantity, seen.lookup s!"'{b.subject}@{rigidOwner decls d}") then
          -- (What is needed of a reference to a `T` is not needed of a `T`.)
          let mentions := fun (need : Ty) => show M Bool from match param with
            | .var id => tyHoldsVar [] id need
            | _ => pure false
          if lower ≥ 1 then
            if let some (_, why) ← (opened.getD 1 #[]).findM? fun (need, _) => mentions need then
              throw (inFunction d.name s!"`{b.subject}: Use<[{lower}, ..]>` says a `{b.subject}` has to be used, but {why}")
          if upper.isSome then
            if let some (_, why) ← (opened.getD 0 #[]).findM? fun (need, _) => mentions need then
              throw (inFunction d.name s!"`{b.subject}: Use<[.., 1]>` says a `{b.subject}` is used at most once, but {why}")
          said := said.push (param, lower == 0, upper.isNone)
    modify fun s =>
      { s with
        drops := s.drops ++ said.filterMap fun (param, drops, _) =>
          if drops then some (param, "its type parameter is said to be one that can go unused") else none
        dups := s.dups ++ said.filterMap fun (param, _, dups) =>
          if dups then some (param, "its type parameter is said to be one that can be used more than once") else none }
    let scheme ← generalize t1 [] false
    modify fun s => { s with dups := before.dups, drops := before.drops, stays := before.stays }
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
      match seen.lookup s!"'{p}@{rigidOwner decls d}" with
      | some (.var id) => if scheme.tvars.contains id then some id else none
      | _ => none
    modify fun s => { s with typeParams := (d.name, written) :: s.typeParams }
    -- A type parameter may be in the function's type only as what a trait's
    -- type is said to be, `X: Graph<Node = N>`: it is one of the function's
    -- all the same, and what is written of it holds.
    for (_, subject, _, a, owner, _) in (← get).assocUses do
      if owner == d.name then
        let (_, seen') ← openParams seen (← zonk subject)
        let (_, seen'') ← openParams seen' (← zonk a)
        seen := seen''
    let mine : List (String × Nat × Ty) ← match d.impl with
      | some (im, _) =>
        -- An implementation says what it assumes.
        let plain ← im.context.mapM fun (tr, j) => do
          let t := Ty.con s!"'{(im.params[j]?).getD ""}@{d.name}" []
          pure (tr, ((← keyOf t).getD 0), t)
        -- Those kept apart: the trait at its arguments, of a type
        -- parameter, as this function names the implementation's.
        let own := im.pvars.map fun (p, id) => (id, Ty.con s!"'{p}@{d.name}" [])
        let apart ← im.extra.mapM fun (tr, cargs, subject) => do
          let t := subst own [] [] subject
          let key ← if cargs.isEmpty then pure tr else traitKey tr (cargs.map (subst own [] []))
          match ← keyOf t with
          | some k => pure (key, k, t)
          | none =>
            -- Of a type made from them, `(A, B): Apart`: whoever uses the
            -- implementation has to meet it. In here it is known by a
            -- number of its own, which a need of the trait of that very
            -- type is met by.
            let own ← keyOf (Ty.con s!"'%condition:{d.name}:{key}:{← spellTy t}" [])
            pure (key, own.getD 0, t)
        for (key, _, t) in apart do
          if (← keyOf t).isNone then
            compound := (d.name, key, ← spellTy t, Ty.con s!"'%condition:{d.name}:{key}:{← spellTy t}" []) :: compound
        let held := plain ++ apart
        -- (One that leaves a type to be found from its functions, `type Out
        -- = _;`, assumes what they need of its type parameters too: what is
        -- found is found with that, and whoever uses the implementation has
        -- to meet it.)
        let holed := im.assocs.any fun (_, t) => match t with
          | .var id => !im.pvars.any (·.2 == id)
          | _ => false
        if !holed then pure held
        else
          let back := im.pvars.map fun (p, id) => (s!"'{p}@{d.name}", id)
          let more := leafs.toList.filter fun (tr, k, t) =>
            match t with
            | .con n [] => (back.lookup n).isSome && !held.any (fun h => h.1 == tr && h.2.1 == k)
            | _ => false
          let mut asked : List (String × List Ty × Ty) := []
          for (tr, _, t) in more do
            let (base, cargs) := match keyed.find? (·.1 == tr) with
              | some (_, b, as) => (b, as)
              | none => (tr, [])
            let cargs ← cargs.mapM zonk
            asked := asked ++ [(base, cargs.map (unrigidTy back), unrigidTy back t)]
          unless asked.isEmpty do
            modify fun s => { s with impls := s.impls.map fun i =>
              if i.dictFn == im.dictFn then { i with extra := i.extra ++ asked } else i }
          pure (held ++ more)
      | none =>
        let inferred := leafs.toList.filter fun (_, _, k) =>
          match k with
          | .var id => scheme.tvars.contains id
          | .con n [] => (seen.lookup n).isSome
          | _ => false
        -- Where traits are written of the function's type parameters, they
        -- are all a type parameter has: what the body needs of one must be
        -- among them, or among the traits those need.
        let ordinary := d.bounds.filter fun b =>
          !["Fn", "RunsIn", "Environment", "Use"].contains b.trait && !b.trait.startsWith "'"
        if ordinary.isEmpty then pure inferred
        else
          let mut written : List (String × Nat × Ty) := []
          for (b, at_) in ordinary.zipIdx do
            let t := Ty.con s!"'{b.subject}@{rigidOwner decls d}" []
            if (seen.lookup s!"'{b.subject}@{rigidOwner decls d}").isSome then
              let k := (← keyOf t).getD 0
              -- The trait at the arguments written, if it takes some: this
              -- bound's, where the trait is asked of the type more than
              -- once (`F: Family<Int>, F: Family<Str>`).
              let nth := ((ordinary.take at_).filter fun o => o.subject == b.subject && o.trait == b.trait).length
              let theirs := (← get).writtenArgs.filterMap fun (f, subject, tr, args) =>
                if f == d.name && subject == b.subject && tr == b.trait then some args else none
              let args := (theirs[nth]?).getD (theirs.headD [])
              let key ← traitKey b.trait args
              unless args.isEmpty || keyed.any (·.1 == key) do keyed := (key, b.trait, args) :: keyed
              for tr in key :: (← supersAll b.trait) do
                unless written.any (fun w => w.1 == tr && w.2.1 == k) do
                  written := written ++ [(tr, k, t)]
          let blankets := (← get).blanketTraits
          for (tr, k, t) in inferred do
            if let .con n [] := t then
              -- (How a type parameter is destroyed is never written.)
              unless tr == Syntax.destroyTrait || written.any (fun w => w.1 == tr && w.2.1 == k) do
                -- (A trait every type has that has what is written of this
                -- one is had by it too: met where the function is used.)
                let had := fun (c : String) => written.any fun w => Syntax.traitBase w.1 == c && w.2.1 == k
                if blankets.any (fun (b, asked) => b == Syntax.traitBase tr && asked.all had) then
                  written := written ++ [(tr, k, t)]
                else
                throw (inFunction d.name s!"`{bareName n}` is not said to have `{tr}`: write `{bareName n}: {tr}`")
          pure (written ++ inferred.filter fun (tr, k, _) =>
            !written.any (fun w => w.1 == tr && w.2.1 == k))
    -- As the function's type has them: a trait with arguments is asked of
    -- the type together with them, so that each use says them anew.
    let mut bounds : List (String × Ty) := []
    for (tr, _, k) in mine do
      let self := match k with
        | .con n [] => (seen.lookup n).getD k
        | k => k
      match keyed.find? (·.1 == tr) with
      | some (_, base, args) =>
        let args ← args.mapM fun a => do pure (← openParams seen (← zonk a)).1
        bounds := bounds ++ [(base, Ty.tuple (self :: args))]
      | none => bounds := bounds ++ [(tr, self)]
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
        fns := (d.name, { scheme with bounds := bounds }) :: s.fns
        fnBounds := (d.name, mine.length) :: s.fnBounds }
  let impls := (← get).impls
  let kimpls := (← get).kimpls
  let mut table : List (Nat × List Elab.DictE) := []
  let record := fun (table : List (Nat × List Elab.DictE)) (call : Nat) (d : Elab.DictE) =>
    match table.lookup call with
    | some ds => (call, ds ++ [d]) :: table.filter (·.1 != call)
    | none => (call, [d]) :: table
  -- (A bound of a type not all decided waits for the others: meeting them
  -- may decide it. In the last round, what is left is refused.)
  let mut waiting := pending.toList
  let mut round := 0
  while !waiting.isEmpty do
   round := round + 1
   let last := round > 3
   -- (What the bounds met so far said a type left to an implementation is.)
   if round > 1 then settleAssocsAll
   let now := waiting
   waiting := []
   for b in now do
    let b ← rekey b
    let givens := (givensOf.lookup b.owner).getD []
    -- What `Traits.coherent` asks of the assumptions.
    unless Traits.distinct givens do
      throw (inFunction b.owner s!"{b.pos}a bound is assumed twice; this is a compiler defect")
    -- How a value is destroyed: a part of its type that nothing decides, and
    -- the function is not given, has nothing to destroy.
    let sty ← if b.trait == Syntax.destroyTrait then do
        let rec settle : Traits.STy → Traits.STy
          | .var k => if givens.contains (Syntax.destroyTrait, k) then .var k else .con "(reference)" []
          | .con n args => .con n (args.map settle)
        pure (settle (← toSTy b.ty))
      else toSTy b.ty
    -- (A need of the trait of a type the implementation said has it: met by
    -- what it said.)
    let spelled ← spellTy b.ty
    let said := compound.find? fun (owner, key, ty, _) =>
      owner == b.owner && Syntax.traitBase key == Syntax.traitBase b.trait && ty == spelled
    let solve := fun (trait : String) (ty : Ty) (sty : Traits.STy) => do
      if (← get).patterned && b.trait != Syntax.destroyTrait then solveFitting givens 200 trait ty b.args
      else pure (Traits.solve kimpls givens 100000 trait sty)
    let solved ← match ← solve b.trait b.ty sty with
      | some d => pure (some d)
      | none =>
        match said with
        | some (_, key, _, cond) => solve key cond (← toSTy cond)
        | none => pure none
    match solved with
    | some d => table := record table b.call (toDictE impls d)
    | none =>
      if b.trait == Syntax.destroyTrait then continue
      if !last && !(← zonk b.ty).ground then
        waiting := waiting ++ [b]
        continue
      -- (A dot call of a trait's function, of a value whose type does not
      -- implement the trait but has a function of the name of its own: that
      -- one, and the program read again.)
      dotOwnInstead b.call b.ty s!"{b.pos}`{b.trait}` is not implemented"
      for (tr, k, t) in ← leaves b.pos b.trait b.ty do
        unless givens.contains (tr, k) do
          match t with
          | .con n [] =>
            let hint := if (decls.find? (·.name == b.owner)).any (·.impl.isSome) then
              s!": add `where {bareName n}: {tr}` to the implementation" else ""
            throw (inFunction b.owner
              s!"{b.pos}`{bareName n}` is not known to implement `{tr}`{hint}")
          | _ =>
            throw (inFunction b.owner
              s!"{b.pos}`{tr}` is needed of a type that nothing here decides")
      throw (inFunction b.owner s!"{b.pos}no implementation of `{b.trait}` was found; this is a compiler defect")
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
  modify fun s => { s with dictTable := s.dictTable ++ table.toArray }

end Glorious.Check
