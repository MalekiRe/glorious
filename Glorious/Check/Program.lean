module

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
      match keys.toList.idxOf? n with
      | some i => pure (some (2 * i + 1))
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
  pure (((← get).rigidKeys.toList.zipIdx.filter fun (n, _) =>
    n.startsWith "'%condition:" && n.endsWith suffix).map fun (_, i) => 2 * i + 1)

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
  for (j, want) in im.fixed do
    if let some got := hargs[j]? then
      try unify got (← fixedAt at_ want) catch _ => return none
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
partial def leavesFitting (pos key : String) (t : Ty) (args : List Ty) (owner : String := "") :
    M (List (String × Nat × Ty)) := do
  let t ← find t
  if let some k ← keyOf t then return [(key, k, t)]
  -- (What the function is given of a type made from its type parameters.)
  let said := s!"'%condition:{owner}:{key}:{← spellTy (← zonk t)}"
  if let some i := (← get).rigidKeys.toList.idxOf? said then return [(key, 2 * i + 1, t)]
  let missing : M (List (String × Nat × Ty)) := do
    throw s!"{pos}`{showTy (← zonk t)}` does not implement `{Syntax.traitShown key}`"
  if let .fn _ _ effs tail _ := t then
    try unifyRow ⟨effs, tail⟩ ⟨[], none⟩
    catch _ => throw s!"{pos}`{showTy (← zonk t)}` performs effects, and `{Syntax.traitShown key}` is implemented for functions that perform none"
  let some (h, hargs) := t.head | missing
  let some (i, _) := Traits.findImpl key h hargs.length (← get).kimpls | missing
  let some im := (← get).impls[i]? | missing
  let at_ ← implAt im hargs
  for (j, want) in im.fixed do
    if let some got := hargs[j]? then
      try unify got (← fixedAt at_ want) catch _ => return ← missing
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
  let mut out : List (String × Nat × Ty) := []
  for (tr, j) in im.context do
    let arg := hargs[j]?.getD .unit
    out := out ++ (← leavesFitting pos (← subKey tr arg []) arg [] owner)
  for (tr, cargs, subject) in im.extra do
    let subject := subst at_ [] [] subject
    let cargs := cargs.map (subst at_ [] [])
    out := out ++ (← leavesFitting pos (← subKey tr subject cargs) subject cargs owner)
  pure out

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
        unless (freeTys ty).isEmpty && !hasParam ty && (← needsDestroying [] ty) do continue
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
      match cur with
      | .tuple ts =>
        steps := steps.push (none, ts.length)
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
          steps := steps.push (some (if said.isSome && several then "#" ++ c else c), fields.length)
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
                  try unify got want catch _ => pure ()
                else
                try unify got want
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
  for b in pending do
    -- (How to destroy a type that nothing decides is not asked for.)
    let ls ← try (if (← get).patterned && b.trait != Syntax.destroyTrait then leavesFitting b.pos b.trait b.ty b.args b.owner
        else leaves b.pos b.trait b.ty) catch e =>
      if b.trait == Syntax.destroyTrait then pure [] else throw (inFunction b.owner e)
    for l in ls do
      unless leafs.any (fun x => x.1 == l.1 && x.2.1 == l.2.1) do leafs := leafs.push l
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
        pure (plain ++ apart)
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
          for (tr, k, t) in inferred do
            if let .con n [] := t then
              -- (How a type parameter is destroyed is never written.)
              unless tr == Syntax.destroyTrait || written.any (fun w => w.1 == tr && w.2.1 == k) do
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
  for b in pending do
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

/-- What a type says of its own uses may only narrow what its fields allow. -/
def checkUseDecls : M Unit := do
  for (head, must, once) in (← get).useDecls do
    if must && (← get).kimpls.any (fun I => I.trait == "Drop" && I.head == head) then
      throw s!"`impl Drop for {Syntax.lastSegment head}`: a `{Syntax.lastSegment head}` has to be used, so one is never destroyed, and `drop` would never run"
    let arity := (((← get).types.lookup head).map (·.arity)).getD 0
    let args ← (List.range arity).mapM fun _ => freshTy
    for part in ← partsOf (.con head args) do
      unless must do
        if let some what ← tyMustUse {} [head] part then
          throw s!"`impl Use` for `{head}`: it holds {what}, which has to be used, so the fewest uses of a `{head}` cannot be 0"
      unless once do
        modify fun s => { s with seen := [] }
        if ← tyOwnsOnce [head] part then
          throw s!"`impl Use` for `{head}`: it holds a value that can be used only once, so the most uses of a `{head}` cannot be `infinity`"

/-- Strongly connected components of the call graph, callees first. -/
partial def components (names : List String) (deps : String → List String) : List (List String) :=
  let rec visit (v : String) (st : Nat × List String × List (String × Nat × Nat) × List (List String)) :
      Nat × List String × List (String × Nat × Nat) × List (List String) :=
    let (index, stack, info, out) := st
    let info := (v, index, index) :: info
    let st := (index + 1, v :: stack, info, out)
    let st := (deps v).foldl (fun st w =>
      let (index, stack, info, out) := st
      match info.lookup w with
      | none =>
        let (index, stack, info, out) := visit w (index, stack, info, out)
        let lowW := ((info.lookup w).map (·.2)).getD 0
        (index, stack, lower info v lowW, out)
      | some (idxW, _) =>
        if stack.contains w then (index, stack, lower info v idxW, out) else st) st
    let (index, stack, info, out) := st
    match info.lookup v with
    | some (idx, low) =>
      if idx == low then
        let comp := (stack.takeWhile (· != v)) ++ [v]
        (index, stack.drop comp.length, info, out ++ [comp])
      else st
    | none => st
  let (_, _, _, out) := names.foldl (fun st v =>
    if (st.2.2.1.lookup v).isSome then st else visit v st) (0, [], [], [])
  out
where
  lower (info : List (String × Nat × Nat)) (v : String) (bound : Nat) : List (String × Nat × Nat) :=
    info.map fun (n, idx, low) => if n == v then (n, idx, min low bound) else (n, idx, low)

/-- The lifetime of each reference a written type has in it, none where it is
not written; not looking inside a callable's type, which has lifetimes of its
own. -/
partial def refLives : TypeExpr → List (Option String)
  | .ref _ t life => life :: refLives t
  | .name x args => if x == Syntax.rankedMark then [] else args.flatMap refLives
  | .tuple args => args.flatMap refLives
  | .performs r _ => refLives r
  | _ => []

/-- Infer one group of mutually recursive functions and generalise their types. -/
def checkGroup (decls : List FnDecl) : M Unit := do
  let mut group : List (String × Ty) := []
  for d in decls do
    group := (d.name, ← freshTy) :: group
  modify fun s => { s with group := group }
  let mut defs : List (String × Ty) := []
  let mut reused : List (String × Ty) := []
  for d in decls do
    let (defs', reused') ← onError (do
        let mut defs := defs
        let mut reused := reused
        modify fun s => { s with pos := "", owner := d.name, later := [], temps := [], anon := [] }
        -- The function's own type parameters stand for themselves while it is
        -- checked, and so do its lifetimes: each is no other.
        let mut rigid : List (String × Ty) := []
        let mut lifetimes : List (Nat × String) := []
        for p in genericParams d.params do
          if isLifetime p then
            let cap ← freshCap
            rigid := rigid ++ [(p, Ty.life cap)]
            -- (One an implementation's function writes is its trait's of
            -- the same name, which the trait's declaration makes its own.)
            if d.impl.isNone then lifetimes := (cap, p) :: lifetimes
          else rigid := rigid ++ [(p, Ty.con s!"'{p}@{rigidOwner decls d}" [])]
        -- An implementation written for another name of its type: the
        -- arguments the name fixes are those types here, not parameters.
        if let some (im, _) := d.impl then
          -- (A type it has to be may be made of the implementation's own
          -- type parameters, `(A, A)`, `Wrap<Option<T>>`: those are the
          -- function's here.)
          let own := im.pvars.filterMap fun (p, id) => (rigid.lookup p).map fun t => (id, t)
          for (j, fixed) in im.fixed do
            if let some name := im.params[j]? then
              -- (With lifetimes of this function's own.)
              let fixed ← fixedAt own fixed
              rigid := rigid.map fun (p, old) => if p == name then (p, fixed) else (p, old)
          -- What its conditions say of a type left to another trait's
          -- implementations holds in its functions.
          for (j, asked, name, said) in im.equal do
            match (im.params[j]?).bind fun p => rigid.lookup p with
            | some subject =>
              let mine := im.pvars.filterMap fun (p, id) => (rigid.lookup p).map fun t => (id, t)
              let use := (asked, subject, name, subst mine [] [] said, d.name, "")
              modify fun s => { s with assocUses := s.assocUses.push use }
            | none => pure ()
        -- A row parameter stands for a row no one here knows: it is held as
        -- the row of a callable type that is nothing else.
        let mut rowParams : List (String × Ty) := []
        for p in d.params do
          if let some e := Syntax.rowParam p then
            let carrier := Ty.fn [] (.tuple []) [] (some (← freshRowVar)) (← freshCap)
            rowParams := rowParams ++ [(e, carrier)]
            rigid := rigid ++ [(e, carrier)]
        let mut bounds : List (Nat × Nat) := []
        for p in d.params do
          if let some (longer, shorter) := lifetimeBound p then
            let a ← lifetimeCap rigid false (some longer)
            let b ← lifetimeCap rigid false (some shorter)
            bounds := (a, b) :: bounds
            -- What lasts for the shorter may hold what lasts for the longer.
            captures b (.ty (Ty.life a))
        modify fun s =>
          { s with rigidCaps := lifetimes ++ s.rigidCaps.filter (·.2 == "'static"),
                   outlives := bounds }
        -- A type parameter said to be a callable is the type of that callable:
        -- `F: Fn<(A, B), Output = R, Effects = {E}>` is `fn(A, B) -> R / {E}`.
        let callable := fun (b : Syntax.Bound) => b.trait == "Fn" || b.trait == "RunsIn" || b.trait == "Label"
        for b in d.bounds do
          unless (genericParams d.params).contains b.subject do
            throw s!"`{b.subject}: {b.trait}`: `{b.subject}` is not a type parameter of `{d.name}`"
          if callable b then
            let t ← freshTy
            rigid := rigid.map fun (p, old) => if p == b.subject then (p, t) else (p, old)
        for b in d.bounds do
          if callable b then
            for (name, _) in b.assoc do
              unless name == "Output" || name == "Effects" || (name == "After" && b.trait == "RunsIn") do
                throw s!"`{b.subject}: {b.trait}`: `{name}` cannot be said of a callable here (`Output` and `Effects` can)"
            let args := if b.trait == "RunsIn" then b.args.drop 1 else b.args
            let out := (b.assoc.lookup "Output").getD .hole
            let result := match b.assoc.lookup "Effects" with
              | some (.performs _ effects) => TypeExpr.performs out effects
              | _ => out
            let written : TypeExpr := .fn args result
            let said ← resolveType rigid false
              (if b.ranked.isEmpty then written
               else .name Syntax.rankedMark (b.ranked.map (TypeExpr.name · []) ++ [written]))
            unifyAt s!"`{b.subject}` is said twice to be a callable" ((rigid.lookup b.subject).getD said) said
          else if b.trait == "Environment" || b.trait == "Use" then pure ()
          else if b.trait.startsWith "'" then
            -- `T: 'a`: what lasts for `'a` may hold a `T`, so a `T` given here
            -- has to last as long: whatever it borrows, `'a` is taken to.
            let cap ← lifetimeCap rigid false (some b.trait)
            captures cap (.ty ((rigid.lookup b.subject).getD .unit))
          else
            unless ((← get).traits.lookup b.trait).isSome do
              throw s!"`{b.subject}: {b.trait}`: unknown trait `{b.trait}`"
            let arity := (((← get).traitShape.lookup b.trait).map (·.1)).getD 0
            unless b.args.length == arity do
              throw s!"`{b.subject}: {b.trait}`: `{b.trait}` takes {arity} type arguments, but is given {b.args.length}"
            let args ← b.args.mapM (resolveType rigid false)
            modify fun s => { s with writtenArgs := (d.name, b.subject, b.trait, args) :: s.writtenArgs }
        -- Callables that run in an environment the function is given whole.
        let environments := (d.bounds.filter (·.trait == "Environment")).map (·.subject)
        for b in d.bounds do
          if b.trait == "Use" then
            -- Of an environment, or of a type parameter.
            unless environments.contains b.subject || (genericParams d.params).contains b.subject do
              throw s!"`{b.subject}: Use<..>`: how often it is used is said of a type parameter or an environment of `{d.name}`"
        for env in environments do
          let quantity := (d.bounds.find? fun b => b.trait == "Use" && b.subject == env).bind (·.quantity)
          let (must, once) : Bool × Bool := match quantity with
            | some (lower, upper) => (decide (lower ≥ 1), upper == some 1)
            | none => (false, true)
          if once then
            -- The type parameters whose callables are given the environment itself.
            let owners := d.bounds.filterMap fun b =>
              match b.trait, b.args.head? with
              | "RunsIn", some (.name e []) => if e == env then some (b.subject, b.args.length - 1) else none
              | _, _ => none
            let (pats, body) := match d.clauses with
              | [.mk pats body] => (pats, body)
              | _ => ([], [])
            let mut members : List (String × Nat) := []
            for (pat, annot) in pats.zip d.annots do
              match annot with
              | some (.name f []) =>
                if let some arity := owners.lookup f then
                  match pat with
                  | .var x => members := members ++ [(x, arity)]
                  | _ => throw s!"a parameter of type `{f}`, which runs in the environment `{env}`, has to be given a name"
              | _ => pure ()
            unless members.isEmpty do
              let names := pats.flatMap Elab.patVars
              modify fun s => { s with envGroups := s.envGroups.push (env, members, must, names, body) }
              -- Several that take nothing: a caller can build them over one
              -- environment, which the first holds.
              if members.length ≥ 2 && members.all (·.2 == 0) then
                let places := members.filterMap fun (x, _) =>
                  pats.findIdx? fun
                    | .var y => y == x
                    | _ => false
                if must then modify fun s => { s with envMust := d.name :: s.envMust }
                modify fun s =>
                  { s with
                    fnGroups := (d.name, places :: ((s.fnGroups.lookup d.name).getD []))
                      :: s.fnGroups.filter (·.1 != d.name)
                    envFns := (d.name, members.map (·.1) :: ((s.envFns.lookup d.name).getD []))
                      :: s.envFns.filter (·.1 != d.name) }
        -- `After = E2`: the environment a callable leaves, in which others run
        -- only once it has.
        let (pats', body') := match d.clauses with
          | [.mk pats body] => (pats, body)
          | _ => ([], [])
        let named := fun (f : String) => (pats'.zip d.annots).filterMap fun (pat, annot) =>
          match pat, annot with
          | .var x, some (.name g []) => if g == f then some x else none
          | _, _ => none
        for env in environments do
          let leaving := d.bounds.filterMap fun b =>
            match b.trait, b.assoc.lookup "After" with
            | "RunsIn", some (.name e []) => if e == env then some (b.subject, b.args.length - 1) else none
            | _, _ => none
          let lent := d.bounds.filterMap fun b =>
            match b.trait, b.args.head? with
            | "RunsIn", some (.ref _ (.name e []) _) =>
              if e == env then some (b.subject, b.args.length - 1) else none
            | _, _ => none
          let given := d.bounds.filterMap fun b =>
            match b.trait, b.args.head? with
            | "RunsIn", some (.name e []) =>
              -- (One that leaves the environment as it was does not use it up.)
              let keeps := match b.assoc.lookup "After" with
                | some (.name e' []) => e' == env
                | _ => false
              if e == env && !keeps then some (b.subject, b.args.length - 1) else none
            | _, _ => none
          -- Lent after it was given away: the environment is no longer there.
          unless lent.isEmpty || given.isEmpty do
            let owners := given.flatMap fun (f, arity) => (named f).map (·, arity)
            let borrowers := lent.flatMap fun (f, arity) => (named f).map (·, arity)
            unless owners.isEmpty || borrowers.isEmpty do
              modify fun s =>
                { s with envLent := s.envLent.push (env, owners, borrowers, pats'.flatMap Elab.patVars, body') }
          let running := given ++ lent ++ d.bounds.filterMap fun b =>
            match b.trait, b.args.head? with
            | "RunsIn", some (.name e []) =>
              if e == env && !given.any (·.1 == b.subject) then some (b.subject, b.args.length - 1) else none
            | _, _ => none
          unless leaving.isEmpty do
            let producers := leaving.flatMap fun (f, arity) => (named f).map (·, arity)
            let members := running.flatMap fun (f, arity) => (named f).map (·, arity)
            modify fun s =>
              { s with envAfter := s.envAfter.push (env, producers, members, pats'.flatMap Elab.patVars, body') }
        for b in d.bounds do
          if let some (.name e []) := b.assoc.lookup "After" then
            unless environments.contains e do
              throw s!"`{b.subject}: RunsIn<.., After = {e}>`: `{e}` is not said to be an environment (`{e}: Environment<'e>`)"
        for b in d.bounds do
          if b.trait == "RunsIn" then
            let env := match b.args.head? with
              | some (.name e []) => some e
              | some (.ref _ (.name e []) _) => some e
              | _ => none
            match env with
            | some e =>
              unless environments.contains e do
                throw s!"`{b.subject}: RunsIn<{e}, ..>`: `{e}` is not said to be an environment (`{e}: Environment<'e>`)"
            | none => throw s!"`{b.subject}: RunsIn<..>`: the environment is `E`, `&E` or `&mut E`"
        -- A reference given back with no lifetime written lasts as long as
        -- the one reference the function is given; with several to choose
        -- from, which one is written (9.2).
        if d.annots.all Option.isSome then
          if let some ret := d.ret then
            let given := d.annots.flatMap fun a => (a.map refLives).getD []
            let candidates := (given.filterMap id).eraseDups.length + (given.filter Option.isNone).length
            if (refLives ret).any Option.isNone && candidates ≥ 2 then
              throw "it gives back a reference and is given more than one: say which the result lasts as long as, `fn f<'a>(x: &'a T, y: &U) -> &'a T`"
        modify fun s => { s with rigidParams := rigid }
        -- `T: Trait<Item = Type>`: the type the trait leaves to `T`'s
        -- implementation is that one, in the body and for whoever calls.
        for b in d.bounds do
          unless ["Fn", "RunsIn", "Environment", "Use", "Label"].contains b.trait do
            for (name, said) in b.assoc do
              match rigid.lookup b.subject, (← get).traitShape.find? fun (tr, _, _) => tr == b.trait with
              | some self, some (_, _, assocs) =>
                unless assocs.contains name do
                  throw s!"`{b.subject}: {Syntax.lastSegment b.trait}<{name} = ..>`: `{Syntax.lastSegment b.trait}` leaves no type `{name}` to its implementations"
                let a ← resolveType rigid false said
                -- (Of the trait at the arguments written: `F: Family<Int, Of
                -- = A>` and `F: Family<Str, Of = B>` are two questions.)
                let targs ← b.args.mapM (resolveType rigid false)
                let subject := if targs.isEmpty then self else Ty.tuple (self :: targs)
                modify fun s => { s with assocUses := s.assocUses.push (b.trait, subject, name, a, d.name, "") }
              | _, _ => throw s!"`{b.subject}: {Syntax.lastSegment b.trait}<{name} = ..>`: `{b.subject}` is not a type parameter of `{d.name}`, or `{Syntax.lastSegment b.trait}` is not a trait"
        let rankedBefore := (← get).ranked.length
        let annots ← d.annots.mapM fun
          | some t => some <$> resolveType rigid false t
          | none => pure none
        -- A callable for every lifetime is asked for as a parameter, where
        -- what is given can be held to it; not inside another type.
        let asked := annots.filterMap fun
          | some (.fn _ _ _ _ cap) => some cap
          | _ => none
        for (cap, _) in (← get).ranked.take ((← get).ranked.length - rankedBefore) do
          unless asked.contains cap do
            throw "`for<..>` is written of the type of a parameter, not inside another type"
        -- The result may say what the function performs: that, and no more.
        let (retExpr, declared) := match d.ret with
          | some (.performs t effects) => (some t, some effects)
          | other => (other, none)
        let ret ← match retExpr with
          | some t => some <$> resolveType rigid false t
          | none => pure none
        -- A function an implementation gives is the function its trait declares,
        -- at the implementation's type. What it is given is known from that
        -- before its clauses are looked at, so they can read a field of it.
        let wanted ← match d.impl with
          | none => pure none
          | some (im, sig) => do
            -- A tuple is the tuple of its parts; any other is made with its name.
            let parts := im.params.filterMap fun p => rigid.lookup p
            let self ← if im.head.startsWith "(tuple" then pure (Ty.tuple parts)
              -- (A function that performs nothing; a reference with a
              -- lifetime of its own.)
              else if im.head.startsWith "(fn" then
                -- The lifetimes of the references it is given are the
                -- function's to choose at each call: it is one for every
                -- lifetime, as `for<'a> fn(&'a T)` is.
                let cap ← freshCap
                let given := (parts.dropLast.filterMap fun
                  | .ref _ _ c => some c
                  | _ => none).eraseDups
                unless given.isEmpty do
                  modify fun s => { s with ranked := (cap, given.map (·, "'_")) :: s.ranked }
                pure (Ty.fn parts.dropLast (parts.getLast?.getD .unit) [] none cap)
              else if im.head == "(&mut)" then pure (Ty.ref Ty.uniq (parts.headD .unit) (← freshCap))
              else if im.head == "(&)" then pure (Ty.ref Ty.shared (parts.headD .unit) (← freshCap))
              else pure (Ty.con im.head parts)
            -- The trait at the arguments the implementation gives it, and the
            -- types it leaves to the implementation as the implementation says.
            let own := im.pvars.filterMap fun (p, id) => (rigid.lookup p).map fun t => (id, t)
            let tm := (sig.self, self) :: sig.tparams.zip (im.targs.map (subst own [] []))
              ++ sig.assocs.filterMap fun (a, id) =>
                (im.assocs.lookup a).map fun t => (id, subst own [] [] t)
            let tm ← tm.mapM fun (id, t) => do pure (id, ← unproject t)
            -- Its own type parameters are the function's, each itself here;
            -- and where its types ask a type the trait leaves at types, that
            -- is what the implementation says at them.
            let tm := tm ++ sig.mparams.filterMap fun (g, id) => (rigid.lookup g).map fun t => (id, t)
            let tm := tm ++ sig.gats.filterMap fun (a, asked, id) =>
              (im.assocs.lookup a).map fun said =>
                (id, gatAt own ((im.gatParams.lookup a).getD []) (asked.map (subst tm [] [])) said)
            let tm ← tm.mapM fun (id, t) => do pure (id, ← unproject t)
            -- The trait's lifetimes are each itself here, as a function's own
            -- are: what the trait says is borrowed from one thing may not be
            -- borrowed from another.
            -- What it may perform is what the trait says, with a row the trait
            -- leaves to the implementation as the implementation says it.
            let mut rm : List (Nat × Nat) := []
            for (a, k) in sig.rowAssocs do
              let k' ← freshRowVar
              rm := (k, k') :: rm
              if let some said := im.assocs.lookup a then
                try unify (.fn [] .unit [] (some k') (← freshCap)) (← unproject (subst own [] [] said))
                catch _ =>
                  throw (inFunction d.name s!"`{a}` is a row of effects here: write `type {a} = \{Effect, ..};`")
            let row : Row :=
              ⟨sig.row.effs.map fun (e, args) => (e, args.map (subst tm rm [])),
                sig.row.tail.map fun k => (rm.lookup k).getD k⟩
            let declared ← zonk (← unproject
              (.func (sig.params.map (subst tm rm [])) (subst tm rm [] sig.ret) row (← freshCap)))
            let cm ← (freeCaps declared).eraseDups.mapM fun c => do pure (c, ← freshCap)
            let want := subst [] [] cm declared
            -- (A callable in it that is for every lifetime is one still,
            -- under the lifetimes' new names.)
            for (c, every) in (← get).ranked do
              if let some c' := cm.lookup c then
                let renamed := every.map fun (q, name) => ((cm.lookup q).getD q, name)
                modify fun s => { s with ranked := (c', renamed) :: s.ranked }
            let theirs := cm.filterMap fun (old, new) =>
              (sig.lifetimes.lookup old).map fun l =>
                (new, if l == "'_" then "the lifetime the trait leaves unwritten" else s!"the trait's {l}")
            modify fun s => { s with rigidCaps := s.rigidCaps ++ theirs }
            -- (A lifetime it writes, `fn at<'a>(..)`, is the trait's of that
            -- name.)
            for (old, new) in cm do
              if let some l := sig.lifetimes.lookup old then
                if let some written := rigid.lookup l then
                  unify written (Ty.life new)
            pure (some (want, sig.trait))
        let annots := match wanted with
          | some (.fn ps _ _ _ _, _) =>
            if ps.length == annots.length then (annots.zip ps).map fun (a, p) => a <|> some p else annots
          | _ => annots
        -- (And what it gives, as its trait says: a borrow made in its body is
        -- known to be given back while the body is checked, not only after.)
        let ret := ret <|> match wanted with
          | some (.fn _ r _ _ _, _) => some r
          | _ => none
        let t ← inferCallable [] annots ret (some d.name) d.clauses s!"the clauses of `{d.name}` do"
        if let some effects := declared then
          let (effects, rest) ← resolveRow rigid false effects
          if let .fn _ _ effs tail _ ← find t then
            try unifyRow ⟨effs, tail⟩ ⟨effects, rest⟩
            catch e =>
              let said := if effects.isEmpty then "nothing" else showEffs effects
              throw s!"`{d.name}` says it performs {said}, and that is not what it performs: {e}"
        modify fun s => { s with rowChecks := s.rowChecks ++ [(d.name, rowParams)] }
        -- A function an implementation gives is the function its trait declares,
        -- at the implementation's type.
        if let some (want, trait) := wanted then
          try unify t want
          catch e =>
            throw s!"this is not the function `{trait}` declares, in what it takes, gives or performs: {e}"
        -- A use of the function inside its group has the function's type, but
        -- what it is given there need not be what the function itself was given:
        -- the captures of the two are kept apart, and related below.
        let used := (group.lookup d.name).getD t
        if let .var _ ← find used then unify used t
        else
          unifyAt s!"`{d.name}` is used recursively at a different type" (← freshenCaps used) t
          reused := (d.name, used) :: reused
        defs := (d.name, t) :: defs
        runPending
        runLowerChecks t
        checkDups (← get).dups
        checkGivenReads
        checkDrops (← get).drops
        checkAparts
        checkUnrun
        checkStays (← get).stays
        checkLifetimes
        modify fun s =>
          { s with rigidCaps := s.rigidCaps.filter (·.2 == "'static"), outlives := [] }
        pure (defs, reused))
      fun e =>
        -- The usual cause: the body ends in an expression run only for its effect,
        -- whose value has become the function's result.
        let recursive := (e.splitOn "is used recursively").length > 1
          && (e.splitOn "contains itself").length > 1
        let hint := if recursive then
          "; if the last expression of the body is not meant as the result, end it with `;`"
          else ""
        -- Functions that call each other share the type parameters they name
        -- alike, and no others.
        let named := fun (d : FnDecl) => (genericParams d.params).filter (!isLifetime ·)
        let other := decls.find? fun o => o.name != d.name && o.impl.isNone && named o != named d
        let hint := match other with
          | some o =>
            if d.impl.isNone && !(named d).isEmpty && !(named o).isEmpty && (e.splitOn "expected `").length > 1 then
              hint ++ s!" (`{d.name}` and `{o.name}` call each other: a type parameter is one type to both only where both give it the same name)"
            else hint
          | none => hint
        inFunction d.name (e ++ hint)
    defs := defs'
    reused := reused'
  -- Each use inside the group is a use like any other: of the function's type
  -- with captures of its own, which capture what the function's do.
  for (name, used) in reused do
    if let some t := defs.lookup name then
      try unify (← instantiate (← generalize t) (some name)) used
      catch e => throw (inFunction name s!"`{name}` is used recursively at a different type: {e}")
  checkLoans
  settleBounds decls defs
  modify fun s => { s with assocUses := #[] }
  -- Later functions follow calls into these as they will be elaborated.
  let cs := (← get).coercions.toList
  unless cs.isEmpty do
    modify fun s =>
      { s with fnBodies := s.fnBodies.map fun (name, clauses) =>
          if decls.any (·.name == name) then (name, Elab.coerceFn cs name clauses)
          else (name, clauses),
               runFns := decls.foldl (fun m d =>
                 match m[d.name]? with
                 | some clauses => m.insert d.name (Elab.coerceFn cs d.name clauses)
                 | none => m) s.runFns }
  -- A later function can still decide a requirement made here, through a
  -- declaration whose field types are inferred, so each is checked again at
  -- the end of the program.
  let owner := (decls.head?.map (·.name)).getD "the program"
  let late := (← get).dups.map fun (t, why) => (t, inFunction owner why)
  let lateDrops := (← get).drops.map fun (t, why) => (t, inFunction owner why)
  let lateStays := (← get).stays.map fun (t, why) => (t, inFunction owner why)
  modify fun s =>
    { s with group := [], dups := #[], lateDups := s.lateDups ++ late, drops := #[],
             lateDrops := s.lateDrops ++ lateDrops, stays := #[],
             lateStays := s.lateStays ++ lateStays }

/-- What one check keeps for the next of a program that changed a little: the
checker's state after the declarations and after each group of functions,
each under a key of everything it was made from, in order. -/
abbrev Kept := List (UInt64 × St)

/-- An item as its declarations have it: its functions without their bodies. -/
partial def withoutBodies : Item → Item
  | .fn name params annots ret _ => .fn name params annots ret []
  | .impl params tr head args ctx methods => .impl params tr head args ctx (methods.map withoutBodies)
  | .pub parent item => .pub parent (withoutBodies item)
  | other => other

/-- A group of functions, as what its check is made from. -/
def groupKey (key : UInt64) (group : List FnDecl) : UInt64 :=
  group.foldl (fun h d => mixHash h (hash (d.name, d.params, d.annots, d.ret, d.clauses, d.bounds))) key

/-- Check items. With `kept` from an earlier check of a program that began
alike (`seed`: what was checked before them), the state after each step whose
key is among them is taken from there instead of checked again: the
declarations' key is of every item without the bodies of its functions, each
group's is of the key before it and the group's functions whole. A step
depends on no more than that: a group follows calls only into groups before
it. What the functions of later groups are is put back as this program has
them. Gives what this check kept. -/
def checkItems (items : List Item) (seed : UInt64 := 0) (kept : Kept := []) : M Kept := do
  let written := items.filterMap fun
    | .bounds fn bounds => some (fn, bounds)
    | _ => none
  let decls : List FnDecl := items.filterMap fun
    | .fn name params annots ret clauses =>
      some { name, params, annots, ret, clauses, bounds := (written.lookup name).getD [] }
    | _ => none
  -- What is asked of a declared type's parameters: a trait without arguments
  -- of its own, of the parameter at a place.
  let asked := items.filterMap fun
    | .struct name params _ => (written.lookup name).map (name, params, ·)
    | .enum name params _ => (written.lookup name).map (name, params, ·)
    | .effect name params _ => (written.lookup name).map (name, params, ·)
    | _ => none
  modify fun s =>
    { s with typeBounds := s.typeBounds ++ asked.map fun (name, params, bounds) =>
        (name, bounds.filterMap fun b =>
          if b.trait.startsWith "'" || !b.args.isEmpty then none
          else (params.idxOf? b.subject).map (b.trait, ·)) }
  let names := decls.map (·.name)
  let mentions := fun (name : String) =>
    match decls.find? (·.name == name) with
    | some d => ((d.clauses.flatMap (Elab.fvClause [])).filter names.contains).eraseDups
    | none => []
  let coercing := items.filterMap fun
    | .coerce name => some name
    | _ => none
  for c in coercing do
    unless names.contains c do throw s!"`coerce {c}`: there is no function `{c}`"
  -- A coercion can be applied in any function, so the coercions are checked
  -- before all the others: all, that is, but the functions the coercions are
  -- themselves built from, in which none is applied.
  let builtFrom := Id.run do
    let mut seen := coercing
    for _ in [0:names.length] do
      seen := (seen ++ seen.flatMap mentions).eraseDups
    pure seen
  let deps := fun (name : String) =>
    if builtFrom.contains name then mentions name else (mentions name ++ coercing).eraseDups
  do
    let before := (← get).impls.size
    let mut made : Kept := []
    let mut key := mixHash seed (hash (items.map withoutBodies))
    match kept.lookup key with
    | some st => set st
    | none =>
      declare items
      computeVariances
      declareTraits items
      checkUseDecls
    made := (key, ← get) :: made
    modify fun s =>
      { s with fnBodies := s.fnBodies ++ (decls.map fun d => (d.name, d.clauses)),
               runFns := decls.foldl (fun m d => m.insertIfNew d.name d.clauses) s.runFns }
    -- (A state kept from before has the bodies that program's later
    -- functions had: this one's are put in their place.)
    let restore := fun (st : St) (later : List FnDecl) => (do
      set st
      modify fun s =>
        { s with fnBodies := s.fnBodies.map fun (name, clauses) =>
                   match later.find? (·.name == name) with
                   | some d => (name, d.clauses)
                   | none => (name, clauses),
                 runFns := later.foldl (fun m d => m.insert d.name d.clauses) s.runFns } : M Unit)
    let groups := (components names deps).map fun comp => comp.filterMap fun n => decls.find? (·.name == n)
    for (group, k) in groups.zipIdx do
      key := groupKey key group
      match kept.lookup key with
      | some st => restore st ((groups.drop (k + 1)).flatten)
      | none => checkGroup group
      made := (key, ← get) :: made
    -- The functions implementations give, each on its own: any function may
    -- call them, but only through a trait, whose types are declared.
    for im in (← get).impls.toList.drop before do
      for item in im.methods do
        if let .fn m written annots ret clauses := item then
          if let some sig := (← get).methods.lookup m then
            -- (Its type parameters: the head's arguments, and then those
            -- that are only inside one, or among the trait's own; and the
            -- lifetimes it writes of its own, `fn at<'a>(..)`.)
            let inner := (im.pvars.map (·.1)).filter (!im.params.contains ·)
            let lifetimes := (genericParams written).filter isLifetime
            let d : FnDecl := { name := Syntax.implFnName im.trait im.head m,
                                params := im.params ++ inner ++ sig.mparams.map (·.1) ++ lifetimes, annots,
                                ret, clauses, impl := some (im, sig) }
            key := groupKey key [d]
            match kept.lookup key with
            | some st => restore st []
            | none => checkGroup [d]
            made := (key, ← get) :: made
    for c in coercing do
      unless (((← get).fnBounds.lookup c).getD 0) == 0 do
        throw s!"`coerce {c}`: a coercion cannot need a trait of a type it is used at"
    checkDups (← get).lateDups
    checkDrops (← get).lateDrops
    checkStays (← get).lateStays
    modify fun s => { s with lateDups := #[], lateDrops := #[], lateStays := #[] }
    pure made

/-- The declared types a type is made of. -/
partial def namedIn : Ty → List String
  | .var _ => []
  | .con name args => name :: args.flatMap namedIn
  | .tuple args => args.flatMap namedIn
  | .fn params ret effs _ _ =>
    params.flatMap namedIn ++ namedIn ret ++ effs.flatMap fun (_, args) => args.flatMap namedIn
  | .ref _ t _ => namedIn t

/-- What the checker tells the elaborator, once every item is checked. -/
def finish : M Elab.Blocks := do
  do
    -- One who calls a `pub` function has to be able to write its type.
    let info := (← get).modules
    for f in info.pubFns do
      if let some scheme := (← get).fns.lookup f then
        let t ← zonk (← instantiate scheme)
        for n in namedIn t do
          if let some home := info.privTypes.lookup n then
            if info.homes.lookup f == some home then
              throw s!"`{Syntax.lastSegment f}` is `pub`, but its type, `{showTy t}`, has `{Syntax.lastSegment n}` in it, which is private to its module: one who calls `{Syntax.lastSegment f}` could not write that type (`pub struct` with fields that are not `pub` keeps what is inside private)"
    unless (((← get).fnBounds.lookup "main").getD 0) == 0 do
      throw "`main` needs a trait of a type that nothing decides"
    match (← get).fns.lookup "main" with
    | none => pure ()
    | some scheme =>
      match ← zonk (← instantiate scheme) with
      | .fn ps r effs _ _ =>
        unless ps.isEmpty do throw "`main` takes no arguments"
        unless effs.isEmpty do
          throw s!"`main` performs effects that nothing handles: {showEffs effs}"
        -- Nothing uses what the program gives.
        modify fun s => { s with pos := "", drops := #[] }
        mustDrop r "the result of `main` is let go when the program ends"
        checkDrops (← get).drops
      | _ => pure ()
    let s ← get
    let mut links : List (Nat × Nat) := []
    for (id, cap) in s.unrun do
      let root ← findCap cap
      let mut owners : List Nat := []
      for (owner, c) in s.blockCaps do
        if owner != id && owner != 0 && (← findCap c) == root && !owners.contains owner then
          owners := owner :: owners
      if let [owner] := owners then links := (id, owner) :: links
    -- A block taken to be given one particular block, where in the end it
    -- may be given another, lets go of whatever it is given.
    let mut unlinked : Array (Ty × String) := #[]
    for (id, owner, input, why) in s.assumedLinks do
      unless links.contains (id, owner) do unlinked := unlinked.push (input, why)
    -- (What such a block lets go of, nothing destroys.)
    checkDrops unlinked (callables := true)
    let implEs := s.impls.toList.map fun im =>
      let names := (s.traits.lookup (Syntax.traitBase im.trait)).getD []
      (⟨im.dictFn, im.context.length + im.extra.length, names.map fun m =>
        (Syntax.implFnName im.trait im.head m,
          if im.trait == Syntax.destroyTrait then 1
          else ((s.methods.lookup m).map (·.params.length)).getD 0)⟩ :
        Elab.ImplE)
    -- How each type is destroyed, for the elaborator to write the function:
    -- its own `Drop` first, if it has one, and then for each constructor
    -- which fields are destroyed, each by how its type is.
    let mut destroys : List Elab.Destroy := []
    for im in s.impls do
      if im.trait == Syntax.destroyTrait then
        let givens : Traits.Givens := im.context
        let place := fun (j : Nat) => (im.context.idxOf? (Syntax.destroyTrait, j)).map Elab.DictE.param
        let arity := im.params.length
        let hook := if s.kimpls.any fun I => I.trait == "Drop" && I.head == im.head then
            (Traits.solve s.kimpls givens 1000 "Drop"
              (.con im.head ((List.range arity).map Traits.STy.var))).map (toDictE s.impls)
          else none
        let mut ctors : List (String × List (Option Elab.DictE)) := []
        let isArray := some im.head == s.arrayType
        if isArray then ctors := [("%each", [place 0])]
        else if im.head.startsWith "(tuple" then
          ctors := [("", (List.range arity).map place)]
        else if let some decl := s.types.lookup im.head then
          for c in decl.ctors do
            if let some sig := s.ctors.lookup c then
              -- A field's type, as the solver knows types: a parameter of
              -- the type by its place among them.
              let places := (List.range arity).filter fun j => sig.kinds[j]? != some true
              let sty := fieldSTy sig.tvars places
              let mut parts : List (Option Elab.DictE) := []
              for f in sig.fields do
                let plain := (freeTys f).isEmpty && !(← needsDestroying [] f)
                parts := parts ++ [if plain then none
                  else (Traits.solve s.kimpls givens 1000 Syntax.destroyTrait (sty f)).map (toDictE s.impls)]
              ctors := ctors ++ [(c, parts)]
        destroys := destroys ++ [⟨im.head, im.context.length, hook, isArray, ctors⟩]
    pure ⟨s.given.toList, links ++ s.envLinks.toList, s.coercions.toList,
      ⟨s.dictTable.toList, s.methodCalls.toList, s.fnBounds, implEs, s.dropSites.toList, destroys⟩,
      s.fieldTable.toList, s.fieldReads.toList, s.packs.toList, s.envFns, s.envWraps.toList,
      s.derefReads.toList, s.siteTable, s.siteTypes⟩

/-- Check a whole program. Gives what the elaborator needs to know about its
blocks: which take an argument they do not name, and for each that is handed a
block which was not run, the identity of that block if it can only be one. The
elaborator then lets those two share what they capture. -/
def checkProgram (items : List Item) (modules : Syntax.ModuleInfo := {}) (drops : Bool := false) :
    Except String Elab.Blocks := do
  let action : M Elab.Blocks := do
    modify fun s => { s with modules }
    let _ ← checkItems items
    finish
  let (blocks, _) ← action.run { dropMode := drops }
  pure blocks

/-- What is known once some items are checked: for a program that is checked
after them, against what they declare. -/
def checkFirst (items : List Item) (modules : Syntax.ModuleInfo := {}) (drops : Bool := false) :
    Except String St := do
  let action : M Unit := do
    modify fun s => { s with modules }
    let _ ← checkItems items
  let (_, st) ← action.run { dropMode := drops }
  pure st

/-- Check a program whose first items are already checked. -/
def checkAfter (first : St) (items : List Item) (modules : Syntax.ModuleInfo := {}) :
    Except String Elab.Blocks := do
  let action : M Elab.Blocks := do
    modify fun s => { s with modules, ownItems := true }
    let _ ← checkItems items
    finish
  let (blocks, _) ← action.run first
  pure blocks

/-- The same, taking what an earlier check of a program that began alike kept
(`seed`: what the first items were), and giving what this one keeps. -/
def checkAfterKept (first : St) (items : List Item) (modules : Syntax.ModuleInfo) (seed : UInt64)
    (kept : Kept) : Except String (Elab.Blocks × Kept) := do
  let action : M (Elab.Blocks × Kept) := do
    modify fun s => { s with modules, ownItems := true }
    let made ← checkItems items (mixHash seed (hash modules)) kept
    pure (← finish, made)
  let (r, _) ← action.run first
  pure r

end Glorious.Check
