import Glorious.Check.Expr

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
  | .con name args =>
    if (← get).kimpls.any fun I => I.trait == "Drop" && I.head == name then return true
    let key ← spellTy (.con name args)
    if seen.contains key then return false
    (← partsOf (.con name args)).anyM (needsDestroying (key :: seen))
  | _ => pure false

/-- How a value of this type is destroyed, written down once for each type,
under the type as written; and the `Drop`s that then have to be found. -/
partial def destroyPlan (owner pos : String) (t : Ty) : M (String × Array Bound) := do
  let t ← zonk t
  let key ← spellTy t
  if (← get).glue.any (·.1 == key) then return (key, #[])
  -- Said first, so that a type that holds itself finds itself.
  modify fun s => { s with glue := s.glue.push (key, none, []) }
  let mut asked : Array Bound := #[]
  let mut hook : Option Nat := none
  let part := fun (field : Ty) => do
    if ← needsDestroying [] field then
      let (k, more) ← destroyPlan owner pos field
      pure (some k, more)
    else pure (none, #[])
  let mut ctors : List (String × List (Option String)) := []
  match t with
  | .tuple args =>
    let mut parts : List (Option String) := []
    for a in args do
      let (p, more) ← part a
      parts := parts ++ [p]
      asked := asked ++ more
    ctors := [("", parts)]
  | .con name args =>
    if (← get).kimpls.any fun I => I.trait == "Drop" && I.head == name then
      let id := 2000000000 + (← get).dropAsked
      modify fun s => { s with dropAsked := s.dropAsked + 1 }
      asked := asked.push ⟨"Drop", t, id, 0, owner, pos⟩
      hook := some id
    if let some decl := (← get).types.lookup name then
      for c in decl.ctors do
        if let some sig := (← get).ctors.lookup c then
          let mut parts : List (Option String) := []
          for a in sig.fieldsAt args do
            let (p, more) ← part a
            parts := parts ++ [p]
            asked := asked ++ more
          ctors := ctors ++ [(c, parts)]
  | _ => pure ()
  modify fun s =>
    { s with glue := s.glue.map fun entry => if entry.1 == key then (key, hook, ctors) else entry }
  pure (key, asked)

/-- Meet the bounds of the group just inferred, and give each of its functions
its type. A bound on a type the function is generic in becomes something the
function is given; every other is met by `Traits.solve`. -/
def settleBounds (decls : List FnDecl) (defs : List (String × Ty)) : M Unit := do
  let mut pending := (← get).bounds
  let uses := (← get).groupUses
  let cands := (← get).dropCands
  modify fun s => { s with bounds := #[], groupUses := #[], dropCands := #[] }
  -- A variable whose value's type has `Drop` needs the implementation, to run
  -- its function when the value is destroyed.
  for (site, ty, pos) in cands do
    if ← needsDestroying [] ty then
      let (key, asked) ← destroyPlan site.owner pos ty
      pending := pending ++ asked
      modify fun s => { s with dropSites := s.dropSites.push (site, key) }
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
          steps := steps.push (some (if said.isSome then "#" ++ c else c), fields.length)
          cur ← zonk (fields.getD idx .unit)
        | none =>
          throw (inFunction owner (pos ++ s!"a field of a `{showTy cur}` cannot be borrowed: it has more than one constructor"))
      | _ =>
        throw (inFunction owner (pos ++ "the type whose field is borrowed here is not known: say what it is"))
    modify fun s => { s with fieldTable := s.fieldTable.push (id, viaRef, path, steps.toList) }
  -- A trait with arguments is asked of a type together with them: from here
  -- on it is the trait at those arguments, asked of the type.
  settleAssocs
  let mut keyed : List (String × String × List Ty) := []
  let mut split : Array Bound := #[]
  for b in pending do
    let (self, args) ← subjectOf b.trait b.ty
    if args.isEmpty then split := split.push b
    else
      let key ← traitKey b.trait args
      unless keyed.any (·.1 == key) do keyed := (key, b.trait, args) :: keyed
      split := split.push { b with trait := key, ty := self }
  pending := split
  -- What the group's functions need of the types they are generic in.
  let mut leafs : Array (String × Nat × Ty) := #[]
  for b in pending do
    let ls ← try leaves b.pos b.trait b.ty catch e => throw (inFunction b.owner e)
    for l in ls do
      unless leafs.any (fun x => x.1 == l.1 && x.2.1 == l.2.1) do leafs := leafs.push l
  let mut givensOf : List (String × List (String × Nat)) := []
  for d in decls do
    let t0 ← zonk ((defs.lookup d.name).getD .unit)
    let (t1, seen) ← openParams [] t0
    let scheme ← generalize t1 [] false
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
    let scheme := { scheme with edges := edges.toList, ranked }
    let mine : List (String × Nat × Ty) ← match d.impl with
      | some (im, _) =>
        -- An implementation says what it assumes.
        im.context.mapM fun (tr, j) => do
          let t := Ty.con s!"'{(im.params[j]?).getD ""}@{d.name}" []
          pure (tr, ((← keyOf t).getD 0), t)
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
          for b in ordinary do
            let t := Ty.con s!"'{b.subject}@{d.name}" []
            if (seen.lookup s!"'{b.subject}@{d.name}").isSome then
              let k := (← keyOf t).getD 0
              -- The trait at the arguments written, if it takes some.
              let args := ((← get).writtenArgs.findSome? fun (f, subject, tr, args) =>
                if f == d.name && subject == b.subject && tr == b.trait then some args else none).getD []
              let key ← traitKey b.trait args
              unless args.isEmpty || keyed.any (·.1 == key) do keyed := (key, b.trait, args) :: keyed
              for tr in key :: (← supersAll b.trait) do
                unless written.any (fun w => w.1 == tr && w.2.1 == k) do
                  written := written ++ [(tr, k, t)]
          for (tr, k, t) in inferred do
            if let .con n [] := t then
              unless written.any (fun w => w.1 == tr && w.2.1 == k) do
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
    let found := (assocs.flatMap fun (_, subject, _, a) => freeTys subject ++ freeTys a).eraseDups
    let scheme := { scheme with assocs, tvars := (scheme.tvars ++ found).eraseDups }
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
    match Traits.solve kimpls givens 100000 b.trait (← toSTy b.ty) with
    | some d => table := record table b.call (toDictE impls d)
    | none =>
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

/-- Infer one group of mutually recursive functions and generalise their types. -/
def checkGroup (decls : List FnDecl) : M Unit := do
  let mut group : List (String × Ty) := []
  for d in decls do
    group := (d.name, ← freshTy) :: group
  modify fun s => { s with group := group }
  let mut defs : List (String × Ty) := []
  let mut reused : List (String × Ty) := []
  for d in decls do
    try
      modify fun s => { s with pos := "", owner := d.name, later := [], temps := [], anon := [] }
      -- The function's own type parameters stand for themselves while it is
      -- checked, and so do its lifetimes: each is no other.
      let mut rigid : List (String × Ty) := []
      let mut lifetimes : List (Nat × String) := []
      for p in genericParams d.params do
        if isLifetime p then
          let cap ← freshCap
          rigid := rigid ++ [(p, Ty.life cap)]
          lifetimes := (cap, p) :: lifetimes
        else rigid := rigid ++ [(p, Ty.con s!"'{p}@{d.name}" [])]
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
          unless environments.contains b.subject do
            throw s!"`{b.subject}: Use<..>`: how often it is used can be said here only of an environment, `{b.subject}: Environment<'e>`"
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
        let running := d.bounds.filterMap fun b =>
          match b.trait, b.args.head? with
          | "RunsIn", some (.name e []) => if e == env then some (b.subject, b.args.length - 1) else none
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
      modify fun s => { s with rigidParams := rigid }
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
      modify fun s => { s with fieldCaps := #[] }
      let t ← inferCallable [] annots ret (some d.name) d.clauses s!"the clauses of `{d.name}` do"
      -- A borrow of a field through a reference is written out as a variable
      -- of this function's, so nothing the function gives back or is given
      -- may come to hold it.
      let reached ← capsReached t
      for (cap, pos) in (← get).fieldCaps do
        if reached.contains (← findCap cap) then
          throw (pos ++ "a borrow of a field of what a reference points to lasts only inside the function that makes it, and here it is given back or kept: give back the reference itself, or the field's value")
      if let some effects := declared then
        let effects ← resolveEffects rigid false effects
        if let .fn _ _ effs tail _ ← find t then
          try unifyRow ⟨effs, tail⟩ ⟨effects, none⟩
          catch e =>
            let said := if effects.isEmpty then "nothing" else showEffs effects
            throw s!"`{d.name}` says it performs {said}, and that is not what it performs: {e}"
      -- A function an implementation gives is the function its trait declares,
      -- at the implementation's type.
      if let some (im, sig) := d.impl then
        -- A tuple is the tuple of its parts; any other is made with its name.
        let self := if im.head.startsWith "(tuple" then Ty.tuple (rigid.map (·.2))
          else Ty.con im.head (rigid.map (·.2))
        -- The trait at the arguments the implementation gives it, and the
        -- types it leaves to the implementation as the implementation says.
        let own := im.pvars.filterMap fun (p, id) => (rigid.lookup p).map fun t => (id, t)
        let tm := (sig.self, self) :: sig.tparams.zip im.targs
          ++ sig.assocs.filterMap fun (a, id) =>
            (im.assocs.lookup a).map fun t => (id, subst own [] [] t)
        -- The trait's lifetimes are each itself here, as a function's own
        -- are: what the trait says is borrowed from one thing may not be
        -- borrowed from another.
        let declared ← zonk (.func (sig.params.map (subst tm [] [])) (subst tm [] [] sig.ret) ⟨[], none⟩ (← freshCap))
        let cm ← (freeCaps declared).eraseDups.mapM fun c => do pure (c, ← freshCap)
        let want := subst [] [] cm declared
        let theirs := cm.filterMap fun (old, new) =>
          (sig.lifetimes.lookup old).map fun l =>
            (new, if l == "'_" then "the lifetime the trait leaves unwritten" else s!"the trait's {l}")
        modify fun s => { s with rigidCaps := s.rigidCaps ++ theirs }
        try unify t want
        catch e =>
          throw s!"this is not the function `{sig.trait}` declares, which takes its arguments, gives its result and performs nothing: {e}"
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
      checkDrops (← get).drops
      checkStays (← get).stays
      checkLifetimes
      modify fun s =>
        { s with rigidCaps := s.rigidCaps.filter (·.2 == "'static"), outlives := [] }
    catch e =>
      -- The usual cause: the body ends in an expression run only for its effect,
      -- whose value has become the function's result.
      let recursive := (e.splitOn "is used recursively").length > 1
        && (e.splitOn "contains itself").length > 1
      let hint := if recursive then
        "; if the last expression of the body is not meant as the result, end it with `;`"
        else ""
      throw (inFunction d.name (e ++ hint))
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
          else (name, clauses) }
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

/-- Check a whole program. Gives what the elaborator needs to know about its
blocks: which take an argument they do not name, and for each that is handed a
block which was not run, the identity of that block if it can only be one. The
elaborator then lets those two share what they capture. -/
def checkProgram (items : List Item) (modules : Syntax.ModuleInfo := {}) :
    Except String Elab.Blocks := do
  let written := items.filterMap fun
    | .bounds fn bounds => some (fn, bounds)
    | _ => none
  let decls : List FnDecl := items.filterMap fun
    | .fn name params annots ret clauses =>
      some { name, params, annots, ret, clauses, bounds := (written.lookup name).getD [] }
    | _ => none
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
  let action : M Elab.Blocks := do
    modify fun s => { s with fnBodies := decls.map fun d => (d.name, d.clauses), modules }
    declare items
    computeVariances
    declareTraits items
    checkUseDecls
    for comp in components names deps do
      checkGroup (comp.filterMap fun n => decls.find? (·.name == n))
    -- The functions implementations give, each on its own: any function may
    -- call them, but only through a trait, whose types are declared.
    for im in (← get).impls do
      for item in im.methods do
        if let .fn m _ annots ret clauses := item then
          if let some sig := (← get).methods.lookup m then
            checkGroup [{ name := Syntax.implFnName im.trait im.head m, params := im.params, annots,
                          ret, clauses, impl := some (im, sig) }]
    for c in coercing do
      unless (((← get).fnBounds.lookup c).getD 0) == 0 do
        throw s!"`coerce {c}`: a coercion cannot need a trait of a type it is used at"
    unless (((← get).fnBounds.lookup "main").getD 0) == 0 do
      throw "`main` needs a trait of a type that nothing decides"
    checkDups (← get).lateDups
    checkDrops (← get).lateDrops
    checkStays (← get).lateStays
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
    checkDrops unlinked
    let implEs := s.impls.toList.map fun im =>
      let names := (s.traits.lookup (Syntax.traitBase im.trait)).getD []
      (⟨im.dictFn, im.context.length, names.map fun m =>
        (Syntax.implFnName im.trait im.head m, ((s.methods.lookup m).map (·.params.length)).getD 0)⟩ :
        Elab.ImplE)
    pure ⟨s.given.toList, links ++ s.envLinks.toList, s.coercions.toList,
      ⟨s.dictTable.toList, s.methodCalls.toList, s.fnBounds, implEs, s.dropSites.toList, s.glue.toList⟩,
      s.fieldTable.toList, s.fieldReads.toList, s.packs.toList, s.envFns, s.envWraps.toList,
      s.derefReads.toList⟩
  let (blocks, _) ← action.run {}
  pure blocks

end Glorious.Check
