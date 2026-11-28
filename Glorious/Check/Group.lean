module

public import Glorious.Check.Bounds

public section

namespace Glorious.Check

open Syntax

/-- What a type says of its own uses may only narrow what its fields allow. -/
def checkUseDecls : M Unit := do
  for (head, must, once) in ((← get).useDecls.toList.map fun (h, m, o) => (h, m, o)).mergeSort (fun a b => a.1 ≤ b.1) do
    if must && (← get).kimpls.has (.of "Drop") head then
      throw s!"`impl Drop for {Syntax.lastSegment head}`: a `{Syntax.lastSegment head}` has to be used, so one is never destroyed, and `drop` would never run"
    let arity := (((← get).types[head]?).map (·.arity)).getD 0
    let args ← (List.range arity).mapM fun _ => freshTy
    for part in ← partsOf (.con head args) do
      unless must do
        if let some what ← tyMustUse {} [head] part then
          throw s!"`impl Use` for `{head}`: it holds {what}, which has to be used, so the fewest uses of a `{head}` cannot be 0"
      unless once do
        modify fun s => { s with seen := {} }
        if ← tyOwnsOnce [head] part then
          throw s!"`impl Use` for `{head}`: it holds a value that can be used only once, so the most uses of a `{head}` cannot be `infinity`"

/-- (What `components` has found so far: Tarjan's, with each lookup by a
map, not a list: on the chain of 2,000 functions the lists took 17 ms.) -/
structure ComponentsSt where
  index : Nat := 0
  stack : List String := []
  onStack : Std.HashSet String := {}
  info : Std.HashMap String (Nat × Nat) := {}
  out : Array (List String) := #[]

/-- Strongly connected components of the call graph, callees first. -/
partial def components (names : List String) (deps : String → List String) : List (List String) :=
  let rec visit (v : String) (st : ComponentsSt) : ComponentsSt :=
    let st := { st with index := st.index + 1, stack := v :: st.stack, onStack := st.onStack.insert v,
                        info := st.info.insert v (st.index, st.index) }
    let st := (deps v).foldl (fun st w =>
      match st.info[w]? with
      | none =>
        let st := visit w st
        let lowW := ((st.info[w]?).map (·.2)).getD 0
        { st with info := lower st.info v lowW }
      | some (idxW, _) =>
        if st.onStack.contains w then { st with info := lower st.info v idxW } else st) st
    match st.info[v]? with
    | some (idx, low) =>
      if idx == low then
        let comp := (st.stack.takeWhile (· != v)) ++ [v]
        { st with stack := st.stack.drop comp.length, onStack := comp.foldl (·.erase ·) st.onStack
                  out := st.out.push comp }
      else st
    | none => st
  (names.foldl (fun st v => if st.info.contains v then st else visit v st) ({} : ComponentsSt)).out.toList
where
  lower (info : Std.HashMap String (Nat × Nat)) (v : String) (bound : Nat) : Std.HashMap String (Nat × Nat) :=
    match info[v]? with
    | some (idx, low) => info.insert v (idx, min low bound)
    | none => info

/-- The lifetime of each reference a written type has in it, none where it is
not written; not looking inside a callable's type, which has lifetimes of its
own. -/
partial def refLives : TypeExpr → List (Option String)
  | .ref _ t life => life :: refLives t
  | .name x args => if x == Syntax.rankedMark then [] else args.flatMap refLives
  | .tuple args => args.flatMap refLives
  | .performs r _ => refLives r
  | _ => []

/-- What the trait declares of a function an implementation gives, at the
implementation's type, with the trait's name (`checkGroupFn`). -/
def implWanted (d : FnDecl) (rigid : List (String × Ty)) : M (Option (Ty × String)) := do
  match d.impl with
    | none => pure none
    | some (im, sig) => do
      -- A tuple is the tuple of its parts; any other is made with its name.
      let parts := im.params.filterMap fun p => rigid.lookup p
      let self ← if im.head.startsWith "(tuple" then pure (Ty.tuple parts)
        -- (A function of as many arguments as a tuple has.)
        else if im.head == Traits.fnHead then
          match parts with
          | [ps, r] => do pure (Ty.fn [.con Syntax.spreadParams [ps]] r [] none (← freshCap))
          | _ => pure (Ty.con im.head parts)
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
      -- (`Self` written in its body is that type; so is `T` in a copy of
      -- an implementation for every type, `impl<T: Show> .. for T`.)
      let blanket := im.blanket.toList.map (·, self)
      modify fun s => { s with rigidParams := s.rigidParams ++ [("Self", self)] ++ blanket }
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

/-- A function's type as its signature says it (`checkGroupFn`). -/
def signatureTy (rigid : List (String × Ty)) (annots : List (Option Ty)) (ret : Option Ty) : M Ty := do
  -- (What it takes and gives as written, what it performs as the
  -- signature or its trait says, below.)
  let ps ← annots.mapM fun
    | some t => pure t
    | none => freshTy
  let r ← match ret with
    | some r => pure r
    | none => pure Ty.unit
  -- A reference given back with no lifetime written lasts as long
  -- as the one reference it is given (refused above where there
  -- are more): what it holds, that one holds.
  let named ← (rigid.filterMap fun (_, t) => match t with
    | .ref _ _ c => some c
    | _ => none).mapM findCap
  let given ← (ps.flatMap outerRefCaps).mapM findCap
  let given := given.eraseDups.filter (!named.contains ·)
  if let [one] := given then
    for c in outerRefCaps r do
      let c ← findCap c
      unless named.contains c || c == one do
        captures c (.ty (Ty.life one))
  -- A callable it gives back holds what it was given, as Rust's `impl Fn`
  -- captures what is in scope: its signature says so, whatever its body
  -- made the callable of.
  let rec callableCaps : Ty → List Nat
    | .fn _ _ _ _ c => [c]
    | .con _ args | .tuple args => args.flatMap callableCaps
    | _ => []
  for c in callableCaps r do
    for p in ps do captures c (.ty p)
  pure (Ty.fn ps r [] (some (← freshRowVar)) (← freshCap))

/-- What is checked of a function once its type `t` is found
(`checkGroupFn`). -/
def afterGroupFn (t : Ty) : M Unit := do
  (fun s => Glorious.Trace.said "pending" fun _ => (runPending : M Unit).run s : M Unit)
  (fun s => Glorious.Trace.said "lower" fun _ => (timedM "group: lower checks" (runLowerChecks t) : M Unit).run s : M Unit)
  (fun s => Glorious.Trace.said "dups" fun _ => (do checkDups (← get).dups : M Unit).run s : M Unit)
  (fun s => Glorious.Trace.said "reads" fun _ => (checkGivenReads : M Unit).run s : M Unit)
  (fun s => Glorious.Trace.said "drops" fun _ => (do checkDrops (← get).drops : M Unit).run s : M Unit)
  (fun s => Glorious.Trace.said "aparts" fun _ => (checkAparts : M Unit).run s : M Unit)
  (fun s => Glorious.Trace.said "unrun" fun _ => (checkUnrun : M Unit).run s : M Unit)
  (fun s => Glorious.Trace.said "stays" fun _ => (do checkStays (← get).stays : M Unit).run s : M Unit)
  checkStatics (← get).statics
  modify fun s => { s with statics := #[] }
  (fun s => Glorious.Trace.said "lifetimes" fun _ => (checkLifetimes : M Unit).run s : M Unit)
  modify fun s =>
    { s with rigidCaps := s.rigidCaps.filter (·.2 == "'static"), outlives := [] }

/-- One function of a group checked (`checkGroup`): the types found of it
and of the uses of its group's functions, with those before. -/
def checkGroupFn (decls : List FnDecl) (signature : Bool) (group : List (String × Ty)) (d : FnDecl)
    (defs reused : List (String × Ty)) (announce : Bool := false) : M (List (String × Ty) × List (String × Ty)) := do
  let mut defs := defs
  let mut reused := reused
  modify fun s => { s with pos := "", owner := d.name, later := [], temps := [], anon := [], implConds := [], assocMemo := {}, nodeTys := #[], callInsts := #[],
                           copyParams := d.bounds.filterMap fun b =>
                             if b.trait == "Use" && (b.quantity.any fun (_, hi) => hi.isNone) then some b.subject else none }
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
    else rigid := rigid ++ [(p, Ty.rigid (.param p (rigidOwner decls d)))]
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
    -- (What it says of types made of them, as this function names
    -- them: met by that, where an implementation would be chosen.)
    let mine := im.pvars.filterMap fun (p, id) => (rigid.lookup p).map fun t => (id, t)
    let conds ← im.extra.mapM fun (tr, cargs, subject) => do
      let key ← traitKey tr (cargs.map (subst mine [] []))
      pure (key, ← tyKey (subst mine [] [] subject))
    modify fun s => { s with implConds := conds }
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
    unless b.subjectTy.isSome || (genericParams d.params).contains b.subject do
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
      -- (What it performs is what `Effects` says: nothing, where nothing is,
      -- as in the rest of the signature.)
      modify fun s => { s with closedRows := true }
      let said ← resolveType rigid false
        (if b.ranked.isEmpty then written
         else .name Syntax.rankedMark (b.ranked.map (TypeExpr.name · []) ++ [written]))
      modify fun s => { s with closedRows := false }
      unifyAt s!"`{b.subject}` is said twice to be a callable" ((rigid.lookup b.subject).getD said) said
    else if b.trait == "Environment" || b.trait == "Use" || b.trait == "Returns" then pure ()
    else if b.trait.startsWith "'" then
      -- `T: 'a`: what lasts for `'a` may hold a `T`, so a `T` given here
      -- has to last as long: whatever it borrows, `'a` is taken to.
      let cap ← lifetimeCap rigid false (some b.trait)
      captures cap (.ty ((rigid.lookup b.subject).getD .unit))
    else
      unless ((← get).traits.lookup b.trait).isSome do
        throw s!"`{b.subject}: {b.trait}`: unknown trait `{b.trait}`"
      let arity := (((← get).traitShape[b.trait]?).map (·.1)).getD 0
      unless b.args.length == arity do
        throw s!"`{b.subject}: {b.trait}`: `{b.trait}` takes {arity} type arguments, but is given {b.args.length}"
      let args ← b.args.mapM (resolveType rigid false)
      modify fun s => { s with writtenArgs := (d.name, b.subject, b.trait, args) :: s.writtenArgs }
      if let some sty := b.subjectTy then
        let t ← resolveType rigid false sty
        modify fun s => { s with writtenSubjects := (d.name, b.subject, t) :: s.writtenSubjects }
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
      let (pats, body) : List Pattern × List Flat.StmtId := match d.body.roots with
        | #[c] => let cl := d.body.clause c; (cl.pats, cl.body.toList)
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
        modify fun s => { s with envGroups := s.envGroups.push (env, members, must, names, d.body, body) }
        if members.length ≥ 2 then
          let places := members.filterMap fun (x, _) =>
            pats.findIdx? fun
              | .var y => y == x
              | _ => false
          if must && !(← get).envMust.contains d.name then modify fun s => { s with envMust := d.name :: s.envMust }
          unless (((← get).fnGroups.lookup d.name).getD []).contains places do
            modify fun s =>
              { s with
                fnGroups := (d.name, places :: ((s.fnGroups.lookup d.name).getD []))
                  :: s.fnGroups.filter (·.1 != d.name) }
  -- The parameters said to run in an environment, and of them those given
  -- one argument of a type parameter's type: a caller's block for one
  -- of those runs in the place of what it is given, where that is a
  -- block given to run in an environment too.
  let runsIn := (d.annots.zipIdx).filterMap fun (annot, i) =>
    match annot with
    | some (.name f []) =>
      (d.bounds.find? fun b => b.trait == "RunsIn" && b.subject == f).map fun b =>
        (i, match b.args.drop 1 with
          | [.name x []] => (genericParams d.params).contains x
          | _ => false)
    | _ => none
  -- (Once: its signature's and its body's are the same.)
  unless runsIn.isEmpty || (← get).fnRunsIn.lookup d.name == some runsIn do
    modify fun s => { s with fnRunsIn := (d.name, runsIn) :: s.fnRunsIn.filter (·.1 != d.name) }
  -- `After = E2`: the environment a callable leaves, in which others run
  -- only once it has.
  let (pats', body') : List Pattern × List Flat.StmtId := match d.body.roots with
    | #[c] => let cl := d.body.clause c; (cl.pats, cl.body.toList)
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
          { s with envLent := s.envLent.push (env, owners, borrowers, pats'.flatMap Elab.patVars, d.body, body') }
    let running := given ++ lent ++ d.bounds.filterMap fun b =>
      match b.trait, b.args.head? with
      | "RunsIn", some (.name e []) =>
        if e == env && !given.any (·.1 == b.subject) then some (b.subject, b.args.length - 1) else none
      | _, _ => none
    unless leaving.isEmpty do
      let producers := leaving.flatMap fun (f, arity) => (named f).map (·, arity)
      let members := running.flatMap fun (f, arity) => (named f).map (·, arity)
      modify fun s =>
        { s with envAfter := s.envAfter.push (env, producers, members, pats'.flatMap Elab.patVars, d.body, body') }
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
  -- (What is written of its type parameters, from here on: `I::Item` in
  -- `J: Iterator<Item = I::Item>` is of the trait written of `I`.)
  modify fun s => { s with rigidParams := rigid, paramTraits := d.bounds.map fun b => (b.subject, b.trait, b.args) }
  -- `T: Trait<Item = Type>`: the type the trait leaves to `T`'s
  -- implementation is that one, in the body and for whoever calls.
  for b in d.bounds do
    unless ["Fn", "RunsIn", "Environment", "Use", "Label", "Returns"].contains b.trait do
      for (name, said) in b.assoc do
        match rigid.lookup b.subject, ((← get).traitShape[b.trait]?).map (fun x => (b.trait, x)) with
        | some self, some (_, _, assocs) =>
          unless assocs.contains name do
            throw s!"`{b.subject}: {Syntax.lastSegment b.trait}<{name} = ..>`: `{Syntax.lastSegment b.trait}` leaves no type `{name}` to its implementations"
          let a ← resolveType rigid false said
          -- (Of the trait at the arguments written: `F: Family<Int, Of
          -- = A>` and `F: Family<String, Of = B>` are two questions.)
          let targs ← b.args.mapM (resolveType rigid false)
          let subject := if targs.isEmpty then self else Ty.tuple (self :: targs)
          modify fun s => { s with assocUses := s.assocUses.push (b.trait, subject, name, a, d.name, "") }
        | _, _ => throw s!"`{b.subject}: {Syntax.lastSegment b.trait}<{name} = ..>`: `{b.subject}` is not a type parameter of `{d.name}`, or `{Syntax.lastSegment b.trait}` is not a trait"
  let rankedBefore := (← get).ranked.length
  -- (What is written of its type parameters: `B::Had` of `B: Bundle<S>`
  -- is found by it.)
  modify fun s => { s with paramTraits := d.bounds.map fun b => (b.subject, b.trait, b.args) }
  modify fun s => { s with closedRows := true }
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
  -- A callable parameter whose references are written without a
  -- lifetime is for every lifetime of them, as `fn(&mut T)` is in Rust:
  -- the lifetimes are each call's to choose.
  for (written, t) in d.annots.zip annots do
    if let (some (.fn ps _), some (.fn tps _ _ _ cap)) := (written, t) then
      unless (← get).ranked.any (·.1 == cap) do
        let lives ← ((ps.zip tps).filterMapM fun
          | (.ref _ _ none, p) => do
            match ← find p with
            | .ref _ _ c => pure (some (← findCap c))
            | _ => pure none
          | _ => pure none)
        unless lives.isEmpty do
          modify fun s => { s with ranked := (cap, lives.eraseDups.map (·, "'_")) :: s.ranked }
  -- The result may say what the function performs: that, and no more.
  -- What it performs is written, as what it takes and gives is: nothing
  -- written is nothing. (An implementation's function performs what
  -- its trait's says.)
  let (retExpr, declared) := match d.ret with
    | some (.performs t effects) => (some t, some effects)
    | other => (other, if d.impl.isNone then some [] else none)
  let firstRef := annots.findSome? fun
    | some (.ref _ _ c) => some c
    | _ => none
  modify fun s => { s with projElided := firstRef }
  let ret ← match retExpr with
    | some t => some <$> resolveType rigid false t
    | none => pure none
  modify fun s => { s with paramTraits := [], projElided := none, closedRows := false }
  -- A function an implementation gives is the function its trait declares,
  -- at the implementation's type. What it is given is known from that
  -- before its clauses are looked at, so they can read a field of it.
  let wanted ← implWanted d rigid
  let annots := match wanted with
    | some (.fn ps _ _ _ _, _) =>
      if ps.length == annots.length then (annots.zip ps).map fun (a, p) => a <|> some p
      -- (One it takes from its trait, which says nothing of its own.)
      else if annots.all Option.isNone then ps.map some
      else annots
    | _ => annots
  -- (And what it gives, as its trait says: a borrow made in its body is
  -- known to be given back while the body is checked, not only after.)
  let ret := ret <|> match wanted with
    | some (.fn _ r _ _ _, _) => some r
    | _ => none
  -- (A function of the group whose signature is written whole is known to
  -- the group's calls of it by it before any body is read, `announce`: each
  -- at lifetimes of its own, `freshSigCaps`.)
  if announce then
    if (← get).groupSigned.contains d.name && annots.all Option.isSome && ret.isSome then
      if let some u := group.lookup d.name then
        if let .var _ ← find u then unify u (← signatureTy rigid annots ret)
    return (defs, reused)
  let t ← if signature then signatureTy rigid annots ret
    else (fun s => Glorious.Trace.said "infer" fun _ => (timedM "group: infer" (do
        modify fun s => { s with body := d.body }
        let t ← inferCallable [] annots ret (some d.name) d.body.roots s!"the clauses of `{d.name}` do"
        countUsesNow
        -- (The type of each expression, by node, the function's own
        -- (`Syntax.Flat.selfNode`), an implementation's function's `Self`
        -- (`implSelfNode`), and what each callee's type parameters are at
        -- each call: written once the program is checked, `finish`.)
        let mut read := (← get).nodeTys.push (Syntax.Flat.selfNode, t)
        if d.impl.isSome then
          if let some self := (← get).rigidParams.lookup "Self" then
            read := read.push (Syntax.Flat.implSelfNode, self)
        let calls := (← get).callInsts
        modify fun s => { s with nodeTys := #[], callInsts := #[]
                                 bodyTys := s.bodyTys.insert d.name read
                                 bodyInsts := s.bodyInsts.insert d.name calls }
        -- (The body as read, with what was written where it was found: what
        -- the count of uses follows, `placeLets`.)
        modify fun s => { s with runFns := s.runFns.insert d.name s.body, decidedFns := s.decidedFns.insert d.name s.body }
        pure t) : M Ty).run s : M Ty)
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
  afterGroupFn t
  pure (defs, reused)

/-- The variables of `body` as `sig` has them, where the two are one type
written with variables of their own (`schemeWithin`): types, rows and
captures by their places. -/
partial def varsAs (body sig : Ty) (acc : List (Nat × Ty) × List (Nat × Nat) × List (Nat × Nat)) :
    List (Nat × Ty) × List (Nat × Nat) × List (Nat × Nat) :=
  let all := fun (xs ys : List Ty) acc => (xs.zip ys).foldl (fun acc (x, y) => varsAs x y acc) acc
  match body, sig with
  | .var a, t => if acc.1.any (·.1 == a) then acc else ((a, t) :: acc.1, acc.2)
  | .con _ xs, .con _ ys | .tuple xs, .tuple ys => all xs ys acc
  | .fn ps r effs tail c, .fn ps' r' effs' tail' c' =>
    let acc := varsAs r r' (all ps ps' acc)
    -- (Effects of a name in the order each row has them.)
    let acc := (effs.map (·.1)).eraseDups.foldl (fun acc e =>
      let mine := (effs.filter (·.1 == e)).map (·.2)
      let theirs := (effs'.filter (·.1 == e)).map (·.2)
      (mine.zip theirs).foldl (fun acc (xs, ys) => all xs ys acc) acc) acc
    let acc := match tail, tail' with
      | some a, some b => (acc.1, (a, b) :: acc.2.1, acc.2.2)
      | _, _ => acc
    (acc.1, acc.2.1, (c, c') :: acc.2.2)
  | .ref h t c, .ref h' t' c' =>
    let acc := varsAs t t' (varsAs h h' acc)
    (acc.1, acc.2.1, (c, c') :: acc.2.2)
  | _, _ => acc

/-- A function's type as its signature says it, with what its body found
that is not a contract but how a call is made: the instances of effects at
its sites, and the types left to implementations it uses, in the
signature's variables (`varsAs`); those only the body has stay its own.
None where the body found nothing more (`St.fnCalls`). -/
def withBodyParts (sig body : Scheme) (params : List (Nat × Nat)) : Option Scheme := Id.run do
  -- (Nothing more than the signature has: none.)
  if body.sites.isEmpty && body.incls.isEmpty && body.assocs.length == sig.assocs.length then return none
  -- (The type parameters it writes, by their places; then the type, and
  -- what is left to implementations of what both have.)
  let mut acc := varsAs body.ty sig.ty (params.map (fun (b, s) => (b, Ty.var s)), [], [])
  for _ in [0:3] do
    for (tr, subject, name, a) in body.assocs do
      let (tm, rm, cm) := acc
      let subject := subst tm rm cm subject
      if let some (_, _, _, a') := sig.assocs.find? fun (tr', subject', name', _) =>
          tr' == tr && name' == name && showTy subject' == showTy subject && freeTys subject' == freeTys subject then
        acc := varsAs a a' acc
  let (tm, rm, cm) := acc
  let tr := subst tm rm cm
  return some { sig with
    sites := body.sites.map tr
    assocs := body.assocs.map fun (a, t, n, u) => (a, tr t, n, tr u)
    incls := body.incls.map fun (t, u) => (tr t, tr u)
    tvars := sig.tvars ++ body.tvars.filter fun v => !tm.any (·.1 == v)
    rvars := sig.rvars ++ body.rvars.filter fun v => !rm.any (·.1 == v)
    cvars := sig.cvars ++ body.cvars.filter fun v => !cm.any (·.1 == v) }

/-- Infer one group of mutually recursive functions and generalise their types.
With `signature`, each function's type is what its signature says, its
clauses not looked at: what a caller is checked with (`declareSignatures`). -/
def checkGroup (decls : List FnDecl) (signature : Bool := false) : M Unit := do
  if Glorious.Trace.groupsTraced then
    (dbgTrace s!"group: {", ".intercalate (decls.map (·.name))}" fun _ => (pure () : M Unit))
  let loansAt := (← get).loans.size
  let cellsAt := (← get).cells.size
  modify fun s => { s with valReads := {}, altFound := {}, altArms := {} }
  let mut group : List (String × Ty) := []
  for d in decls do
    group := (d.name, ← freshTy) :: group
  -- (Those written whole, every parameter's type and the result's: a call
  -- of one in the group is at lifetimes of its own, its signature saying
  -- how they are related, as a caller's is.)
  let signed := (decls.filter fun d => !d.annots.isEmpty && d.annots.all Option.isSome && d.ret.isSome).map (·.name)
  let first := decls.filterMap fun d => d.annots.head?.bind id |>.map fun
    | .ref true _ _ => (d.name, 2)
    | .ref false _ _ => (d.name, 1)
    | _ => (d.name, 0)
  modify fun s => { s with group := group, groupSigned := signed, groupFirst := first }
  -- (Of a body checked against its signature: the signature stays what
  -- callers are checked with, with the numbers of its type parameters,
  -- `f<T>(..)`; what the body needs is kept beside it, `schemeWithin`.)
  let fns := (← get).fns
  let params := (← get).typeParams
  -- (What the group finds of a capture made before it is its own: put back
  -- when it is done, `St.capUndo`.)
  let outerBase := (← get).capsBase
  let outerUndo := (← get).capUndo
  modify fun s => { s with capsBase := s.caps.size, capUndo := #[] }
  let sigs := if signature then [] else decls.filterMap fun d =>
    (fns[d.name]?).map fun sig => (d.name, sig, params.lookup d.name)
  let mut defs : List (String × Ty) := []
  let mut reused : List (String × Ty) := []
  if !signature then
    for d in decls do
      let called := decls.any fun e => e.body.exprs.any fun n => match n with
        | .name _ y => y == d.name
        | _ => false
      if called && signed.contains d.name then
        tryCatch (discard (checkGroupFn decls signature group d [] [] (announce := true))) fun _ => pure ()
  for d in decls do
    let (defs', reused') ← onError (checkGroupFn decls signature group d defs reused)
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
  (fun s => Glorious.Trace.said "loans" fun _ => (timedM "group: loans" (checkLoans loansAt cellsAt) : M Unit).run s : M Unit)
  (fun s => Glorious.Trace.said "bounds" fun _ => (timedM "group: bounds" (settleBounds decls defs) : M Unit).run s : M Unit)
  modify fun s => { s with assocUses := #[] }
  -- A callable kept in a declared type's field with no type parameter of its
  -- own is called any number of times, as Rust's `Box<dyn Fn()>`; at most
  -- once where the type says it is used at most once (`Box<dyn FnOnce()>`).
  let s ← get
  let saysOnce := fun (out : Array Nat) => out.any fun e => match s.capEdges.get? e with
    | some (_, .once) => true
    | _ => false
  for (c, was, out) in s.capUndo do
    if was.isNone && s.monoCaps.contains c && !saysOnce out then
      let now := s.capOut.getD c #[]
      for e in now.extract (min out.size now.size) now.size do
        match s.capEdges.get? e with
        | some (_, .once) | some (_, .must) =>
          throw s!"in `{s.owner}`: a callable kept in a field of a declared type written `fn(..)` may be called any number of times, as Rust's `Box<dyn Fn()>`, and this one holds what is used once: give the declaration a type parameter for the field, `R: Fn<..>, R: Use<[0, 1]>`, or say the type is used at most once, `impl Use<[0, 1]> for T \{}`, as Rust's `Box<dyn FnOnce()>`"
        | _ => pure ()
  modify fun s => { s with
    caps := s.capUndo.foldl (fun cs (c, was, _) => cs.set! c was) s.caps
    capOut := s.capUndo.foldl (fun os (c, _, out) => os.set! c out) s.capOut
    capsBase := outerBase, capUndo := outerUndo }
  for (name, sig, ids) in sigs do
    modify fun s => match s.fns[name]? with
      | some body =>
        let written := match ids, s.typeParams.lookup name with
          | some ids, some own => (own.zip ids).filterMap fun
              | (some b, some a) => some (b, a)
              | _ => none
          | _, _ => []
        -- (A constant's type is its value's: a call of it, that.)
        let call := if Syntax.isConstFn name then some body else withBodyParts sig body written
        { s with
          bodySchemes := s.bodySchemes.insert name body
          fns := s.fns.insert name sig
          fnCalls := match call with
            | some call => s.fnCalls.insert name call
            | none => s.fnCalls
          typeParams := match ids with
            | some ids => if Syntax.isConstFn name then s.typeParams else (name, ids) :: s.typeParams
            | none => s.typeParams }
      | none => s
  -- Later functions follow calls into these as they will be elaborated.
  let cs := Elab.firstOf (← get).coercions.toList
  unless cs.isEmpty do
    let write := fun (m : Std.HashMap String Flat.Body) (alt : Std.HashMap String Flat.Body) => decls.foldl (fun m d =>
      match (m[d.name]?).orElse fun _ => alt[d.name]? with
      | some fb => m.insert d.name (Elab.coerceFn cs d.name fb)
      | none => m) m
    modify fun s => { s with runFns := write s.runFns s.declFns }
  -- A later function can still decide a requirement made here: of a type an
  -- implementation's condition says, at the type a later use gives it
  -- (`impl<T> Twice for W<T> where T: Use<[0, *]>`, used at a `Ticket`), so
  -- each is checked again at the end of the program.
  let owner := (decls.head?.map (·.name)).getD "the program"
  -- (Each type once, the first: two alike now are alike whatever is found
  -- later, and what is said is of the first, `checkDrops`.)
  let once := fun (xs : Array (Ty × String)) => (do
    let mut seen : Std.HashSet String := {}
    let mut out : Array (Ty × String) := #[]
    for (t, why) in xs do
      let t ← zonk t
      let key := s!"{showTy t} {← (freeCaps t).mapM findCap} {why}"
      unless seen.contains key do
        seen := seen.insert key
        out := out.push (t, inFunction owner why)
    pure out : M (Array (Ty × String)))
  let late ← once (← get).dups
  let lateDrops ← once (← get).drops
  let lateStays ← once (← get).stays
  modify fun s =>
    { s with group := [], groupSigned := [], groupFirst := [], dups := #[], lateDups := s.lateDups ++ late, drops := #[],
             lateDrops := s.lateDrops ++ lateDrops, stays := #[],
             lateStays := s.lateStays ++ lateStays }

end Glorious.Check
