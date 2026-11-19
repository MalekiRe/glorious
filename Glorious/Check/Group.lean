module

public import Glorious.Check.Bounds

public section

namespace Glorious.Check

open Syntax

/-- What a type says of its own uses may only narrow what its fields allow. -/
def checkUseDecls : M Unit := do
  for (head, must, once) in ((← get).useDecls.toList.map fun (h, m, o) => (h, m, o)).mergeSort (fun a b => a.1 ≤ b.1) do
    if must && (← get).kimpls.has "Drop" head then
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
  let loansAt := (← get).loans.size
  let cellsAt := (← get).cells.size
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
              if members.length ≥ 2 then
                let places := members.filterMap fun (x, _) =>
                  pats.findIdx? fun
                    | .var y => y == x
                    | _ => false
                if must then modify fun s => { s with envMust := d.name :: s.envMust }
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
        unless runsIn.isEmpty do
          modify fun s => { s with fnRunsIn := (d.name, runsIn) :: s.fnRunsIn.filter (·.1 != d.name) }
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
        -- (What is written of its type parameters: `B::Had` of `B: Bundle<S>`
        -- is found by it.)
        modify fun s => { s with paramTraits := d.bounds.map fun b => (b.subject, b.trait, b.args) }
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
        let ret ← match retExpr with
          | some t => some <$> resolveType rigid false t
          | none => pure none
        modify fun s => { s with paramTraits := [] }
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
            -- (`Self` written in its body is that type; so is `T` in a copy of
            -- an implementation for every type, `impl<T: Show> .. for T`.)
            let blanket := im.methods.filterMap fun
              | .typeAlias n _ _ => (Syntax.blanketParam n).map (·, self)
              | _ => none
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
        let t ← timedM "group: infer" (inferCallable [] annots ret (some d.name) d.clauses s!"the clauses of `{d.name}` do")
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
        timedM "group: lower checks" (runLowerChecks t)
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
  timedM "group: loans" (checkLoans loansAt cellsAt)
  timedM "group: bounds" (settleBounds decls defs)
  modify fun s => { s with assocUses := #[] }
  -- Later functions follow calls into these as they will be elaborated.
  let cs := Elab.firstOf (← get).coercions.toList
  unless cs.isEmpty do
    modify fun s =>
      { s with runFns := decls.foldl (fun m d =>
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

end Glorious.Check
