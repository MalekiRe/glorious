module

public import Glorious.Check.Unify

public section

namespace Glorious.Check

open Syntax

/-! ## Declarations -/

/-- A type left to be inferred from how the program uses a declaration. -/
def inferredTy : M Ty := do
  let t ← freshTy
  match t with
  | .var id => modify fun s => { s with mono := id :: s.mono }
  | _ => pure ()
  pure t

mutual

/-- Read a type as written. In a declaration, a bare unknown name is a field
whose type is inferred; elsewhere it is an error. -/
partial def resolveType (params : List (String × Ty)) (decl : Bool) : TypeExpr → M Ty
  | .name x args => do
    -- `<T as Trait>::Item`: the same, with the trait said.
    if x == Syntax.assocOfMark then
      match args with
      -- (`<R as Item>::Got<'a>`: of a lifetime, as without it; what is asked
      -- of a type is asked whatever it borrows from.)
      | [self, .name tr targs, .name name nargs] =>
        unless nargs.all (fun | .name l [] => l.startsWith "'" | _ => false) do
          throw s!"`<.. as {Syntax.lastSegment tr}>::{name}<..>`: only lifetimes are written after what a trait leaves"
        let self ← resolveType params decl self
        match ((← get).traitShape[tr]?).map (fun x => (tr, x)) with
        | some (_, arity, assocs) =>
          unless arity == targs.length do
            throw s!"`<.. as {Syntax.lastSegment tr}>::{name}`: `{Syntax.lastSegment tr}` takes {arity} arguments, and is given {targs.length}"
          unless assocs.contains name do
            throw s!"`{Syntax.lastSegment tr}` leaves no `{name}` to its implementations"
          -- (Of a trait with arguments, it is asked of the type together
          -- with them, as the trait is.)
          let targs ← targs.mapM (resolveType params decl)
          let self := if targs.isEmpty then self else Ty.tuple (self :: targs)
          -- (Of a type parameter of an implementation whose types are being
          -- read: kept as written, to be answered at each use.)
          if (freeTys self).any (← get).projecting.contains then
            return .con Syntax.projMark [self, .con tr [], .con name []]
          let a ← freshTy
          modify fun s => { s with assocUses := s.assocUses.push (tr, self, name, a, s.owner, s.pos) }
          return a
        | none => throw s!"unknown trait `{tr}`"
      | _ => throw "`<Type as Trait>::Name` names a trait and what it leaves to an implementation"
    -- `T::Item`: the type a trait of `T` leaves to its implementation.
    if let [p, name] := x.splitOn "::" then
      if let some self := params.lookup p then
        -- In a trait's own declaration, `Self::Item` is the type the trait
        -- leaves open: the one every use of the trait gives its own answer
        -- for, not one answer shared by them all.
        if p == "Self" then
          if !args.isEmpty && (← get).gatScope.contains name then
            return ← resolveType params decl (.name name args)
          if let some own := params.lookup name then return own
        -- (Of a trait written of the parameter that leaves it, with its
        -- arguments: that one, before any other that leaves a type of the
        -- name, `K::Got` of `K: KindOf<T>` in an implementation of `Item`,
        -- which leaves a `Got` too.)
        let mine ← (← get).paramTraits.filterMapM fun (q, tr, targs) => do
          if q != p then return none
          match ((← get).traitShape[tr]?).map (fun x => (tr, x)) with
          | some (_, arity, assocs) => pure (if arity == targs.length && assocs.contains name then some (tr, targs) else none)
          | none => pure none
        if let some (tr, targs) := (if (mine.map (·.1)).eraseDups.length == 1 then mine.head? else none) then
          let targTys ← targs.mapM (resolveType params decl)
          let base := if targTys.isEmpty then self else Ty.tuple (self :: targTys)
          -- (An unwritten lifetime in a function's result is its first
          -- reference's.)
          let asked ← args.mapM fun a => do
            match a, (← get).projElided with
            | .name "'_" [], some c => pure (Ty.life c)
            | _, _ => resolveType params decl a
          let subject := if asked.isEmpty then base else Ty.con Syntax.gatMark (base :: asked)
          if (freeTys self).any (← get).projecting.contains then
            return .con Syntax.projMark [subject, .con tr [], .con name []]
          let a ← freshTy
          modify fun s => { s with assocUses := s.assocUses.push (tr, subject, name, a, s.owner, s.pos) }
          return a
        let traits := (← get).traitShape.toList.filter fun (_, arity, assocs) => arity == 0 && assocs.contains name
        -- (Several: the one written of the parameter, if one is.)
        let written := (← get).paramTraits.filterMap fun (q, tr, _) => if q == p then some tr else none
        -- (None without arguments: one with them written of the parameter,
        -- `B::Had` of `B: Bundle<S>`, asked of the type with those.)
        if traits.isEmpty then
          let withArgs ← (← get).paramTraits.filterMapM fun (q, tr, targs) => do
            if q != p || targs.isEmpty then return none
            match ((← get).traitShape[tr]?).map (fun x => (tr, x)) with
            | some (_, arity, assocs) => pure (if arity == targs.length && assocs.contains name then some (tr, targs) else none)
            | none => pure none
          if let [(tr, targs)] := withArgs then
            let subject := Ty.tuple (self :: (← targs.mapM (resolveType params decl)))
            if (freeTys self).any (← get).projecting.contains then
              return .con Syntax.projMark [subject, .con tr [], .con name []]
            let a ← freshTy
            modify fun s => { s with assocUses := s.assocUses.push (tr, subject, name, a, s.owner, s.pos) }
            return a
        let traits := if traits.length > 1 && !written.isEmpty then
            traits.filter fun (tr, _, _) => written.any fun w => w == tr || Syntax.lastSegment tr == Syntax.lastSegment w
          else traits
        match traits with
        | [(tr, _, _)] =>
          -- (`F::Of<Int>`: asked at types, which go with the type asked. An
          -- unwritten lifetime in a function's result is its first
          -- reference's.)
          let asked ← args.mapM fun a => do
            match a, (← get).projElided with
            | .name "'_" [], some c => pure (Ty.life c)
            | _, _ => resolveType params decl a
          let subject := if asked.isEmpty then self else Ty.con Syntax.gatMark (self :: asked)
          if (freeTys self).any (← get).projecting.contains then
            return .con Syntax.projMark [subject, .con tr [], .con name []]
          let a ← freshTy
          modify fun s => { s with assocUses := s.assocUses.push (tr, subject, name, a, s.owner, s.pos) }
          return a
        | [] => throw s!"`{x}`: no trait leaves a type `{name}` to its implementations"
        | _ => throw s!"`{x}`: more than one trait leaves a type `{name}` to its implementations"
    -- `Of<T>` in a trait's own functions: the type the trait leaves to an
    -- implementation, at these types. Each place it is written has its own
    -- answer, found where the implementation is known.
    if !args.isEmpty && (← get).gatScope.contains x then
      let asked ← args.mapM (resolveType params decl)
      if let .var id ← freshTy then
        modify fun s => { s with gatOccs := s.gatOccs.push (x, asked, id) }
        return .var id
    match params.lookup x with
    | some t =>
      if args.isEmpty then pure t else throw s!"type parameter `{x}` takes no arguments"
    | none =>
      if x.startsWith "'" then Ty.life <$> lifetimeCap params decl (some x)
      else if x == Syntax.rankedMark then
        -- `for<'a> fn(&'a T) -> R`: the callable, noted as one for every `'a`.
        let mut scope := params
        let mut lifetimes : List (Nat × String) := []
        for a in args.dropLast do
          if let .name l [] := a then
            let cap ← freshCap
            scope := (l, Ty.life cap) :: scope
            lifetimes := lifetimes ++ [(cap, l)]
        match args.getLast? with
        | some inner =>
          match ← resolveType scope decl inner with
          | .fn ps r effs tail cap =>
            modify fun s => { s with ranked := (cap, lifetimes) :: s.ranked }
            pure (.fn ps r effs tail cap)
          | _ => throw "`for<..>` is written before the type of a callable: `for<'a> fn(&'a T) -> R`"
        | none => throw "`for<..>` is written before the type of a callable"
      else if x == "Int" then
        if args.isEmpty then pure .int else throw "`Int` takes no arguments"
      else if x == Syntax.consHead then
        -- (A tuple's first and the rest, `(H, ..R)`; a tuple once the rest is.)
        match ← args.mapM (resolveType params decl) with
        | [first, .tuple rest] => pure (.tuple (first :: rest))
        | [first, rest] => pure (.con x [first, rest])
        | _ => throw "a tuple's rest is written last: `(H, ..R)`"
      else if x == Syntax.snocHead then
        -- (All but a tuple's last, and its last, `(..G, X)`.)
        match ← args.mapM (resolveType params decl) with
        | [.tuple init, last] => pure (.tuple (init ++ [last]))
        | [init, last] => pure (.con x [init, last])
        | _ => throw "a tuple's list is written first: `(..G, X)`"
      else if x == Syntax.spreadParams then
        -- (A callable's arguments as many as a tuple has, `Fn<(..P)>`.)
        match ← args.mapM (resolveType params decl) with
        | [t] => pure (.con x [t])
        | _ => throw "`..` before one tuple: `Fn<(..P)>`"
      else if Syntax.isScalar x then
        if args.isEmpty then pure (.con x []) else throw s!"`{x}` takes no arguments"
      else
        match (← get).types[x]? with
        | some d =>
          -- (Its lifetimes not written, `WorldQuery<'_, Q>` or `WorldQuery<Q>`:
          -- each is one left to be found, as in a reference written `&T`.)
          let args := if d.arity != args.length && (d.kinds.filter (!·)).length == args.length then
              (d.kinds.foldl (fun (acc, rest) life =>
                if life then (acc ++ [TypeExpr.name "'_" []], rest)
                else match rest with
                  | a :: more => (acc ++ [a], more)
                  | [] => (acc, [])) (([] : List TypeExpr), args)).1
            else args
          if d.arity != args.length then
            throw s!"type `{x}` takes {d.arity} arguments, but is given {args.length}"
          for (life, a) in d.kinds.zip args do
            let written := match a with
              | .name n [] => n.startsWith "'"
              | _ => false
            unless life == written do
              throw (if life then s!"type `{x}` takes a lifetime where a type is written"
                else s!"type `{x}` takes a type where a lifetime is written")
          pure (.con x (← args.mapM (resolveType params decl)))
        | none =>
          -- (A name written with a capital is a type's, not a field's: one
          -- that is not known is a mistake, not a type to infer.)
          if decl && args.isEmpty && !(Syntax.lastSegment x).front.isUpper then inferredTy
          else if x == "Never" then throw s!"unknown type `Never`: what does not return is written `!`"
          else throw s!"unknown type `{x}`"
  | .tuple args => do
    pure (.tuple (← args.mapM (resolveType params decl)))
  | .fn ps r => do
    let ps ← ps.mapM (resolveType params decl)
    let cap ← freshCap
    -- (In a declaration, one fixed lifetime of its own, as one written is:
    -- what a function that uses the type gives it becomes it, and it does
    -- not become what one function gave, which the next would then see.)
    if decl then modify fun s => { s with monoCaps := cap :: s.monoCaps, rigidCaps := (cap, "the lifetime of a callable a type holds") :: s.rigidCaps }
    match r with
    | .performs r effects =>
      -- What it performs is said: these effects and no others, or these
      -- and whatever a row parameter stands for.
      let r ← resolveType params decl r
      let (effs, tail) ← resolveRow params decl effects
      pure (.fn ps r effs tail cap)
    | _ =>
      let r ← resolveType params decl r
      -- In a declaration, what it performs is what is written: nothing,
      -- where nothing is, as a signature says. (One shared by every function
      -- that uses the type, found from them, would make each depend on the
      -- others' bodies.)
      if decl then pure (.fn ps r [] none cap)
      else pure (.fn ps r [] (some (← freshRowVar)) cap)
  | .performs _ _ =>
    throw "what a callable performs is written after its result: `fn(A) -> R / {Effect}`"
  | .ref uniq t life => do
    let cap ← lifetimeCap params decl life
    pure (.ref (if uniq then .uniq else .shared) (← resolveType params decl t) cap)
  | .never => throw "`!` can only be the result of an operation"
  | .hole => if decl then inferredTy else freshTy

/-- The capture variable a written lifetime stands for. Unwritten, or `'_`,
it is a new one, to be inferred; in a declaration that is one for every value
of the type. -/
partial def lifetimeCap (params : List (String × Ty)) (decl : Bool) (life : Option String) :
    M Nat := do
  let unnamed : M Nat := do
    if let some cap := (← get).elided then return cap
    let cap ← freshCap
    if decl then modify fun s => { s with monoCaps := cap :: s.monoCaps }
    pure cap
  match life with
  | none => unnamed
  | some "'_" => unnamed
  | some "'static" =>
    match (← get).staticCap with
    | some cap => pure cap
    | none =>
      -- A lifetime that is no borrow's: nothing borrowed from a variable has it.
      let cap ← freshCap
      modify fun s =>
        { s with staticCap := some cap, rigidCaps := (cap, "'static") :: s.rigidCaps,
                 monoCaps := cap :: s.monoCaps }
      pure cap
  | some x =>
    match params.lookup x with
    | some (.ref _ _ cap) => pure cap
    | _ => throw s!"unknown lifetime `{x}`: a lifetime is declared with the type parameters, `<{x}>`"

/-- A written row: its effects, and the row parameter that stands for the
rest of it, if one is written (`e`, `{A | e}`). -/
partial def resolveRow (params : List (String × Ty)) (decl : Bool)
    (effects : List (String × List TypeExpr)) : M (List (String × List Ty) × Option Nat) := do
  -- (A row a trait leaves, named of a type parameter of an implementation
  -- being read, is one variable, as any row: not kept as written.)
  let projecting := (← get).projecting
  modify fun s => { s with projecting := [] }
  let r ← resolveRowIn params decl effects
  modify fun s => { s with projecting := projecting }
  pure r

partial def resolveRowIn (params : List (String × Ty)) (decl : Bool)
    (effects : List (String × List TypeExpr)) : M (List (String × List Ty) × Option Nat) := do
  -- What stands for the rest of the row: a row parameter by its name, or
  -- the row a trait leaves to a type's implementation.
  let restOf := fun (entry : String × List TypeExpr) =>
    match entry with
    | (name, [t]) => if name == Syntax.rowMark then some t else none
    | (name, []) =>
      match params.lookup name with
      | some (.fn [] _ [] (some _) _) => some (TypeExpr.name name [])
      | _ => none
    | _ => none
  let rows := effects.filterMap restOf
  let effs ← resolveEffects params decl (effects.filter fun e => (restOf e).isNone)
  -- The row one thing written for the rest stands for.
  let one := fun (t : TypeExpr) => show M Nat from do
    let written := match t with
      | .name e [] => e
      | _ => "what is written after `|`"
    let param := match t with
      | .name e [] => params.lookup e
      | _ => none
    match param with
    | some (.fn [] _ [] (some k) _) => pure k
    | _ =>
      -- `T::Effects`, `<T as Trait>::Effects`: the row a trait of `T` leaves
      -- to its implementation, held as the type of a callable that
      -- performs it.
      let asked := match t with
        | .name e args => e == Syntax.assocOfMark && !args.isEmpty || (e.splitOn "::").length == 2
        | _ => false
      if asked then
        let held ← resolveType params decl t
        match held with
        | .fn [] _ [] (some own) _ => return own
        | _ =>
          let k ← freshRowVar
          unify held (.fn [] .unit [] (some k) (← freshCap))
          return k
      throw s!"`{written}` is not a row parameter here: one is declared `{written}: EffectRow`"
  match rows with
  | [] => pure (effs, none)
  | [t] => pure (effs, some (← one t))
  | _ =>
    -- Several: a row that has each of them in it. What each is is known
    -- where the function is used, and the row is then all of them.
    let all ← freshRowVar
    for t in rows do
      let k ← one t
      modify fun s => { s with rowIncl := s.rowIncl.push (⟨[], some k⟩, ⟨[], some all⟩, s.pos ++ "what is written after `|`") }
    pure (effs, some all)

/-- The effects written after a callable's result. An effect's arguments may
be left out, to be inferred. -/
partial def resolveEffects (params : List (String × Ty)) (decl : Bool)
    (effects : List (String × List TypeExpr)) : M (List (String × List Ty)) := do
  effects.mapM fun (name, args) => do
    match (← get).effects.lookup name with
    | none => throw s!"unknown effect `{name}`"
    | some d =>
      if args.isEmpty then
        pure (name, ← d.fresh)
      else
        unless d.tvars.length == args.length do
          throw s!"effect `{name}` takes {d.tvars.length} arguments, but is given {args.length}"
        pure (name, ← args.mapM (resolveType params decl))

end

/-- Variables for the parameters of a declaration: a type variable for each
type parameter and a capture variable for each lifetime. -/
def freshParams (names : List String) :
    M (List (String × Ty) × List Nat × List Nat) := do
  let mut pairs : Array (String × Ty) := #[]
  let mut ids : Array Nat := #[]
  let mut caps : Array Nat := #[]
  for n in genericParams names do
    if isLifetime n then
      let cap ← freshCap
      pairs := pairs.push (n, Ty.life cap)
      caps := caps.push cap
    else
      match ← freshTy with
      | .var id =>
        pairs := pairs.push (n, .var id)
        ids := ids.push id
      | _ => pure ()
  pure (pairs.toList, ids.toList, caps.toList)

/-- A type with every callable in it performing nothing: what a trait's
function is given performs nothing its caller would have to handle. -/
partial def closeRows : Ty → Ty
  | .var id => .var id
  | .con n args => .con n (args.map closeRows)
  | .tuple args => .tuple (args.map closeRows)
  | .fn ps r _ _ cap => .fn (ps.map closeRows) (closeRows r) [] none cap
  | .ref how t cap => .ref how (closeRows t) cap

/-- Every trait a type must have to have this one, through however many. -/
partial def supersAll (tr : String) : M (List String) := do
  let declared := (← get).supers
  let rec go (fuel : Nat) (seen : List String) (todo : List String) : List String :=
    match fuel, todo with
    | 0, _ => seen
    | _, [] => seen
    | fuel + 1, t :: rest =>
      let more := ((declared.lookup t).getD []).filter fun s => !seen.contains s && s != tr
      go fuel (seen ++ more) (rest ++ more)
  pure (go 64 [] [tr])

/-- The lifetimes a type names, but for `'_` and `'static`. -/
partial def lifetimesOf : TypeExpr → List String
  | .name x args => (if isLifetime x && x != "'_" && x != "'static" then [x] else []) ++ args.flatMap lifetimesOf
  | .tuple args => args.flatMap lifetimesOf
  | .fn ps r => ps.flatMap lifetimesOf ++ lifetimesOf r
  | .performs r effects => lifetimesOf r ++ effects.flatMap fun (_, args) => args.flatMap lifetimesOf
  | .ref _ t life =>
    (match life with
      | some l => if l != "'_" && l != "'static" then [l] else []
      | none => []) ++ lifetimesOf t
  | _ => []

/-- Is a reference written anywhere in a type? -/
partial def writesRef : TypeExpr → Bool
  | .ref _ _ _ => true
  | .name _ args => args.any writesRef
  | .tuple args => args.any writesRef
  | .fn ps r => ps.any writesRef || writesRef r
  | .performs r _ => writesRef r
  | _ => false

/-- Read the traits and their implementations. Types are declared by now. -/
def declareTraits (items : List Item) : M Unit := do
  for item in items do
    if let .fieldNames mark (tr :: asked) [] := item then
      if mark == Syntax.attrMark "blanket_impl" then
        modify fun s => { s with blanketTraits := (tr, asked) :: s.blanketTraits }
  -- `Drop` is the compiler's: its function is run on what a variable holds
  -- when the variable's block ends.
  let dropSelf ← match ← freshTy with
    | .var id => pure id
    | _ => pure 0
  let dropCap ← freshCap
  unless ((← get).traits.lookup "Drop").isSome do
    modify fun s =>
      { s with
        traits := ("Drop", ["drop"]) :: s.traits
        methods := s.methods.insert "drop" ⟨"Drop", 0, dropSelf, [.ref .uniq (.var dropSelf) dropCap], .unit, [], [], [], ⟨[], none⟩, [], [], [], []⟩ }
  for item in items do
    if let .trait name methods := item then
      if ((← get).traits.lookup name).isSome then throw s!"trait `{name}` is declared twice"
      let self ← match ← freshTy with
        | .var id => pure id
        | _ => pure 0
      -- Its own type parameters, and the types it leaves to implementations:
      -- a variable each, the same in all its functions.
      let (params, assocNames) := match items.findSome? fun
          | .traitInfo n _ _ params assocs =>
            -- A lifetime written of a trait is a name its functions' types
            -- may use; it is no argument an implementation gives.
            if n == name then some ((genericParams params).filter (!isLifetime ·), assocs) else none
          | _ => none with
        | some found => found
        | none => ([], [])
      let mut extra : List (String × Ty) := []
      let mut tparams : List Nat := []
      let mut assocVars : List (String × Nat) := []
      for p in params do
        if let .var id ← freshTy then
          extra := extra ++ [(p, .var id)]
          tparams := tparams ++ [id]
      -- A name its functions write after `|` in what they perform is a row
      -- it leaves to an implementation: held as the type of a callable that
      -- takes nothing, gives nothing and performs that row.
      let asRows := methods.flatMap fun (_, _, ret) =>
        match (Syntax.methodGenerics ret).1 with
        | some (.performs _ effects) => effects.filterMap fun
          | (mark, [.name e []]) =>
            match e.splitOn "::" with
            | ["Self", a] => if mark == Syntax.rowMark then some a else none
            | _ => none
          | _ => none
        | _ => []
      let mut rowVars : List (String × Nat) := []
      for a in assocNames do
        if let .var id ← freshTy then
          if asRows.contains a then
            let k ← freshRowVar
            extra := extra ++ [(a, .fn [] .unit [] (some k) (← freshCap))]
            rowVars := rowVars ++ [(a, k)]
          else extra := extra ++ [(a, .var id)]
          assocVars := assocVars ++ [(a, id)]
      -- (In front of what was there, which is kept as it was where it had no
      -- shape of this trait: units checked side by side are put together.)
      modify fun s => { s with traitShape := s.traitShape.insert name (tparams.length, assocNames) }
      let mut index := 0
      for (m, params, ret) in methods do
        -- (The type parameters of its own: a variable each.)
        let (ret, ownNames) := Syntax.methodGenerics ret
        let uses := ownNames.filterMap Syntax.useMarked
        let ownNames := ownNames.filter (!·.startsWith "%")
        let mut mparams : List (String × Nat) := []
        -- (A lifetime among them is one of its lifetimes, as any written.)
        for g in ownNames.filter (!·.startsWith "'") do
          if let .var id ← freshTy then mparams := mparams ++ [(g, id)]
        modify fun s => { s with gatScope := assocNames, gatOccs := #[] }
        if ((← get).methods[m]?).isSome then
          throw s!"`{m}` is declared twice as a function of a trait"
        -- A trait's function has no body its lifetimes could be found from,
        -- so the unwritten ones are one: what it gives may borrow whatever
        -- anything it takes borrows. A lifetime written with a name is its own.
        let named := (params ++ ret.toList).flatMap lifetimesOf
        let mut scope : List (String × Ty) :=
          ("Self", .var self) :: extra ++ mparams.map fun (g, id) => (g, Ty.var id)
        for l in named.eraseDups do
          scope := scope ++ [(l, Ty.life (← freshCap))]
        let one ← freshCap
        -- (Where nothing it gives is a reference, nothing ties what it takes
        -- together: each unwritten lifetime is then its own.)
        modify fun s => { s with elided := if (ret.map writesRef).getD false then some one else none }
        -- (A type another trait of `Self` leaves, `Self::Store` of a trait
        -- this one asks: kept as written, for each implementation and use.)
        -- (And one of what the trait leaves or of its parameters, `<Self::
        -- Components as Registers<S>>::Out`: so each use has its own.)
        modify fun s => { s with projecting := self :: scope.filterMap fun
          | (_, .var id) => some id
          | _ => none }
        let ps ← params.mapM fun p => closeRows <$> resolveType scope false p
        -- What it performs, where the trait says: those effects, and the
        -- row it leaves to an implementation if it names one.
        let (ret, row) ← match ret with
          | some (.performs r effects) => do
            let (effs, tail) ← resolveRow scope false effects
            pure (some r, (⟨effs, tail⟩ : Row))
          | other => pure (other, (⟨[], none⟩ : Row))
        let r ← match ret with
          | some r => closeRows <$> resolveType scope false r
          | none => pure .unit
        modify fun s => { s with elided := none, projecting := [] }
        let written := scope.filterMap fun
          | (l, .ref _ _ cap) => some (cap, l)
          | _ => none
        let gats := (← get).gatOccs.toList
        modify fun s => { s with gatScope := [], gatOccs := #[] }
        let sig : MethodSig :=
          ⟨name, index, self, ps, r, (one, "'_") :: written, tparams, assocVars, row, rowVars, mparams, gats, uses⟩
        modify fun s => { s with methods := s.methods.insert m sig }
        index := index + 1
      modify fun s => { s with traits := (name, methods.map (·.1)) :: s.traits }
  for item in items do
    if let .traitInfo name supers _ _ _ := item then
      for s in supers do
        unless ((← get).traits.lookup s).isSome do
          throw s!"trait `{name}`: unknown trait `{s}`"
        if s == name || (← supersAll s).contains name then
          throw s!"trait `{name}` would need a type to have `{name}` to have it, through `{s}`"
      modify fun st => { st with supers := (name, supers) :: st.supers }
  for item in items do
    if let .impl params tr head args context methods := item then
      let what := s!"`impl {tr} for {head}`"
      -- `tr` is the trait at the arguments the implementation gives it.
      let base := Syntax.traitBase tr
      let names ← match (← get).traits.lookup base with
        | some ns => pure ns
        | none => throw s!"{what}: unknown trait `{base}`"
      let arity ← if head == "Int" || Syntax.isScalar head then pure 0
        else if head.startsWith "(tuple" then pure args.length
        else if head == Syntax.consHead || head == Traits.fnHead then pure 2
        -- (A function's, with what it gives after what it is given; a
        -- reference's, with what it is to.)
        else if head.startsWith "(fn" then pure args.length
        else if head == "(&)" || head == "(&mut)" then pure 1
        else match (← get).types[head]? with
          | some d => pure d.arity
          | none => throw s!"{what}: unknown type `{head}`"
      unless args.length == arity do
        throw s!"{what}: `{head}` takes {arity} type arguments, but is given {args.length}"
      -- (A type parameter that is no argument of the head is inside a type
      -- one of them has to be, or among the trait's own.)
      unless args.eraseDups.length == args.length && args.all params.contains do
        throw s!"{what}: the arguments of `{head}` must be the type parameters after `impl`, each once"
      -- A condition is a trait of one of the head's arguments; or, said
      -- with the trait's own arguments or of a type parameter inside an
      -- argument, one kept apart (`extra`, below).
      let general := fun (k : Nat) (p : String) =>
        !args.contains p || methods.any fun
          | .typeAlias n _ _ => n == Syntax.ctxArgName k 0
          | _ => false
      let ctx ← (context.zipIdx.filter fun ((p, _), k) => !general k p).mapM fun ((p, t'), _) => do
        unless ((← get).traits.lookup t').isSome do throw s!"{what}: unknown trait `{t'}`"
        match args.idxOf? p with
        | some j => pure (t', j)
        | none => throw s!"{what}: `{p}` is not one of its type parameters"
      -- A type parameter said to have a trait has every trait that one needs.
      let mut closed : List (String × Nat) := []
      for (t', j) in ctx do
        for s in t' :: (← supersAll t') do
          unless closed.contains (s, j) do closed := closed ++ [(s, j)]
      -- A function of the implementation may let go of a value of one of
      -- its type parameters: it is given how each is destroyed.
      -- (A lifetime is no value: there is nothing to destroy of one.)
      let ctx := if (← get).dropMode then
          closed ++ ((List.range args.length).filter fun j =>
              !closed.contains (Syntax.destroyTrait, j) && !((args[j]?).getD "").startsWith "'").map
            fun j => (Syntax.destroyTrait, j)
        else closed
      let given := methods.filterMap fun
        | .fn m _ _ _ _ => some m
        | _ => none
      for m in names do
        unless given.contains m do throw s!"{what} lacks the function `{m}`"
      for m in given do
        unless names.contains m do throw s!"{what}: `{m}` is not a function of `{tr}`"
      unless given.eraseDups.length == given.length do
        throw s!"{what} gives a function twice"
      -- A callable that takes hold of a value with a `drop` has to be
      -- called: what is and is not used is then counted, as it is where a
      -- program declares something that has to be used.
      if tr == "Drop" then modify fun s => { s with anyMust := true }
      if (← get).kimpls.has tr head then
        throw s!"`{tr}` is implemented twice for `{head}`"
      -- The arguments it gives its trait, and the types the trait leaves to it.
      let (arityOfTrait, assocNames) := ((← get).traitShape[base]?).getD (0, [])
      let (pmap, _, _) ← freshParams params
      let pvars := pmap.filterMap fun
        | (p, .var id) => some (p, id)
        | _ => none
      let mut targs : List Ty := []
      for i in List.range arityOfTrait do
        match methods.findSome? fun
            | .typeAlias n _ body => if n == Syntax.traitArgName i then some body else none
            | _ => none with
        | some body =>
          let t ← zonk (← resolveType pmap false body)
          targs := targs ++ [t]
        | none => throw s!"{what}: `{base}` takes {arityOfTrait} type arguments"
      if (methods.any fun
          | .typeAlias n _ _ => n == Syntax.traitArgName arityOfTrait
          | _ => false) then
        throw s!"{what}: `{base}` takes {arityOfTrait} type arguments"
      -- An implementation that gives its trait arguments made of its own
      -- type parameters is for the type at all of them: it is the only one
      -- of the trait for the type.
      let generic := targs.any fun t => !(freeTys t).isEmpty
      -- The conditions kept apart, in the implementation's type parameters.
      let mut extra : List (String × List Ty × Ty) := []
      -- (What a trait leaves to implementations, of the implementation's own
      -- type parameters, is kept as written, to be answered at each use:
      -- `<H as Touches>::List: Concat<..>`.)
      modify fun s => { s with projecting := pmap.filterMap fun (_, t) => match t with
        | .var id => some id
        | _ => none }
      for ((p, t'), k) in context.zipIdx do
        if general k p then
          unless ((← get).traits.lookup t').isSome do throw s!"{what}: unknown trait `{t'}`"
          let subject ← match pmap.lookup p with
            | some t => pure t
            | none =>
              match methods.findSome? fun
                  | .typeAlias n _ body => if n == Syntax.ctxSubjectName k then some body else none
                  | _ => none with
              | some body => zonk (← resolveType pmap false body)
              | none => throw s!"{what}: `{p}` is not one of its type parameters"
          let mut cargs : List Ty := []
          for i in List.range ((((← get).traitShape[t']?).map (·.1)).getD 0) do
            match methods.findSome? fun
                | .typeAlias n _ body => if n == Syntax.ctxArgName k i then some body else none
                | _ => none with
            | some body => cargs := cargs ++ [← zonk (← resolveType pmap false body)]
            | none => throw s!"{what}: `{Syntax.lastSegment t'}` takes arguments: `{p}: {Syntax.lastSegment t'}<..>`"
          extra := extra ++ [(t', cargs, subject)]
      modify fun s => { s with projecting := [] }
      -- A type parameter inside one of the head's arguments (`H` of
      -- `(Column<H>, R)`): its functions may let go of a value of it too, so
      -- it is given how that is destroyed, as a head's argument is.
      -- (Not of a callable's parameters and result: a callable holds no
      -- value of those to destroy. Nor of a list of types.)
      if (← get).dropMode && !head.startsWith "(fn" then
        let said := context.filterMap fun (p, t') => if t' == Syntax.destroyTrait then some p else none
        for p in genericParams params do
          if !args.contains p && !p.startsWith "'" && !p.startsWith ".." && !said.contains p then
            if let some subject := pmap.lookup p then
              extra := extra ++ [(Syntax.destroyTrait, [], subject)]
      -- (A value is destroyed knowing only its type's shape and how its
      -- parts are: a `Drop` may ask its type parameters for traits without
      -- arguments, which every value of the type then has to have, and no
      -- more. Rust asks the same: as the type's declaration does.)
      if tr == "Drop" && extra.any (·.1 != Syntax.destroyTrait) then
        throw s!"{what}: a `Drop` may ask its type parameters only for traits without arguments; keep what it needs in the value instead (a callable made where the trait is known)"
      let mut assocs : List (String × Ty) := []
      let mut gatParams : List (String × List (Bool × Nat)) := []
      for a in assocNames do
        match methods.findSome? fun
            | .typeAlias n takes body => if n == a then some (takes, body) else none
            | _ => none with
        | some (takes, body) =>
          -- What an implementation gives is said, as Rust has it: every type
          -- it gives is known before any function's body is checked.
          if let .hole := body then
            throw s!"{what}: `type {a} = _;`: an implementation says what each type it gives is: write it, `type {a} = ..;`"
          -- (`type Of<T> = [T];`: what it takes, a variable each.)
          let mut own : List (String × Ty) := []
          let mut ids : List (Bool × Nat) := []
          for p in takes do
            if p.startsWith "'" then
              let cap ← freshCap
              own := own ++ [(p, Ty.life cap)]
              ids := ids ++ [(true, cap)]
            else if let .var id ← freshTy then
              own := own ++ [(p, .var id)]
              ids := ids ++ [(false, id)]
          unless ids.isEmpty do gatParams := gatParams ++ [(a, ids)]
          -- (`K::Got` of a type parameter: of the trait written of it here,
          -- `K: KindOf<T>`, with its arguments.)
          let written := context.zipIdx.map fun ((p, t'), k) =>
            let targs := (List.range 16).filterMap fun i => methods.findSome? fun
              | .typeAlias n _ body => if n == Syntax.ctxArgName k i then some body else none
              | _ => none
            (p, Syntax.traitBase t', targs)
          let projecting := pmap.filterMap fun (_, t) => match t with
            | .var id => some id
            | _ => none
          modify fun s => { s with projecting := projecting, paramTraits := written }
          let said ← resolveType (own ++ pmap) false body
          modify fun s => { s with projecting := [], paramTraits := [] }
          assocs := assocs ++ [(a, said)]
        | none => throw s!"{what} does not say what `{a}` is: write `type {a} = ..;`"
      for m in methods do
        if let .typeAlias n _ _ := m then
          unless n.startsWith "%" || assocNames.contains n do
            throw s!"{what}: `{n}` is not a type `{base}` leaves to an implementation"
      -- The arguments fixed by the name the implementation was written for.
      let mut fixed : List (Nat × Ty) := []
      for j in List.range arity do
        match methods.findSome? fun
            | .typeAlias n _ body => if n == Syntax.fixedArgName j then some body else none
            | _ => none with
        | some body => fixed := fixed ++ [(j, ← resolveType pmap false body)]
        | none => pure ()
      -- What its conditions say of types left to implementations.
      let mut equal : List (Nat × String × String × Ty) := []
      let mut extraEqual : List (Ty × String × String × Ty) := []
      for m in methods do
        if let .typeAlias n _ body := m then
          if let some (k, name) := Syntax.equalArgParts n then
            match context[k]? with
            | some (subject, asked) =>
              let left := (((← get).traitShape[asked]?).map (·.2)).getD []
              unless left.contains name do
                throw s!"{what}: `{Syntax.lastSegment asked}` leaves no type `{name}` to its implementations"
              match args.idxOf? subject with
              | some j => equal := equal ++ [(j, asked, name, ← resolveType pmap false body)]
              | none =>
                -- (Of another type parameter, or of a type made of them.)
                let whole ← match pmap.lookup subject with
                  | some t => pure t
                  | none =>
                    match methods.findSome? fun
                        | .typeAlias n _ b => if n == Syntax.ctxSubjectName k then some b else none
                        | _ => none with
                    | some b => zonk (← resolveType pmap false b)
                    | none => throw s!"{what}: `{subject}` is not one of its type parameters"
                -- (The trait's own arguments go with the type asked of.)
                let mut cargs : List Ty := []
                for i in List.range ((((← get).traitShape[asked]?).map (·.1)).getD 0) do
                  match methods.findSome? fun
                      | .typeAlias n _ b => if n == Syntax.ctxArgName k i then some b else none
                      | _ => none with
                  | some b => cargs := cargs ++ [← zonk (← resolveType pmap false b)]
                  | none => pure ()
                let whole := if cargs.isEmpty then whole else Ty.tuple (whole :: cargs)
                extraEqual := extraEqual ++ [(whole, asked, name, ← resolveType pmap false body)]
            | none => pure ()
      if let some other := (← get).impls.find? fun I => I.trait == tr && I.head == head then
        unless fixed.isEmpty && other.fixed.isEmpty do
          throw s!"{what}: `{head}` already has an implementation of `{base}`, under this name or another of its names; a type has one"

      -- Chosen by fitting types: where an implementation has a condition
      -- kept apart, or shares its trait and type with another.
      let shared := !(← implsOfHead base head).isEmpty
      if !extra.isEmpty || shared || head.startsWith "(fn" || head.startsWith "(&" then
        modify fun s => { s with patterned := true }
      -- Two implementations of a trait for one type: no type is both's
      -- (`From<Int>`, `From<Str>`), or one asks more of the type than the
      -- other (`Wrap<Int>`, `Wrap<T>`), and is then the one for the types it
      -- fits. Not the same twice, and not two that some type fits with
      -- neither asking more.
      let patternOf := fun (targs : List Ty) (fixed : List (Nat × Ty)) (params : List String)
          (pvars : List (String × Nat)) =>
        targs ++ (List.range arity).map fun j =>
          match fixed.lookup j with
          | some t => t
          | none => (((params[j]?).bind fun p => pvars.lookup p).map Ty.var).getD (.var 0)
      let mine := patternOf targs fixed args pvars
      for other in ← implsOfHead base head do
        if other.targs.length == targs.length then
          let theirs := patternOf other.targs other.fixed other.params other.pvars
          let narrower := (Ty.fitsAll (other.pvars.map (·.2)) theirs mine []).isSome
          let wider := (Ty.fitsAll (pvars.map (·.2)) mine theirs []).isSome
          if narrower && wider then
            throw s!"`{Syntax.traitShown other.trait}` is implemented twice for `{head}`"
          if !narrower && !wider && (Ty.meetAll mine theirs []).isSome then
            throw s!"`impl {Syntax.traitShown tr} for {bareName head}`: some type fits this and another implementation of `{Syntax.traitShown other.trait}` for `{bareName head}` both, and neither asks more of it than the other: say which is for those, with an implementation for just them"
      modify fun s =>
        { s with
          implsByBase := s.implsByBase.insert (Syntax.traitBase tr)
            ((s.implsByBase.getD (Syntax.traitBase tr) #[]).push s.impls.size)
          implsByHead := s.implsByHead.insert (Syntax.traitBase tr, head)
            ((s.implsByHead.getD (Syntax.traitBase tr, head) #[]).push s.impls.size)
          impls := s.impls.push
            { trait := tr, head, params := args, context := ctx, methods,
              dictFn := Elab.implDictName tr head, targs, assocs, pvars, fixed, equal, generic, extra,
              gatParams, extraEqual }
          kimpls := s.kimpls.push ⟨tr, head, arity, ctx⟩ }
  -- Every type can be destroyed: by nothing at all, by its own `Drop` and
  -- then its parts', or part by part. Said as an implementation for each
  -- type, on condition that each type parameter can be destroyed, and that
  -- what its `Drop` asks is met.
  if (← get).dropMode then
    unless ((← get).traits.lookup Syntax.destroyTrait).isSome do
      modify fun s => { s with traits := (Syntax.destroyTrait, [Syntax.destroyFn]) :: s.traits }
    let builtin := ["Int", "(callable)", "(reference)"] ++ Syntax.scalars.map (·.1)
      ++ (List.range 17).map fun n => s!"(tuple{n})"
    let declared := (← get).types.toList.map fun (name, decl) =>
      -- (which of its parameters are types)
      (name, decl.arity, (List.range decl.arity).filter fun j => decl.kinds[j]? != some true)
    let heads := builtin.map (fun h =>
        if h.startsWith "(tuple" then
          let n := ((h.drop 6).takeWhile Char.isDigit).toString.toNat!
          (h, n, List.range n)
        else (h, 0, []))
      ++ declared
    for (head, arity, typeParams) in heads do
      unless (← get).kimpls.has Syntax.destroyTrait head do
        let own := typeParams.map fun j => (Syntax.destroyTrait, j)
        let drops := ((← get).kimpls.firstFor "Drop" head).map (·.context)
        let ctx := own ++ (drops.getD []).filter (!own.contains ·)
        modify fun s =>
          { s with
            implsByBase := s.implsByBase.insert (Syntax.traitBase Syntax.destroyTrait)
              ((s.implsByBase.getD (Syntax.traitBase Syntax.destroyTrait) #[]).push s.impls.size)
            implsByHead := s.implsByHead.insert (Syntax.traitBase Syntax.destroyTrait, head)
              ((s.implsByHead.getD (Syntax.traitBase Syntax.destroyTrait, head) #[]).push s.impls.size)
            impls := s.impls.push
              ⟨Syntax.destroyTrait, head, (List.range arity).map (s!"T{·}"), ctx, [],
                Elab.implDictName Syntax.destroyTrait head, [], [], [], [], [], false, [], [], []⟩
            kimpls := s.kimpls.push ⟨Syntax.destroyTrait, head, arity, ctx⟩ }
  -- What `Traits.coherent` asks of the implementations.
  unless Traits.noOverlap (← get).kimpls.impls.toList do
    throw "two implementations are for the same trait and type"
  unless Traits.noConsOverlap (← get).kimpls.impls.toList do
    let impls := (← get).kimpls.impls.toList
    let tr := ((impls.find? fun J => impls.any fun I => Traits.overlapsView I J).map (·.trait)).getD ""
    throw s!"`{bareName tr}` is implemented for every length, `(H, ..R)` or `fn(..P) -> R`, and for a tuple or a function of one length: each has one implementation"
  -- A type that has a trait has the traits that one needs, on no more
  -- conditions than it has the first.
  let kimpls := (← get).kimpls
  for I in kimpls.impls do
    for s in ((← get).supers.lookup (Syntax.traitBase I.trait)).getD [] do
      match kimpls.find s I.head I.arity with
      | some (_, J) =>
        for c in J.context do
          unless I.context.contains c do
            throw s!"`impl {I.trait} for {bareName I.head}` needs `{s}` of the same type, and `impl {s} for {bareName I.head}` asks `{c.1}` of a type parameter that this one does not"
      | none =>
        throw s!"`impl {I.trait} for {bareName I.head}`: a type that has `{I.trait}` has `{s}`, and there is no `impl {s} for {bareName I.head}`"

def declare (items : List Item) : M Unit := do
  -- What each trait leaves to its implementations, first: an effect's
  -- operation may name it of the effect's type parameters (`S::Out`).
  for item in items do
    if let .traitInfo n _ _ params assocs := item then
      unless (← get).traitShape.contains n do
        let params := (genericParams params).filter (!isLifetime ·)
        modify fun s => { s with traitShape := s.traitShape.insert n (params.length, assocs) }
  -- Names first, so that declarations may refer to each other.
  for item in items do
    match item with
    | .enum name params ctors =>
      if ((← get).types[name]?).isSome then throw s!"type `{name}` is declared twice"
      let params := genericParams params
      modify fun s =>
        { s with types :=
            s.types.insert name ⟨params.length, ctors.map (·.1), params.map isLifetime, []⟩ }
    | .struct name params _ =>
      if ((← get).types[name]?).isSome then throw s!"type `{name}` is declared twice"
      let params := genericParams params
      modify fun s =>
        { s with types := s.types.insert name ⟨params.length, [name], params.map isLifetime, []⟩ }
    | .alias name value => modify fun s =>
      { s with aliases := s.aliases.insert name value, runAliases := s.runAliases.insert name value }
    | .coerce name => modify fun s => { s with coercing := s.coercing ++ [name] }
    | .unsafeFn name => modify fun s => { s with unsafeFns := name :: s.unsafeFns }
    | .fieldNames ctor names _ =>
      if ctor == Syntax.arrayMark then
        modify fun s => { s with arrayType := names.head? }
      else unless names.isEmpty do
        modify fun s => { s with fieldNames := s.fieldNames.insert ctor names }
    | _ => pure ()
  for item in items do
    match item with
    | .enum name params ctors =>
      let (pmap, ids, caps) ← freshParams params
      let kinds := (genericParams params).map isLifetime
      let result := Ty.con name (pmap.map (·.2))
      for (c, fields) in ctors do
        let fields ← fields.mapM (resolveType pmap true)
        modify fun s =>
          { s with ctors := s.ctors.insert c ⟨name, ids, fields, result, caps, kinds⟩,
                   runCtors := s.runCtors.insert c }
    | .struct name params fields =>
      let (pmap, ids, caps) ← freshParams params
      let kinds := (genericParams params).map isLifetime
      let fields ← fields.mapM (resolveType pmap true)
      modify fun s =>
        { s with ctors := s.ctors.insert name ⟨name, ids, fields, .con name (pmap.map (·.2)), caps, kinds⟩,
                 runCtors := s.runCtors.insert name }
    | .effect name params ops =>
      -- A lifetime of an effect is given where the effect is handled: what
      -- an operation gives or takes may borrow for that long.
      let (pmap, _, _) ← freshParams params
      let mut ids : List Nat := []
      let mut lifetimes : List (Option Nat) := []
      for (_, t) in pmap do
        match t with
        | .var id =>
          ids := ids ++ [id]
          lifetimes := lifetimes ++ [none]
        | .ref _ _ cap =>
          ids := ids ++ [match ← freshTy with
            | .var id => id
            | _ => 0]
          lifetimes := lifetimes ++ [some cap]
        | _ => pure ()
      for op in ops do
        -- (Its own lifetimes, and those it does not write: not the
        -- declaration's, but each use's.)
        let before := (← get).monoCaps
        let mut own : List (String × Ty) := []
        for l in op.lifetimes do
          own := own ++ [(l, Ty.life (← freshCap))]
        let opMap := own ++ pmap
        -- (`S::Out` of a type parameter of the effect: kept as written, and
        -- answered at each use, at the type the use gives.)
        let projecting := (← get).projecting
        let written := items.findSome? fun
          | .bounds n bs => if n == name then some bs else none
          | .module _ (some inner) => inner.findSome? fun
            | .bounds n bs => if n == name then some bs else none
            | _ => none
          | _ => none
        modify fun s => { s with projecting := ids
                                 paramTraits := ((written.getD []).map fun b => (b.subject, b.trait, b.args)) }
        let payload ← op.payload.mapM (resolveType opMap true)
        let result ← if op.terminal then pure none
          else match op.result with
            | some t => some <$> resolveType opMap true t
            | none => some <$> resolveType opMap true .hole
        modify fun s => { s with projecting := projecting, paramTraits := [] }
        -- (Of references only: a callable it is given or gives is held to
        -- what the declaration says, as before.)
        let rec refCaps : Ty → List Nat
          | .ref _ t c => c :: refCaps t
          | .con _ args => args.flatMap refCaps
          | .tuple args => args.flatMap refCaps
          | _ => []
        let atRefs := (payload ++ result.toList).flatMap refCaps
        let made := (← get).monoCaps.filter fun c => !before.contains c && atRefs.contains c
        modify fun s => { s with monoCaps := s.monoCaps.filter (!made.contains ·) }
        let caps := made ++ own.filterMap fun (_, t) => match t with
          | .ref _ _ c => some c
          | _ => none
        -- A resumption is resumed at most once, so the most uses is one; the
        -- fewest says whether it may simply be let go.
        let must ← match op.quantity with
          | none => pure false
          | some (lower, upper) =>
            if op.terminal then
              throw s!"operation `{op.name}` does not return, so it has no resumption to say this of"
            unless upper == some 1 do
              throw s!"operation `{op.name}`: a resumption is used at most once, so write `[0, 1]` or `[1, 1]`"
            pure (lower == 1)
        if must then modify fun s => { s with anyMust := true }
        modify fun s =>
          { s with ops := (op.name, ⟨name, ids, payload, result, must, lifetimes, caps⟩) :: s.ops,
                   runOps := s.runOps.insert op.name result.isSome,
                   runExact := if must && result.isSome then s.runExact.insert op.name
                     else s.runExact.erase op.name }
      modify fun s =>
        { s with effects := (name, ⟨ids, ops.map (·.name), lifetimes.map (·.isSome)⟩) :: s.effects }
    | .use head lower upper =>
      unless ((← get).types[head]?).isSome do
        throw s!"`impl Use` for `{head}`: there is no such declared type"
      if (← get).useDecls.contains head then
        throw s!"`impl Use` for `{head}` is written twice"
      -- The language has three: any number of uses, at most one, and exactly
      -- one (specification 7.1). At least one is counted here as well.
      unless lower ≤ 1 && (upper == some 1 || upper == none) do
        throw s!"`impl Use` for `{head}`: a type is used any number of times (`[0, infinity]`), at most once (`[0, 1]`) or exactly once (`[1, 1]`); the language has no other count"
      if lower == 1 then modify fun s => { s with anyMust := true }
      modify fun s => { s with useDecls := s.useDecls.insert head (lower == 1, upper == some 1) }
    | _ => pure ()
  -- A type each constructor of which holds a value of the type itself, with
  -- nothing between, has no value that can be built: its layout does not end
  -- (specification 5). A type is founded if one of its constructors holds
  -- only founded values; what is not a declared type is.
  let s ← get
  let rec heads : Ty → List String
    | .con n _ => [n]
    | .tuple ts => ts.flatMap heads
    | _ => []
  let ctorsOf := fun (n : String) => ((s.types[n]?).map (·.ctors)).getD []
  let mut founded : List String := (s.types.toList.filter fun (_, d) => d.ctors.isEmpty).map (·.1)
  let mut changed := true
  let mut fuel := s.types.size + 1
  while changed && fuel > 0 do
    changed := false
    fuel := fuel - 1
    for (n, d) in s.types do
      unless founded.contains n do
        let ok := d.ctors.any fun c =>
          match s.ctors[c]? with
          | some sig => (sig.fields.flatMap heads).all fun h =>
              founded.contains h || (s.types[h]?).isNone
          | none => true
        if ok then
          founded := n :: founded
          changed := true
  for item in items do
    let name := match item with
      | .enum name _ _ => some name
      | .struct name _ _ => some name
      | _ => none
    if let some name := name then
      unless founded.contains name || (ctorsOf name).isEmpty do
        throw s!"type `{name}` holds a value of itself in every constructor, so no value of it can be built: give it a constructor that does not, or hold the value in an `Array` or behind a reference"

/-- A constructor's field types and result type at fresh type arguments. -/
def instCtor (sig : CtorSig) : M (List Ty × Ty) := do
  let tm ← sig.tvars.mapM fun id => do
    pure (id, ← freshTy)
  let cm ← sig.cvars.mapM fun c => do
    pure (c, ← freshCap)
  pure (sig.fields.map (subst tm [] cm), subst tm [] cm sig.result)

/-- An operation's payload and result types at the given effect arguments. -/
def instOp (sig : OpSig) (inst : List Ty) (own : List (Nat × Nat) := []) : List Ty × Option Ty :=
  let tm := sig.tvars.zip inst
  -- A lifetime of the effect is the one it is given; one of the operation's
  -- own is this use's (`own`).
  let cm := own ++ (sig.lifetimes.zip inst).filterMap fun
    | (some cap, .ref _ _ given) => some (cap, given)
    | _ => none
  (sig.payload.map (subst tm [] cm), sig.result.map (subst tm [] cm))

/-- Resolve a name to a constructor, following constructor aliases. -/
partial def resolveCtor (name : String) (qual : Option String) : M (Option (String × CtorSig)) := do
  let s ← get
  match s.ctors[name]? with
  | some sig =>
    match qual with
    | some q =>
      if q == sig.owner then pure (some (name, sig))
      else throw s!"`{name}` is not a constructor of `{q}`"
    | none => pure (some (name, sig))
  | none =>
    -- `[a, b, c]` in a pattern: the array type's constructor of so many
    -- elements, each of the element's type.
    if let (some n, some array) := (Syntax.arrayPatLen name, s.arrayType) then
      if let some sig := s.ctors[array]? then
        return some (name, { sig with fields := List.replicate n (sig.fields.headD .unit) })
    match (s.aliases[name]?).map Syntax.aliasValue with
    | some (.name q y) => resolveCtor y q
    | _ => pure none

/-- Read a constant expression as a pattern. -/
partial def exprToPat : Expr → M Pattern
  | .int n => pure (.int n)
  | .name q x => pure (if q.isSome then .ctor x q [] else .var x)
  | .call _ (.name q x) args => do
    -- A constant written with its type is its value.
    if q.isNone && x == Syntax.ascribeMark then
      if let value :: _ := args then return ← exprToPat value
    pure (.ctor x q (← args.mapM exprToPat))
  | .tuple args => do
    pure (.tuple (← args.mapM exprToPat))
  | _ => throw "this constant cannot be used as a pattern"

end Glorious.Check
