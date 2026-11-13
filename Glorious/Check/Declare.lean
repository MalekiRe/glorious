import Glorious.Check.Unify

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
    -- `T::Item`: the type a trait of `T` leaves to its implementation.
    if let [p, name] := x.splitOn "::" then
      if let some self := params.lookup p then
        let traits := (← get).traitShape.filter fun (_, arity, assocs) => arity == 0 && assocs.contains name
        match traits with
        | [(tr, _, _)] =>
          let a ← freshTy
          modify fun s => { s with assocUses := s.assocUses.push (tr, self, name, a, s.owner, s.pos) }
          return a
        | [] => throw s!"`{x}`: no trait leaves a type `{name}` to its implementations"
        | _ => throw s!"`{x}`: more than one trait leaves a type `{name}` to its implementations"
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
      else if Syntax.isScalar x then
        if args.isEmpty then pure (.con x []) else throw s!"`{x}` takes no arguments"
      else
        match (← get).types.lookup x with
        | some d =>
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
          if decl && args.isEmpty then inferredTy
          else throw s!"unknown type `{x}`"
  | .tuple args => do
    pure (.tuple (← args.mapM (resolveType params decl)))
  | .fn ps r => do
    let ps ← ps.mapM (resolveType params decl)
    let cap ← freshCap
    match r with
    | .performs r effects =>
      -- What it performs is said: these effects and no others.
      let r ← resolveType params decl r
      let effs ← resolveEffects params decl effects
      if decl then modify fun s => { s with monoCaps := cap :: s.monoCaps }
      pure (.fn ps r effs none cap)
    | _ =>
      let r ← resolveType params decl r
      let tail ← freshRowVar
      if decl then
        modify fun s => { s with monoRows := tail :: s.monoRows, monoCaps := cap :: s.monoCaps }
      pure (.fn ps r [] (some tail) cap)
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

/-- Read the traits and their implementations. Types are declared by now. -/
def declareTraits (items : List Item) : M Unit := do
  -- `Drop` is the compiler's: its function is run on what a variable holds
  -- when the variable's block ends.
  let dropSelf ← match ← freshTy with
    | .var id => pure id
    | _ => pure 0
  let dropCap ← freshCap
  modify fun s =>
    { s with
      traits := ("Drop", ["drop"]) :: s.traits
      methods := ("drop", ⟨"Drop", 0, dropSelf, [.ref .uniq (.var dropSelf) dropCap], .unit, [], [], []⟩)
        :: s.methods }
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
      for a in assocNames do
        if let .var id ← freshTy then
          extra := extra ++ [(a, .var id)]
          assocVars := assocVars ++ [(a, id)]
      modify fun s => { s with traitShape := (name, tparams.length, assocNames) :: s.traitShape }
      let mut index := 0
      for (m, params, ret) in methods do
        if ((← get).methods.lookup m).isSome then
          throw s!"`{m}` is declared twice as a function of a trait"
        -- A trait's function has no body its lifetimes could be found from,
        -- so the unwritten ones are one: what it gives may borrow whatever
        -- anything it takes borrows. A lifetime written with a name is its own.
        let named := (params ++ ret.toList).flatMap lifetimesOf
        let mut scope : List (String × Ty) := ("Self", .var self) :: extra
        for l in named.eraseDups do
          scope := scope ++ [(l, Ty.life (← freshCap))]
        let one ← freshCap
        modify fun s => { s with elided := some one }
        let ps ← params.mapM fun p => closeRows <$> resolveType scope false p
        let r ← match ret with
          | some r => closeRows <$> resolveType scope false r
          | none => pure .unit
        modify fun s => { s with elided := none }
        let written := scope.filterMap fun
          | (l, .ref _ _ cap) => some (cap, l)
          | _ => none
        let sig : MethodSig := ⟨name, index, self, ps, r, (one, "'_") :: written, tparams, assocVars⟩
        modify fun s => { s with methods := (m, sig) :: s.methods }
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
        else match (← get).types.lookup head with
          | some d => pure d.arity
          | none => throw s!"{what}: unknown type `{head}`"
      unless args.length == arity do
        throw s!"{what}: `{head}` takes {arity} type arguments, but is given {args.length}"
      unless args.eraseDups.length == args.length && args.all params.contains
          && params.all args.contains do
        throw s!"{what}: the arguments of `{head}` must be the type parameters after `impl`, each once"
      let ctx ← context.mapM fun (p, t') => do
        unless ((← get).traits.lookup t').isSome do throw s!"{what}: unknown trait `{t'}`"
        match args.idxOf? p with
        | some j => pure (t', j)
        | none => throw s!"{what}: `{p}` is not one of its type parameters"
      -- A type parameter said to have a trait has every trait that one needs.
      let mut closed : List (String × Nat) := []
      for (t', j) in ctx do
        for s in t' :: (← supersAll t') do
          unless closed.contains (s, j) do closed := closed ++ [(s, j)]
      let ctx := closed
      let given := methods.filterMap fun
        | .fn m _ _ _ _ => some m
        | _ => none
      for m in names do
        unless given.contains m do throw s!"{what} lacks the function `{m}`"
      for m in given do
        unless names.contains m do throw s!"{what}: `{m}` is not a function of `{tr}`"
      unless given.eraseDups.length == given.length do
        throw s!"{what} gives a function twice"
      if (← get).kimpls.any fun I => I.trait == tr && I.head == head then
        throw s!"`{tr}` is implemented twice for `{head}`"
      -- The arguments it gives its trait, and the types the trait leaves to it.
      let (arityOfTrait, assocNames) := ((← get).traitShape.lookup base).getD (0, [])
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
          unless (freeTys t).isEmpty do
            throw s!"{what}: an argument given to the trait is a type without the implementation's type parameters"
          targs := targs ++ [t]
        | none => throw s!"{what}: `{base}` takes {arityOfTrait} type arguments"
      if (methods.any fun
          | .typeAlias n _ _ => n == Syntax.traitArgName arityOfTrait
          | _ => false) then
        throw s!"{what}: `{base}` takes {arityOfTrait} type arguments"
      let mut assocs : List (String × Ty) := []
      for a in assocNames do
        match methods.findSome? fun
            | .typeAlias n _ body => if n == a then some body else none
            | _ => none with
        | some body => assocs := assocs ++ [(a, ← resolveType pmap false body)]
        | none => throw s!"{what} does not say what `{a}` is: write `type {a} = ..;`"
      for m in methods do
        if let .typeAlias n _ _ := m then
          unless n.startsWith "%" || assocNames.contains n do
            throw s!"{what}: `{n}` is not a type `{base}` leaves to an implementation"
      modify fun s =>
        { s with
          impls := s.impls.push ⟨tr, head, args, ctx, methods, Elab.implDictName tr head, targs, assocs, pvars⟩
          kimpls := s.kimpls ++ [⟨tr, head, arity, ctx⟩] }
  -- What `Traits.coherent` asks of the implementations.
  unless Traits.noOverlap (← get).kimpls do
    throw "two implementations are for the same trait and type"
  -- A type that has a trait has the traits that one needs, on no more
  -- conditions than it has the first.
  let kimpls := (← get).kimpls
  for I in kimpls do
    for s in ((← get).supers.lookup (Syntax.traitBase I.trait)).getD [] do
      match Traits.findImpl s I.head I.arity kimpls with
      | some (_, J) =>
        for c in J.context do
          unless I.context.contains c do
            throw s!"`impl {I.trait} for {bareName I.head}` needs `{s}` of the same type, and `impl {s} for {bareName I.head}` asks `{c.1}` of a type parameter that this one does not"
      | none =>
        throw s!"`impl {I.trait} for {bareName I.head}`: a type that has `{I.trait}` has `{s}`, and there is no `impl {s} for {bareName I.head}`"

def declare (items : List Item) : M Unit := do
  -- Names first, so that declarations may refer to each other.
  for item in items do
    match item with
    | .enum name params ctors =>
      if ((← get).types.lookup name).isSome then throw s!"type `{name}` is declared twice"
      let params := genericParams params
      modify fun s =>
        { s with types :=
            (name, ⟨params.length, ctors.map (·.1), params.map isLifetime, []⟩) :: s.types }
    | .struct name params _ =>
      if ((← get).types.lookup name).isSome then throw s!"type `{name}` is declared twice"
      let params := genericParams params
      modify fun s =>
        { s with types := (name, ⟨params.length, [name], params.map isLifetime, []⟩) :: s.types }
    | .alias name value => modify fun s => { s with aliases := (name, value) :: s.aliases }
    | .coerce name => modify fun s => { s with coercing := s.coercing ++ [name] }
    | .fieldNames ctor names _ =>
      unless names.isEmpty do
        modify fun s => { s with fieldNames := (ctor, names) :: s.fieldNames }
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
          { s with ctors := (c, ⟨name, ids, fields, result, caps, kinds⟩) :: s.ctors }
    | .struct name params fields =>
      let (pmap, ids, caps) ← freshParams params
      let kinds := (genericParams params).map isLifetime
      let fields ← fields.mapM (resolveType pmap true)
      modify fun s =>
        { s with ctors :=
            (name, ⟨name, ids, fields, .con name (pmap.map (·.2)), caps, kinds⟩) :: s.ctors }
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
        let payload ← op.payload.mapM (resolveType pmap true)
        let result ← if op.terminal then pure none
          else match op.result with
            | some t => some <$> resolveType pmap true t
            | none => some <$> resolveType pmap true .hole
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
        modify fun s => { s with ops := (op.name, ⟨name, ids, payload, result, must, lifetimes⟩) :: s.ops }
      modify fun s =>
        { s with effects := (name, ⟨ids, ops.map (·.name), lifetimes.map (·.isSome)⟩) :: s.effects }
    | .use head lower upper =>
      unless ((← get).types.lookup head).isSome do
        throw s!"`impl Use` for `{head}`: there is no such declared type"
      if ((← get).useDecls.lookup head).isSome then
        throw s!"`impl Use` for `{head}` is written twice"
      -- Counting stops at one: the bounds a type can ask for are none or one
      -- use at least, and one use or any number at most.
      unless lower ≤ 1 && (upper == some 1 || upper == none) do
        throw s!"`impl Use` for `{head}`: the fewest uses can be 0 or 1 and the most 1 or `infinity`; other bounds are not counted yet"
      if lower == 1 then modify fun s => { s with anyMust := true }
      modify fun s => { s with useDecls := (head, lower == 1, upper == some 1) :: s.useDecls }
    | _ => pure ()

/-- A constructor's field types and result type at fresh type arguments. -/
def instCtor (sig : CtorSig) : M (List Ty × Ty) := do
  let tm ← sig.tvars.mapM fun id => do
    pure (id, ← freshTy)
  let cm ← sig.cvars.mapM fun c => do
    pure (c, ← freshCap)
  pure (sig.fields.map (subst tm [] cm), subst tm [] cm sig.result)

/-- An operation's payload and result types at the given effect arguments. -/
def instOp (sig : OpSig) (inst : List Ty) : List Ty × Option Ty :=
  let tm := sig.tvars.zip inst
  -- A lifetime of the effect is the one it is given.
  let cm := (sig.lifetimes.zip inst).filterMap fun
    | (some cap, .ref _ _ given) => some (cap, given)
    | _ => none
  (sig.payload.map (subst tm [] cm), sig.result.map (subst tm [] cm))

/-- Resolve a name to a constructor, following constructor aliases. -/
partial def resolveCtor (name : String) (qual : Option String) : M (Option (String × CtorSig)) := do
  let s ← get
  match s.ctors.lookup name with
  | some sig =>
    match qual with
    | some q =>
      if q == sig.owner then pure (some (name, sig))
      else throw s!"`{name}` is not a constructor of `{q}`"
    | none => pure (some (name, sig))
  | none =>
    match s.aliases.lookup name with
    | some (.name q y) => resolveCtor y q
    | _ => pure none

/-- Read a constant expression as a pattern. -/
partial def exprToPat : Expr → M Pattern
  | .int n => pure (.int n)
  | .name q x => pure (if q.isSome then .ctor x q [] else .var x)
  | .call _ (.name q x) args => do
    pure (.ctor x q (← args.mapM exprToPat))
  | .tuple args => do
    pure (.tuple (← args.mapM exprToPat))
  | _ => throw "this constant cannot be used as a pattern"

end Glorious.Check
