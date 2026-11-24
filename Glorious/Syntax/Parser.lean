module

public import Glorious.Syntax.Parser.Expr
public import Glorious.Syntax.Resolve

public section

namespace Glorious.Syntax

open Parse

/-- The aliases a declaration's type parameters' defaults are kept under:
by their place among the parameters, and, where lifetimes come before, by
their place among the types alone, for a use that writes no lifetime. -/
private def defaultAliases (name : String) (params : List String)
    (defaults : List (Nat × List String × TypeExpr)) : List Item :=
  defaults.flatMap fun (i, earlier, ty) =>
    if earlier == [variadicMark] then [.typeAlias (variadicName name) [] (.name (toString i) [])] else
    let lives := ((params.take i).filter (·.startsWith "'")).length
    .typeAlias (defaultName name i) earlier ty
      :: (if lives == 0 then [] else [.typeAlias (defaultName name (i - lives) ++ "~") earlier ty])

/-- A constant's value, `const NAME: T = value`: worked out at compile time,
of that type (`constItems`), in a body of its own. -/
private def constValue (ty : TypeExpr) : P (Flat.Body × Flat.ExprId) := valueOf do
  let value ← callOf 0 none ascribeMark #[← parseBinary 0 false, ← tree ty.asExpr]
  callOf 0 none comptimeMark #[value]

/-- A function that takes nothing and gives the value written. -/
private def valueFn : P Flat.Body := bodyOf do
  pure #[← mkC [] #[← mkS (.expr (← parseBinary 0 false))]]

private partial def parseItem : P Item := do
  match ← peek with
  | .ident "effect" =>
    advance
    let name ← expectIdent
    -- What is asked of an effect's parameter is asked where one of its
    -- operations is performed.
    let (params, bounds) ← parseGenericsWith
    let (_, more) ← parseWhere
    let asked := bounds ++ more
    expectPunct "{"
    let mut ops : Array OpDecl := #[]
    repeat
      if (← peek) == .punct "}" then break
      let quantity ← if (← peek) == .punct "[" then some <$> parseQuantity else pure none
      let op ← expectIdent
      -- (The machine's types give an operation one type wherever an effect
      -- is handled, so it has no type parameters apart from the effect's;
      -- lifetimes it may have, each performance its own.)
      let mut own : List String := []
      if ← isOp "<" then
        let lifetimeFirst := match ← peek 1 with
          | .ident l => l.startsWith "'"
          | _ => false
        let names ← if lifetimeFirst then parseGenerics else pure ["T"]
        unless names.all (·.startsWith "'") do
          failAt s!"the operation `{op}` cannot have type parameters of its own: an operation has one type wherever its effect is handled. Give the effect the parameter, `effect {name}<T> \{ {op}(..) }`"
        own := names
      expectPunct "("
      let payload ← parseTypeList ")"
      let mut terminal := false
      let mut result : Option TypeExpr := none
      if ← acceptPunct "->" then
        if ← isOp "!" then
          advance
          terminal := true
        else
          result := some (← parseType)
      ops := ops.push ⟨op, payload, result, terminal, quantity, own⟩
      -- An operation ends with `,` or `;`, or with nothing at all.
      if !(← acceptPunct ",") then
        let _ ← acceptPunct ";"
    expectPunct "}"
    if asked.isEmpty then pure (.effect name params ops.toList)
    else pure (.module inherentMark (some [.effect name params ops.toList, .bounds name asked]))
  | .ident "fn" =>
    let (item, bounds) ← parseFn
    unless bounds.isEmpty do
      failAt "what is asked of a type parameter is written on a function of a module, not of an implementation"
    pure item
  | .ident "let" =>
    advance
    let name ← expectIdent
    -- `let NAME: Type = value;`: the value, of that type.
    let ty ← if ← acceptPunct ":" then some <$> parseType else pure none
    expectPunct "="
    let (body, value) ← valueOf do
      let value ← parseBinary 0 false
      match ty with
      | some ty => callOf 0 none ascribeMark #[value, ← tree ty.asExpr]
      | none => pure value
    expectPunct ";"
    pure (.alias name body value)
  | .ident "const" =>
    -- `const NAME: Type = value;`: worked out once, at compile time
    -- (`constItems`).
    advance
    let name ← expectIdent
    expectPunct ":"
    let ty ← parseType
    expectPunct "="
    let (body, value) ← constValue ty
    expectPunct ";"
    pure (.alias name body value)
  | .ident "impl" =>
    advance
    -- (`impl<T: Show> ..`: what is asked of a parameter, as `where T: Show`.)
    let (params, early) ← if ← isOp "<" then parseGenericsWith else pure ([], [])
    let early := early.filter (·.trait != knownTrait)
    -- `impl !Trait for Type {}`: the type does not have the trait, and no
    -- implementation may say it does.
    if ← isOp "!" then
      advance
      let tr ← expectPath
      match ← peek with
      | .ident "for" => advance
      | _ => failAt "expected `for`: `impl !Trait for Type {}`"
      let head ← expectPath
      let _ ← parseGenerics
      expectPunct "{"
      expectPunct "}"
      return .fieldNames (attrMark "negative_impl") [tr, head] []
    let tr ← expectPath
    -- `impl From<Int> for u8`: the trait's own arguments, kept among what
    -- the implementation declares.
    let mut given : Array Item := #[]
    -- (All that is written between the brackets, lifetimes too: what `Self`
    -- is where the functions are the type's own.)
    let mut selfArgs : Array TypeExpr := #[]
    if tr != "Use" && (← isOp "<") then
      advance
      repeat
        if ← isOp ">" then break
        match ← peek with
        | .ident l =>
          -- A lifetime here is only a name: nothing is given for it.
          if l.startsWith "'" then
            advance
            selfArgs := selfArgs.push (.name l [])
          else
            let arg ← parseType
            selfArgs := selfArgs.push arg
            given := given.push (.typeAlias (traitArgName given.size) [] arg)
        | _ =>
          let arg ← parseType
          selfArgs := selfArgs.push arg
          given := given.push (.typeAlias (traitArgName given.size) [] arg)
        if !(← acceptPunct ",") then break
      expectOp ">"
    if tr == "Use" && (← isOp "<") then
      advance
      let (lower, upper) ← parseQuantity
      if ← isOp ">" then advance else failAt "expected `>`"
      match ← peek with
      | .ident "for" => advance
      | _ => failAt "expected `for`: `impl Use<[1, 1]> for Type {}`"
      let head ← expectPath
      let _ ← parseGenerics
      expectPunct "{"
      expectPunct "}"
      return .use head lower upper
    -- `impl Type { fn .. }`: functions of the type's own. Each is a function
    -- of this module named `Type::f`, and is written that way where it is
    -- called.
    -- (`impl<T> Type<T> where T: Hash { .. }`: asked of each of its functions.)
    let (_, shared) ← if (← peek) == .ident "where" then parseWhere else pure ([], [])
    let shared := early ++ shared
    if (← peek) == .punct "{" then
      advance
      let self := TypeExpr.name tr selfArgs.toList
      let mut items : Array Item := #[]
      repeat
        if (← peek) == .punct "}" then break
        let vis ← acceptPub
        -- `const NAME: Type = value;`: a value of the type's own, named
        -- `Type::NAME`.
        if (← peek) == .ident "const" then
          advance
          let name ← expectIdent
          expectPunct ":"
          let ty := TypeExpr.withSelf self (← parseType)
          expectPunct "="
          let (body, value) ← constValue ty
          expectPunct ";"
          let c := Item.alias s!"{tr}::{name}" body value
          items := items.push (match vis with
            | some parent => .pub parent c
            | none => c)
          continue
        if (← peek) != .ident "fn" then failAt "expected `fn` or `const`: an implementation gives functions and values"
        let (item, bounds) ← withReader (fun c =>
          if c.records.contains tr then { c with records := "Self" :: c.records } else c) parseFn
        match item with
        | .fn name ps annots ret body =>
          -- (Its own type parameters first: `app.on<E, P>(..)` gives those,
          -- as `.on::<E, P>()` does in Rust; the type's are known from what
          -- the function is given.)
          let mine := ps.filter (!params.contains ·)
          let ps := if (mine.filter (!·.startsWith "'")).isEmpty then params ++ mine else mine ++ params
          let own := s!"{tr}::{name}"
          let f := Item.fn own ps (annots.map (·.map (TypeExpr.withSelf self)))
            (ret.map (TypeExpr.withSelf self)) ((Flat.selfRewrite tr none).body body)
          items := items.push (match vis with
            | some parent => .pub parent f
            | none => f)
          let bounds := bounds ++ shared
          unless bounds.isEmpty do items := items.push (.bounds own bounds)
        | other => items := items.push other
      expectPunct "}"
      return .module inherentMark (some items.toList)
    match ← peek with
    | .ident "for" => advance
    | _ => failAt "expected `for`: `impl Trait for Type`, or `{`: `impl Type { fn .. }`"
-- What it is for: a type made with a name, a tuple, a callable or a
    -- reference, or a type parameter said to be a callable.
    let target ← parseType
    -- (`impl<F: Fn<(A,), Output = R>> T for F`: what is asked of `F` is what
    -- it is, a callable, so it is not asked as a trait is.)
    let callableBound := fun (b : Bound) => b.trait == "Fn" || b.trait == "RunsIn"
    let mut calls : Array Bound := (early.filter callableBound).toArray
    let early := early.filter (!callableBound ·)
    let mut context : Array (String × String) := #[]
    -- (What `impl<T: Show>` asked of its parameters, as `where` asks it.)
    for b in early do
      if b.quantity.isSome || !b.ranked.isEmpty then
        failAt "what is asked of a parameter of an implementation is written after `where`"
      context := context.push (b.subject, b.trait)
      for (a, place) in b.args.zipIdx do
        given := given.push (.typeAlias (ctxArgName (context.size - 1) place) [] a)
      for (name, ty) in b.assoc do
        given := given.push (.typeAlias (equalArgName (context.size - 1) name) [] ty)
    if (← peek) == .ident "where" then
      advance
      repeat
        -- `R: Get<T>`, of a type parameter; or of a type made from them,
        -- `(A, B): Apart`.
        let named := match ← peek, ← peek 1 with
          | .ident _, .punct ":" => true
          | _, _ => false
        let p ← if named then expectIdent else do
          let subject ← parseType
          given := given.push (.typeAlias (ctxSubjectName context.size) [] subject)
          pure s!"%subject{context.size}"
        expectPunct ":"
        if named && params.contains p then
          match ← peek with
          | .ident "Fn" | .ident "RunsIn" | .ident "for" =>
            calls := calls ++ (← parseBoundsOf p).toArray
            if !(← acceptPunct ",") then break
            continue
          -- `T: Use<[0, *]>`: how often the implementation's functions use a
          -- `T`, said to them all.
          | .ident "Use" =>
            for b in ← parseBoundsOf p do
              if let some (lower, upper) := b.quantity then
                given := given.push (.typeAlias (useMark p lower upper) [] .hole)
            if !(← acceptPunct ",") then break
            continue
          | _ => pure ()
        let asked ← expectPath
        context := context.push (p, asked)
        -- `I: Iterator<Item = A>`: what the trait leaves to `I`'s
        -- implementation is that type.
        if ← isOp "<" then
          advance
          let mut place := 0
          repeat
            if ← isOp ">" then break
            if (← peek 1) == .punct "=" then
              let name ← expectIdent
              expectPunct "="
              given := given.push (.typeAlias (equalArgName (context.size - 1) name) [] (← parseType))
            else
              -- `R: Get<T>`: the trait at an argument.
              given := given.push (.typeAlias (ctxArgName (context.size - 1) place) [] (← parseType))
              place := place + 1
            if !(← acceptPunct ",") then break
          expectOp ">"
        if !(← acceptPunct ",") then break
    -- A type parameter said to be a callable is that callable's type:
    -- `F: Fn<(A, B), Output = R, Effects = {E}>` is `fn(A, B) -> R / {E}`,
    -- wherever the implementation writes `F`. Where nothing is said of what
    -- it gives, that is a type parameter of its own.
    let mut callable : List (String × TypeExpr) := []
    let mut outputs : Array String := #[]
    for b in calls do
      unless params.contains b.subject do
        failAt s!"`{b.subject}: {b.trait}`: `{b.subject}` is not a type parameter of the implementation"
      if (callable.lookup b.subject).isSome then
        failAt s!"`{b.subject}` is said twice to be a callable"
      unless b.ranked.isEmpty do
        failAt s!"`{b.subject}: for<..> {b.trait}`: an implementation is not for a callable at every lifetime"
      for (name, _) in b.assoc do
        unless name == "Output" || name == "Effects" do
          failAt s!"`{b.subject}: {b.trait}`: `{name}` cannot be said of a callable here (`Output` and `Effects` can)"
      let takes := if b.trait == "RunsIn" then b.args.drop 1 else b.args
      let out ← match b.assoc.lookup "Output" with
        | some t => pure t
        | none =>
          let name := s!"%output{outputs.size}"
          outputs := outputs.push name
          pure (TypeExpr.name name [])
      let result := match b.assoc.lookup "Effects" with
        | some (.performs _ effects) => TypeExpr.performs out effects
        | _ => out
      callable := callable ++ [(b.subject, .fn takes result)]
    let params := params.filter (fun p => (callable.lookup p).isNone) ++ outputs.toList
    given := given.map fun
      | .typeAlias n ps body => .typeAlias n ps (substTypeExpr callable body)
      | item => item
    -- An argument that is one of the implementation's type parameters, the
    -- first time it is written, is that parameter. Any other is a type the
    -- argument has to be: `impl<T, R> Get<T> for (Column<T>, R)` is for the
    -- pairs whose first part is a `Column<T>`.
    let (head, written) ← match substTypeExpr callable target with
      | .tuple ts => pure (s!"(tuple{ts.length})", ts)
      -- `impl<T: Show> Print for T`: for every type, written out for each
      -- that may have what is asked of `T` (`Syntax.Flat.expandBlankets`).
      | .name h [] => if params.contains h then pure (blanketHead, [.name h []]) else pure (h, [])
      | .name h ts => pure (h, ts)
      -- `impl<P, R> System for fn(P) -> R`: for the functions of one
      -- argument that perform nothing. `impl<T> Fetch for &mut T`.
      -- `fn(..P) -> R`: for functions of every number of arguments.
      | .fn [.name s [ps]] r => if s == spreadParams then pure ("%Fn", [ps, r]) else pure ("(fn1)", [.name s [ps], r])
      | .fn ps r => pure (s!"(fn{ps.length})", ps ++ [r])
      | .ref true t _ => pure ("(&mut)", [t])
      | .ref false t _ => pure ("(&)", [t])
      | _ => failAt "an implementation is for a type made with a name, a tuple, a function or a reference"
    let mut names : Array String := #[]
    let mut fresh : Array String := #[]
    for (t, j) in written.zipIdx do
      let plain := match t with
        | .name p [] => if params.contains p && !names.contains p then some p else none
        | _ => none
      match plain with
      | some p => names := names.push p
      | none =>
        let name := s!"%fixed{j}"
        names := names.push name
        fresh := fresh.push name
        given := given.push (.typeAlias (fixedArgName j) [] t)
    let args := names.toList
    let params := params ++ fresh.toList
    expectPunct "{"
    let mut methods : Array Item := given
    repeat
      if (← peek) == .punct "}" then break
      match ← peek with
      | .ident "fn" =>
        methods := methods.push (← withReader (fun c =>
          if c.records.contains head then { c with records := "Self" :: c.records } else c)
          parseItem)
      | .ident "unsafe" =>
        -- `unsafe fn`: its body may name what is unsafe, as an `unsafe { .. }`
        -- block's may.
        advance
        match ← withReader (fun c =>
            if c.records.contains head then { c with records := "Self" :: c.records } else c) parseItem with
        | .fn name ps annots ret b => methods := methods.push (.fn name ps annots ret b.unsafeBody)
        | _ => failAt "`unsafe` in an implementation is written before `fn`"
      | .ident "type" =>
        -- `type Item = Int;`: a type the trait leaves to the implementation.
        advance
        let name ← expectIdent
        -- `type Of<T> = [T];`: what it is at each type it is asked at.
        let takes ← parseGenerics
        expectPunct "="
        -- `type Effects = {Log};`: a row, kept as the type of a callable
        -- that takes nothing, gives nothing and performs it.
        let body ← if (← peek) == .punct "{" then do
            pure (TypeExpr.fn [] (.performs (.tuple []) (← parseRow)))
          else parseType
        let _ ← acceptPunct ";"
        -- (A type parameter said to be a callable is that callable here too.)
        methods := methods.push (.typeAlias name takes (substTypeExpr callable body))
      | .ident "const" =>
        -- `const NAME: Type = value;`: the trait's function of that name,
        -- which takes nothing and gives the value.
        advance
        let name ← expectIdent
        expectPunct ":"
        let ty ← parseType
        expectPunct "="
        let body ← valueFn
        let _ ← acceptPunct ";"
        methods := methods.push (Item.fn name [] [] (some ty) body)
      | _ => failAt "expected `fn`: an implementation gives the trait's functions"
    expectPunct "}"
    -- `Self` is the type the implementation is for.
    let self := selfTypeOf head (args.map (TypeExpr.name · []))
    -- (A type parameter said to be a callable is that callable in the
    -- functions too: `<L as Fetch<F>>::fetch(..)`.)
    let called := fun (t : TypeExpr) => substTypeExpr callable t
    let calledBody := fun (b : Flat.Body) =>
      if callable.isEmpty then b else
      match Flat.mapTypes (fun t => pure (called t)) b with
      | .ok b => b
      | .error _ => b
    -- (A lifetime of the implementation, `impl<'a, A> .. for &'a A`, is in
    -- its functions' types the one the type it is for has at each use, which
    -- is not named there: as `Self`'s is.)
    let implLives := params.filter (·.startsWith "'")
    let rec unnamed (mine : List String) : TypeExpr → TypeExpr
      | .name x [] => if implLives.contains x && !mine.contains x then .name "'_" [] else .name x []
      | .ref uniq t (some l) => .ref uniq (unnamed mine t) (if implLives.contains l && !mine.contains l then none else some l)
      | t => t.mapParts (unnamed mine)
    let written := methods.toList.map fun
      | .fn name ps annots ret body =>
        let fix := unnamed ps ∘ TypeExpr.withSelf self ∘ called
        Item.fn name ps (annots.map (·.map fix)) (ret.map fix)
          ((Flat.selfRewrite head (some (tr, (TypeExpr.tuple [self]).asExpr))).body (calledBody body))
      | other => other
    pure (.impl params tr head args context.toList written)
  | .ident "coerce" =>
    advance
    let name ← match ← peek with
      | .ident s => do
        advance
        pure s
      | .op s => do
        advance
        pure s
      | _ => failAt "expected the name of a function"
    let _ ← acceptPunct ";"
    pure (.coerce name)
  | .ident kind =>
    if fixityKinds.contains kind then
      advance
      advance
      advance
      if ← acceptPunct "=" then
        let _ ← expectPath
      let _ ← acceptPunct ";"
      pure .fixity
    else failAt "expected a declaration"
  | _ => failAt "expected a declaration"

/-- What follows `use`: a path, perhaps renamed with `as`, `*` for every name
of a module, or names in braces that share what is before them. -/
private partial def parseUseTree (before : List String) : P (List Item) := do
  if ← acceptPunct "{" then
    let out ← listUntil (atPunct "}") (parseUseTree before)
    expectPunct "}"
    pure out.flatten
  else if (← peek) == .op "*" then
    advance
    pure [.import before none true]
  else
    -- An operator is a name like any other.
    if let .op s := ← peek then
      advance
      return [.import (before ++ [s]) none false]
    let seg ← expectIdent
    if ← acceptPunct "::" then parseUseTree (before ++ [seg])
    else
      let rename ← if (← peek) == .ident "as" then do
          advance
          some <$> expectIdent
        else pure none
      -- `use a::{self}` is `use a`.
      let path := if seg == "self" && !before.isEmpty then before else before ++ [seg]
      pure [.import path rename false]

/-- The fields of a struct or of an enum's constructor: none, `(A, B)`, or
`{ a: A, b: B }`. Each may be `pub`. Gives the types, the names if they were
written with names, and which are `pub`. -/
private partial def parseFieldDecls : P (List TypeExpr × List String × List Bool) := do
  if ← acceptPunct "(" then
    let mut types : Array TypeExpr := #[]
    let mut pubs : Array Bool := #[]
    repeat
      if (← peek) == .punct ")" then break
      pubs := pubs.push (← acceptPub).isSome
      match ← peek, ← peek 1 with
      | .ident _, .punct ":" =>
        advance
        advance
      | _, _ => pure ()
      types := types.push (← parseType)
      if !(← acceptPunct ",") then break
    expectPunct ")"
    pure (types.toList, [], pubs.toList)
  else if ← acceptPunct "{" then
    let mut types : Array TypeExpr := #[]
    let mut names : Array String := #[]
    let mut pubs : Array Bool := #[]
    repeat
      if (← peek) == .punct "}" then break
      pubs := pubs.push (← acceptPub).isSome
      let field ← expectIdent
      if names.contains field then failAt s!"field `{field}` is declared twice"
      names := names.push field
      expectPunct ":"
      types := types.push (← parseType)
      if !(← acceptPunct ",") then break
    expectPunct "}"
    pure (types.toList, names.toList, pubs.toList)
  else pure ([], [], [])

/-- A trait: its functions, each as the types it takes and gives, and beside
them what else it says. A function written with a body, its parameters named
and typed, is given to every implementation that does not write it. -/
private partial def parseTrait : P (List Item) := do
  advance
  let name ← expectIdent
  let params ← parseGenerics
  let mut supers : Array String := #[]
  if ← acceptPunct ":" then
    repeat
      supers := supers.push (← expectPath)
      if ← isOp "+" then advance else break
  expectPunct "{"
  let mut methods : Array (String × List TypeExpr × Option TypeExpr) := #[]
  let mut unsafeMethods : Array String := #[]
  let mut defaults : Array Item := #[]
  let mut assocs : Array String := #[]
  repeat
    if (← peek) == .punct "}" then break
    if (← peek) == .ident "type" then
      advance
      let a ← expectIdent
      assocs := assocs.push a
      -- `type Of<T>;`: a type for each type it is asked at. How many it
      -- takes is seen where an implementation says what it is.
      let takes ← parseGenerics
      -- `type Effects: EffectRow;`: what is said of it is read and not kept;
      -- a row is known by where the trait's functions use it.
      if ← acceptPunct ":" then
        let _ ← expectPath
      -- `type Components = ();`: what an implementation has if it does not
      -- say.
      if ← acceptPunct "=" then
        defaults := defaults.push (.typeAlias a takes (← parseType))
      let _ ← acceptPunct ";"
      continue
    if (← peek) == .ident "const" then
      -- `const NAME: Type;`: a value each implementation says. It is a
      -- function of the trait that takes nothing, and naming it calls it.
      advance
      let c ← expectIdent
      expectPunct ":"
      let ty ← parseType
      methods := methods.push (c, [], some ty)
      if ← acceptPunct "=" then
        -- What an implementation has if it does not say.
        defaults := defaults.push (Item.fn c [] [] none (← valueFn))
      let _ ← acceptPunct ";"
      continue
    -- `unsafe fn`: one that can be called only where `unsafe` is written.
    let isUnsafe ← if (← peek) == .ident "unsafe" then do advance; pure true else pure false
    match ← peek with
    | .ident "fn" => advance
    | _ => failAt "expected `fn`: a trait lists the functions a type must have"
    let m ← match ← peek with
      | .op s => do
        advance
        pure s
      | _ => expectIdent
    -- `fn single<T>(..)`: type parameters of the function's own.
    let own ← parseGenerics
    expectPunct "("
    let mut types : Array TypeExpr := #[]
    let mut names : Array (Option String) := #[]
    repeat
      if (← peek) == .punct ")" then break
      match ← peek, ← peek 1 with
      | .ident x, .punct ":" =>
        advance
        advance
        names := names.push (some x)
      | _, _ => names := names.push none
      types := types.push (← parseType)
      if !(← acceptPunct ",") then break
    expectPunct ")"
    -- `-> R`, `-> R / {E}`, or `/ {E}` alone for a function that gives `()`.
    let ret ← if (← acceptPunct "->") || (← peek) == .op "/" then some <$> parseResult else pure none
    -- `where T: Use<[0, *]>`: how often it uses a value of a type parameter
    -- of its own, carried among them.
    let mut uses : Array String := #[]
    if (← peek) == .ident "where" then
      advance
      repeat
        let p ← expectIdent
        expectPunct ":"
        for b in ← parseBoundsOf p do
          match b.trait, b.quantity with
          | "Use", some (lower, upper) => uses := uses.push (useMark p lower upper)
          | _, _ => failAt "a trait's function says here only how often it uses a type parameter of its own: `T: Use<[0, *]>`"
        if !(← acceptPunct ",") then break
    methods := methods.push (m, types.toList, withMethodGenerics ret (genericParams own ++ uses.toList))
    if isUnsafe then unsafeMethods := unsafeMethods.push m
    if (← peek) == .punct "{" then
      -- A body: what an implementation gets if it does not write its own.
      let pats ← names.toList.mapM fun
        | some x => pure (Pattern.var x)
        | none => failAt s!"`{m}` has a body, so its parameters have names: `{m}(a: Self)`"
      advance
      let body ← bodyOf do pure #[← mkC pats (← parseStmts)]
      expectPunct "}"
      defaults := defaults.push (Item.fn m [] [] none body)
    let _ ← acceptPunct ";"
  expectPunct "}"
  let info : List Item :=
    if supers.isEmpty && defaults.isEmpty && params.isEmpty && assocs.isEmpty then []
    else [.traitInfo name supers.toList defaults.toList params assocs.toList]
  pure (.trait name methods.toList :: info ++ unsafeMethods.toList.map fun m => .fieldNames (attrMark "unsafe_method") [name, m] [])

/-- What is written before a declaration in `#[..]`, and the declaration:
`next` reads the declaration. A function of its own, as the one below is,
so that Lean reads each in a second and not all three in ten. -/
private partial def parseAttributed (next : P (List Item)) : P (List Item) := do
  -- `#[name]`, `#[name(arg)]`, `#[name = "text"]` before a declaration;
  -- `#![name]` of the whole text.
  advance
  let inner ← isOp "!"
  if inner then advance
  expectPunct "["
  let name ← expectIdent
  let mut arg : String := ""
  if ← acceptPunct "(" then
    arg ← expectIdent
    -- (`#[derive(Clone, Debug)]`: refused below, by its name.)
    while ← acceptPunct "," do
      let _ ← expectIdent
    expectPunct ")"
  else if ← acceptPunct "=" then
    match ← peek with
    | .str codes =>
      advance
      arg := String.ofList (codes.map Char.ofNat)
    | _ => failAt "expected a text: `#[export_name = \"name\"]`"
  expectPunct "]"
  if inner then
    unless name == "no_std" || name == "no_implicit_prelude" do
      failAt s!"`#![{name}]` is not known: `#![no_std]` and `#![no_implicit_prelude]` are"
    return [.fieldNames (attrMark name) [] []]
  -- `#[fallback] impl ..`: the implementation a type nothing decides is
  -- taken to have, where the trait is asked of it.
  if name == "intrinsic" then
    let items ← withReader (fun ctx => { ctx with intrinsic := true }) next
    return items ++ items.filterMap fun
      | .fn n .. | .pub _ (.fn n ..) => some (.fieldNames (attrMark "intrinsic") [n] [])
      | _ => none
  if name == "fallback" then
    let items ← next
    return items.map fun
      | .impl ps tr head args context methods => .impl (ps ++ [fallbackMark]) tr head args context methods
      | item => item
  let known := match name, arg with
    | "non_exhaustive", "" => true
    | "repr", "C" => true
    | "repr", "transparent" => true
    | "export_name", a => a != ""
    | _, _ => false
  unless known do
    failAt s!"`#[{name}]` is not known: `#[non_exhaustive]`, `#[repr(C)]`, `#[repr(transparent)]` and `#[export_name = \"..\"]` are"
  let items ← next
  let subject := items.findSome? fun item =>
    let item := match item with
      | .pub _ i => i
      | i => i
    match item with
    | .enum n _ _ => some n
    | .struct n _ _ => some n
    | .fn n _ _ _ _ => some n
    | _ => none
  -- `#[repr(C)]` on a struct of whole numbers, floats and addresses: the
  -- struct can be written to memory and read from it as C lays it out,
  -- by `Type::c_write(value, at)`, `Type::c_read(at)` and `Type::c_size()`.
  let mut made : List Item := []
  if name == "repr" && arg == "C" then
    let plain := items.map fun
      | .pub _ i => i
      | i => i
    let found := plain.findSome? fun
      | .struct n [] fields => some (n, fields)
      | _ => none
    if let some (n, fields) := found then
      let names := (plain.findSome? fun
        | .fieldNames owner names _ => if owner == n && !names.isEmpty then some names else none
        | _ => none)
      let call1 := fun (f : String) (x : Expr) => Expr.call 0 (.name none f) [x]
      -- How a field lies in memory: its bytes, how a value of it is made
      -- the bits there, how the bits are made a value of it, and how they
      -- are read (so many bits, without a sign if below zero).
      let rec lies (fuel : Nat) : TypeExpr → Option (Nat × (Expr → Expr) × (Expr → Expr) × Int)
        | .name "Int" [] => some (8, id, id, 64)
        | .name "i64" [] => some (8, id, id, 64)
        | .name "f64" [] => some (8, call1 "f64_bits", call1 "f64_of", 64)
        | .name "f32" [] => some (4, call1 "f32_bits", call1 "f32_of", -32)
        | .name "%prelude::Ptr" [_] =>
          some (8, fun x => call1 "usize_bits" (.proj x 0),
            fun r => call1 "Ptr" (call1 "usize_of" r), -64)
        | .name "%prelude::PtrMut" [_] =>
          some (8, fun x => call1 "usize_bits" (.proj x 0),
            fun r => call1 "PtrMut" (call1 "usize_of" r), -64)
        | .name t [] =>
          match scalars.lookup t, cTypes.lookup (lastSegment t), fuel with
          | some (some w), _, _ => some (w.natAbs / 8, call1 (t ++ "_bits"), call1 (t ++ "_of"), w)
          | _, some as, fuel + 1 => lies fuel (.name as [])
          | _, _, _ => none
        | _ => none
      let laid := fields.map (lies 4)
      if laid.all Option.isSome && !fields.isEmpty then
        -- Each field at the next place that is a multiple of its size;
        -- the whole a multiple of the largest.
        let mut at_ : Nat := 0
        let mut most : Nat := 1
        let mut places : Array (Nat × (Expr → Expr) × (Expr → Expr) × Int × Nat) := #[]
        for l in laid do
          if let some (size, into, back, how) := l then
            at_ := (at_ + size - 1) / size * size
            places := places.push (at_, into, back, how, size)
            at_ := at_ + size
            most := max most size
        let size := (at_ + most - 1) / most * most
        let place := fun (off : Nat) =>
          call1 "usize_of" (.call 0 (.name none "int_add") [call1 "usize_bits" (.name none "%at"), .int off])
        let vars := (List.range fields.length).map fun i => s!"%f{i}"
        let taken : Pattern := match names with
          | some ns =>
            .ctor n none (.var recordMark :: (ns.zip vars).map fun (f, v) => .ctor (fieldMark f) none [.var v])
          | none => .ctor n none (vars.map Pattern.var)
        let writes : List Stmt := (places.toList.zip vars).map fun ((off, into, _, _, bytes), v) =>
          .expr (.call 0 (.name none "ptr_write") [place off, .int (8 * bytes), into (.name none v)])
        let reads : List Expr := places.toList.map fun (off, _, back, how, _) =>
          back (.call 0 (.name none "ptr_read") [place off, .int how])
        let built : Expr := match names with
          | some ns =>
            .call 0 (.name none n)
              (.name none recordMark :: (ns.zip reads).map fun (f, r) => .call 0 (.name none (fieldMark f)) [r])
          | none => .call 0 (.name none n) reads
        let self := TypeExpr.name n []
        let usize := TypeExpr.name "usize" []
        made := [
          Item.fnOf s!"{n}::c_size" [] [] (some usize) [.mk [] [.expr (call1 "usize_of" (.int size))]],
          Item.fnOf s!"{n}::c_write" [] [some self, some usize] (some (.tuple []))
            [.mk [taken, .var "%at"] (writes ++ [.expr (.tuple [])])],
          .unsafeFn s!"{n}::c_write",
          Item.fnOf s!"{n}::c_read" [] [some usize] (some self) [.mk [.var "%at"] [.expr built]],
          .unsafeFn s!"{n}::c_read"]
  match subject with
  | some n => pure (items ++ made ++ [.fieldNames (attrMark name) [n, arg] []])
  | none => failAt s!"`#[{name}]` is written before a type or a function"

/-- `extern "C" { .. }`: the functions it declares. -/
private partial def parseExtern : P (List Item) := do
  -- `extern "C" { fn name(a: usize) -> i32; }`: functions that are not
  -- written in the language, each called by its name as C has it.
  advance
  if let .str _ := ← peek then advance
  expectPunct "{"
  let mut items : Array Item := #[]
  repeat
    if (← peek) == .punct "}" then break
    unless (← peek) == .ident "fn" do failAt "expected `fn`: a foreign function"
    advance
    let name ← expectIdent
    expectPunct "("
    -- (Each with where it is written: what names the calls made of it, of
    -- functions generic in what a pointer points to, whose callers say how
    -- that is destroyed.)
    let params ← listUntil (atPunct ")") do
      let _ ← expectIdent
      expectPunct ":"
      let id := (← read).base + (← get) + 1
      pure (id, ← parseType)
    expectPunct ")"
    let retId := (← read).base + (← get) + 1
    let ret ← if ← acceptPunct "->" then parseType else pure (.tuple [])
    expectPunct ";"
    -- How a type is given to C and taken from it: the type the function
    -- is declared with, how a value of it is made the bits C takes, how
    -- what C gives is made a value of it, what C gives (so many bits; 1000
    -- a double, 1001 a float), and where C takes it (0 with the whole
    -- numbers and addresses, 1 as a double, 2 as a float).
    let call1 := fun (f : String) (x : Expr) => Expr.call 0 (.name none f) [x]
    let rec kind (site : Nat) (fuel : Nat) : TypeExpr →
        P (TypeExpr × (Expr → Expr) × (Expr → Expr) × Int × Nat) := fun t =>
      match t with
      | .name "Int" [] => pure (t, id, id, 64, 0)
      | .name "i64" [] => pure (t, id, id, 64, 0)
      | .name "f64" [] => pure (t, call1 "f64_bits", call1 "f64_of", 1000, 1)
      | .name "f32" [] => pure (t, call1 "f32_bits", call1 "f32_of", 1001, 2)
      | .name "%prelude::Ptr" [_] =>
        pure (t, fun x => call1 "usize_bits" (.call site (.name none "ptr_address") [x]),
          fun r => .call site (.name none "ptr_at") [call1 "usize_of" r], 64, 0)
      | .name "%prelude::PtrMut" [_] =>
        pure (t, fun x => call1 "usize_bits" (.call site (.name none "ptr_mut_address") [x]),
          fun r => .call site (.name none "ptr_mut_at") [call1 "usize_of" r], 64, 0)
      | .name name [] =>
        match scalars.lookup name, cTypes.lookup (lastSegment name), fuel with
        | some (some w), _, _ => pure (t, call1 (name ++ "_bits"), call1 (name ++ "_of"), w, 0)
        -- C's own names for its types are the types they are here.
        | _, some as, fuel + 1 => kind site fuel (.name as [])
        | _, _, _ => failAt s!"a foreign function takes and gives whole numbers, floats and addresses (`Int`, a type such as `i32`, `usize` or `f64`, `*const T`, `*mut T`), not `{name}`"
      | _ => failAt "a foreign function takes and gives whole numbers, floats and addresses (`Int`, a type such as `i32`, `usize` or `f64`, `*const T`, `*mut T`)"
    let mut args : Array Expr := #[]
    let mut declared : Array TypeExpr := #[]
    let mut classes : Nat := 0
    let mut place : Nat := 1
    for ((pid, p), i) in params.zipIdx do
      let (ty, into, _, _, cls) ← kind pid 4 p
      declared := declared.push ty
      args := args.push (into (Expr.name none s!"%a{i}"))
      classes := classes + cls * place
      place := place * 3
    let (retTy, back, bits) ← match ret with
      | .tuple [] => pure (TypeExpr.tuple [], (id : Expr → Expr), (0 : Int))
      | t => do
        let (ty, _, back, bits, _) ← kind retId 4 t
        pure (ty, back, bits)
    let symbol := name.toUTF8.toList.map fun b => Expr.int b.toNat
    let call := Expr.call 0 (.name none foreignCall)
      (symbol ++ [.int 0, .int bits, .int classes] ++ args.toList)
    let body : List Stmt := match ret with
      | .tuple [] => [.expr call, .expr (.tuple [])]
      | _ => [.expr (back call)]
    let pats := (List.range params.length).map fun i => Pattern.var s!"%a{i}"
    items := items.push (Item.fnOf name [] (declared.toList.map some) (some retTy) [.mk pats body])
    items := items.push (.unsafeFn name)
  expectPunct "}"
  pure items.toList

/-- Is this a value written out, with nothing to work out: a number, a
text, a constructor of such, a tuple of them, given a type? -/
private partial def writtenOut : Expr → Bool
  | .int _ => true
  | .name none x => (x.splitOn "::").getLastD x |>.front.isUpper
  | .tuple es => es.all writtenOut
  | .call _ (.name none mark) [value, _] => mark == ascribeMark && writtenOut value
  | .call _ (.name q f) args =>
    (q == some "%prelude" || ((f.splitOn "::").getLastD f).front.isUpper || isScalar f) && args.all writtenOut
  | _ => false

/-- Each constant, `const NAME: T = value;`, as a function that works its
value out (`NAME$const`, run at compile time), and the name, which reads
what that function gave. -/
private def constItems (items : List Item) : List Item :=
  let one := fun (name : String) (b : Flat.Body) (e : Flat.ExprId) (item : Item) (wrap : Item → Item) =>
    match Flat.treeExpr b e with
    | .call _ (.name none mark) [value] =>
      -- (A value written out, `3`, `Some(4)`, `"text"`, is one already: it
      -- stays a name for it, which a pattern can be.)
      if mark == comptimeMark && writtenOut value then [wrap (Item.aliasOf name value)]
      else if mark == comptimeMark then
        let fn := constFnName name
        [wrap (Item.aliasOf name (.call 0 (.name none fn) [])), wrap (Item.fnOf fn [] [] none [.mk [] [.expr value]])]
      else [item]
    | _ => [item]
  items.flatMap fun
    | item@(.alias name b e) => one name b e item id
    | item@(.pub parent (.alias name b e)) => one name b e item (.pub parent)
    | item => [item]

/-- A declaration, and with it what was written beside it. -/
private partial def parseItemGroup : P (List Item) := do
  match ← peek with
  | .punct "#" =>
    parseAttributed parseItemGroup
  | .ident "pub" =>
    let parent := (← acceptPub).getD false
    -- `pub extern "C" { .. }`: each of its functions is `pub`.
    if (← peek) == .ident "extern" then
      return (← parseItemGroup).map fun
        | .fn name ps annots ret clauses => .pub parent (.fn name ps annots ret clauses)
        | item => item
    -- `pub use a::{b, c}` is `pub` for each; with a declaration, for it and
    -- not for what is written out beside it.
    match ← parseItemGroup with
    | items@(.import _ _ _ :: _) => pure (items.map (.pub parent))
    -- (A constant's function is as visible as it is: its uses call it.)
    | item :: more => pure (.pub parent item :: more.map fun
        | .fn n ps annots ret clauses => if isConstFn n then .pub parent (.fn n ps annots ret clauses) else .fn n ps annots ret clauses
        | other => other)
    | [] => pure []
  | .ident "mod" =>
    advance
    let name ← expectIdent
    if ← acceptPunct ";" then return [.module name none]
    expectPunct "{"
    -- A module has its own operators: those it declares and those it brings
    -- in, and the prelude's.
    let ctx ← read
    let inner := ctx.path ++ [name]
    let fix := (ctx.tables.lookup inner).getD ctx.fix
    -- The functions written in blocks of this module are the module's.
    let madeBefore := (← getThe (Array Item)).size
    let items ← withReader (fun r => { r with path := inner, fix }) do
      let mut items : Array Item := #[]
      repeat
        if (← peek) == .punct "}" then break
        items := items ++ (← parseItemGroup).toArray
      pure items
    expectPunct "}"
    let made ← getThe (Array Item)
    modifyThe (Array Item) (·.extract 0 madeBefore)
    pure [.module name (some (items.toList ++ (made.extract madeBefore made.size).toList))]
  | .ident "use" =>
    advance
    let items ← parseUseTree []
    expectPunct ";"
    pure items
  | .ident "unsafe" =>
    -- `unsafe fn`: a function that can be named only where `unsafe` is written.
    advance
    match ← parseItemGroup with
    | items@(.fn name _ _ _ _ :: _) => pure (items ++ [.unsafeFn name])
    -- `unsafe trait`: one whose implementations promise more than the
    -- checker sees; `unsafe impl` is the promise.
    | items@(.trait name _ :: _) => pure (items ++ [.fieldNames (attrMark "unsafe_trait") [name] []])
    | items@(.impl _ tr head _ _ _ :: _) =>
      pure (items ++ [.fieldNames (attrMark "unsafe_impl") [tr, head] []])
    | _ => failAt "`unsafe` is written before `fn`, `trait` or `impl`, or before a block"
  | .ident "extern" =>
    parseExtern
  | .ident "struct" =>
    advance
    let name ← expectIdent
    -- What is asked of a type parameter, `struct W<T: Show>` or `where T:
    -- Show` before or after the fields, is asked where a `W` is built.
    let (params, bounds, defaults) ← parseGenericsFull
    let (_, before) ← parseWhere
    let (fields, names, pubs) ← parseFieldDecls
    let (_, after) ← parseWhere
    let _ ← acceptPunct ";"
    let asked := bounds ++ before ++ after
    pure ([.struct name params fields, .fieldNames name names pubs]
      ++ (if asked.isEmpty then [] else [.bounds name asked])
      ++ defaultAliases name params defaults)
  | .ident "enum" =>
    advance
    let name ← expectIdent
    let (params, bounds, defaults) ← parseGenericsFull
    let (_, more) ← parseWhere
    let asked := bounds ++ more
    expectPunct "{"
    let mut ctors : Array (String × List TypeExpr) := #[]
    let mut named : Array Item := #[]
    repeat
      if (← peek) == .punct "}" then break
      let c ← expectIdent
      let (fields, names, _) ← parseFieldDecls
      ctors := ctors.push (c, fields)
      -- A constructor's fields are as visible as the type.
      -- (Kept for one without names too: how many fields it has is what
      -- `..` in a pattern stands for the rest of.)
      named := named.push (.fieldNames c names (fields.map fun _ => true))
      if !(← acceptPunct ",") then break
    expectPunct "}"
    pure (.enum name params ctors.toList :: named.toList
      ++ (if asked.isEmpty then [] else [.bounds name asked])
      ++ defaultAliases name params defaults)
  | .ident "type" =>
    advance
    let name ← expectIdent
    let params ← parseGenerics
    expectPunct "="
    let body ← parseType
    let _ ← acceptPunct ";"
    pure [.typeAlias name params body]
  | .ident "fn" =>
    let (item, bounds) ← parseFn
    match item, bounds with
    | .fn name _ _ _ _, _ :: _ => pure [item, .bounds name bounds]
    | _, _ => pure [item]
  | .ident "trait" => parseTrait
  | _ =>
    match ← parseItem with
    -- The functions of `impl Type { .. }` are this module's.
    | .module name (some items) => if name == inherentMark then pure (constItems items) else pure [.module name (some items)]
    | item => pure (constItems [item])

private partial def parseItems : P (List Item) := do
  let mut out : Array Item := #[]
  repeat
    if (← peek) == .eof then break
    out := out ++ (← parseItemGroup).toArray
  pure out.toList

/-- What an earlier parse of a text made of each group of its items, by the
token the group began at: where it ended; a hash of its tokens, of the one
after, and of what it was read with; its items; and the functions written in
its blocks. -/
abbrev ItemsKept := Std.HashMap Nat (Nat × UInt64 × List Item × Array Item)

/-- The tokens from `i` to `j`, and the one after, with `seed`. -/
def tokensHash (toks : Array Token) (i j : Nat) (seed : UInt64) : UInt64 := Id.run do
  let mut h := seed
  for k in [i:min (j + 1) toks.size] do
    h := mixHash h (hash toks[k]!)
  h

/-- A text's operators, as what its items are read with. -/
def fixKey (f : Fixities) : UInt64 :=
  hash (f.infixes.map (fun (o, p, a) => (o, p, match a with
    | .left => (0 : Nat)
    | .right => 1
    | .non => 2)), f.prefixes, f.bound)

/-- `parseItems`, each group of items taken from `kept` where it began at the
same token, its tokens and the one after the same, read with the same: the
items are numbered by where their tokens are, so they are what parsing them
again would give. Each group's items as `unmutItems` makes them, which goes
item by item; the functions written in blocks as parsed. Gives
each group, for the next. -/
private partial def parseItemsKept (kept : ItemsKept) : P (List Item × ItemsKept) := do
  let ctx ← read
  let seed := hash (ctx.records, ctx.base, ctx.path, ctx.fixed, fixKey ctx.fix,
    ctx.tables.map fun (p, f) => (p, fixKey f))
  let mut out : Array Item := #[]
  let mut made : ItemsKept := {}
  repeat
    if (← peek) == .eof then break
    let i ← getThe Nat
    if let some (j, h, items, locals) := kept[i]? then
      if j ≤ ctx.toks.size && tokensHash ctx.toks i j seed == h then
        set (σ := Nat) j
        modifyThe (Array Item) (· ++ locals)
        out := out ++ items.toArray
        made := made.insert i (j, h, items, locals)
        continue
    let before := (← getThe (Array Item)).size
    let group := unmutItems (← parseItemGroup)
    let j ← getThe Nat
    let m ← getThe (Array Item)
    out := out ++ group.toArray
    made := made.insert i (j, tokensHash ctx.toks i j seed, group, m.extract before m.size)
  pure (out.toList, made)

/-- The constructors a token stream declares with named fields: `struct Name
{ a: A }` and, inside an enum, `Name { a: A }`. -/
private def collectRecords (toks : Array Token) : List String := Id.run do
  let tok := fun (i : Nat) => (toks[i]?.map (·.tok)).getD .eof
  -- Past `<...>`, if it starts at `i`.
  let pastGenerics := fun (i : Nat) => Id.run do
    if tok i != .op "<" then return i
    let mut j := i + 1
    let mut depth := 1
    while j < toks.size && depth != 0 do
      match tok j with
      | .op "<" => depth := depth + 1
      | .op ">" => depth := depth - 1
      | _ => pure ()
      j := j + 1
    j
  -- Past `where ..`, if it starts at `i`: up to the brace, bracket or `;`
  -- that ends it.
  let pastWhere := fun (i : Nat) => Id.run do
    if tok i != .ident "where" then return i
    let mut j := i + 1
    let mut depth := 0
    while j < toks.size do
      match tok j with
      | .op "<" => depth := depth + 1
      | .op ">" => depth := depth - 1
      | .punct "{" | .punct ";" => if depth == 0 then break
      | _ => pure ()
      j := j + 1
    j
  let mut out : List String := []
  for i in [0:toks.size] do
    match tok i, tok (i + 1) with
    | .ident "struct", .ident name =>
      if tok (pastWhere (pastGenerics (i + 2))) == .punct "{" then out := name :: out
    | .ident "enum", .ident _ =>
      -- Each constructor at the top of the enum's braces that has braces.
      let mut j := pastWhere (pastGenerics (i + 2))
      if tok j == .punct "{" then
        let mut depth := 0
        j := j + 1
        while j < toks.size do
          match tok j with
          | .punct "}" => if depth == 0 then break else depth := depth - 1
          | .punct "(" => depth := depth + 1
          | .punct ")" => depth := depth - 1
          | .punct "{" => depth := depth + 1
          | .ident c => if depth == 0 && tok (j + 1) == .punct "{" then out := c :: out
          | _ => pure ()
          j := j + 1
    | _, _ => pure ()
  out

/-- Collect the fixity declarations of a token stream. -/
private def collectFixities (toks : Array Token) (fix : Fixities)
    (here : Nat → Bool := fun _ => true) : Except String Fixities := do
  let mut fix := fix
  for i in [0:toks.size] do
    match toks[i]?.map (·.tok), toks[i + 1]?.map (·.tok), toks[i + 2]?.map (·.tok) with
    | some (.ident kind), some (.int prec), some nameTok =>
      if fixityKinds.contains kind && here i then
        let name ← match nameTok with
          | .ident s => pure s
          | .op s => pure s
          | _ => throw s!"{(toks[i]?.getD default).line}: a fixity declaration needs an operator name"
        if prec > 255 then
          throw s!"{(toks[i]?.getD default).line}: a precedence is from 0 to 255, and `{name}` is given {prec}"
        if kind == "prefix" then
          fix := { fix with prefixes := (name, prec) :: fix.prefixes }
        else
          let assoc := if kind == "infixl" then Assoc.left
            else if kind == "infixr" then Assoc.right else Assoc.non
          fix := { fix with infixes := (name, prec, assoc) :: fix.infixes }
        -- `= function`: the function the operator stands for in this place.
        match toks[i + 3]?.map (·.tok), toks[i + 4]?.map (·.tok) with
        | some (Tok.punct "="), some (Tok.ident f) =>
          -- (the function may be written with the module it is in)
          let mut path := f
          let mut j := i + 5
          while (toks[j]?.map (·.tok)) == some (Tok.punct "::") do
            match toks[j + 1]?.map (·.tok) with
            | some (Tok.ident g) =>
              path := path ++ "::" ++ g
              j := j + 2
            | _ => break
          fix := { fix with bound := (name, kind == "prefix", path) :: fix.bound }
        | _, _ => pure ()
    | _, _, _ => pure ()
  pure fix

/-- What a text declares that has to be known before any text of the program
is parsed: its operators, added to `fix`, and its constructors with named
fields. -/
def declaredSyntax (fix : Fixities) (src : String) (lexed : Option (Array Token) := none) :
    Except String (Fixities × List String) := do
  let toks ← match lexed with
    | some toks => pure toks
    | none => lex src
  pure (← collectFixities toks fix, collectRecords toks)

/-- The module each token of a text is written in, as a path from the text's
own module. -/
private def tokenModules (toks : Array Token) : Array (List String) := Id.run do
  let tok := fun (i : Nat) => (toks[i]?.map (·.tok)).getD .eof
  let mut out : Array (List String) := #[]
  let mut inside : List (String × Nat) := []
  let mut depth := 0
  for i in [0:toks.size] do
    match tok i, tok (i + 1), tok (i + 2) with
    | .ident "mod", .ident name, .punct "{" =>
      out := out.push (inside.map (·.1)).reverse
      inside := (name, depth + 1) :: inside
    | .punct "{", _, _ =>
      depth := depth + 1
      out := out.push (inside.map (·.1)).reverse
    | .punct "}", _, _ =>
      if (inside.head?.map (·.2)) == some depth then inside := inside.drop 1
      depth := depth - 1
      out := out.push (inside.map (·.1)).reverse
    | _, _, _ => out := out.push (inside.map (·.1)).reverse
  out

/-- The modules a text says are files of their own, `mod name;`: each as its
path from the module the text is, through the modules written in the text. -/
def fileModules (src : String) : Except String (List (List String)) := do
  -- (A text that never writes `mod` declares none: not read as tokens.)
  if (src.splitOn "mod").length == 1 then return []
  let toks ← lex src
  let tok := fun (i : Nat) => (toks[i]?.map (·.tok)).getD .eof
  let at_ := tokenModules toks
  pure ((List.range toks.size).filterMap fun i =>
    match tok i, tok (i + 1), tok (i + 2) with
    | .ident "mod", .ident name, .punct ";" => some ((at_[i]?).getD [] ++ [name])
    | _, _, _ => none)

/-- What a `use` written from token `i` on brings: each path, and whether it
is everything of a module. -/
private partial def useLeaves (tok : Nat → Tok) (i : Nat) (before : List String) :
    List (List String × Bool) × Nat :=
  match tok i with
  | .punct "{" => Id.run do
    let mut out : List (List String × Bool) := []
    let mut at_ := i + 1
    let mut fuel := 256
    while fuel > 0 && tok at_ != .punct "}" && tok at_ != .eof do
      fuel := fuel - 1
      let (more, next) := useLeaves tok at_ before
      out := out ++ more
      at_ := if tok next == .punct "," then next + 1 else next
    (out, at_ + 1)
  | .op "*" => ([(before, true)], i + 1)
  | .op s => ([(before ++ [s], false)], i + 1)
  | .ident seg =>
    if tok (i + 1) == .punct "::" then useLeaves tok (i + 2) (before ++ [seg])
    else
      let path := if seg == "self" && !before.isEmpty then before else before ++ [seg]
      ([(path, false)], if tok (i + 1) == .ident "as" then i + 3 else i + 1)
  | _ => ([], i + 1)

/-- What one text of a program says that has to be known before any text is
parsed: the operators each of its modules declares, what each brings in with
`use`, its constructors with named fields, and every name written in it. -/
structure TextSyntax where
  own : List (List String × Fixities)
  uses : List (List String × List String × Bool)
  records : List String
  names : List String

/-- That, for the text that is the module `base`. -/
def textSyntax (base : List String) (src : String) (lexed : Option (Array Token) := none) :
    Except String TextSyntax := do
  let toks ← match lexed with
    | some toks => pure toks
    | none => lex src
  let mods := tokenModules toks
  let tok := fun (i : Nat) => (toks[i]?.map (·.tok)).getD .eof
  let mut own : List (List String × Fixities) := []
  let mut uses : List (List String × List String × Bool) := []
  for rel in ([] :: mods.toList).eraseDups do
    own := own ++ [(base ++ rel, ← collectFixities toks {} (fun i => mods[i]? == some rel))]
  for i in [0:toks.size] do
    if tok i == .ident "use" then
      let first := i == 0 || match tok (i - 1) with
        | .punct ";" | .punct "}" | .punct "{" | .punct ")" | .ident "pub" => true
        | _ => false
      if first then
        uses := uses ++ (useLeaves tok (i + 1) []).1.map fun (p, glob) => (base ++ mods[i]?.getD [], p, glob)
  let names := toks.toList.filterMap fun t =>
    match t.tok with
    | .ident s => some s
    | _ => none
  pure { own, uses, records := collectRecords toks, names }

/-- The operators of each module of a program. An operator's fixity holds in
the module that declares it, and in one that brings in, with `use`, the
function the operator stands for; the prelude's hold in every module. `texts`
is what each of the program's texts says, in the program's order. -/
def joinFixities (prelude : Fixities) (texts : List TextSyntax) :
    Except String (List (List String × Fixities)) := do
  let own := texts.flatMap (·.own)
  let uses := texts.flatMap (·.uses)
  own.mapM fun (m, mine) => do
    let mut fix := mine
    for (user, path, glob) in uses do
      if user == m then
        let (segs, name) := if glob then (path, none) else (path.dropLast, path.getLast?)
        let target := match segs with
          | "crate" :: rest => rest
          | "self" :: rest => m ++ rest
          | "super" :: rest => m.dropLast ++ rest
          | _ => if (own.lookup (m ++ segs)).isSome then m ++ segs else segs
        if let some theirs := own.lookup target then
          for (op, prec, assoc) in theirs.infixes do
            if glob || name == some op || name == some (theirs.function op false) then
              match fix.infixes.lookup op with
              | some (p, a) =>
                unless p == prec && a == assoc do
                  throw s!"the operator `{op}` is brought in with one fixity where it already has another"
              | none =>
                fix := { fix with
                  infixes := (op, prec, assoc) :: fix.infixes
                  bound := (theirs.bound.filter fun (o, pre, _) => o == op && !pre) ++ fix.bound }
          for (op, prec) in theirs.prefixes do
            if glob || name == some op || name == some (theirs.function op true) then
              match fix.prefixes.lookup op with
              | some p =>
                unless p == prec do
                  throw s!"the operator `{op}` is brought in with one fixity where it already has another"
              | none =>
                fix := { fix with
                  prefixes := (op, prec) :: fix.prefixes
                  bound := (theirs.bound.filter fun (o, pre, _) => o == op && pre) ++ fix.bound }
    pure (m, { infixes := fix.infixes ++ prelude.infixes, prefixes := fix.prefixes ++ prelude.prefixes,
               bound := fix.bound ++ prelude.bound })

/-! ## Lists of types as parameters

`impl<H, ..R> Count for (H, ..R) where (..R): Count { .. }` is one
implementation for tuples of every length: `(H, ..R)` is a tuple's first and
the rest. What its functions spread of a list of values, `let (h, ..rest) =
t`, `(x, ..rest)`, `f(..rest)`, is the prelude's spreads, as long as the
implementation's list. A `..` in square brackets is an array's rest, and one
before no list is a pattern's, as before. -/

/-- The tokens with each implementation that has a list of types as a
parameter, `impl<H, ..R> Trait for (H, ..R)`, made one implementation for
every length (`consOnly`); refused where its list is used one by one. -/
def expandPacks (toks : Array Token) : Except String (Array Token) := do
  let tok := fun (i : Nat) => (toks[i]?.map (·.tok)).getD .eof
  let isDots := fun (i : Nat) => tok i == .punct "." && tok (i + 1) == .punct "."
  let mut out : Array Token := #[]
  let mut i := 0
  while i < toks.size do
    -- `impl<..`: the names after `..` in its parameters.
    if tok i == .ident "impl" && tok (i + 1) == .op "<" then
      let mut j := i + 2
      let mut packs : List String := []
      let mut depth := 1
      while j < toks.size && depth != 0 do
        match tok j with
        | .op "<" => depth := depth + 1
        | .op ">" => depth := depth - 1
        | _ => pure ()
        if depth == 1 && isDots j then
          if let .ident x := tok (j + 2) then packs := packs ++ [x]
        j := j + 1
      if packs.isEmpty then
        out := out.push toks[i]!
        i := i + 1
        continue
      -- The implementation runs to the `}` that closes its body.
      -- (Braces inside `<..>`, an effect row's `Effects = {Threads}` in a
      -- condition, are not its body's.)
      let mut e := j
      let mut braces := 0
      let mut opened := false
      let mut angle : Int := 0
      while e < toks.size && !(opened && braces == 0) do
        match tok e with
        | .op "<" => if !opened then angle := angle + 1
        | .op ">" => if !opened then angle := angle - 1
        | .op ">>" => if !opened then angle := angle - 2
        | .punct "{" => if opened || angle <= 0 then braces := braces + 1; opened := true
        | .punct "}" => if opened then braces := braces - 1
        | _ => pure ()
        e := e + 1
      let body := toks.extract i e
      -- One whose lists are only the rest of a tuple, `(H, ..R)` or
      -- `(..R)`, is one implementation for every length: the rest is a type
      -- parameter of its own (`Traits.consHead`). (Its lists of values
      -- spread written with the prelude's spreads, `spreadValues`.)
      if let some once := consOnly (spreadValues body (j - i) packs) (j - i) packs then
        out := out ++ once
        i := e
        continue
      let at_ := toks[i]!
      throw s!"{at_.line}:{at_.col}: this implementation uses its list of types `..{packs.headD ""}` one by one (what is in it, `(..Option<R>)`; what each element has, `..R: Trait`; two lists in one tuple; or a list of values spread elsewhere than first or last of a tuple): write it for the list's first and rest, `impl<H, ..R> Trait for (H, ..R)`, each element a step of its own"
    else
      out := out.push toks[i]!
      i := i + 1
  return out
where
  /-- An implementation (`body`, its parameters ending before `params`)
  whose lists of types are each a tuple, read as one: `..R` among its
  parameters written `R`, and what is spread read by the parser as types
  (`(H, ..R)`, `(..G, X)`, `Fn<(..P)>`: `parseType`, `parsePack`). None if
  it spreads a list of values (`spreadValues` writes those it can),
  something of a list's elements (`(..Option<T>)`), or asks something of
  each element (`..S: Get<T>`): those are refused (`expandPacks`). -/
  consOnly (body : Array Token) (params : Nat) (packs : List String) : Option (Array Token) := Id.run do
    let tok := fun (i : Nat) => (body[i]?.map (·.tok)).getD .eof
    let dots := fun (k : Nat) => tok k == .punct "." && tok (k + 1) == .punct "."
      && tok (k + 2) != .punct "." && !(k > 0 && tok (k - 1) == .punct ".")
    for k in [0:body.size] do
      unless dots k do continue
      -- (Among the parameters, one declared: `<..T`, `, ..T`.)
      if k < params && k > 0 && (tok (k - 1) == .op "<" || tok (k - 1) == .punct ",") then continue
      -- (`..` alone: the parts of a tuple pattern not written.)
      if tok (k + 2) == .punct ")" || tok (k + 2) == .punct "," then continue
      -- (Of each element, after `where`: written out.)
      if let .ident _ := tok (k + 2) then
        if tok (k + 3) == .punct ":" then return none
      -- What is spread, to the next `,` or closing bracket.
      let mut j := k + 2
      let mut depth : Int := 0
      while j < body.size && !(depth == 0 &&
          (tok j == .punct "," || tok j == .punct ")" || tok j == .op ">" || tok j == .punct "]"
            || tok j == .punct "{")) do
        match tok j with
        | .punct "(" | .punct "[" | .op "<" => depth := depth + 1
        | .punct ")" | .punct "]" | .op ">" => depth := depth - 1
        | .op ">>" => depth := depth - 2
        | _ => pure ()
        j := j + 1
      -- One name: a list of types, spread; of values, written out.
      if j == k + 3 then
        match tok (k + 2) with
        | .ident x => if packs.contains x then continue else return none
        | _ => return none
      -- Else each list it names is itself spread whole, `(..R)`, or is what
      -- is asked of, `..R::Got<'a>`: what the list's implementation of the
      -- trait gives.
      for m in [k + 2:j] do
        if let .ident x := tok m then
          let whole := m ≥ 3 && tok (m - 3) == .punct "(" && dots (m - 2) && tok (m + 1) == .punct ")"
          let asked := m == k + 2 && tok (m + 1) == .punct "::"
          if packs.contains x && !whole && !asked then return none
    -- The parameters, without `..` before those declared.
    let mut out : Array Token := #[]
    let mut k := 0
    while k < params do
      if dots k && k > 0 && (tok (k - 1) == .op "<" || tok (k - 1) == .punct ",") then k := k + 2
      else
        out := out.push body[k]!
        k := k + 1
    pure (some (out ++ body.extract params body.size))
  /-- What an implementation for every length spreads of a list of values,
  written with the prelude's `spread_split`, `spread_cons` and
  `spread_snoc`, which are written out for the length each use has where the
  implementations are known (`Elab.Specialize`), and `R: Spread` asked of
  each of its lists of types for that: `let (p, ..r) = e` is `let (p, r) =
  spread_split(e)`, `let (..r) = e` is `let r = e`, `(a, ..e)` is
  `spread_cons(a, e)`, `(..e, a)` is `spread_snoc(e, a)`, and `(..e)` is
  `(e)`. Others are left as they are (`consOnly` turns them away). -/
  spreadValues (body : Array Token) (params : Nat) (packs : List String) : Array Token := Id.run do
    -- (Not for one whose type is a list alone, `(..R)`: its first and rest
    -- are not said.)
    let headTok := fun (i : Nat) => (body[i]?.map (·.tok)).getD .eof
    let mut f := params
    while f < body.size && headTok f != .ident "for" do f := f + 1
    if headTok (f + 1) == .punct "(" && headTok (f + 2) == .punct "." && headTok (f + 3) == .punct "."
        && headTok (f + 5) == .punct ")" then
      return body
    let mut toks := body
    let mut changed := false
    for _ in [0:body.size] do
      match spreadOne toks params packs with
      | some t =>
        toks := t
        changed := true
      | none => break
    if !changed then return body
    -- (`R: Spread` for each list, after what is asked of the rest: before the
    -- body's `{`, the first outside `<..>`.)
    let tok := fun (i : Nat) => (toks[i]?.map (·.tok)).getD .eof
    let mut b := params
    let mut angle : Int := 0
    let mut hasWhere := false
    while b < toks.size do
      match tok b with
      | .op "<" => angle := angle + 1
      | .op ">" => angle := angle - 1
      | .op ">>" => angle := angle - 2
      | .ident "where" => if angle <= 0 then hasWhere := true
      | .punct "{" => if angle <= 0 then break
      | _ => pure ()
      b := b + 1
    let at_ := toks[b]?.getD default
    let mk := fun (t : Tok) => { at_ with tok := t }
    let mut added : Array Token := if hasWhere then #[] else #[mk (.ident "where")]
    for (p, k) in packs.zipIdx do
      if hasWhere || k > 0 then added := added.push (mk (.punct ","))
      added := added ++ #[mk (.ident p), mk (.punct ":"), mk (.ident "Spread")]
    return toks.extract 0 b ++ added ++ toks.extract b toks.size
  /-- The first list of values spread that `spreadValues` writes otherwise,
  written so; none if none is left. -/
  spreadOne (toks : Array Token) (params : Nat) (packs : List String) : Option (Array Token) := Id.run do
    let tok := fun (i : Nat) => (toks[i]?.map (·.tok)).getD .eof
    let dots := fun (k : Nat) => tok k == .punct "." && tok (k + 1) == .punct "."
      && tok (k + 2) != .punct "." && !(k > 0 && tok (k - 1) == .punct ".")
    let keywords := ["for", "as", "return", "in", "else", "where", "let", "mut"]
    let mk := fun (at_ : Token) (t : Tok) => { at_ with tok := t }
    -- (Only in the functions' bodies, inside the implementation's braces
    -- and theirs: what is outside is types.)
    let mut braces : Nat := 0
    let mut depthAt : Array Nat := Array.mkEmpty toks.size
    for i in [0:toks.size] do
      depthAt := depthAt.push braces
      match tok i with
      | .punct "{" => braces := braces + 1
      | .punct "}" => braces := braces - 1
      | _ => pure ()
    for k in [params:toks.size] do
      unless dots k && (depthAt[k]?.getD 0) ≥ 2 do continue
      -- (`..` alone, a list of types, or what is asked of each: not values.)
      if tok (k + 2) == .punct ")" || tok (k + 2) == .punct "," then continue
      if let .ident x := tok (k + 2) then
        if packs.contains x then continue
      -- The bracket it is in, and where that closes.
      let mut o := k
      let mut depth : Nat := 0
      let mut found := false
      while o > 0 do
        o := o - 1
        match tok o with
        | .punct ")" | .punct "]" | .punct "}" => depth := depth + 1
        | .punct "(" | .punct "[" | .punct "{" =>
          if depth == 0 then
            found := true
            break
          depth := depth - 1
        | _ => pure ()
      unless found && tok o == .punct "(" do continue
      let mut c := o + 1
      depth := 0
      let mut parts : Array (Nat × Nat) := #[]
      let mut start := o + 1
      while c < toks.size do
        match tok c with
        | .punct "(" | .punct "[" | .punct "{" => depth := depth + 1
        | .punct ")" | .punct "]" | .punct "}" =>
          if depth == 0 then break
          depth := depth - 1
        | .punct "," => if depth == 0 then
            parts := parts.push (start, c)
            start := c + 1
        | _ => pure ()
        c := c + 1
      if start < c then parts := parts.push (start, c)
      let spread := fun ((s, _) : Nat × Nat) => dots s
      let at_ := toks[o]!
      let piece := fun ((s, e) : Nat × Nat) => toks.extract s e
      let inner := fun ((s, e) : Nat × Nat) => toks.extract (s + 2) e
      let paren := fun (a : Array Token) => #[mk at_ (.punct "(")] ++ a ++ #[mk at_ (.punct ")")]
      -- (As long as the implementation's one list: none where it has more.)
      let some list := (match packs with | [p] => some p | _ => none) | continue
      let named := fun (f : String) =>
        (#[mk at_ (.ident s!"{f}_as"), mk at_ (.op "<"), mk at_ (.ident list), mk at_ (.op ">")] : Array Token)
      let call := fun (f : String) (a b : Array Token) =>
        named f ++ #[mk at_ (.punct "(")] ++ a ++ #[mk at_ (.punct ",")] ++ b ++ #[mk at_ (.punct ")")]
      -- A pattern of a `let`: what it is given split first.
      if o > 0 && (tok (o - 1) == .ident "let" || tok (o - 1) == .ident "mut") then
        unless tok (c + 1) == .punct "=" do continue
        -- (What is given, to the `;` that ends the statement.)
        let mut e := c + 2
        depth := 0
        while e < toks.size do
          match tok e with
          | .punct "(" | .punct "[" | .punct "{" => depth := depth + 1
          | .punct ")" | .punct "]" | .punct "}" =>
            if depth == 0 then break
            depth := depth - 1
          | .punct ";" => if depth == 0 then break
          | _ => pure ()
          e := e + 1
        let given := toks.extract (c + 2) e
        match parts.toList with
        | [r] =>
          if spread r then
            return some (toks.extract 0 o ++ inner r ++ #[mk at_ (.punct "=")] ++ given ++ toks.extract e toks.size)
        | [p, r] =>
          if !spread p && spread r then
            return some (toks.extract 0 o ++ paren (piece p ++ #[mk at_ (.punct ",")] ++ inner r)
              ++ #[mk at_ (.punct "=")] ++ named "spread_split" ++ paren given ++ toks.extract e toks.size)
        | _ => pure ()
        continue
      -- A call given a tuple's parts and nothing else, `f(..t)` or
      -- `(*f)(..t)`: `spread_call`.
      let callee : Option Nat := if o == 0 then none else
        match tok (o - 1) with
        | .ident w => if keywords.contains w then none else some (o - 1)
        | .punct ")" => Id.run do
          let mut m := o - 1
          let mut depth : Nat := 0
          while m > 0 do
            m := m - 1
            match tok m with
            | .punct ")" => depth := depth + 1
            | .punct "(" =>
              if depth == 0 then return some m
              depth := depth - 1
            | _ => pure ()
          return none
        | _ => none
      if let some from_ := callee then
        if let [r] := parts.toList then
          if spread r then
            return some (toks.extract 0 from_ ++ named "spread_call" ++ paren (toks.extract from_ o
              ++ #[mk at_ (.punct ",")] ++ inner r) ++ toks.extract (c + 1) toks.size)
        continue
      if o > 0 then
        match tok (o - 1) with
        | .punct "]" | .op ">" => continue
        | _ => pure ()
      -- A tuple: the one list spread first, last or alone.
      let spreads := parts.filter spread
      unless spreads.size == 1 do continue
      let some at' := parts.findIdx? spread | continue
      let front := parts.extract 0 at'
      let back := parts.extract (at' + 1) parts.size
      let rest := paren (inner parts[at']!)
      let made ← if back.isEmpty then
          pure (front.foldr (fun p acc => call "spread_cons" (piece p) acc) rest)
        else if front.isEmpty then
          pure (back.foldl (fun acc p => call "spread_snoc" acc (piece p)) rest)
        else continue
      return some (toks.extract 0 o ++ made ++ toks.extract (c + 1) toks.size)
    return none

/-! ## What the compiler writes of each type: its `Reflect`

Each declared struct and enum is given `impl Reflect for T`, written as text
and read as the program's is, after the module's items: its description
(`INFO`: its name, kind, whether it is `pub`, each constructor's fields
with their names, types and whether each is `pub`), and how a value is
described and a field set from text, field by field. A field of a type the
program describes is described by its type's; a reference or a callable is
opaque. A type with a field whose type is left to be found has none. -/

/-- A text in Glorious, quoted. -/
def quoted (s : String) : String :=
  "\"" ++ (s.toList.map fun c => if c == '"' then "\\\"" else if c == '\\' then "\\\\" else c.toString).foldl (· ++ ·) "" ++ "\""

/-- Is a field's type one a value of can be described: not a reference, a
callable, or a type left to be found. -/
partial def describable (t : TypeExpr) : Bool :=
  match t with
  | .name x args => !x.isEmpty && (x.toList.headD 'a').isUpper || x == "Int" || (scalars.lookup x).isSome || args.all describable
  | .tuple _ => false
  | _ => false

/-- The text of `impl Reflect for` a declared type, or nothing. -/
def reflectText (name : String) (params : List String) (isPub : Bool)
    (ctors : List (String × List TypeExpr × List String × List Bool)) (enum : Bool) : Option String := Id.run do
  if name == "Array" || name == "Str" then return none
  let tys := params.filter (!·.startsWith "'")
  let head := if params.isEmpty then name else s!"{name}<{", ".intercalate params}>"
  let generics := if params.isEmpty then "" else s!"<{", ".intercalate params}>"
  let bounds := if tys.isEmpty then "" else " where " ++ ", ".intercalate (tys.map (· ++ ": std::reflect::Reflect"))
  -- (A bare field name, whose type is left to be found: no description.)
  for (_, fs, _, _) in ctors do
    for f in fs do
      if let .name x [] := f then
        if !(x.toList.headD 'a').isUpper && x != "Int" && (scalars.lookup x).isNone && !params.contains x then return none
  let fieldInfo := fun (n : String) (t : TypeExpr) (p : Bool) =>
    s!"std::reflect::field_info({quoted n}, {quoted t.spell}, {if p then "true" else "false"})"
  let variants := ctors.map fun (c, fs, ns, ps) =>
    s!"std::reflect::variant_info({quoted c}, [{", ".intercalate ((fs.zip (ns.zip ps)).map fun (t, n, p) => fieldInfo n t p)}])"
  let kind := if enum then "std::reflect::KindEnum" else "std::reflect::KindStruct"
  let info := s!"std::reflect::type_info_of({quoted name}, {kind}, {if isPub then "true" else "false"}, [{", ".intercalate variants}])"
  -- (Each constructor's pattern, its fields bound `f0`, `f1`, ..)
  let pattern := fun (c0 : String) (fs : List TypeExpr) (ns : List String) =>
    -- (An enum's constructor by its type's name: another type of the
    -- module may have one of the same name.)
    let c := if enum then s!"{name}::{c0}" else c0
    let named := !ns.isEmpty && !(ns.headD "").all Char.isDigit
    if fs.isEmpty then c
    else if named then s!"{c} \{ {", ".intercalate ((ns.zipIdx).map fun (n, k) => s!"{n}: f{k}")} }"
    else s!"{c}({", ".intercalate ((List.range fs.length).map (s!"f{·}"))})"
  let describeArm := fun (c : String) (fs : List TypeExpr) (ns : List String) (ps : List Bool) =>
    let parts := (fs.zip (ns.zip ps)).zipIdx.map fun ((t, n, p), k) =>
      let value := if t.spell == "Bool" then s!"std::reflect::FlagValue(*f{k})"
        else if describable t then s!"std::reflect::reflect_describe(f{k}, all, token)" else s!"std::reflect::OpaqueValue({quoted t.spell})"
      s!"if({if p then "true" else "all"}) \{ fields = push(fields, ({quoted n}, {value})) } else \{ () };"
    s!"{pattern c fs ns} => let mut fields = []; {" ".intercalate parts} std::reflect::StructValue({quoted c}, fields)"
  let setArm := fun (c : String) (fs : List TypeExpr) (ns : List String) (ps : List Bool) =>
    let tries := (fs.zip (ns.zip ps)).zipIdx.map fun ((t, n, p), k) =>
      let set := if t.spell == "Bool" then s!"match(std::reflect::reflect_bool(text)) \{ Some(b) => *f{k} = b; Ok(std::reflect::FlagValue(b)), None => Err(\"not true or false\") }"
        else if describable t then s!"std::reflect::reflect_set(f{k}, text, all, token)" else s!"Err({quoted ("`" ++ n ++ "` is not set from text")})"
      s!"if(path == {quoted n}) \{ if({if p then "true" else "all"}) \{ {set} } else \{ Err({quoted ("`" ++ n ++ "` is private: set it with `set_field_unchecked`")}) } } else "
    let none := s!"Err(\"no field `\" ++ path ++ \"` in `{c}`\")"
    if tries.isEmpty then s!"{pattern c fs ns} => {none}" else s!"{pattern c fs ns} => {String.join tries}\{ {none} }"
  let arms := fun (f : String → List TypeExpr → List String → List Bool → String) =>
    ", ".intercalate (ctors.map fun (c, fs, ns, ps) => f c fs ns ps)
  some s!"impl{generics} std::reflect::Reflect for {head}{bounds} \{
    const INFO: std::reflect::TypeInfo = {info};
    fn describe_as(v: &{head}, all: Bool, token: std::reflect::Unchecked) -> std::reflect::Described \{ if(if(all) \{ true } else \{ {if isPub then "true" else "false"} }) \{ match(v) \{ {arms describeArm} } } else \{ std::reflect::OpaqueValue({quoted name}) } }
    fn set_from(v: &mut {head}, path: Str, text: Str, all: Bool, token: std::reflect::Unchecked) -> Result<std::reflect::Described, Str> \{ match(v) \{ {arms setArm} } }
}
"

/-- The `Reflect` of each declared type of a module's items, as text. -/
def reflectTexts (items : List Item) : List String := Id.run do
  let mut out : List String := []
  for (item, k) in items.zipIdx do
    let (isPub, inner) : Bool × Item := match item with
      | .pub _ i => (true, i)
      | i => (false, i)
    -- (The names of its constructors' fields, written beside it.)
    let beside : List (String × List String × List Bool) :=
      ((items.drop (k + 1)).takeWhile fun
        | .fieldNames c _ _ => !c.startsWith "%"
        | _ => false).filterMap fun
        | .fieldNames c ns ps => some (c, ns, ps)
        | _ => none
    let fieldsOf := fun (c : String) (n : Nat) =>
      -- (A constructor's fields without names are named by their places.)
      let places := (List.range n).map toString
      match beside.find? (·.1 == c) with
      | some (_, ns, ps) => (if ns.length == n then ns else places, if ps.length == n then ps else List.replicate n false)
      | none => (places, List.replicate n false)
    match inner with
    | .struct n ps fs =>
      let (ns, pubs) := fieldsOf n fs.length
      if let some t := reflectText n ps isPub [(n, fs, ns, pubs)] false then out := out ++ [t]
    | .enum n ps cs =>
      let ctors := cs.map fun (c, fs) => let (ns, pubs) := fieldsOf c fs.length; (c, fs, ns, pubs)
      if let some t := reflectText n ps isPub ctors true then out := out ++ [t]
    | _ => pure ()
  out

/-- Where the identities of a text's reflections begin, after its own: clear
of every text's (each has a million from its base), so that no call of a
reflection is known by the identity of one of the text's. -/
def reflectionBase : Nat := 1000000000000

/-- Each declared type's `Reflect` among a module's items, read as its text
is; checked only where something asks it. -/
def reflectionsOf (fix : Fixities) (items : List Item) (base : Nat) (records : List String)
    (tables : List (List String × Fixities)) (path : List String) (fixed : Bool) : Except String (List Item) := do
  let texts := reflectTexts items
  if texts.isEmpty then return []
  let gtoks ← lex (String.join texts)
  let fix := if tables.isEmpty then fix else ((tables.lookup path).getD fix)
  let (gitems, ⟨_, glocal, _⟩) ← parseItems { toks := gtoks, fix, records, base, tables, path, fixed } ⟨0, #[], {}⟩
  pure ((gitems ++ glocal.toList).map fun
    | .impl ps tr h args ctx ms => Item.impl ps tr h args ctx (ms ++ [.typeAlias askedOnlyName [] (.tuple [])])
    | other => other)

/-- Parse a source text, given the fixities already in scope. Returns the items
and the fixities including those it declares. `base` keeps the identities of
this text's callable literals apart from those of a text parsed before it.
With `tables`, each module of the text has the operators the table gives it,
and the text is the module `path`. -/
def parseKept (fix : Fixities) (src : String) (base : Nat := 0) (records : List String := [])
    (tables : List (List String × Fixities) := []) (path : List String := [])
    (fixed : Bool := false) (lexed : Option (Array Token) := none)
    (reflect : Bool := true) (kept : Option ItemsKept := none) :
    Except String (List Item × Fixities × ItemsKept) := do
  let toks ← match lexed with
    | some toks => pure toks
    | none => lex src
  let toks ← expandPacks toks
  let fix ← if tables.isEmpty then collectFixities toks fix else pure ((tables.lookup path).getD fix)
  let ctx : PCtx := { toks, fix, records := collectRecords toks ++ records, base, tables, path, fixed }
  match kept with
  | some kept =>
    let ((items, groups), ⟨_, local_, _⟩) ← parseItemsKept kept ctx ⟨0, #[], {}⟩
    let made ← if reflect then reflectionsOf fix (items ++ local_.toList) (base + reflectionBase) (collectRecords toks ++ records) tables path fixed else pure []
    pure (items ++ unmutItems (local_.toList ++ made), fix, groups)
  | none =>
    let (items, ⟨_, local_, _⟩) ← parseItems ctx ⟨0, #[], {}⟩
    let items := items ++ local_.toList
    -- (Each declared type's `Reflect`, read as the text is, after its items;
    -- checked only where something asks it.)
    let made ← if reflect then reflectionsOf fix items (base + reflectionBase) (collectRecords toks ++ records) tables path fixed else pure []
    pure (unmutItems (items ++ made), fix, {})

/-- `parseKept`, nothing taken from an earlier parse. -/
def parse (fix : Fixities) (src : String) (base : Nat := 0) (records : List String := [])
    (tables : List (List String × Fixities) := []) (path : List String := [])
    (fixed : Bool := false) (lexed : Option (Array Token) := none)
    (reflect : Bool := true) :
    Except String (List Item × Fixities) := do
  let (items, fix, _) ← parseKept fix src base records tables path fixed lexed reflect
  pure (items, fix)

end Glorious.Syntax
