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
    let value ← parseBinary 0 false
    expectPunct ";"
    pure (.alias name (match ty with
      | some ty => Expr.call 0 (.name none ascribeMark) [value, ty.asExpr]
      | none => value))
  | .ident "const" =>
    -- `const NAME: Type = value;`: worked out once, at compile time
    -- (`constItems`).
    advance
    let name ← expectIdent
    expectPunct ":"
    let ty ← parseType
    expectPunct "="
    let value ← parseBinary 0 false
    expectPunct ";"
    pure (.alias name (Expr.call 0 (.name none comptimeMark) [Expr.call 0 (.name none ascribeMark) [value, ty.asExpr]]))
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
          let value ← parseBinary 0 false
          expectPunct ";"
          let c := Item.alias s!"{tr}::{name}"
            (Expr.call 0 (.name none comptimeMark) [Expr.call 0 (.name none ascribeMark) [value, ty.asExpr]])
          items := items.push (match vis with
            | some parent => .pub parent c
            | none => c)
          continue
        if (← peek) != .ident "fn" then failAt "expected `fn` or `const`: an implementation gives functions and values"
        let (item, bounds) ← withReader (fun c =>
          if c.records.contains tr then { c with records := "Self" :: c.records } else c) parseFn
        match item with
        | .fn name ps annots ret clauses =>
          -- (Its own type parameters first: `app.on<E, P>(..)` gives those,
          -- as `.on::<E, P>()` does in Rust; the type's are known from what
          -- the function is given.)
          let mine := ps.filter (!params.contains ·)
          let ps := if (mine.filter (!·.startsWith "'")).isEmpty then params ++ mine else mine ++ params
          let own := s!"{tr}::{name}"
          let f := Item.fn own ps (annots.map (·.map (TypeExpr.withSelf self)))
            (ret.map (TypeExpr.withSelf self)) (clauses.map (selfClause tr none))
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
        let value ← parseBinary 0 false
        let _ ← acceptPunct ";"
        methods := methods.push (.fn name [] [] (some ty) [.mk [] [.expr value]])
      | _ => failAt "expected `fn`: an implementation gives the trait's functions"
    expectPunct "}"
    -- `Self` is the type the implementation is for.
    let self := selfTypeOf head (args.map (TypeExpr.name · []))
    -- (A type parameter said to be a callable is that callable in the
    -- functions too: `<L as Fetch<F>>::fetch(..)`.)
    let called := fun (t : TypeExpr) => substTypeExpr callable t
    let calledClause := fun (c : Clause) =>
      if callable.isEmpty then c else
      match mapTypesClause (fun t => pure (called t)) c with
      | .ok c => c
      | .error _ => c
    -- (A lifetime of the implementation, `impl<'a, A> .. for &'a A`, is in
    -- its functions' types the one the type it is for has at each use, which
    -- is not named there: as `Self`'s is.)
    let implLives := params.filter (·.startsWith "'")
    let rec unnamed (mine : List String) : TypeExpr → TypeExpr
      | .name x [] => if implLives.contains x && !mine.contains x then .name "'_" [] else .name x []
      | .name x args => .name x (args.map (unnamed mine))
      | .tuple args => .tuple (args.map (unnamed mine))
      | .fn ps r => .fn (ps.map (unnamed mine)) (unnamed mine r)
      | .performs r effects => .performs (unnamed mine r) (effects.map fun (e, args) => (e, args.map (unnamed mine)))
      | .ref uniq t (some l) => .ref uniq (unnamed mine t) (if implLives.contains l && !mine.contains l then none else some l)
      | .ref uniq t none => .ref uniq (unnamed mine t) none
      | .never => .never
      | .hole => .hole
    let written := methods.toList.map fun
      | .fn name ps annots ret clauses =>
        let fix := unnamed ps ∘ TypeExpr.withSelf self ∘ called
        Item.fn name ps (annots.map (·.map fix)) (ret.map fix)
          (clauses.map (selfClause head (some (tr, (TypeExpr.tuple [self]).asExpr)) ∘ calledClause))
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
        let value ← parseBinary 0 false
        defaults := defaults.push (.fn c [] [] none [.mk [] [.expr value]])
      let _ ← acceptPunct ";"
      continue
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
    if (← peek) == .punct "{" then
      -- A body: what an implementation gets if it does not write its own.
      let pats ← names.toList.mapM fun
        | some x => pure (Pattern.var x)
        | none => failAt s!"`{m}` has a body, so its parameters have names: `{m}(a: Self)`"
      advance
      let body ← parseStmts
      expectPunct "}"
      defaults := defaults.push (.fn m [] [] none [.mk pats body])
    let _ ← acceptPunct ";"
  expectPunct "}"
  let info : List Item :=
    if supers.isEmpty && defaults.isEmpty && params.isEmpty && assocs.isEmpty then []
    else [.traitInfo name supers.toList defaults.toList params assocs.toList]
  pure (.trait name methods.toList :: info)

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
          some (8, fun x => call1 "usize_bits" (call1 "ptr_address" x),
            fun r => call1 "ptr_at" (call1 "usize_of" r), -64)
        | .name "%prelude::PtrMut" [_] =>
          some (8, fun x => call1 "usize_bits" (call1 "ptr_mut_address" x),
            fun r => call1 "ptr_mut_at" (call1 "usize_of" r), -64)
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
          .fn s!"{n}::c_size" [] [] (some usize) [.mk [] [.expr (call1 "usize_of" (.int size))]],
          .fn s!"{n}::c_write" [] [some self, some usize] (some (.tuple []))
            [.mk [taken, .var "%at"] (writes ++ [.expr (.tuple [])])],
          .unsafeFn s!"{n}::c_write",
          .fn s!"{n}::c_read" [] [some usize] (some self) [.mk [.var "%at"] [.expr built]],
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
    let params ← listUntil (atPunct ")") do
      let _ ← expectIdent
      expectPunct ":"
      parseType
    expectPunct ")"
    let ret ← if ← acceptPunct "->" then parseType else pure (.tuple [])
    expectPunct ";"
    -- How a type is given to C and taken from it: the type the function
    -- is declared with, how a value of it is made the bits C takes, how
    -- what C gives is made a value of it, what C gives (so many bits; 1000
    -- a double, 1001 a float), and where C takes it (0 with the whole
    -- numbers and addresses, 1 as a double, 2 as a float).
    let call1 := fun (f : String) (x : Expr) => Expr.call 0 (.name none f) [x]
    let rec kind (fuel : Nat) : TypeExpr →
        P (TypeExpr × (Expr → Expr) × (Expr → Expr) × Int × Nat) := fun t =>
      match t with
      | .name "Int" [] => pure (t, id, id, 64, 0)
      | .name "i64" [] => pure (t, id, id, 64, 0)
      | .name "f64" [] => pure (t, call1 "f64_bits", call1 "f64_of", 1000, 1)
      | .name "f32" [] => pure (t, call1 "f32_bits", call1 "f32_of", 1001, 2)
      | .name "%prelude::Ptr" [_] =>
        pure (t, fun x => call1 "usize_bits" (call1 "ptr_address" x),
          fun r => call1 "ptr_at" (call1 "usize_of" r), 64, 0)
      | .name "%prelude::PtrMut" [_] =>
        pure (t, fun x => call1 "usize_bits" (call1 "ptr_mut_address" x),
          fun r => call1 "ptr_mut_at" (call1 "usize_of" r), 64, 0)
      | .name name [] =>
        match scalars.lookup name, cTypes.lookup (lastSegment name), fuel with
        | some (some w), _, _ => pure (t, call1 (name ++ "_bits"), call1 (name ++ "_of"), w, 0)
        -- C's own names for its types are the types they are here.
        | _, some as, fuel + 1 => kind fuel (.name as [])
        | _, _, _ => failAt s!"a foreign function takes and gives whole numbers, floats and addresses (`Int`, a type such as `i32`, `usize` or `f64`, `*const T`, `*mut T`), not `{name}`"
      | _ => failAt "a foreign function takes and gives whole numbers, floats and addresses (`Int`, a type such as `i32`, `usize` or `f64`, `*const T`, `*mut T`)"
    let mut args : Array Expr := #[]
    let mut declared : Array TypeExpr := #[]
    let mut classes : Nat := 0
    let mut place : Nat := 1
    for (p, i) in params.zipIdx do
      let (ty, into, _, _, cls) ← kind 4 p
      declared := declared.push ty
      args := args.push (into (Expr.name none s!"%a{i}"))
      classes := classes + cls * place
      place := place * 3
    let (retTy, back, bits) ← match ret with
      | .tuple [] => pure (TypeExpr.tuple [], (id : Expr → Expr), (0 : Int))
      | t => do
        let (ty, _, back, bits, _) ← kind 4 t
        pure (ty, back, bits)
    let symbol := name.toUTF8.toList.map fun b => Expr.int b.toNat
    let call := Expr.call 0 (.name none foreignCall)
      (symbol ++ [.int 0, .int bits, .int classes] ++ args.toList)
    let body : List Stmt := match ret with
      | .tuple [] => [.expr call, .expr (.tuple [])]
      | _ => [.expr (back call)]
    let pats := (List.range params.length).map fun i => Pattern.var s!"%a{i}"
    items := items.push (.fn name [] (declared.toList.map some) (some retTy) [.mk pats body])
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
  items.flatMap fun
    | .alias name (.call _ (.name none mark) [value]) =>
      -- (A value written out, `3`, `Some(4)`, `"text"`, is one already: it
      -- stays a name for it, which a pattern can be.)
      if mark == comptimeMark && writtenOut value then [.alias name value]
      else if mark == comptimeMark then
        let fn := constFnName name
        [.alias name (.call 0 (.name none fn) []), .fn fn [] [] none [.mk [] [.expr value]]]
      else [.alias name (.call 0 (.name none mark) [value])]
    | .pub parent (.alias name (.call _ (.name none mark) [value])) =>
      if mark == comptimeMark && writtenOut value then [.pub parent (.alias name value)]
      else if mark == comptimeMark then
        let fn := constFnName name
        [.pub parent (.alias name (.call 0 (.name none fn) [])), .pub parent (.fn fn [] [] none [.mk [] [.expr value]])]
      else [.pub parent (.alias name (.call 0 (.name none mark) [value]))]
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
again would give. Each group's items as `unmutItems` and `promoteItems` make
them, which go item by item; the functions written in blocks as parsed. Gives
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
    let group := promoteItems (unmutItems (← parseItemGroup))
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

/-- The modules a text says are files of their own, `mod name;`: each as its
path from the module the text is, through the modules written in the text. -/
def fileModules (src : String) : Except String (List (List String)) := do
  -- (A text that never writes `mod` declares none: not read as tokens.)
  if (src.splitOn "mod").length == 1 then return []
  let toks ← lex src
  let tok := fun (i : Nat) => (toks[i]?.map (·.tok)).getD .eof
  let mut out : Array (List String) := #[]
  -- The modules being read, each with how deep in braces its own are.
  let mut inside : List (String × Nat) := []
  let mut depth := 0
  for i in [0:toks.size] do
    match tok i, tok (i + 1), tok (i + 2) with
    | .ident "mod", .ident name, .punct ";" =>
      out := out.push ((inside.map (·.1)).reverse ++ [name])
    | .ident "mod", .ident name, .punct "{" =>
      inside := (name, depth + 1) :: inside
    | .punct "{", _, _ => depth := depth + 1
    | .punct "}", _, _ =>
      if (inside.head?.map (·.2)) == some depth then inside := inside.drop 1
      depth := depth - 1
    | _, _, _ => pure ()
  pure out.toList

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

`impl<H, ..R> Count for (H, ..R) where (..R): Count { .. }` is an
implementation for tuples of every length: it is written out once for each
length the program can need, before it is read, with `..R` standing for `R0, R1, ..`
wherever it is written in parentheses or angle brackets: in types, in
patterns (`let (h, ..rest) = t` binds `rest0`, `rest1`, ..), and in what is
built (`(x, ..rest)`). What follows `..` may be more than a name: it is
written once for each, the lists it names indexed, so `(..Option<R>)` is
`(Option<R0>, Option<R1>, ..)` and `(..show(r))` calls `show` on each. A
list of values is as long as the list of types of its name in other case,
or the first. A `..` in square brackets is an array's rest, and one before
no list is a pattern's, as before. -/

/-- The most things written between one pair of brackets: a tuple's parts,
a function's parameters or arguments. A list of types is written out for
every length up to this, at first (see `compileSource` for when it is not
enough). -/
def longestList (toks : Array Token) : Nat := Id.run do
  let tok := fun (i : Nat) => (toks[i]?.map (·.tok)).getD .eof
  -- (For each bracket open, how many parts it has so far.)
  let mut open_ : List Nat := []
  let mut most := 0
  for i in [0:toks.size] do
    match tok i with
    | .punct "(" => open_ := 1 :: open_
    | .punct "[" => open_ := 1 :: open_
    | .punct "{" => open_ := 1 :: open_
    | .punct "," =>
      match open_ with
      | n :: rest => open_ := (n + 1) :: rest
      | [] => pure ()
    | .punct ")" | .punct "]" | .punct "}" =>
      match open_ with
      | n :: rest =>
        -- (Only parentheses: `[..]` and `{..}` are counted apart.)
        if tok i == .punct ")" then most := max most n
        open_ := rest
      | [] => pure ()
    | _ => pure ()
  pure most

/-- The tokens with each implementation that has a list of types as a
parameter written out for every length up to `most`: together, where it has
more than one list. -/
def expandPacks (toks : Array Token) (most : Nat) : Array Token := Id.run do
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
      -- parameter of its own (`Traits.consHead`).
      if let some once := consOnly body (j - i) packs then
        out := out ++ once
        i := e
        continue
      -- Lists named together after one `..` are as long as each other.
      let together := linked body packs
      let leaders := packs.filter fun p => (together.lookup p).getD p == p
      -- Every length for each list, as long as together they are no
      -- longer than `most`.
      let rec lengths : List String → Nat → List (List (String × Nat))
        | [], _ => [[]]
        | p :: ps, left => (List.range (left + 1)).flatMap fun n =>
            (lengths ps (left - n)).map ((p, n) :: ·)
      for choice in lengths leaders most do
        let all := packs.map fun p => (p, (choice.lookup ((together.lookup p).getD p)).getD 0)
        -- (Each copy says it is one, `type %pack = ();` last in its body,
        -- before the `}` that closes it: one nothing uses need not be
        -- checked, `Check.checkItems`.)
        let copy := expandOne body all
        let closes := copy.size - 1
        let at_ := copy[closes]?.getD default
        let mark : Array Token := #[.ident "type", .ident Syntax.packCopyName, .punct "=", .punct "(", .punct ")", .punct ";"].map
          fun tk => { at_ with tok := tk }
        out := out ++ copy.extract 0 closes ++ mark ++ copy.extract closes copy.size
      i := e
    else
      out := out.push toks[i]!
      i := i + 1
  return out
where
  /-- An implementation (`body`, its parameters ending before `params`)
  whose lists of types are each a tuple, read as one: `..R` among its
  parameters written `R`, and what is spread read by the parser as types
  (`(H, ..R)`, `(..G, X)`, `Fn<(..P)>`: `parseType`, `parsePack`). None if
  it spreads a list of values (`let (..t) = ..`, `(..g, x)`, `f(..p)`;
  `std::tuple::Tuple` does those for every length), something of a list's
  elements (`(..Option<T>)`, `..R::Got<'a>`), or asks something of each
  element (`..S: Get<T>`): those are written out for each length. -/
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
  /-- For each list of types, the first of those it is named together with
  after one `..` (`..P: Parameter<Asks = A>`), itself if none. -/
  linked (body : Array Token) (packs : List String) : List (String × String) := Id.run do
    let tok := fun (i : Nat) => (body[i]?.map (·.tok)).getD .eof
    let mut leader : List (String × String) := packs.map fun p => (p, p)
    let rec find (l : List (String × String)) (fuel : Nat) (p : String) : String :=
      match fuel, l.lookup p with
      | 0, _ => p
      | _, none => p
      | fuel + 1, some q => if q == p then p else find l fuel q
    let mut i := 0
    while i + 1 < body.size do
      if tok i == .punct "." && tok (i + 1) == .punct "." then
        let mut j := i + 2
        let mut depth : Int := 0
        let mut named : List String := []
        while j < body.size && !(depth == 0 &&
            (tok j == .punct "," || tok j == .punct ")" || tok j == .op ">" || tok j == .punct "]"
              || tok j == .punct "{")) do
          match tok j with
          | .punct "(" => depth := depth + 1
          | .punct "[" => depth := depth + 1
          | .op "<" => depth := depth + 1
          | .punct ")" => depth := depth - 1
          | .punct "]" => depth := depth - 1
          | .op ">" => depth := depth - 1
          | .ident x => if packs.contains x && !named.contains x then named := named ++ [x]
          | _ => pure ()
          j := j + 1
        match named with
        | first :: rest =>
          let root := find leader packs.length first
          for p in rest do
            let r := find leader packs.length p
            if r != root then leader := leader.map fun (a, b) => if b == r then (a, root) else (a, b)
        | [] => pure ()
        i := j
      else i := i + 1
    return leader.map fun (p, _) => (p, find leader packs.length p)

  /-- One implementation with every `..x` in parentheses or angle brackets
  written as `x0, .., x{n-1}`. -/
  expandOne (body : Array Token) (lengths : List (String × Nat)) : Array Token := Id.run do
    let tok := fun (i : Nat) => (body[i]?.map (·.tok)).getD .eof
    let keywords := ["for", "as", "return", "in", "else", "where", "let", "mut"]
    -- How long a list is: a list of values `..xs` is as long as the list of
    -- types of its name, or the first.
    let lengthOf := fun (x : String) =>
      match lengths.lookup x with
      | some n => n
      | none =>
        match lengths.find? fun (p, _) => p.toLower == x.toLower with
        | some (_, n) => n
        | none => (lengths.head?.map (·.2)).getD 0
    let mut out : Array Token := #[]
    -- What each open bracket is, innermost last: its kind, where it is in
    -- what is written out, and whether a list was spread in it.
    let mut stack : List (String × Nat × Bool) := []
    -- Lists of values, by the names they were given (`let (..xs) = t`).
    let mut values : List String := []
    -- Is the bracket opened `opened` in what is written out a call's or a function
    -- type's arguments, rather than a tuple?
    let callLike := fun (out : Array Token) (opened : Nat) =>
      match (if opened == 0 then none else out[opened - 1]?.map (·.tok)) with
      | some (.ident w) => !keywords.contains w
      | some (.punct ")") => true
      | some (.punct "]") => true
      | some (.op ">") => true
      | _ => false
    let mut i := 0
    while i < body.size do
      let t := body[i]!
      -- (In brackets, or in the conditions after `where`, outside any.)
      let inside := match stack with
        | ("(", _) :: _ => true
        | ("<", _) :: _ => true
        | ("[", _) :: _ => true
        | [] => true
        | _ => false
      if inside && t.tok == .punct "." && tok (i + 1) == .punct "." then
        -- What `..` stands before: to the next `,` or closing bracket.
        let mut j := i + 2
        let mut depth : Int := 0
        while j < body.size && !(depth == 0 &&
            (tok j == .punct "," || tok j == .punct ")" || tok j == .op ">" || tok j == .punct "]"
              || tok j == .punct "{")) do
          match tok j with
          | .punct "(" => depth := depth + 1
          | .punct "[" => depth := depth + 1
          | .op "<" => depth := depth + 1
          | .punct ")" => depth := depth - 1
          | .punct "]" => depth := depth - 1
          | .op ">" => depth := depth - 1
          | _ => pure ()
          j := j + 1
        let span := body.extract (i + 2) j
        -- (A name alone is a list of its own: of types if it is one, and
        -- otherwise of values from here on.)
        if let #[⟨.ident x, _, _⟩] := span then
          unless lengths.any (·.1 == x) || values.contains x do values := values ++ [x]
        let isPack := fun (x : String) => lengths.any (·.1 == x) || values.contains x
        let mentioned := span.toList.filterMap fun tk => match tk.tok with
          | .ident x => if isPack x then some x else none
          | _ => none
        match mentioned with
        | [] =>
          out := out.push t
          i := i + 1
        | x :: _ =>
          stack := match stack with
            | (k, opened, _) :: rest => (k, opened, true) :: rest
            | [] => []
          let n := lengthOf x
          if n == 0 then
            -- (and the comma after it, or the one before it; and a `where`
            -- with nothing left after it)
            if tok j == .punct "{" && (out.back?.map (·.tok)) == some (.ident "where") then
              out := out.pop
            if tok j != .punct "," && (out.back?.map (·.tok)) == some (.punct ",") then
              out := out.pop
            i := if tok j == .punct "," then j + 1 else j
            continue
          for k in [0:n] do
            if k > 0 then out := out.push ⟨.punct ",", t.line, t.col⟩
            for tk in span do
              out := out.push (match tk.tok with
                | .ident y => if isPack y then ⟨.ident s!"{y}{k}", tk.line, tk.col⟩ else tk
                | _ => tk)
          i := j
          continue
      match t.tok with
      | .punct "(" => stack := ("(", out.size, false) :: stack
      | .punct "[" => stack := ("[", out.size, false) :: stack
      | .punct "{" => stack := ("{", out.size, false) :: stack
      | .op "<" => stack := ("<", out.size, false) :: stack
      | .punct ")" =>
        -- A tuple a list was spread in that is left with one part is a
        -- tuple of one: `(x0,)`.
        match stack.dropWhile (·.1 != "(") with
        | (_, opened, true) :: _ =>
          let mut depth : Int := 0
          let mut commas := 0
          for k in [opened + 1:out.size] do
            match (out[k]?.map (·.tok)).getD .eof with
            | .punct "(" => depth := depth + 1
            | .punct "[" => depth := depth + 1
            | .punct "{" => depth := depth + 1
            | .op "<" => depth := depth + 1
            | .punct ")" => depth := depth - 1
            | .punct "]" => depth := depth - 1
            | .punct "}" => depth := depth - 1
            -- (A type's arguments, `Query<Q, N, St>`, are inside it.)
            | .op ">" => if depth > 0 then depth := depth - 1
            | .punct "," => if depth == 0 then commas := commas + 1
            | _ => pure ()
          if commas == 0 && out.size > opened + 1 && !callLike out opened then
            out := out.push ⟨.punct ",", t.line, t.col⟩
        | _ => pure ()
        stack := (stack.dropWhile (·.1 != "(")).drop 1
      | .punct "]" => stack := (stack.dropWhile (·.1 != "[")).drop 1
      | .punct "}" => stack := (stack.dropWhile (·.1 != "{")).drop 1
      | .op ">" => if (stack.head?.map (·.1)) == some "<" then stack := stack.drop 1
      | _ => pure ()
      out := out.push t
      i := i + 1
    return out

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

/-- Each declared type's `Reflect` among a module's items, read as its text
is; checked only where something asks it, as a copy for each length of a
list is. -/
def reflectionsOf (fix : Fixities) (items : List Item) (base : Nat) (records : List String)
    (tables : List (List String × Fixities)) (path : List String) (fixed : Bool) : Except String (List Item) := do
  let texts := reflectTexts items
  if texts.isEmpty then return []
  let gtoks ← lex (String.join texts)
  let fix := if tables.isEmpty then fix else ((tables.lookup path).getD fix)
  let (gitems, _, glocal) ← parseItems { toks := gtoks, fix, records, base, tables, path, fixed } 0 #[]
  pure ((gitems ++ glocal.toList).map fun
    | .impl ps tr h args ctx ms => Item.impl ps tr h args ctx (ms ++ [.typeAlias packCopyName [] (.tuple [])])
    | other => other)

/-- Parse a source text, given the fixities already in scope. Returns the items
and the fixities including those it declares. `base` keeps the identities of
this text's callable literals apart from those of a text parsed before it.
With `tables`, each module of the text has the operators the table gives it,
and the text is the module `path`. -/
def parseKept (fix : Fixities) (src : String) (base : Nat := 0) (records : List String := [])
    (tables : List (List String × Fixities) := []) (path : List String := [])
    (fixed : Bool := false) (packs : Nat := 0) (lexed : Option (Array Token) := none)
    (reflect : Bool := true) (kept : Option ItemsKept := none) :
    Except String (List Item × Fixities × ItemsKept) := do
  -- (`packs`: how long lists of types are written out to; by default, as
  -- long as the longest list this text writes.)
  let toks ← match lexed with
    | some toks => pure toks
    | none => lex src
  let toks := expandPacks toks (if packs == 0 then max 2 (longestList toks) else packs)
  let fix ← if tables.isEmpty then collectFixities toks fix else pure ((tables.lookup path).getD fix)
  let ctx : PCtx := { toks, fix, records := collectRecords toks ++ records, base, tables, path, fixed }
  match kept with
  | some kept =>
    let ((items, groups), _, local_) ← parseItemsKept kept ctx 0 #[]
    let made ← if reflect then reflectionsOf fix (items ++ local_.toList) (base + 700000) (collectRecords toks ++ records) tables path fixed else pure []
    pure (items ++ promoteItems (unmutItems (local_.toList ++ made)), fix, groups)
  | none =>
    let (items, _, local_) ← parseItems ctx 0 #[]
    let items := items ++ local_.toList
    -- (Each declared type's `Reflect`, read as the text is, after its items;
    -- checked only where something asks it, as a copy for each length of a
    -- list is.)
    let made ← if reflect then reflectionsOf fix items (base + 700000) (collectRecords toks ++ records) tables path fixed else pure []
    pure (promoteItems (unmutItems (items ++ made)), fix, {})

/-- `parseKept`, nothing taken from an earlier parse. -/
def parse (fix : Fixities) (src : String) (base : Nat := 0) (records : List String := [])
    (tables : List (List String × Fixities) := []) (path : List String := [])
    (fixed : Bool := false) (packs : Nat := 0) (lexed : Option (Array Token) := none)
    (reflect : Bool := true) :
    Except String (List Item × Fixities) := do
  let (items, fix, _) ← parseKept fix src base records tables path fixed packs lexed reflect
  pure (items, fix)

end Glorious.Syntax
