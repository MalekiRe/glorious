module

public import Glorious.Syntax.Parser.Base

public section

namespace Glorious.Syntax.Parse

open Flat (ExprId StmtId ClauseId FExpr FStmt FClause)

mutual

partial def parsePatternRest : P Pattern := do
  match ← peek with
  | .ident "_" =>
    advance
    pure .wild
  | .punct "[" =>
    -- `[a, b, c]`: an array of exactly so many elements. With `..` or
    -- `..rest` among them, one of at least so many: `[first, ..rest]`.
    let opened := (← read).base + (← get)
    let at_ ← peekTok
    advance
    let mut ps : Array Pattern := #[]
    let mut before : Option Nat := none
    repeat
      if (← peek) == .punct "]" then break
      if (← peek) == .punct "." && (← peek 1) == .punct "." then
        if before.isSome then failAt "an array pattern has one `..`"
        advance
        advance
        before := some ps.size
        match ← peek with
        | .ident "_" =>
          advance
          ps := ps.push .wild
        | .ident name =>
          advance
          ps := ps.push (.var name)
        | _ => ps := ps.push .wild
      else ps := ps.push (← parsePattern)
      if !(← acceptPunct ",") then break
    expectPunct "]"
    match before with
    | some k => pure (.ctor (restPatName k opened at_.line at_.col) none ps.toList)
    | none => pure (.ctor ((if (← read).fixed then fixedPatName else arrayPatName) ps.size) none ps.toList)
  | .ident "let" =>
    -- `let name`: a new name, whatever constant or constructor has it.
    advance
    pure (.ctor letMark none [.var (← expectIdent)])
  | .ident "mut" =>
    -- `mut name`: what it binds is a variable (`unmutItems`).
    advance
    pure (.ctor mutPatMark none [.var (← expectIdent)])
  | .ident x =>
    advance
    let (qual, name) := splitPath (← parsePathRest x)
    if ← acceptPunct "(" then
      let args ← parsePatternList
      pure (.ctor name qual args)
    else if (← peek) == .punct "{" && (← read).records.contains name then
      -- `Point { x, y: p }`: each field by name, `x` alone binding `x`; `..`
      -- lets the fields not named go.
      advance
      let mut given : Array Pattern := #[.var recordMark]
      repeat
        if (← peek) == .punct "}" then break
        if (← peek) == .punct "." && (← peek 1) == .punct "." then
          advance
          advance
          given := given.push (.var restMark)
          break
        let field ← expectIdent
        let pat ← if ← acceptPunct ":" then parsePattern else pure (.var field)
        given := given.push (.ctor (fieldMark field) none [pat])
        if !(← acceptPunct ",") then break
      expectPunct "}"
      pure (.ctor name qual given.toList)
    else if qual.isSome then pure (.ctor name qual [])
    else pure (.var name)
  | .int n =>
    let v ← plainInt false n
    advance
    pure (.int v)
  | .op "-" =>
    match ← peek 1 with
    | .int n =>
      advance
      let v ← plainInt true n
      advance
      pure (.int v)
    | .typed _ _ =>
      advance
      match ← literalOf (← scalarLiteral true) with
      | some p => pure p
      | none => failAt "expected a pattern"
    | _ => failAt "expected a pattern"
  | .typed _ _ | .char _ | .str _ =>
    match ← literalOf (← scalarLiteral false) with
    | some p => pure p
    | none => failAt "expected a pattern"
  | .float _ _ _ => failAt "a floating point number is not a pattern: compare it instead"
  | .op "&" =>
    -- `&mut Pattern`: what a reference points to, its names references.
    advance
    let uniq := (← peek) == .ident "mut"
    if uniq then advance
    pure (.ctor (byRefMark uniq) none [← parsePattern])
  | .punct "(" =>
    let opened := (← read).base + (← get)
    advance
    let args ← parsePatternList
    -- How many parts a tuple has is not written anywhere a pattern could
    -- read it: `..` is for a constructor's fields.
    -- `(first, ..)`: the parts not written, however many the tuple has.
    -- How many is the checker's to find; until then `..` has a name.
    let rests := args.filter fun p => match p with
      | .var r => r == restMark
      | _ => false
    if rests.length > 1 then failAt "a tuple pattern has one `..`"
    if rests.length == 1 then
      return .tuple (args.map fun p => match p with
        | .var r => if r == restMark then .var (tupleRestName opened) else .var r
        | p => p)
    match args with
    | [p] => if ← closedAfterComma then pure (.tuple [p]) else pure p
    | _ => pure (.tuple args)
  | _ => failAt "expected a pattern"

/-- Patterns separated by commas up to and including the closing `)`. -/
partial def parsePattern : P Pattern := do
  match ← peek with
  -- (A word of the language bound as a name could not be written after.)
  | .ident w =>
    if ["tail", "handle", "move", "fn"].contains w then
      failAt s!"`{w}` is a word of the language: what is bound here is named otherwise"
    parsePatternRest
  | _ => parsePatternRest

partial def parsePatternList : P (List Pattern) := do
  let out ← listUntil (atPunct ")") do
    -- `..`: the fields not written, let go.
    if (← peek) == .punct "." && (← peek 1) == .punct "." then
      advance
      advance
      pure (.var restMark)
    else parsePattern
  expectPunct ")"
  pure out

/-- Expressions separated by commas up to and including the closing `)`. -/
partial def parseArgs : P (List ExprId) := do
  let out ← listUntil (atPunct ")") (parseBinary 0 false)
  expectPunct ")"
  pure out

/-- Binary operators by precedence climbing. With `noBlock`, a `{` after a call
is not taken as a trailing block. -/
partial def parseBinary (minPrec : Nat) (noBlock : Bool)
    (before : Option (Nat × Assoc) := none) : P ExprId := do
  let mut lhs ← parseUnary noBlock
  -- The operator this operand follows, at its precedence.
  let mut last := before
  repeat
    let t ← peek
    match ← infixOf t with
    | some (name, prec, assoc) =>
      if prec < minPrec then break
      -- Two operators of one precedence in a row group one way or need
      -- brackets.
      if let some (prec', assoc') := last then
        if prec' == prec then
          if assoc == .non || assoc' == .non then
            failAt s!"`{name}` does not group with an operator of its own precedence: write brackets"
          if assoc != assoc' then
            failAt s!"`{name}` and the operator before it have one precedence and group opposite ways: write brackets"
      last := some (prec, assoc)
      -- Each call is known by the token that makes it one.
      let id := (← read).base + (← get) + 1
      advance
      let next := match assoc with
        | .right => prec
        | _ => prec + 1
      -- `else if(c) { .. } else { .. }`: the `if` after `else` is its
      -- fallback, a block run in its place, as `else { if(c) .. }` is.
      let elseIf := name == "else" && (← peek) == .ident "if"
      -- (The block is known by the place of `else`, which nothing else is.)
      let blockId := id - 1
      let rhs ← parseBinary next noBlock (some (prec, assoc))
      let rhs ← if elseIf then mk (.closure blockId #[← mkC [] #[← mkS (.expr rhs)]]) else pure rhs
      let (qual, f) := splitPath (((← read).fix.function name false).splitOn "::")
      lhs ← callOf id qual f #[lhs, rhs]
    | none =>
      match t with
      | .op s =>
        if s.length == 2 && s.endsWith "=" && ["+=", "-=", "*=", "/=", "%="].contains s then
          failAt s!"`x {s} e` is not an assignment here: write `x = x {(s.take 1).toString} e`"
        failAt s!"operator `{s}` has no infix fixity in this module (a fixity is its module's: `use` the function the operator stands for)"
      | .ident "is" =>
        -- `subject is Pattern`, which binds as a comparison does.
        if 4 < minPrec then break
        let id := (← read).base + (← get) + 1
        advance
        let pat ← parsePattern
        lhs ← callOf id none isMark #[lhs, ← mk (.closure 0 #[← mkC [pat] #[]])]
      | _ => break
  pure lhs

partial def parseUnary (noBlock : Bool) : P ExprId := do
  let t ← peek
  let fix := (← read).fix
  -- `-` straight before a number is part of the number.
  if t == .op "-" then
    match ← peek 1 with
    | .int n =>
      advance
      let v ← plainInt true n
      advance
      return ← mk (.int v)
    | .typed _ _ | .float _ _ _ =>
      advance
      match ← scalarLiteral true with
      | some e => return e
      | none => failAt "expected a number"
    | _ => pure ()
  let name? := match t with
    | .op s => some s
    | .ident s => some s
    | _ => none
  match name? with
  | some s =>
    match fix.prefixes.lookup s with
    | some prec =>
      let id := (← read).base + (← get) + 1
      advance
      let operand ← parseBinary prec noBlock
      let (qual, f) := splitPath ((fix.function s true).splitOn "::")
      callOf id qual f #[operand]
    | none =>
      if t == .op "-" then failAt "operator `-` has no prefix fixity"
      else if t == .op "&" then
        advance
        let uniq := (← peek) == .ident "mut"
        if uniq then advance
        if (← peek) == .op "*" then
          advance
          mk (.reborrow uniq (← parseUnary noBlock))
        else
          let id := (← read).base + (← get) + 1
          let mark := if uniq then borrowMutMark else borrowMark
          -- `&x`, `&x.0.1`, `&(*p).0`, or `&f().0` through what an
          -- expression gives.
          let e ← parsePostfix true
          match ← node e with
          -- (A name written with a capital is a constructor or a constant, a
          -- value and no variable: it is borrowed as any value is, below.)
          | .name none x =>
            if x.front.isUpper then callOf id none mark #[e]
            else mk (.ref uniq x)
          | _ =>
            if let some at_ ← elementBorrow uniq e then return at_
            match ← fieldRoot e with
            -- (A field of an array's element, `&a[i].f`: through a borrow of
            -- the element.)
            | some (.through b, path) =>
              match ← elementBorrow uniq b with
              | some r => fieldBorrow id uniq (.through r) path
              | none => fieldBorrow id uniq (.through b) path
            | some (root, path) => fieldBorrow id uniq root path
            -- A value with no name: it is given one where the statement
            -- starts, and that is borrowed.
            | none => callOf id none mark #[e]
      else if t == .op "&*" then
        -- `&*e`, which the lexer reads as one symbol.
        advance
        mk (.reborrow false (← parseUnary noBlock))
      else if t == .op "*" then
        advance
        mk (.deref (← parseUnary noBlock))
      else
        -- `&**e` and `**e`, which the lexer reads as one symbol each: a
        -- borrow through, or a reading through, as many references.
        match t with
        | .op s =>
          let stars := (s.dropWhile (· == '&')).toString
          let amps := s.length - stars.length
          if amps ≤ 1 && stars.length ≥ 2 && stars.all (· == '*') then
            advance
            let mut e ← parseUnary noBlock
            for _ in [0:stars.length - amps] do
              e ← mk (.deref e)
            if amps == 1 then mk (.reborrow false e) else pure e
          else parsePostfix noBlock
        | _ => parsePostfix noBlock
  | none => parsePostfix noBlock

partial def parsePostfix (noBlock : Bool) : P ExprId := do
  let mut e ← parsePrimary noBlock
  repeat
    match ← peek with
    | .ident "as" =>
      failAt "`as` is not read: `int(x)` is an `Int` of a number or a character, `f64(n)` an `f64` of an `Int`, and `T::from(x)` what `From` gives"
    | .op "<" =>
      -- `f<A, B>(args)`: types written for the function's type parameters.
      -- It is that, and not a comparison, if what follows reads as types
      -- closed by `>` with `(` straight after.
      -- (`value.f<A>(args)` too.)
      let isName := match ← node e with
        | .name _ _ => true
        | .fieldOf _ _ _ => true
        | _ => false
      if !isName then break
      let saved ← get
      let attempt : P (Option (List TypeExpr)) :=
        try
          advance
          let tys ← listUntil (isOp ">") parseType
          if !(← isOp ">") then pure none
          else
            advance
            if (← peek) != .punct "(" then pure none else pure (some tys)
        catch _ => pure none
      match ← attempt with
      | none =>
        set saved
        break
      | some tys =>
        let id := (← read).base + (← get) + 1
        advance
        let mut args ← parseArgs
        while !noBlock && (← peek) == .punct "{" do
          args := args ++ [← parseBraces]
        e ← callOf 0 none instMark #[← mk (.call id e args.toArray), ← tree (TypeExpr.tuple tys).asExpr]
    | .punct "(" =>
      let id := (← read).base + (← get) + 1
      advance
      let mut args ← parseArgs
      while !noBlock && (← peek) == .punct "{" do
        args := args ++ [← parseBraces]
      e ← mk (.call id e args.toArray)
    | .punct "{" =>
      -- `Point { x: 1, y: 2 }` builds a value of a type declared with names.
      let records := (← read).records
      let isRecord := match ← node e with
        | .name _ x => records.contains x
        | _ => false
      if isRecord then
        let id := (← read).base + (← get) + 1
        advance
        let mut given : Array ExprId := #[← mkName none recordMark]
        repeat
          if (← peek) == .punct "}" then break
          let field ← expectIdent
          let value ← if ← acceptPunct ":" then parseBinary 0 false else mkName none field
          given := given.push (← callOf 0 none (fieldMark field) #[value])
          if !(← acceptPunct ",") then break
        expectPunct "}"
        e ← mk (.call id e given)
        continue
      -- `f { body }` is `f({ body })`.
      if noBlock then break
      let id := (← read).base + (← get) + 1
      let mut args : Array ExprId := #[]
      while (← peek) == .punct "{" do
        args := args.push (← parseBraces)
      e ← mk (.call id e args)
    | .punct "[" =>
      -- `a[i]`: the element at a place.
      let id := (← read).base + (← get) + 1
      advance
      let place ← parseBinary 0 false
      expectPunct "]"
      e ← mk (.call id (← preludeFn "index") #[e, place])
    | .punct "." =>
      match ← peek 1 with
      | .int n =>
        -- A field of what a name stands for, or of what a call gives, is
        -- known by an identity, so that the checker can say it is read
        -- through a reference.
        let id := (← read).base + (← get) + 1
        advance
        advance
        e ← match ← node e with
          | .name none _ | .call .. => mk (.fieldOf id e (toString n))
          | _ => mk (.proj e n)
      | .ident field =>
        let id := (← read).base + (← get) + 1
        advance
        advance
        e ← mk (.fieldOf id e field)
      | _ => failAt "expected a field after `.`"
    | _ => break
  pure e

partial def parsePrimary (noBlock : Bool) : P ExprId := do
  -- (`println!(..)`: a Rust macro; there are none.)
  if let .ident m ← peek then
    if (← peek 1) == .op "!" && ((← peek 2) == .punct "(" || (← peek 2) == .punct "[") then
      failAt s!"`{m}!` is not read: there are no macros; call a function, `say(value)`, `assert(condition)`, `abort(message)`"
  -- A parameter that stands for a number, written as a value: the number.
  if let .ident x ← peek then
    if (← read).consts.contains x && (← peek 1) != .punct "::" then
      let id := (← read).base + (← get) + 1
      advance
      return ← callOf 0 none instMark
        #[← mk (.call id (← mkName (some knownTrait) "VALUE") #[]), ← tree (TypeExpr.tuple [.name x []]).asExpr]
  match ← peek with
  | .int n =>
    let v ← plainInt false n
    advance
    mk (.int v)
  | .typed _ _ | .float _ _ _ | .char _ | .str _ | .bytes _ =>
    match ← scalarLiteral false with
    | some e => pure e
    | none => failAt "expected a value"
  | .punct "[" =>
    -- `[a, b, c]`, or `[x; n]`: `n` of `x`.
    -- (The calls a literal stands for are numbered from where it is, apart
    -- from the numbers of what is written; in a file too long for that
    -- they go without.)
    let base := (← read).base
    -- (Past the first 100,000 tokens of a text, where `base + at_ + offset`
    -- would be another token's: numbered in a space of their own, by the
    -- text's place, the token and the offset.)
    let numbered := fun (at_ offset : Nat) =>
      if at_ < 100000 then base + at_ + offset
      else 800000000000000000 + (base / 1000000) * 100000000 + at_ * 10 + (offset / 100000) % 10
    let opened ← get
    let empty := numbered opened 600000
    advance
    -- Where the program has arrays of a fixed length, the literal is an
    -- array or one of exactly so many: whichever is wanted of it.
    -- (A program's own literal, where every one is a `[T; N]`.)
    let own := fixedLiterals && (← read).base ≥ 1000000 && (← read).path.head? != some "std"
    let fixedOf := fun (value : ExprId) (n : Nat) => do
      callOf 0 none instMark #[← mk (.call (numbered opened 800000) (← preludeFn (if own then "fixed_literal" else "array_literal")) #[value]),
        ← tree (TypeExpr.tuple [numberType n]).asExpr]
    if ← acceptPunct "]" then
      let value ← arrayValue [] empty
      return ← if (← read).fixed || own then fixedOf value 0 else pure value
    let mut starts : Array Nat := #[numbered (← get) 700000]
    let first ← parseBinary 0 false
    if ← acceptPunct ";" then
      let count ← parseBinary 0 false
      expectPunct "]"
      return ← mk (.call (numbered opened 900000) (← preludeFn "array_repeat") #[first, count])
    let mut elements : Array ExprId := #[first]
    while ← acceptPunct "," do
      if (← peek) == .punct "]" then break
      starts := starts.push (numbered (← get) 700000)
      elements := elements.push (← parseBinary 0 false)
    expectPunct "]"
    let value ← arrayValue elements.toList empty starts.toList
    if (← read).fixed || own then fixedOf value elements.size else pure value
  | .ident "tail" =>
    advance
    let e ← parsePostfix noBlock
    match ← node e with
    | .call id f args => mk (.tailCall id f args)
    | _ => failAt "`tail` must be followed by a call"
  | .op "<" =>
    -- `<Type as Trait>::function(args)`: the trait's function, for that type.
    advance
    let self ← parseType
    unless (← peek) == .ident "as" do failAt "expected `as`: `<Type as Trait>::function(..)`"
    advance
    let (trait, targs) ← match ← parseType with
      | .name tr targs => pure (tr, targs)
      | _ => failAt "expected a trait: `<Type as Trait>::function(..)`"
    if ← isOp ">" then advance else failAt "expected `>`"
    expectPunct "::"
    -- (The name's own place numbers the call where nothing is written
    -- after it: the next token's number is its own to use.)
    let nameAt := (← read).base + (← get) + 1
    let name ← expectIdent
    -- `<Type as Trait>::NAME`: a value the trait leaves to implementations,
    -- which is its function of that name called with nothing.
    let mut args : List ExprId := []
    let mut id := nameAt
    if (← peek) == .punct "(" then
      id := (← read).base + (← get) + 1
      advance
      args ← parseArgs
      while !noBlock && (← peek) == .punct "{" do
        args := args ++ [← parseBraces]
    callOf 0 none instMark #[← mk (.call id (← mkName (some trait) name) args.toArray),
      ← tree (TypeExpr.tuple (self :: targs)).asExpr]
  | .ident "move" =>
    advance
    -- `move (a, b) { body }`: the block, holding the values `a` and `b`
    -- have where it is written. It is a callable given them at once.
    if (← peek) == .punct "(" then
      let saved ← get
      advance
      let mut names : Array String := #[]
      let mut listed := true
      repeat
        match ← peek with
        | .punct ")" => break
        | .ident x =>
          advance
          names := names.push x
          if !(← acceptPunct ",") then break
        | _ =>
          listed := false
          break
      if listed && (← peek) == .punct ")" && (← peek 1) == .punct "{" then
        advance
        let id := (← read).base + (← get) + 1
        let block ← parseBraces
        let f ← mk (.closure 0 #[← mkC (names.toList.map Pattern.var) #[← mkS (.expr block)]])
        return ← mk (.call id f (← names.mapM (mkName none)))
      set saved
    -- `move place`: the value, handed on; the place is not used after.
    let id := (← read).base + (← get) + 1
    let operand ← parseUnary noBlock
    callOf id none moveMark #[operand]
  | .ident "handle" =>
    advance
    let subject ← parseBinary 0 true
    unless (← peek) == .punct "{" do
      failAt "`handle` is a word of the language, `handle computation { arms }`: nothing else can be named `handle`"
    expectPunct "{"
    let arms ← parseClauses
    expectPunct "}"
    mk (.handle subject arms.toArray)
  | .ident "const" =>
    -- `const { .. }`: a block worked out at compile time, as a constant is,
    -- by a function of the module (it uses nothing of where it is written).
    if (← peek 1) != .punct "{" then failAt "expected an expression"
    let id := (← read).base + (← get)
    advance
    let (types, bounds) := (← read).enclosing
    match ← node (← parseBraces) with
    | .closure _ clauses =>
      let fn := constFnName s!"const%{id}"
      -- (Generic in the type parameters of the function it is in, with what
      -- is written of them: each copy of that function at known types has
      -- one at those types.)
      let wanted := bounds.filter (types.contains ·.subject)
      -- (Its clauses, out of the body they were read in.)
      let body := { (← getThe Flat.Body) with roots := clauses }.compact
      modifyThe (Array Item) fun made =>
        (made.push (Item.fn fn types [] none body)) ++ (if wanted.isEmpty then #[] else #[.bounds fn wanted])
      -- (Known by the place of `const`: what it needs is given there.)
      let call ← mk (.call id (← mkName none fn) #[])
      if types.isEmpty then pure call
      else callOf 0 none instMark #[call, ← tree (TypeExpr.tuple (types.map (TypeExpr.name · []))).asExpr]
    | _ => failAt "expected a block after `const`"
  | .ident "fn" =>
    -- `fn(a: A, b) -> R / {E} { body }`: a callable written out. A type may
    -- be written of a parameter, and what it gives and performs after.
    advance
    expectPunct "("
    let mut pats : Array Pattern := #[]
    let mut annots : Array (Option TypeExpr) := #[]
    repeat
      if (← peek) == .punct ")" then break
      pats := pats.push (← parsePattern)
      annots := annots.push (← if ← acceptPunct ":" then some <$> parseType else pure none)
      if !(← acceptPunct ",") then break
    expectPunct ")"
    let ret ← if (← acceptPunct "->") || (← peek) == .op "/" then some <$> parseResult else pure none
    expectPunct "{"
    let body ← parseStmts
    expectPunct "}"
    let written ← mk (.closure 0 #[← mkC pats.toList body])
    if annots.all Option.isNone && ret.isNone then pure written
    else
      -- With types written it is the callable, of the type they make.
      let ty := TypeExpr.fn (annots.toList.map (·.getD .hole)) (ret.getD .hole)
      callOf 0 none ascribeMark #[written, ← tree ty.asExpr]
  | .ident x =>
    if x.startsWith "'" then failAt "a lifetime is not a value"
    if x == "unsafe" && (← peek 1) == .punct "{" then
      -- `unsafe { .. }`: a block run where it is written, in which what is
      -- unsafe may be named.
      let call := (← read).base + (← get) + 1
      advance
      advance
      let id := (← read).base + (← get)
      let marked ← mkS (.expr (← mkName none unsafeMark))
      let body ← parseStmts
      expectPunct "}"
      return ← mk (.call call (← mk (.closure id #[← mkC [] (#[marked] ++ body)])) #[])
    advance
    let (qual, name) := splitPath (← parsePathRest x)
    -- `Type::NAME`, in capitals and not called: perhaps a value a trait
    -- leaves to implementations. What it is, is found with the names.
    let capitals := name.any Char.isUpper && name.all fun c => c.isUpper || c.isDigit || c == '_'
    if qual.isSome && capitals && (← peek) != .punct "(" && (← peek) != .punct "{" then
      return ← callOf ((← read).base + (← get)) none pathMark #[← mkName qual name]
    mkName qual name
  | .punct "@" =>
    advance
    let l ← expectIdent
    -- `@name: T { .. }`: the scope gives a `T`.
    if !noBlock && (← peek) == .punct ":" then
      advance
      let ty ← parseType
      expectPunct "{"
      let body ← parseStmts
      expectPunct "}"
      return ← callOf 0 none ascribeMark #[← mk (.labelScope l body), ← tree ty.asExpr]
    if !noBlock && (← peek) == .punct "{" then
      advance
      let body ← parseStmts
      expectPunct "}"
      mk (.labelScope l body)
    else mk (.label l)
  | .punct "(" =>
    advance
    let args ← parseArgs
    match args with
    | [e] =>
      if ← closedAfterComma then mk (.tuple #[e])
      -- `(s.f)(..)`: the field, a callable, called; not the function of the
      -- name of what `s` is. (A block of its own, which a dot call is not.)
      else if (← peek) == .punct "(" then
        match ← node e with
        | .fieldOf .. => mk (.labelScope "%paren" #[← mkS (.expr e)])
        | _ => pure e
      else pure e
    | _ => mk (.tuple args.toArray)
  | .punct "{" => parseBraces
  | .op "|" => failAt "a callable is written `{ x => body }`, or `fn(x) { body }`; `|x| body` is not read"
  | .op "||" => failAt "a callable is written `{ => body }`, or `fn() { body }`; `|| body` is not read"
  | _ => failAt "expected an expression"

/-- A callable literal in braces. -/
partial def parseBraces : P ExprId := do
  expectPunct "{"
  let ctx ← read
  let id := ctx.base + (← get)
  if scanClauseForm ctx.toks (← get) 0 then
    let clauses ← parseClauses
    expectPunct "}"
    mk (.closure id clauses.toArray)
  else
    let body ← parseStmts
    expectPunct "}"
    mk (.closure id #[← mkC [] body])

/-- Clauses separated by commas, up to but not including the closing `}`. -/
partial def parseClauses : P (List ClauseId) := do
  restClauses (← listUntil (atPunct "}") parseClause)

/-- One clause: a pattern for the argument, or none for a callable taking no
arguments. Several patterns, `{ a, b, c => .. }`, are one tuple taken apart,
`{ (a, b, c) => .. }`: given one tuple, its parts; wanted where a callable of
several arguments is, the arguments (5.4). -/
partial def parseClause : P ClauseId := do
  let pats ←
    if (← peek) == .punct "=>" then pure []
    else do
      let first ← parsePattern
      let mut more : Array Pattern := #[]
      while ← acceptPunct "," do
        more := more.push (← parsePattern)
      pure [if more.isEmpty then first else .tuple (first :: more.toList)]
  -- (Rust's, which version 1 does not have.)
  if (← peek) == .ident "if" then
    failAt "a pattern has no guard: test in the clause, `x => if(c) { .. } else { .. }`, or match again"
  if ← isOp "|" then
    failAt "a pattern has no alternatives: write a clause for each, or `_ =>` for the rest"
  if (← peek) == .punct ".." || (← peek) == .punct "." || (← isOp "..=") || (← isOp "..") then
    failAt "a pattern has no ranges: test in the clause, `x => if(x <= 9) { .. } else { .. }`"
  expectPunct "=>"
  let body ← parseStmts
  mkC pats body

/-- Statements up to a `}` or a `,`. A trailing `;` makes the value unit. -/
partial def parseStmts : P (Array StmtId) := do
  let mut out : Array StmtId := #[]
  -- The functions written in this block, each with the name it has as a
  -- function of the module.
  let mut local_ : Array (String × String) := #[]
  let madeBefore := (← getThe (Array Item)).size
  let unit := fun (_ : Unit) => do mkS (.expr (← mk (.tuple #[])))
  repeat
    let t ← peek
    if t == .punct "}" || t == .punct "," || t == .eof then break
    -- `fn name(..) { .. }` in a block: a function of the module, which only
    -- this block can name. It uses nothing of the block's.
    if t == .ident "fn" then
      match ← peek 1, ← peek 2 with
      | .ident name, .punct "(" | .ident name, .op "<" =>
        let own := s!"{name}%{(← read).base + (← get)}"
        let (item, bounds) ← parseFn
        let _ ← acceptPunct ";"
        match item with
        | .fn _ ps annots ret body =>
          modifyThe (Array Item) fun made =>
            (made.push (.fn own ps annots ret body)) ++ (if bounds.isEmpty then #[] else #[.bounds own bounds])
          local_ := local_.push (name, own)
        | _ => pure ()
        continue
      | _, _ => pure ()
    -- (What is written as in other languages, where it is not this one's.)
    -- (Only where what follows the word could not follow a name.)
    let operand := fun (tok : Tok) => match tok with
      | .ident _ => true
      | .int _ => true
      | _ => false
    match t, ← peek 1 with
    | .ident "return", next =>
      if operand next then
        failAt "`return` is the library's function of a value and the function's label, `return(value, @f)`; or the value is written last, without `;`"
    | .ident "for", .ident _ =>
      if (← peek 2) == .ident "in" then
        failAt "there is no `for .. in` loop: go through an iterator with `for_each(&mut it, { (x) => .. })`, or loop with `while({ condition }, { body })`"
    | .ident "match", next =>
      if operand next then
        failAt "`match` is given what it matches in parentheses: `match(x) { pattern => .. }`"
    | .ident "if", .ident "let" =>
      failAt "`if let` is not read: test with `is`, `if(a is Some(x)) { .. } else { .. }`"
    | .ident "while", .ident "let" =>
      failAt "`while let` is not read: test with `is`, `while({ a is Some(x) }) { .. }`"
    | .ident "if", next =>
      if operand next then
        failAt "`if` is given its condition in parentheses: `if(c) { .. } else { .. }`"
    | _, _ => pure ()
    let here ← peekTok
    -- A borrow of a field of what an expression points to: the reference is
    -- given a name first; each statement placed where it starts.
    let settle := fun (s : FStmt) => (do
      match ← hoistStmt s with
      | some ss => ss.toArray.mapM fun s => do mkS (.located here.line here.col (← mkS s))
      | none => throw s!"{here.line}:{here.col}: a field is borrowed of what an expression points to, after something else in the statement is computed: give the reference a `let` of its own first" : P (Array StmtId))
    if t == .ident "let" then
      advance
      let mutName ← if (← peek) == .ident "mut" then do advance; some <$> expectIdent else pure none
      let pat ← if mutName.isSome then pure .wild else parsePattern
      -- `let x: Type = value`: the value is made that type.
      let typed ← if ← acceptPunct ":" then some <$> parseType else pure none
      expectPunct "="
      let value ← parseBinary 0 false
      let value ← match typed with
        | some ty => callOf 0 none ascribeMark #[value, ← tree ty.asExpr]
        | none => pure value
      expectPunct ";"
      if let some name := mutName then
        out := out ++ (← settle (.letMut name value))
      else
        match pat with
        | .wild =>
          -- `let _ = value;` is the value computed and let go, as `value;`
          -- is: what it is has its `drop` run, where a name would keep it.
          out := out ++ (← settle (.expr value))
          let t' ← peek
          if t' == .punct "}" || t' == .punct "," then
            out := out.push (← unit ())
        | _ =>
          -- `let [a, b, c] = xs`, where the program has arrays of a fixed
          -- length: `xs` is one of exactly three, taken apart as a tuple.
          let here ← get
          let ctx ← read
          let id := if here < 100000 then ctx.base + here + 900000 else 0
          let (pat, value) ← match pat, ctx.fixed with
            | .ctor name none args, true =>
              if (arrayPatLen name).isSome then
                pure (Pattern.tuple args, ← mk (.call id (← preludeFn "elements") #[value]))
              else pure (pat, value)
            | _, _ => pure (pat, value)
          out := out ++ (← settle (.let_ pat value))
    else if t == .ident "defer" then
      advance
      let e ← parseBinary 0 false
      -- `defer { .. }`: the block is what is run on the way out, not a
      -- callable to be made then and let go.
      let block ← match ← node e with
        | .closure _ #[c] => pure ((← getThe Flat.Body).clause c).pats.isEmpty
        | _ => pure false
      let e ← if block then mk (.call 0 e #[]) else pure e
      if block then
        let _ ← acceptPunct ";"
      else expectPunct ";"
      out := out ++ (← settle (.defer e))
    else
      let e ← parseBinary 0 false
      if ← acceptPunct "=" then
        let id := (← read).base + (← get) + 1
        let mut value ← parseBinary 0 false
        -- `x.0 = v` and `(*p).0 = v` assign through a borrow of the field.
        -- `a[i] = v` makes `a` the array with `v` at that place: `a =
        -- index_set(a, i, v)`, and so on outwards for `a[i][j] = v`.
        -- Where the array is a place, the element is written where it is:
        -- what was there is destroyed, and nothing is read out of the array.
        let mut e := e
        match ← elementBorrow true e with
        | some place => e ← mk (.deref place)
        | none =>
          for _ in [0:16] do
            let some (at_, inner, place) ← indexed? e | break
            -- Known by the identity of the `[`, moved clear of every token's.
            value ← mk (.call (at_ + 500000) (← preludeFn "index_set") #[← copy inner, place, value])
            e := inner
        -- (A field of an array's element, `a[i].f = v`, is written through
        -- a borrow of the element.)
        let target ← match ← fieldRoot e with
          | some (.through b, path) =>
            match ← elementBorrow true b with
            | some r => mk (.deref (← fieldBorrow id true (.through r) path))
            | none => mk (.deref (← fieldBorrow id true (.through b) path))
          | some (root, path) => mk (.deref (← fieldBorrow id true root path))
          | none => pure e
        out := out ++ (← settle (.assign target value))
        -- An assignment may end a block; its value is unit.
        if !(← acceptPunct ";") then break
      else
        out := out ++ (← settle (.expr e))
        if ← acceptPunct ";" then
          let t' ← peek
          if t' == .punct "}" || t' == .punct "," then
            out := out.push (← unit ())
        else break
  -- The functions written in this block are named, in it and in each
  -- other, by the names they have as functions of the module.
  if local_.isEmpty then return out
  modifyThe (Array Item) fun made =>
    made.mapIdx fun k item =>
      if k < madeBefore then item
      else match item with
        | .fn f ps annots ret b => .fn f ps annots ret (Flat.renameInBody local_.toList b)
        | other => other
  let mut stmts := out.toList
  for (name, own) in local_ do
    stmts ← build (Flat.renameStmts name own [] stmts)
  pure stmts.toArray


/-- A function, and what is written of its type parameters. -/
partial def parseFn : P (Item × List Bound) := do
  advance
  let name ← match ← peek with
    | .ident s => do
      advance
      pure s
    | .op s => do
      advance
      pure s
    | _ => failAt "expected a function name"
  let (params, bounds) ← parseGenericsWith
  if ← acceptPunct "(" then
    let mut pats : Array Pattern := #[]
    let mut annots : Array (Option TypeExpr) := #[]
    let mut params := params
    let mut bounds := bounds
    repeat
      if (← peek) == .punct ")" then break
      let pat ← parsePattern
      pats := pats.push pat
      if ← acceptPunct ":" then
        -- `x: impl Trait`: a type parameter of its own with the trait.
        if (← peek) == .ident "impl" then
          advance
          let p := s!"Impl{params.length}"
          params := params ++ [p]
          bounds := bounds ++ (← parseBoundsOf p)
          annots := annots.push (some (.name p []))
        else annots := annots.push (some (← parseType))
      -- What a function takes is written, as in Rust: its body is checked
      -- against it, and every use of it is checked against it alone.
      else failAt s!"parameter {pats.size} of `{name}` has no type: write it, `{name}(x: T)`"
      if !(← acceptPunct ",") then break
    expectPunct ")"
    -- `-> R`, `-> R / {E}`, or `/ {E}` alone for a function that gives `()`.
    -- (No result written is `()`.)
    let ret ← if (← acceptPunct "->") || (← peek) == .op "/" then some <$> parseResult else pure (some (.tuple []))
    let (lifetimes, more) ← parseWhere
    -- `where I::Item: Ord`: a type parameter for `I::Item`, which `I`'s one
    -- written trait is asked to leave (`I: Iterator<Item = ItemOfI>`).
    let mut more := more
    let projected := more.filter fun b => (b.subject.splitOn "::").length == 2
    for b in projected do
      if let [p, name] := b.subject.splitOn "::" then
        let fresh := s!"{name}Of{p}"
        let theirs := (bounds ++ more).filter (·.subject == p)
        match theirs with
        | [own] =>
          unless params.contains fresh do params := params ++ [fresh]
          bounds := bounds.map fun c =>
            if c.subject == p && c.trait == own.trait && !c.assoc.any (·.1 == name) then
              { c with assoc := c.assoc ++ [(name, .name fresh [])] } else c
          more := more.map fun c =>
            if c.subject == p && c.trait == own.trait && !c.assoc.any (·.1 == name) then
              { c with assoc := c.assoc ++ [(name, .name fresh [])] } else c
        | _ => failAt s!"`{b.subject}`: `{p}` is asked one trait, which leaves `{name}`, to say this of"
    more := more.map fun c =>
      match c.subject.splitOn "::" with
      | [p, name] => { c with subject := s!"{name}Of{p}" }
      | _ => c
    let consts := (bounds.filter (·.trait == knownTrait)).map (·.subject)
    let types := params.filter (!·.startsWith "'")
    -- (`#[intrinsic] fn int_add(a: Int, b: Int) -> Int;`: a machine
    -- operation, its type written here. It stands for itself: a call of it
    -- is the operation.)
    let body ← if (← read).intrinsic && (← acceptPunct ";") then
        bodyOf do
          let args ← pats.mapM fun
            | .var x => mk (.name none x)
            | _ => failAt "an intrinsic's parameters are names"
          pure #[← mkC pats.toList #[← mkS (.expr (← callOf 0 none name args))]]
      else do
        expectPunct "{"
        let body ← bodyOf do
          let body ← withReader (fun ctx => { ctx with consts := consts ++ ctx.consts, enclosing := (types, bounds ++ more) }) parseStmts
          pure #[← mkC pats.toList body]
        expectPunct "}"
        pure body
    -- `-> !`: a function that does not come back gives whatever is wanted
    -- of it, which only a body that does not come back can.
    let (allParams, ret) := match ret with
      | some .never => (params ++ [neverParam], some (TypeExpr.name neverParam []))
      | some (.performs .never effects) =>
        (params ++ [neverParam], some (TypeExpr.performs (.name neverParam []) effects))
      | other => (params, other)
    pure (Item.fn name (allParams ++ lifetimes) annots.toList ret body, bounds ++ more)
  else
    failAt s!"`{name}` is written as clauses, which say no types: write `fn {name}(x: T) -> R \{ match(x) \{ .. } }`"

end

end Glorious.Syntax.Parse
