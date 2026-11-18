module

public import Glorious.Syntax.Parser.Base

public section

namespace Glorious.Syntax.Parse

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
    | none => pure (.ctor (arrayPatName ps.size) none ps.toList)
  | .ident "let" =>
    -- `let name`: a new name, whatever constant or constructor has it.
    advance
    pure (.ctor letMark none [.var (← expectIdent)])
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
      match (← scalarLiteral true).bind literalPattern with
      | some p => pure p
      | none => failAt "expected a pattern"
    | _ => failAt "expected a pattern"
  | .typed _ _ | .char _ | .str _ =>
    match (← scalarLiteral false).bind literalPattern with
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
partial def parseArgs : P (List Expr) := do
  let out ← listUntil (atPunct ")") (parseBinary 0 false)
  expectPunct ")"
  pure out

/-- Binary operators by precedence climbing. With `noBlock`, a `{` after a call
is not taken as a trailing block. -/
partial def parseBinary (minPrec : Nat) (noBlock : Bool)
    (before : Option (Nat × Assoc) := none) : P Expr := do
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
      let rhs := if elseIf then Expr.closure blockId [.mk [] [.expr rhs]] else rhs
      let (qual, f) := splitPath (((← read).fix.function name false).splitOn "::")
      lhs := .call id (.name qual f) [lhs, rhs]
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
        lhs := .call id (.name none isMark) [lhs, .closure 0 [.mk [pat] []]]
      | _ => break
  pure lhs

partial def parseUnary (noBlock : Bool) : P Expr := do
  let t ← peek
  let fix := (← read).fix
  -- `-` straight before a number is part of the number.
  if t == .op "-" then
    match ← peek 1 with
    | .int n =>
      advance
      let v ← plainInt true n
      advance
      return .int v
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
      pure (.call id (.name qual f) [operand])
    | none =>
      if t == .op "-" then failAt "operator `-` has no prefix fixity"
      else if t == .op "&" then
        advance
        let uniq := (← peek) == .ident "mut"
        if uniq then advance
        if (← peek) == .op "*" then
          advance
          pure (.reborrow uniq (← parseUnary noBlock))
        else
          let id := (← read).base + (← get) + 1
          -- `&x`, `&x.0.1`, `&(*p).0`, or `&f().0` through what an
          -- expression gives.
          match ← parsePostfix true with
          -- (A name written with a capital is a constructor or a constant, a
          -- value and no variable: it is borrowed as any value is, below.)
          | .name none x =>
            if (x.front.isUpper) then
              pure (.call id (.name none (if uniq then borrowMutMark else borrowMark)) [.name none x])
            else pure (.ref uniq x)
          | e =>
            if let some at_ := elementBorrow uniq e then return at_
            match fieldRoot e with
            -- (A field of an array's element, `&a[i].f`: through a borrow of
            -- the element.)
            | some (.through b, path) =>
              match elementBorrow uniq b with
              | some r => pure (fieldBorrow id uniq (.through r) path)
              | none => pure (fieldBorrow id uniq (.through b) path)
            | some (root, path) => pure (fieldBorrow id uniq root path)
            -- A value with no name: it is given one where the statement
            -- starts, and that is borrowed.
            | none => pure (.call id (.name none (if uniq then borrowMutMark else borrowMark)) [e])
      else if t == .op "&*" then
        -- `&*e`, which the lexer reads as one symbol.
        advance
        pure (.reborrow false (← parseUnary noBlock))
      else if t == .op "*" then
        advance
        pure (.deref (← parseUnary noBlock))
      else
        -- `&**e` and `**e`, which the lexer reads as one symbol each: a
        -- borrow through, or a reading through, as many references.
        match t with
        | .op s =>
          let stars := (s.dropWhile (· == '&')).toString
          let amps := s.length - stars.length
          if amps ≤ 1 && stars.length ≥ 2 && stars.all (· == '*') then
            advance
            let inner ← parseUnary noBlock
            let derefs := (List.range (stars.length - amps)).foldl (fun e _ => Expr.deref e) inner
            pure (if amps == 1 then .reborrow false derefs else derefs)
          else parsePostfix noBlock
        | _ => parsePostfix noBlock
  | none => parsePostfix noBlock

partial def parsePostfix (noBlock : Bool) : P Expr := do
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
      let isName := match e with
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
        e := .call 0 (.name none instMark) [.call id e args, (TypeExpr.tuple tys).asExpr]
    | .punct "(" =>
      let id := (← read).base + (← get) + 1
      advance
      let mut args ← parseArgs
      while !noBlock && (← peek) == .punct "{" do
        args := args ++ [← parseBraces]
      e := .call id e args
    | .punct "{" =>
      -- `Point { x: 1, y: 2 }` builds a value of a type declared with names.
      let records := (← read).records
      let isRecord := match e with
        | .name _ x => records.contains x
        | _ => false
      if isRecord then
        let id := (← read).base + (← get) + 1
        advance
        let mut given : Array Expr := #[.name none recordMark]
        repeat
          if (← peek) == .punct "}" then break
          let field ← expectIdent
          let value ← if ← acceptPunct ":" then parseBinary 0 false else pure (.name none field)
          given := given.push (.call 0 (.name none (fieldMark field)) [value])
          if !(← acceptPunct ",") then break
        expectPunct "}"
        e := .call id e given.toList
        continue
      -- `f { body }` is `f({ body })`.
      if noBlock then break
      let id := (← read).base + (← get) + 1
      let mut args : List Expr := []
      while (← peek) == .punct "{" do
        args := args ++ [← parseBraces]
      e := .call id e args
    | .punct "[" =>
      -- `a[i]`: the element at a place.
      let id := (← read).base + (← get) + 1
      advance
      let place ← parseBinary 0 false
      expectPunct "]"
      e := .call id (preludeFn "index") [e, place]
    | .punct "." =>
      match ← peek 1 with
      | .int n =>
        -- A field of what a name stands for, or of what a call gives, is
        -- known by an identity, so that the checker can say it is read
        -- through a reference.
        let id := (← read).base + (← get) + 1
        advance
        advance
        e := match e with
          | .name none _ | .call .. => .fieldOf id e (toString n)
          | _ => .proj e n
      | .ident field =>
        let id := (← read).base + (← get) + 1
        advance
        advance
        e := .fieldOf id e field
      | _ => failAt "expected a field after `.`"
    | _ => break
  pure e

partial def parsePrimary (noBlock : Bool) : P Expr := do
  -- (`println!(..)`: a Rust macro; there are none.)
  if let .ident m ← peek then
    if (← peek 1) == .op "!" && ((← peek 2) == .punct "(" || (← peek 2) == .punct "[") then
      failAt s!"`{m}!` is not read: there are no macros; call a function, `say(value)`, `assert(condition)`, `abort(message)`"
  -- A parameter that stands for a number, written as a value: the number.
  if let .ident x ← peek then
    if (← read).consts.contains x && (← peek 1) != .punct "::" then
      let id := (← read).base + (← get) + 1
      advance
      return .call 0 (.name none instMark)
        [.call id (.name (some knownTrait) "VALUE") [], (TypeExpr.tuple [.name x []]).asExpr]
  match ← peek with
  | .int n =>
    let v ← plainInt false n
    advance
    pure (.int v)
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
    let numbered := fun (at_ offset : Nat) => if at_ < 100000 then base + at_ + offset else 0
    let opened ← get
    let empty := numbered opened 600000
    advance
    if ← acceptPunct "]" then
      if (← read).fixed then
        return .call 0 (.name none instMark)
          [.call (numbered opened 800000) (preludeFn "array_literal") [arrayValue [] empty],
           (TypeExpr.tuple [numberType 0]).asExpr]
      return arrayValue [] empty
    let mut starts : Array Nat := #[numbered (← get) 700000]
    let first ← parseBinary 0 false
    if ← acceptPunct ";" then
      let count ← parseBinary 0 false
      expectPunct "]"
      return .call 0 (preludeFn "array_repeat") [first, count]
    let mut elements : Array Expr := #[first]
    while ← acceptPunct "," do
      if (← peek) == .punct "]" then break
      starts := starts.push (numbered (← get) 700000)
      elements := elements.push (← parseBinary 0 false)
    expectPunct "]"
    let value := arrayValue elements.toList empty starts.toList
    -- Where the program has arrays of a fixed length, the literal is an
    -- array or one of exactly so many: whichever is wanted of it.
    if (← read).fixed then
      let id := numbered opened 800000
      return .call 0 (.name none instMark)
        [.call id (preludeFn "array_literal") [value], (TypeExpr.tuple [numberType elements.size]).asExpr]
    pure value
  | .ident "tail" =>
    advance
    match ← parsePostfix noBlock with
    | .call id f args => pure (.tailCall id f args)
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
    let mut args : List Expr := []
    let mut id := nameAt
    if (← peek) == .punct "(" then
      id := (← read).base + (← get) + 1
      advance
      args ← parseArgs
      while !noBlock && (← peek) == .punct "{" do
        args := args ++ [← parseBraces]
    pure (.call 0 (.name none instMark)
      [.call id (.name (some trait) name) args, (TypeExpr.tuple (self :: targs)).asExpr])
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
        return .call id (.closure 0 [.mk (names.toList.map Pattern.var) [.expr block]])
          (names.toList.map (Expr.name none))
      set saved
    -- `move place`: the value, handed on; the place is not used after.
    let id := (← read).base + (← get) + 1
    let operand ← parseUnary noBlock
    pure (.call id (.name none moveMark) [operand])
  | .ident "handle" =>
    advance
    let subject ← parseBinary 0 true
    unless (← peek) == .punct "{" do
      failAt "`handle` is a word of the language, `handle computation { arms }`: nothing else can be named `handle`"
    expectPunct "{"
    let arms ← parseClauses
    expectPunct "}"
    pure (.handle subject arms)
  | .ident "const" =>
    -- `const { .. }`: a block worked out at compile time, as a constant is,
    -- by a function of the module (it uses nothing of where it is written).
    if (← peek 1) != .punct "{" then failAt "expected an expression"
    let id := (← read).base + (← get)
    advance
    let (types, bounds) := (← read).enclosing
    match ← parseBraces with
    | .closure _ clauses =>
      let fn := constFnName s!"const%{id}"
      -- (Generic in the type parameters of the function it is in, with what
      -- is written of them: each copy of that function at known types has
      -- one at those types.)
      let wanted := bounds.filter (types.contains ·.subject)
      modifyThe (Array Item) fun made =>
        (made.push (.fn fn types [] none clauses)) ++ (if wanted.isEmpty then #[] else #[.bounds fn wanted])
      -- (Known by the place of `const`: what it needs is given there.)
      let call := Expr.call id (.name none fn) []
      if types.isEmpty then pure call
      else pure (.call 0 (.name none instMark) [call, (TypeExpr.tuple (types.map (TypeExpr.name · []))).asExpr])
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
    let written := Expr.closure 0 [.mk pats.toList body]
    if annots.all Option.isNone && ret.isNone then pure written
    else
      -- With types written it is the callable, of the type they make.
      let ty := TypeExpr.fn (annots.toList.map (·.getD .hole)) (ret.getD .hole)
      pure (.call 0 (.name none ascribeMark) [written, ty.asExpr])
  | .ident x =>
    if x.startsWith "'" then failAt "a lifetime is not a value"
    if x == "unsafe" && (← peek 1) == .punct "{" then
      -- `unsafe { .. }`: a block run where it is written, in which what is
      -- unsafe may be named.
      let call := (← read).base + (← get) + 1
      advance
      advance
      let id := (← read).base + (← get)
      let body ← parseStmts
      expectPunct "}"
      return .call call (.closure id [.mk [] (.expr (.name none unsafeMark) :: body)]) []
    advance
    let (qual, name) := splitPath (← parsePathRest x)
    -- `Type::NAME`, in capitals and not called: perhaps a value a trait
    -- leaves to implementations. What it is, is found with the names.
    let capitals := name.any Char.isUpper && name.all fun c => c.isUpper || c.isDigit || c == '_'
    if qual.isSome && capitals && (← peek) != .punct "(" && (← peek) != .punct "{" then
      return .call ((← read).base + (← get)) (.name none pathMark) [.name qual name]
    pure (.name qual name)
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
      return .call 0 (.name none ascribeMark) [.labelScope l body, ty.asExpr]
    if !noBlock && (← peek) == .punct "{" then
      advance
      let body ← parseStmts
      expectPunct "}"
      pure (.labelScope l body)
    else pure (.label l)
  | .punct "(" =>
    advance
    let args ← parseArgs
    match args with
    | [e] =>
      if ← closedAfterComma then pure (.tuple [e])
      -- `(s.f)(..)`: the field, a callable, called; not the function of the
      -- name of what `s` is. (A block of its own, which a dot call is not.)
      else if (← peek) == .punct "(" then
        match e with
        | .fieldOf .. => pure (.labelScope "%paren" [.expr e])
        | _ => pure e
      else pure e
    | _ => pure (.tuple args)
  | .punct "{" => parseBraces
  | .op "|" => failAt "a callable is written `{ x => body }`, or `fn(x) { body }`; `|x| body` is not read"
  | .op "||" => failAt "a callable is written `{ => body }`, or `fn() { body }`; `|| body` is not read"
  | _ => failAt "expected an expression"

/-- A callable literal in braces. -/
partial def parseBraces : P Expr := do
  expectPunct "{"
  let ctx ← read
  let id := ctx.base + (← get)
  if scanClauseForm ctx.toks (← get) 0 then
    let clauses ← parseClauses
    expectPunct "}"
    pure (.closure id clauses)
  else
    let body ← parseStmts
    expectPunct "}"
    pure (.closure id [.mk [] body])

/-- Clauses separated by commas, up to but not including the closing `}`. -/
partial def parseClauses : P (List Clause) := do
  pure (restClauses (← listUntil (atPunct "}") parseClause))

/-- One clause: a single pattern for the argument, or none for a callable taking
no arguments. Callables of several arguments are written `fn(x, y) { body }`. -/
partial def parseClause : P Clause := do
  let pats ←
    if (← peek) == .punct "=>" then pure []
    else do
      pure [← parsePattern]
  -- (Rust's, which version 1 does not have.)
  if (← peek) == .ident "if" then
    failAt "a pattern has no guard: test in the clause, `x => if(c) { .. } else { .. }`, or match again"
  if ← isOp "|" then
    failAt "a pattern has no alternatives: write a clause for each, or `_ =>` for the rest"
  if (← peek) == .punct ".." || (← peek) == .punct "." || (← isOp "..=") || (← isOp "..") then
    failAt "a pattern has no ranges: test in the clause, `x => if(x <= 9) { .. } else { .. }`"
  expectPunct "=>"
  let body ← parseStmts
  pure (.mk pats body)

/-- Statements up to a `}` or a `,`. A trailing `;` makes the value unit. -/
partial def parseStmts : P (List Stmt) := do
  let mut out : Array Stmt := #[]
  -- The functions written in this block, each with the name it has as a
  -- function of the module.
  let mut local_ : Array (String × String) := #[]
  let madeBefore := (← getThe (Array Item)).size
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
        | .fn _ ps annots ret clauses =>
          modifyThe (Array Item) fun made =>
            (made.push (.fn own ps annots ret clauses)) ++ (if bounds.isEmpty then #[] else #[.bounds own bounds])
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
    let mark := fun (s : Stmt) => Stmt.located here.line here.col s
    -- A borrow of a field of what an expression points to: the reference is
    -- given a name first.
    let settle := fun (s : Stmt) => (match hoistStmt s with
      | some (lets, s) => pure (lets.map mark ++ [mark s])
      | none => throw s!"{here.line}:{here.col}: a field is borrowed of what an expression points to, after something else in the statement is computed: give the reference a `let` of its own first" : P (List Stmt))
    if t == .ident "let" then
      advance
      if (← peek) == .ident "mut" then
        advance
        let name ← expectIdent
        let typed ← if ← acceptPunct ":" then some <$> parseType else pure none
        expectPunct "="
        let value ← parseBinary 0 false
        let value := match typed with
          | some ty => Expr.call 0 (.name none ascribeMark) [value, ty.asExpr]
          | none => value
        expectPunct ";"
        out := out ++ (← settle (.letMut name value)).toArray
      else
        let pat ← parsePattern
        -- `let x: Type = value`: the value is made that type.
        let typed ← if ← acceptPunct ":" then some <$> parseType else pure none
        expectPunct "="
        let value ← parseBinary 0 false
        let value := match typed with
          | some ty => Expr.call 0 (.name none ascribeMark) [value, ty.asExpr]
          | none => value
        expectPunct ";"
        match pat with
        | .wild =>
          -- `let _ = value;` is the value computed and let go, as `value;`
          -- is: what it is has its `drop` run, where a name would keep it.
          out := out ++ (← settle (.expr value)).toArray
          let t' ← peek
          if t' == .punct "}" || t' == .punct "," then
            out := out.push (.expr (.tuple []))
        | _ =>
          -- `let [a, b, c] = xs`, where the program has arrays of a fixed
          -- length: `xs` is one of exactly three, taken apart as a tuple.
          let here ← get
          let ctx ← read
          let id := if here < 100000 then ctx.base + here + 900000 else 0
          let (pat, value) := match pat, ctx.fixed with
            | .ctor name none args, true =>
              if (arrayPatLen name).isSome then
                (Pattern.tuple args, Expr.call id (preludeFn "elements") [value])
              else (pat, value)
            | _, _ => (pat, value)
          out := out ++ (← settle (.let_ pat value)).toArray
    else if t == .ident "defer" then
      advance
      let e ← parseBinary 0 false
      -- `defer { .. }`: the block is what is run on the way out, not a
      -- callable to be made then and let go.
      let (e, block) := match e with
        | .closure _ [.mk [] _] => (Expr.call 0 e [], true)
        | e => (e, false)
      if block then
        let _ ← acceptPunct ";"
      else expectPunct ";"
      out := out ++ (← settle (.defer e)).toArray
    else
      let e ← parseBinary 0 false
      if ← acceptPunct "=" then
        let id := (← read).base + (← get) + 1
        let value ← parseBinary 0 false
        -- `x.0 = v` and `(*p).0 = v` assign through a borrow of the field.
        -- `a[i] = v` makes `a` the array with `v` at that place: `a =
        -- index_set(a, i, v)`, and so on outwards for `a[i][j] = v`.
        let rec lower (fuel : Nat) (target value : Expr) : Expr × Expr :=
          match fuel, indexed? target with
          | fuel + 1, some (at_, inner, place) =>
            -- Known by the identity of the `[`, moved clear of every token's.
            lower fuel inner (.call (at_ + 500000) (preludeFn "index_set") [inner, place, value])
          | _, _ => (target, value)
        -- Where the array is a place, the element is written where it is:
        -- what was there is destroyed, and nothing is read out of the array.
        let (e, value) := match elementBorrow true e with
          | some place => (Expr.deref place, value)
          | none => lower 16 e value
        -- (A field of an array's element, `a[i].f = v`, is written through
        -- a borrow of the element.)
        let target := match fieldRoot e with
          | some (.through b, path) =>
            match elementBorrow true b with
            | some r => Expr.deref (fieldBorrow id true (.through r) path)
            | none => Expr.deref (fieldBorrow id true (.through b) path)
          | some (root, path) => Expr.deref (fieldBorrow id true root path)
          | none => e
        out := out ++ (← settle (.assign target value)).toArray
        -- An assignment may end a block; its value is unit.
        if !(← acceptPunct ";") then break
      else
        out := out ++ (← settle (.expr e)).toArray
        if ← acceptPunct ";" then
          let t' ← peek
          if t' == .punct "}" || t' == .punct "," then
            out := out.push (.expr (.tuple []))
        else break
  -- The functions written in this block are named, in it and in each
  -- other, by the names they have as functions of the module.
  if local_.isEmpty then return out.toList
  let named := fun (stmts : List Stmt) =>
    local_.foldl (fun stmts (name, own) => renameStmts name own [] stmts) stmts
  modifyThe (Array Item) fun made =>
    made.mapIdx fun k item =>
      if k < madeBefore then item
      else match item with
        | .fn f ps annots ret clauses =>
          .fn f ps annots ret (clauses.map fun
            | .mk pats body => .mk pats (local_.foldl (fun body (name, own) =>
                renameStmts name own (pats.flatMap patternNames) body) body))
        | other => other
  pure (named out.toList)


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
      pats := pats.push (← parsePattern)
      if ← acceptPunct ":" then
        -- `x: impl Trait`: a type parameter of its own with the trait.
        if (← peek) == .ident "impl" then
          advance
          let p := s!"Impl{params.length}"
          params := params ++ [p]
          bounds := bounds ++ (← parseBoundsOf p)
          annots := annots.push (some (.name p []))
        else annots := annots.push (some (← parseType))
      else annots := annots.push none
      if !(← acceptPunct ",") then break
    expectPunct ")"
    -- `-> R`, `-> R / {E}`, or `/ {E}` alone for a function that gives `()`.
    let ret ← if (← acceptPunct "->") || (← peek) == .op "/" then some <$> parseResult else pure none
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
    expectPunct "{"
    let consts := (bounds.filter (·.trait == knownTrait)).map (·.subject)
    let types := params.filter (!·.startsWith "'")
    let body ← withReader (fun ctx => { ctx with consts := consts ++ ctx.consts, enclosing := (types, bounds ++ more) }) parseStmts
    expectPunct "}"
    -- `-> !`: a function that does not come back gives whatever is wanted
    -- of it, which only a body that does not come back can.
    let (allParams, ret) := match ret with
      | some .never => (params ++ [neverParam], some (TypeExpr.name neverParam []))
      | some (.performs .never effects) =>
        (params ++ [neverParam], some (TypeExpr.performs (.name neverParam []) effects))
      | other => (params, other)
    pure (.fn name (allParams ++ lifetimes) annots.toList ret [.mk pats.toList body], bounds ++ more)
  else
    expectPunct "{"
    let clauses ← parseClauses
    expectPunct "}"
    pure (.fn name params [] none clauses, bounds)

end

end Glorious.Syntax.Parse
