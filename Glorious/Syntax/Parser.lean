import Glorious.Syntax.Ast
import Glorious.Syntax.Lexer

/-!
# Parser

Recursive descent with precedence climbing. Operators and their fixities are
declared by the program, so they are collected from the token stream first.

Braces in expression position always denote a callable: `{ x => body }` and
`{ P => a, Q => b }` take one argument, a plain block `{ body }` takes none
unless one is expected of it, which the checker decides. `coerce name` declares
the function `name` a coercion. A
callable of several arguments is written `fn(x, y) { body }`. A block written
directly after a call is passed as its last argument, and `f { body }` calls `f`
with the block.
-/

namespace Glorious.Syntax

structure PCtx where
  toks : Array Token
  fix : Fixities
  /-- Added to the identity of each callable literal, so that the literals of
  texts parsed separately stay distinct. -/
  base : Nat

abbrev P := ReaderT PCtx (StateT Nat (Except String))

instance {α : Type} : Inhabited (P α) := ⟨throw "parser: unreachable"⟩

private def peekTok (k : Nat := 0) : P Token := do
  let ctx ← read
  let i ← get
  pure (ctx.toks[i + k]?.getD ⟨.eof, 0, 0⟩)

private def peek (k : Nat := 0) : P Tok := do
  pure (← peekTok k).tok

private def advance : P Unit := modify (· + 1)

private def failAt {α : Type} (msg : String) : P α := do
  let t ← peekTok
  throw s!"{t.line}:{t.col}: {msg}, found {t.tok.describe}"

private def expectPunct (s : String) : P Unit := do
  if (← peek) == .punct s then advance else failAt s!"expected `{s}`"

private def acceptPunct (s : String) : P Bool := do
  if (← peek) == .punct s then
    advance
    pure true
  else pure false

private def expectIdent : P String := do
  match ← peek with
  | .ident s =>
    advance
    pure s
  | _ => failAt "expected a name"

/-- Does the block starting at token `i` have clauses (`... => ...`) rather than statements? -/
private partial def scanClauseForm (toks : Array Token) (i depth : Nat) : Bool :=
  match toks[i]? with
  | none => false
  | some t =>
    match t.tok with
    | .eof => false
    | .punct "(" => scanClauseForm toks (i + 1) (depth + 1)
    | .punct "{" => scanClauseForm toks (i + 1) (depth + 1)
    | .punct ")" => if depth == 0 then false else scanClauseForm toks (i + 1) (depth - 1)
    | .punct "}" => if depth == 0 then false else scanClauseForm toks (i + 1) (depth - 1)
    | .punct "=>" => if depth == 0 then true else scanClauseForm toks (i + 1) depth
    | .punct ";" => if depth == 0 then false else scanClauseForm toks (i + 1) depth
    | _ => scanClauseForm toks (i + 1) depth

private def infixOf (t : Tok) : P (Option (String × Nat × Assoc)) := do
  let fix := (← read).fix
  let name? := match t with
    | .op s => some s
    | .ident s => some s
    | _ => none
  match name? with
  | some s => pure ((fix.infixes.lookup s).map fun (prec, assoc) => (s, prec, assoc))
  | none => pure none

mutual

private partial def parsePattern : P Pattern := do
  match ← peek with
  | .ident "_" =>
    advance
    pure .wild
  | .ident x =>
    advance
    let (qual, name) ← if ← acceptPunct "::" then do
        let y ← expectIdent
        pure (some x, y)
      else pure (none, x)
    if ← acceptPunct "(" then
      let args ← parsePatternList
      pure (.ctor name qual args)
    else if qual.isSome then pure (.ctor name qual [])
    else pure (.var name)
  | .int n =>
    advance
    pure (.int n)
  | .op "-" =>
    match ← peek 1 with
    | .int n =>
      advance
      advance
      pure (.int (-(n : Int)))
    | _ => failAt "expected a pattern"
  | .punct "(" =>
    advance
    let args ← parsePatternList
    match args with
    | [p] => pure p
    | _ => pure (.tuple args)
  | _ => failAt "expected a pattern"

/-- Patterns separated by commas up to and including the closing `)`. -/
private partial def parsePatternList : P (List Pattern) := do
  let mut out : Array Pattern := #[]
  repeat
    if (← peek) == .punct ")" then break
    out := out.push (← parsePattern)
    if !(← acceptPunct ",") then break
  expectPunct ")"
  pure out.toList

/-- Expressions separated by commas up to and including the closing `)`. -/
private partial def parseArgs : P (List Expr) := do
  let mut out : Array Expr := #[]
  repeat
    if (← peek) == .punct ")" then break
    out := out.push (← parseBinary 0 false)
    if !(← acceptPunct ",") then break
  expectPunct ")"
  pure out.toList

/-- Binary operators by precedence climbing. With `noBlock`, a `{` after a call
is not taken as a trailing block. -/
private partial def parseBinary (minPrec : Nat) (noBlock : Bool) : P Expr := do
  let mut lhs ← parseUnary noBlock
  repeat
    let t ← peek
    match ← infixOf t with
    | some (name, prec, assoc) =>
      if prec < minPrec then break
      -- Each call is known by the token that makes it one.
      let id := (← read).base + (← get) + 1
      advance
      let next := match assoc with
        | .right => prec
        | _ => prec + 1
      let rhs ← parseBinary next noBlock
      lhs := .call id (.name none name) [lhs, rhs]
    | none =>
      match t with
      | .op s => failAt s!"operator `{s}` has no infix fixity"
      | _ => break
  pure lhs

private partial def parseUnary (noBlock : Bool) : P Expr := do
  let t ← peek
  let fix := (← read).fix
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
      pure (.call id (.name none s) [operand])
    | none =>
      if t == .op "-" then
        match ← peek 1 with
        | .int n =>
          advance
          advance
          pure (.int (-(n : Int)))
        | _ => failAt "operator `-` has no prefix fixity"
      else if t == .op "&" then
        advance
        let uniq := (← peek) == .ident "mut"
        if uniq then advance
        if (← peek) == .op "*" then
          advance
          pure (.reborrow uniq (← parseUnary noBlock))
        else
          let id := (← read).base + (← get) + 1
          let x ← expectIdent
          -- `&x.0.1` borrows a field of what `x` holds.
          let mut path : Array Nat := #[]
          repeat
            match ← peek, ← peek 1 with
            | .punct ".", .int n =>
              advance
              advance
              path := path.push n
            | _, _ => break
          if path.isEmpty then pure (.ref uniq x) else pure (.refField id uniq x path.toList)
      else if t == .op "&*" then
        -- `&*e`, which the lexer reads as one symbol.
        advance
        pure (.reborrow false (← parseUnary noBlock))
      else if t == .op "*" then
        advance
        pure (.deref (← parseUnary noBlock))
      else parsePostfix noBlock
  | none => parsePostfix noBlock

private partial def parsePostfix (noBlock : Bool) : P Expr := do
  let mut e ← parsePrimary noBlock
  repeat
    match ← peek with
    | .punct "(" =>
      let id := (← read).base + (← get) + 1
      advance
      let mut args ← parseArgs
      while !noBlock && (← peek) == .punct "{" do
        args := args ++ [← parseBraces]
      e := .call id e args
    | .punct "{" =>
      -- `f { body }` is `f({ body })`.
      if noBlock then break
      let id := (← read).base + (← get) + 1
      let mut args : List Expr := []
      while (← peek) == .punct "{" do
        args := args ++ [← parseBraces]
      e := .call id e args
    | .punct "." =>
      match ← peek 1 with
      | .int n =>
        advance
        advance
        e := .proj e n
      | _ => failAt "expected a field index after `.`"
    | _ => break
  pure e

private partial def parsePrimary (noBlock : Bool) : P Expr := do
  match ← peek with
  | .int n =>
    advance
    pure (.int n)
  | .ident "tail" =>
    advance
    match ← parsePostfix noBlock with
    | .call id f args => pure (.tailCall id f args)
    | _ => failAt "`tail` must be followed by a call"
  | .ident "handle" =>
    advance
    let subject ← parseBinary 0 true
    expectPunct "{"
    let arms ← parseClauses
    expectPunct "}"
    pure (.handle subject arms)
  | .ident "fn" =>
    advance
    expectPunct "("
    let pats ← parsePatternList
    expectPunct "{"
    let body ← parseStmts
    expectPunct "}"
    pure (.closure 0 [.mk pats body])
  | .ident x =>
    if x.startsWith "'" then failAt "a lifetime is not a value"
    advance
    if ← acceptPunct "::" then
      let y ← expectIdent
      pure (.name (some x) y)
    else pure (.name none x)
  | .punct "@" =>
    advance
    let l ← expectIdent
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
    | [e] => pure e
    | _ => pure (.tuple args)
  | .punct "{" => parseBraces
  | _ => failAt "expected an expression"

/-- A callable literal in braces. -/
private partial def parseBraces : P Expr := do
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
private partial def parseClauses : P (List Clause) := do
  let mut out : Array Clause := #[]
  repeat
    if (← peek) == .punct "}" then break
    out := out.push (← parseClause)
    if !(← acceptPunct ",") then break
  pure out.toList

/-- One clause: a single pattern for the argument, or none for a callable taking
no arguments. Callables of several arguments are written `fn(x, y) { body }`. -/
private partial def parseClause : P Clause := do
  let pats ←
    if (← peek) == .punct "=>" then pure []
    else do
      pure [← parsePattern]
  expectPunct "=>"
  let body ← parseStmts
  pure (.mk pats body)

/-- Statements up to a `}` or a `,`. A trailing `;` makes the value unit. -/
private partial def parseStmts : P (List Stmt) := do
  let mut out : Array Stmt := #[]
  repeat
    let t ← peek
    if t == .punct "}" || t == .punct "," || t == .eof then break
    let here ← peekTok
    let mark := fun (s : Stmt) => Stmt.located here.line here.col s
    if t == .ident "let" then
      advance
      if (← peek) == .ident "mut" then
        advance
        let name ← expectIdent
        expectPunct "="
        let value ← parseBinary 0 false
        expectPunct ";"
        out := out.push (mark (.letMut name value))
      else
        let pat ← parsePattern
        expectPunct "="
        let value ← parseBinary 0 false
        expectPunct ";"
        out := out.push (mark (.let_ pat value))
    else if t == .ident "defer" then
      advance
      let e ← parseBinary 0 false
      expectPunct ";"
      out := out.push (mark (.defer e))
    else
      let e ← parseBinary 0 false
      if ← acceptPunct "=" then
        let value ← parseBinary 0 false
        out := out.push (mark (.assign e value))
        -- An assignment may end a block; its value is unit.
        if !(← acceptPunct ";") then break
      else
        out := out.push (mark (.expr e))
        if ← acceptPunct ";" then
          let t' ← peek
          if t' == .punct "}" || t' == .punct "," then
            out := out.push (.expr (.tuple []))
        else break
  pure out.toList

end

private def isOp (s : String) : P Bool := do
  pure ((← peek) == .op s)

private def expectOp (s : String) : P Unit := do
  if (← peek) == .op s then advance else failAt s!"expected `{s}`"

/-- Generic parameters `<'a, 'b: 'a, T>`, if present: type parameters and
lifetimes, a lifetime perhaps with one it lasts at least as long as. -/
private partial def parseGenerics : P (List String) := do
  if !(← isOp "<") then return []
  advance
  let mut out : Array String := #[]
  repeat
    if ← isOp ">" then break
    let x ← expectIdent
    out := out.push x
    if x.startsWith "'" && (← peek) == .punct ":" then
      advance
      let y ← expectIdent
      unless y.startsWith "'" do failAt "expected a lifetime: `'b: 'a`"
      out := out.push s!"{x}: {y}"
    if !(← acceptPunct ",") then break
  expectOp ">"
  pure out.toList

/-- `where 'b: 'a, ...` after a function's result, if present. -/
private partial def parseLifetimeBounds : P (List String) := do
  if (← peek) != .ident "where" then return []
  advance
  let mut out : Array String := #[]
  repeat
    let x ← expectIdent
    expectPunct ":"
    let y ← expectIdent
    unless x.startsWith "'" && y.startsWith "'" do
      failAt "only a bound between lifetimes can be written here: `where 'b: 'a`"
    out := out.push s!"{x}: {y}"
    if !(← acceptPunct ",") then break
  pure out.toList

mutual

private partial def parseType : P TypeExpr := do
  match ← peek with
  | .op "!" =>
    advance
    pure .never
  | .op "&" =>
    advance
    let life ← match ← peek with
      | .ident x =>
        if x.startsWith "'" then
          advance
          pure (some x)
        else pure none
      | _ => pure none
    let uniq := (← peek) == .ident "mut"
    if uniq then advance
    pure (.ref uniq (← parseType) life)
  | .ident "_" =>
    advance
    pure .hole
  | .ident "fn" =>
    advance
    expectPunct "("
    let params ← parseTypeList ")"
    let ret ← if ← acceptPunct "->" then parseResult else pure (.tuple [])
    pure (.fn params ret)
  | .ident x =>
    advance
    if ← isOp "<" then
      advance
      let mut args : Array TypeExpr := #[]
      repeat
        if ← isOp ">" then break
        args := args.push (← parseType)
        if !(← acceptPunct ",") then break
      expectOp ">"
      pure (.name x args.toList)
    else pure (.name x [])
  | .punct "(" =>
    advance
    let args ← parseTypeList ")"
    match args with
    | [t] => pure t
    | _ => pure (.tuple args)
  | _ => failAt "expected a type"

/-- What follows `->` in a callable: its result, which may be left out when
it is unit, and then `/ {Effect, ...}` if what it performs is to be said. -/
private partial def parseResult : P TypeExpr := do
  let startsType := match ← peek with
    | .ident _ => true
    | .punct "(" => true
    | .op "!" => true
    | .op "&" => true
    | _ => false
  let ret ← if startsType then parseType else pure (.tuple [])
  if (← peek) == .op "/" then
    advance
    expectPunct "{"
    let mut effects : Array (String × List TypeExpr) := #[]
    repeat
      if (← peek) == .punct "}" then break
      let name ← expectIdent
      let mut args : Array TypeExpr := #[]
      if (← peek) == .op "<" then
        advance
        repeat
          if (← peek) == .op ">" then break
          args := args.push (← parseType)
          if !(← acceptPunct ",") then break
        match ← peek with
        | .op ">" => advance
        | _ => failAt "expected `>`"
      effects := effects.push (name, args.toList)
      if !(← acceptPunct ",") then break
    expectPunct "}"
    pure (.performs ret effects.toList)
  else pure ret

/-- Types separated by commas up to and including the closing punctuation. An
item may be written `name: Type`. -/
private partial def parseTypeList (close : String) : P (List TypeExpr) := do
  let mut out : Array TypeExpr := #[]
  repeat
    if (← peek) == .punct close then break
    match ← peek, ← peek 1 with
    | .ident _, .punct ":" =>
      advance
      advance
    | _, _ => pure ()
    out := out.push (← parseType)
    if !(← acceptPunct ",") then break
  expectPunct close
  pure out.toList

end

/-- The fields of a constructor, struct or operation, if any are written. -/
private def parseFields : P (List TypeExpr) := do
  if ← acceptPunct "(" then parseTypeList ")" else pure []

private def fixityKinds : List String := ["infixl", "infixr", "infix", "prefix"]

/-- `[lower, upper]`: how often something is to be used. `infinity` is no upper
bound. -/
private def parseQuantity : P (Nat × Option Nat) := do
  expectPunct "["
  let lower ← match ← peek with
    | .int n => do
      advance
      pure n
    | _ => failAt "expected the fewest uses, a number"
  expectPunct ","
  let upper ← match ← peek with
    | .int n => do
      advance
      pure (some n)
    | .ident "infinity" => do
      advance
      pure none
    | _ => failAt "expected the most uses, a number or `infinity`"
  expectPunct "]"
  if let some n := upper then
    if n < lower then failAt "the most uses cannot be fewer than the fewest"
  pure (lower, upper)

private partial def parseItem : P Item := do
  match ← peek with
  | .ident "enum" =>
    advance
    let name ← expectIdent
    let params ← parseGenerics
    expectPunct "{"
    let mut ctors : Array (String × List TypeExpr) := #[]
    repeat
      if (← peek) == .punct "}" then break
      let c ← expectIdent
      ctors := ctors.push (c, ← parseFields)
      if !(← acceptPunct ",") then break
    expectPunct "}"
    pure (.enum name params ctors.toList)
  | .ident "struct" =>
    advance
    let name ← expectIdent
    let params ← parseGenerics
    let fields ← parseFields
    let _ ← acceptPunct ";"
    pure (.struct name params fields)
  | .ident "effect" =>
    advance
    let name ← expectIdent
    let params ← parseGenerics
    expectPunct "{"
    let mut ops : Array OpDecl := #[]
    repeat
      if (← peek) == .punct "}" then break
      let quantity ← if (← peek) == .punct "[" then some <$> parseQuantity else pure none
      let op ← expectIdent
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
      ops := ops.push ⟨op, payload, result, terminal, quantity⟩
      if !(← acceptPunct ",") then
        if !(← acceptPunct ";") then break
    expectPunct "}"
    pure (.effect name params ops.toList)
  | .ident "fn" =>
    advance
    let name ← match ← peek with
      | .ident s => do
        advance
        pure s
      | .op s => do
        advance
        pure s
      | _ => failAt "expected a function name"
    let params ← parseGenerics
    if ← acceptPunct "(" then
      let mut pats : Array Pattern := #[]
      let mut annots : Array (Option TypeExpr) := #[]
      repeat
        if (← peek) == .punct ")" then break
        pats := pats.push (← parsePattern)
        annots := annots.push (← if ← acceptPunct ":" then some <$> parseType else pure none)
        if !(← acceptPunct ",") then break
      expectPunct ")"
      let ret ← if ← acceptPunct "->" then some <$> parseResult else pure none
      let params := params ++ (← parseLifetimeBounds)
      expectPunct "{"
      let body ← parseStmts
      expectPunct "}"
      pure (.fn name params annots.toList ret [.mk pats.toList body])
    else
      expectPunct "{"
      let clauses ← parseClauses
      expectPunct "}"
      pure (.fn name params [] none clauses)
  | .ident "let" =>
    advance
    let name ← expectIdent
    expectPunct "="
    let value ← parseBinary 0 false
    expectPunct ";"
    pure (.alias name value)
  | .ident "trait" =>
    advance
    let name ← expectIdent
    expectPunct "{"
    let mut methods : Array (String × List TypeExpr × Option TypeExpr) := #[]
    repeat
      if (← peek) == .punct "}" then break
      match ← peek with
      | .ident "fn" => advance
      | _ => failAt "expected `fn`: a trait lists the functions a type must have"
      let m ← expectIdent
      expectPunct "("
      let params ← parseTypeList ")"
      let ret ← if ← acceptPunct "->" then some <$> parseType else pure none
      methods := methods.push (m, params, ret)
      let _ ← acceptPunct ";"
    expectPunct "}"
    pure (.trait name methods.toList)
  | .ident "impl" =>
    advance
    let params ← parseGenerics
    let tr ← expectIdent
    if tr == "Use" && (← isOp "<") then
      advance
      let (lower, upper) ← parseQuantity
      if ← isOp ">" then advance else failAt "expected `>`"
      match ← peek with
      | .ident "for" => advance
      | _ => failAt "expected `for`: `impl Use<[1, 1]> for Type {}`"
      let head ← expectIdent
      let _ ← parseGenerics
      expectPunct "{"
      expectPunct "}"
      return .use head lower upper
    match ← peek with
    | .ident "for" => advance
    | _ => failAt "expected `for`: `impl Trait for Type`"
    let head ← expectIdent
    let args ← parseGenerics
    let mut context : Array (String × String) := #[]
    if (← peek) == .ident "where" then
      advance
      repeat
        let p ← expectIdent
        expectPunct ":"
        context := context.push (p, ← expectIdent)
        if !(← acceptPunct ",") then break
    expectPunct "{"
    let mut methods : Array Item := #[]
    repeat
      if (← peek) == .punct "}" then break
      match ← peek with
      | .ident "fn" => methods := methods.push (← parseItem)
      | _ => failAt "expected `fn`: an implementation gives the trait's functions"
    expectPunct "}"
    pure (.impl params tr head args context.toList methods.toList)
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
      let _ ← acceptPunct ";"
      pure .fixity
    else failAt "expected a declaration"
  | _ => failAt "expected a declaration"

private partial def parseItems : P (List Item) := do
  let mut out : Array Item := #[]
  repeat
    if (← peek) == .eof then break
    out := out.push (← parseItem)
  pure out.toList

/-- Collect the fixity declarations of a token stream. -/
private def collectFixities (toks : Array Token) (fix : Fixities) : Except String Fixities := do
  let mut fix := fix
  for i in [0:toks.size] do
    match toks[i]?.map (·.tok), toks[i + 1]?.map (·.tok), toks[i + 2]?.map (·.tok) with
    | some (.ident kind), some (.int prec), some nameTok =>
      if fixityKinds.contains kind then
        let name ← match nameTok with
          | .ident s => pure s
          | .op s => pure s
          | _ => throw s!"{(toks[i]?.getD default).line}: a fixity declaration needs an operator name"
        if kind == "prefix" then
          fix := { fix with prefixes := (name, prec) :: fix.prefixes }
        else
          let assoc := if kind == "infixl" then Assoc.left
            else if kind == "infixr" then Assoc.right else Assoc.non
          fix := { fix with infixes := (name, prec, assoc) :: fix.infixes }
    | _, _, _ => pure ()
  pure fix

/-- Parse a source text, given the fixities already in scope. Returns the items
and the fixities including those it declares. `base` keeps the identities of
this text's callable literals apart from those of a text parsed before it. -/
def parse (fix : Fixities) (src : String) (base : Nat := 0) :
    Except String (List Item × Fixities) := do
  let toks ← lex src
  let fix ← collectFixities toks fix
  let (items, _) ← (parseItems.run ⟨toks, fix, base⟩).run 0
  pure (items, fix)

end Glorious.Syntax
