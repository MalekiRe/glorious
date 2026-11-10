import Glorious.Syntax.Ast
import Glorious.Syntax.Lexer

/-!
# Parser

Recursive descent with precedence climbing. Operators and their fixities are
declared by the program, so they are collected from the token stream first.

Braces in expression position always denote a callable: `{ x => body }` and
`{ P => a, Q => b }` take one argument, a plain block `{ body }` takes none. A
callable of several arguments is written `fn(x, y) { body }`. A block written
directly after a call is passed as its last argument, and `f { body }` calls `f`
with the block.
-/

namespace Glorious.Syntax

structure PCtx where
  toks : Array Token
  fix : Fixities

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
      advance
      let next := match assoc with
        | .right => prec
        | _ => prec + 1
      let rhs ← parseBinary next noBlock
      lhs := .call (.name none name) [lhs, rhs]
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
      advance
      let operand ← parseBinary prec noBlock
      pure (.call (.name none s) [operand])
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
        if (← peek) == .ident "mut" then advance
        pure (.ref (← expectIdent))
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
      advance
      let mut args ← parseArgs
      while !noBlock && (← peek) == .punct "{" do
        args := args ++ [← parseBraces]
      e := .call e args
    | .punct "{" =>
      -- `f { body }` is `f({ body })`.
      if noBlock then break
      let mut args : List Expr := []
      while (← peek) == .punct "{" do
        args := args ++ [← parseBraces]
      e := .call e args
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
    | .call f args => pure (.tailCall f args)
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
    pure (.closure [.mk pats body])
  | .ident x =>
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
  if scanClauseForm ctx.toks (← get) 0 then
    let clauses ← parseClauses
    expectPunct "}"
    pure (.closure clauses)
  else
    let body ← parseStmts
    expectPunct "}"
    pure (.closure [.mk [] body])

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
    if t == .ident "let" then
      advance
      if (← peek) == .ident "mut" then
        advance
        let name ← expectIdent
        expectPunct "="
        let value ← parseBinary 0 false
        expectPunct ";"
        out := out.push (.letMut name value)
      else
        let pat ← parsePattern
        expectPunct "="
        let value ← parseBinary 0 false
        expectPunct ";"
        out := out.push (.let_ pat value)
    else if t == .ident "defer" then
      advance
      let e ← parseBinary 0 false
      expectPunct ";"
      out := out.push (.defer e)
    else
      let e ← parseBinary 0 false
      if ← acceptPunct "=" then
        let value ← parseBinary 0 false
        out := out.push (.assign e value)
        -- An assignment may end a block; its value is unit.
        if !(← acceptPunct ";") then break
      else
        out := out.push (.expr e)
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

/-- Type parameters `<A, B>`, if present. -/
private partial def parseGenerics : P (List String) := do
  if !(← isOp "<") then return []
  advance
  let mut out : Array String := #[]
  repeat
    if ← isOp ">" then break
    out := out.push (← expectIdent)
    if !(← acceptPunct ",") then break
  expectOp ">"
  pure out.toList

mutual

private partial def parseType : P TypeExpr := do
  match ← peek with
  | .op "!" =>
    advance
    pure .never
  | .op "&" =>
    advance
    if (← peek) == .ident "mut" then advance
    pure (.ref (← parseType))
  | .ident "_" =>
    advance
    pure .hole
  | .ident "fn" =>
    advance
    expectPunct "("
    let params ← parseTypeList ")"
    let ret ← if ← acceptPunct "->" then parseType else pure (.tuple [])
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
      -- An optional quantity `[lo, hi]`: the resumption may be used `hi` times.
      let mut shots := 1
      if ← acceptPunct "[" then
        match ← peek, ← peek 1, ← peek 2 with
        | .int _, .punct ",", .int hi =>
          advance
          advance
          advance
          shots := hi
        | _, _, _ => failAt "expected a quantity such as `[2, 2]`"
        expectPunct "]"
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
      ops := ops.push ⟨op, payload, result, terminal, shots⟩
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
      let ret ← if ← acceptPunct "->" then some <$> parseType else pure none
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
and the fixities including those it declares. -/
def parse (fix : Fixities) (src : String) : Except String (List Item × Fixities) := do
  let toks ← lex src
  let fix ← collectFixities toks fix
  let (items, _) ← (parseItems.run ⟨toks, fix⟩).run 0
  pure (items, fix)

end Glorious.Syntax
