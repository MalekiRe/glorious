import Glorious.Syntax.Ast
import Glorious.Syntax.Lexer
import Glorious.Value

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
  /-- The constructors declared with named fields, in any module: found
  before parsing, since `Point { x: 1 }` is otherwise a call given a block. -/
  records : List String := []
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

/-- The rest of a path `a::b::c` whose first name was read: all its names. -/
private partial def parsePathRest (first : String) : P (List String) := do
  match ← peek, ← peek 1 with
  | .punct "::", .ident y =>
    advance
    advance
    pure (first :: (← parsePathRest y))
  | _, _ => pure [first]

/-- A name, perhaps with the path of the module it is in, as one string. -/
private def expectPath : P String := do
  pure ("::".intercalate (← parsePathRest (← expectIdent)))

/-- A path as the name at its end and what is before it. -/
private def splitPath (segs : List String) : Option String × String :=
  match segs.reverse with
  | [] => (none, "")
  | [x] => (none, x)
  | x :: before => (some ("::".intercalate before.reverse), x)

/-- A whole number as written, with its sign: it has to fit in 64 bits. -/
private def plainInt (neg : Bool) (n : Nat) : P Int := do
  let v : Int := if neg then -(n : Int) else n
  unless Glorious.fits v 64 do failAt s!"`{v}` does not fit in 64 bits"
  pure v

/-- A whole number written with a type, `5u8`: it has to fit, and is then a
value of that type. The name of the type's value and the number. -/
private def typedInt (neg : Bool) (n : Nat) (suffix : String) : P (Option String × Int) := do
  let v : Int := if neg then -(n : Int) else n
  if suffix == "i64" || suffix == "Int" then return (none, ← plainInt neg n)
  match scalars.lookup suffix with
  | some (some width) =>
    unless Glorious.fits v width do failAt s!"`{v}` does not fit in `{suffix}`"
    pure (some (suffix ++ "_of"), v)
  | _ => failAt s!"`{suffix}` is not a type of whole numbers"

/-- A number with a point or an exponent: the nearest number its type holds,
as the name of the type's value and its bits. One too large to hold is an
error. -/
private def floatBits (neg : Bool) (digits : Nat) (exp10 : Int) (suffix : String) :
    P (String × Int) := do
  let format ← if suffix == "" || suffix == "f64" then pure Ieee.binary64
    else if suffix == "f32" then pure Ieee.binary32
    else failAt s!"`{suffix}` is not a floating point type"
  let d : Int := if neg then -(digits : Int) else digits
  let bits := if digits == 0 then format.zeroBits neg else Ieee.ofDecimal format d exp10
  if bits == format.infBits neg then failAt "this number is too large for its type"
  pure (if suffix == "f32" then "f32_of" else "f64_of", Ieee.ofBits bits)

/-- The value a scalar's name makes of an integer. -/
private def scalarValue (name : String) (n : Int) : Expr := .call 0 (.name none name) [.int n]

/-- A text as a value: its characters, one after another. -/
private def textValue (codes : List Nat) : Expr :=
  codes.foldr (fun (c : Nat) rest =>
      .call 0 (.name (some "%prelude::Str") "StrChar") [scalarValue "char_of" (c : Int), rest])
    (.name (some "%prelude::Str") "StrEnd")

/-- A literal other than a plain whole number, if one is next, perhaps after
a `-` already read. -/
private def scalarLiteral (neg : Bool) : P (Option Expr) := do
  match ← peek with
  | .typed n suffix =>
    let (name, v) ← typedInt neg n suffix
    advance
    pure (some (match name with
      | some name => scalarValue name v
      | none => .int v))
  | .float digits exp10 suffix =>
    let (name, bits) ← floatBits neg digits exp10 suffix
    advance
    pure (some (scalarValue name bits))
  | .char code =>
    if neg then failAt "a character has no sign"
    advance
    pure (some (scalarValue "char_of" code))
  | .str codes =>
    if neg then failAt "a text has no sign"
    advance
    pure (some (textValue codes))
  | _ => pure none

/-- A literal as a pattern: the value it is, to be compared with. -/
private partial def literalPattern : Expr → Option Pattern
  | .int n => some (.int n)
  | .call _ (.name qual name) args => (args.mapM literalPattern).map (.ctor name qual)
  | .name (some qual) name => some (.ctor name (some qual) [])
  | _ => none

/-- What a field is a field of: a named variable, a named reference written
`(*p)`, or what an expression that gives a reference points to. -/
private inductive FieldRoot where
  | named (x : String) (star : Bool)
  | through (base : Expr)

/-- `root.a.0` as its root and the way to the field, if it is a field. -/
private partial def fieldRoot : Expr → Option (FieldRoot × List String)
  | .proj e idx => step e (toString idx)
  | .fieldOf _ e name => step e name
  | _ => none
where
  step (e : Expr) (s : String) : Option (FieldRoot × List String) :=
    match e with
    | .name none x => some (.named x false, [s])
    | .deref (.name none x) => some (.named x true, [s])
    | .proj _ _ => (fieldRoot e).map fun (root, path) => (root, path ++ [s])
    | .fieldOf _ _ _ => (fieldRoot e).map fun (root, path) => (root, path ++ [s])
    | .deref base => some (.through base, [s])
    | base => some (.through base, [s])

/-- A borrow of a field: of a variable or a named reference as it is, of what
an expression points to as a mark for its statement to settle. -/
private def fieldBorrow (id : Nat) (uniq : Bool) (root : FieldRoot) (path : List String) : Expr :=
  match root with
  | .named x star => .refField id uniq x path star
  | .through base =>
    .call id (.name none throughMark)
      [base, .tuple (path.map fun s => Expr.name none s), .int (if uniq then 1 else 0)]

/-- What a statement's expression leaves to settle: the references to be
named first, whether anything that does something has been come to, and
whether a reference would be computed out of turn. -/
private structure Hoist where
  lets : Array (String × Expr) := #[]
  seen : Bool := false
  bad : Bool := false

/-- Is a borrow through an expression written anywhere in this, outside the
statements of a block or a callable? -/
private partial def hasThrough : Expr → Bool
  | .call _ (.name none f) args => f == throughMark || args.any hasThrough
  | .call _ f args => hasThrough f || args.any hasThrough
  | .tailCall _ f args => hasThrough f || args.any hasThrough
  | .tuple es => es.any hasThrough
  | .proj e _ => hasThrough e
  | .fieldOf _ e _ => hasThrough e
  | .deref e => hasThrough e
  | .reborrow _ e => hasThrough e
  | .handle subject _ => hasThrough subject
  | _ => false

/-- An expression with each borrow through an expression made a borrow
through a name, the expressions to be given those names noted in the order
they are computed. Nothing that does something may come before one: its
reference is computed before the statement it is in. -/
private partial def hoistExpr (h : Hoist) : Expr → Expr × Hoist
  | .call id (.name none f) args =>
    if f == throughMark then
      match args with
      | [base, .tuple steps, .int uniq] =>
        let before := h.seen
        let (base, h) := hoistExpr { h with seen := false } base
        let name := s!"%through{id}"
        let path := steps.filterMap fun
          | .name none s => some s
          | _ => none
        (.refField id (uniq == 1) name path true,
          { h with lets := h.lets.push (name, base), seen := before, bad := h.bad || before })
      | _ => (.call id (.name none f) args, h)
    else
      let (args, h) := hoistAll h args
      (.call id (.name none f) args, { h with seen := true })
  | .call id f args =>
    let (f, h) := hoistExpr h f
    let (args, h) := hoistAll h args
    (.call id f args, { h with seen := true })
  | .tailCall id f args =>
    let (parts, h) := hoistAll h (f :: args)
    (.tailCall id (parts.headD f) (parts.drop 1), { h with seen := true })
  | .tuple es =>
    let (es, h) := hoistAll h es
    (.tuple es, h)
  | .proj e i =>
    let (e, h) := hoistExpr h e
    (.proj e i, h)
  | .fieldOf id e name =>
    let (e, h) := hoistExpr h e
    (.fieldOf id e name, h)
  | .deref e =>
    let (e, h) := hoistExpr h e
    (.deref e, { h with seen := true })
  | .reborrow u e =>
    let (e, h) := hoistExpr h e
    (.reborrow u e, h)
  | .handle subject arms =>
    -- What is handled is computed under the handler, not before it.
    (.handle subject arms, { h with seen := true, bad := h.bad || hasThrough subject })
  | .name q x => (.name q x, { h with seen := true })
  | e => (e, h)
where
  hoistAll (h : Hoist) (es : List Expr) : List Expr × Hoist :=
    es.foldl (fun (acc : List Expr × Hoist) e =>
      let (e, h) := hoistExpr acc.2 e
      (acc.1 ++ [e], h)) ([], h)

/-- A statement, and before it the references its borrows go through, each
given a name. In an assignment the place is found before the value is
computed. None if a reference would be computed out of turn. -/
private def hoistStmt (s : Stmt) : Option (List Stmt × Stmt) :=
  let done := fun (h : Hoist) (s : Stmt) =>
    if h.bad then none
    else some (h.lets.toList.map fun (name, base) => Stmt.let_ (.var name) base, s)
  match s with
  | .let_ pat value =>
    let (value, h) := hoistExpr {} value
    done h (.let_ pat value)
  | .letMut x value =>
    let (value, h) := hoistExpr {} value
    done h (.letMut x value)
  | .expr e =>
    let (e, h) := hoistExpr {} e
    done h (.expr e)
  | .assign target value =>
    let (target, h) := hoistExpr {} target
    let (value, h) := hoistExpr { h with seen := true } value
    done h (.assign target value)
  | .defer e => if hasThrough e then none else some ([], .defer e)
  | s => some ([], s)

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
      | .ident "is" =>
        -- `subject is Pattern`, which binds as a comparison does.
        if 4 < minPrec then break
        let id := (← read).base + (← get) + 1
        advance
        let pat ← parsePattern
        lhs := .call id (.name none isMark) [lhs, .closure 0 [.mk [pat] []]]
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
          let v ← plainInt true n
          advance
          pure (.int v)
        | .typed _ _ | .float _ _ _ =>
          advance
          match ← scalarLiteral true with
          | some e => pure e
          | none => failAt "expected a number"
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
          -- `&x`, `&x.0.1`, `&(*p).0`, or `&f().0` through what an
          -- expression gives.
          match ← parsePostfix true with
          | .name none x => pure (.ref uniq x)
          | e =>
            match fieldRoot e with
            | some (root, path) => pure (fieldBorrow id uniq root path)
            | none => failAt "`&` is followed by a variable, a field of one, or a field of what a reference points to"
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
    | .punct "." =>
      match ← peek 1 with
      | .int n =>
        advance
        advance
        e := .proj e n
      | .ident field =>
        let id := (← read).base + (← get) + 1
        advance
        advance
        e := .fieldOf id e field
      | _ => failAt "expected a field after `.`"
    | _ => break
  pure e

private partial def parsePrimary (noBlock : Bool) : P Expr := do
  match ← peek with
  | .int n =>
    let v ← plainInt false n
    advance
    pure (.int v)
  | .typed _ _ | .float _ _ _ | .char _ | .str _ =>
    match ← scalarLiteral false with
    | some e => pure e
    | none => failAt "expected a value"
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
    let (qual, name) := splitPath (← parsePathRest x)
    pure (.name qual name)
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
        expectPunct "="
        let value ← parseBinary 0 false
        expectPunct ";"
        out := out ++ (← settle (.letMut name value)).toArray
      else
        let pat ← parsePattern
        expectPunct "="
        let value ← parseBinary 0 false
        expectPunct ";"
        out := out ++ (← settle (.let_ pat value)).toArray
    else if t == .ident "defer" then
      advance
      let e ← parseBinary 0 false
      expectPunct ";"
      out := out ++ (← settle (.defer e)).toArray
    else
      let e ← parseBinary 0 false
      if ← acceptPunct "=" then
        let id := (← read).base + (← get) + 1
        let value ← parseBinary 0 false
        -- `x.0 = v` and `(*p).0 = v` assign through a borrow of the field.
        let target := match fieldRoot e with
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
  pure out.toList

end

private def isOp (s : String) : P Bool := do
  pure ((← peek) == .op s)

private def expectOp (s : String) : P Unit := do
  if (← peek) == .op s then advance else failAt s!"expected `{s}`"

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
    if x == "for" && (← isOp "<") then
      -- `for<'a> fn(&'a T) -> R`: a callable for every such lifetime.
      advance
      let mut lifetimes : Array TypeExpr := #[]
      repeat
        if ← isOp ">" then break
        let l ← expectIdent
        unless l.startsWith "'" do failAt "expected a lifetime: `for<'a>`"
        lifetimes := lifetimes.push (.name l [])
        if !(← acceptPunct ",") then break
      expectOp ">"
      let inner ← parseType
      return .name rankedMark (lifetimes.toList ++ [inner])
    let x := "::".intercalate (← parsePathRest x)
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
      let name ← expectPath
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

/-- A row of effects in braces, `{E, F<T>}`. -/
private partial def parseRow : P (List (String × List TypeExpr)) := do
  expectPunct "{"
  let mut effects : Array (String × List TypeExpr) := #[]
  repeat
    if (← peek) == .punct "}" then break
    let name ← expectPath
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
  pure effects.toList

/-- The arguments of a callable as a bound writes them: `()`, `(A,)`,
`(A, B)`. One argument has the comma, so that it is not `A` in brackets. -/
private partial def parsePack : P (List TypeExpr) := do
  expectPunct "("
  let mut out : Array TypeExpr := #[]
  let mut comma := false
  repeat
    if (← peek) == .punct ")" then break
    out := out.push (← parseType)
    comma := ← acceptPunct ","
    if !comma then break
  if out.size == 1 && !comma then
    failAt "a callable of one argument is written `Fn<(T,)>`: without the comma `(T)` is `T` in brackets"
  expectPunct ")"
  pure out.toList

/-- `, Name = Type` as often as it is written, up to the closing `>`. -/
private partial def parseAssoc : P (List (String × TypeExpr)) := do
  let mut out : Array (String × TypeExpr) := #[]
  while ← acceptPunct "," do
    let name ← expectIdent
    expectPunct "="
    if name == "Effects" then out := out.push (name, .performs (.tuple []) (← parseRow))
    else out := out.push (name, ← parseType)
  match ← peek with
  | .op ">" => advance
  | _ => failAt "expected `>`"
  pure out.toList

/-- What is written after `Name:` of a type parameter: bounds joined by `+`. -/
private partial def parseBoundsOf (subject : String) : P (List Bound) := do
  let mut out : Array Bound := #[]
  repeat
    let mut tr ← expectPath
    -- `for<'a>` before a callable: it is asked for at every such lifetime.
    let mut ranked : Array String := #[]
    if tr == "for" && (← isOp "<") then
      advance
      repeat
        if ← isOp ">" then break
        let l ← expectIdent
        unless l.startsWith "'" do failAt "expected a lifetime: `for<'a>`"
        ranked := ranked.push l
        if !(← acceptPunct ",") then break
      expectOp ">"
      tr ← expectPath
      unless tr == "Fn" || tr == "RunsIn" do failAt "`for<..>` is written before `Fn` or `RunsIn`"
    if tr == "Fn" then
      if !(← isOp "<") then failAt "expected `<`: `Fn<(A, B), Output = R>`"
      advance
      let pack ← parsePack
      out := out.push { subject, trait := tr, args := pack, assoc := ← parseAssoc, ranked := ranked.toList }
    else if tr == "RunsIn" then
      if !(← isOp "<") then failAt "expected `<`: `RunsIn<E, (A, B), Output = R>`"
      advance
      let access ← parseType
      expectPunct ","
      let pack ← parsePack
      out := out.push { subject, trait := tr, args := access :: pack, assoc := ← parseAssoc, ranked := ranked.toList }
    else if tr == "Use" then
      if !(← isOp "<") then failAt "expected `<`: `Use<[1, 1]>`"
      advance
      let quantity ← parseQuantity
      if ← isOp ">" then advance else failAt "expected `>`"
      out := out.push { subject, trait := tr, quantity := some quantity }
    else
      let mut args : Array TypeExpr := #[]
      if ← isOp "<" then
        advance
        repeat
          if ← isOp ">" then break
          args := args.push (← parseType)
          if !(← acceptPunct ",") then break
        if ← isOp ">" then advance else failAt "expected `>`"
      out := out.push { subject, trait := tr, args := args.toList }
    if ← isOp "+" then advance else break
  pure out.toList

/-- Generic parameters `<'a, 'b: 'a, T, F: Fn<(T,)>>`, if present: type
parameters and lifetimes, a lifetime perhaps with one it lasts at least as
long as, a type parameter perhaps with what is asked of it. -/
private partial def parseGenericsWith : P (List String × List Bound) := do
  if !(← isOp "<") then return ([], [])
  advance
  let mut out : Array String := #[]
  let mut bounds : Array Bound := #[]
  repeat
    if ← isOp ">" then break
    let x ← expectIdent
    out := out.push x
    if (← peek) == .punct ":" then
      advance
      if x.startsWith "'" then
        let y ← expectIdent
        unless y.startsWith "'" do failAt "expected a lifetime: `'b: 'a`"
        out := out.push s!"{x}: {y}"
      else bounds := bounds ++ (← parseBoundsOf x).toArray
    if !(← acceptPunct ",") then break
  expectOp ">"
  pure (out.toList, bounds.toList)

private partial def parseGenerics : P (List String) := do
  let (params, bounds) ← parseGenericsWith
  unless bounds.isEmpty do failAt "what is asked of a type parameter is written on a function"
  pure params

/-- `where 'b: 'a, F: Fn<(T,)>, ...` after a function's result, if present. -/
private partial def parseWhere : P (List String × List Bound) := do
  if (← peek) != .ident "where" then return ([], [])
  advance
  let mut out : Array String := #[]
  let mut bounds : Array Bound := #[]
  repeat
    let x ← expectIdent
    expectPunct ":"
    if x.startsWith "'" then
      let y ← expectIdent
      unless y.startsWith "'" do failAt "expected a lifetime: `where 'b: 'a`"
      out := out.push s!"{x}: {y}"
    else bounds := bounds ++ (← parseBoundsOf x).toArray
    if !(← acceptPunct ",") then break
  pure (out.toList, bounds.toList)

/-- A function, and what is written of its type parameters. -/
private partial def parseFn : P (Item × List Bound) := do
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
    repeat
      if (← peek) == .punct ")" then break
      pats := pats.push (← parsePattern)
      annots := annots.push (← if ← acceptPunct ":" then some <$> parseType else pure none)
      if !(← acceptPunct ",") then break
    expectPunct ")"
    let ret ← if ← acceptPunct "->" then some <$> parseResult else pure none
    let (lifetimes, more) ← parseWhere
    expectPunct "{"
    let body ← parseStmts
    expectPunct "}"
    pure (.fn name (params ++ lifetimes) annots.toList ret [.mk pats.toList body], bounds ++ more)
  else
    expectPunct "{"
    let clauses ← parseClauses
    expectPunct "}"
    pure (.fn name params [] none clauses, bounds)

private partial def parseItem : P Item := do
  match ← peek with
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
    let (item, bounds) ← parseFn
    unless bounds.isEmpty do
      failAt "what is asked of a type parameter is written on a function of a module, not of an implementation"
    pure item
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
      let m ← match ← peek with
        | .op s => do
          advance
          pure s
        | _ => expectIdent
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
    let tr ← expectPath
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
    match ← peek with
    | .ident "for" => advance
    | _ => failAt "expected `for`: `impl Trait for Type`"
    let head ← expectPath
    let args ← parseGenerics
    let mut context : Array (String × String) := #[]
    if (← peek) == .ident "where" then
      advance
      repeat
        let p ← expectIdent
        expectPunct ":"
        context := context.push (p, ← expectPath)
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

/-- `pub`, if it is next: whether it is `pub(super)`, which lets only the
module this one is written in see. `pub(crate)` is `pub`: there is one package. -/
private def acceptPub : P (Option Bool) := do
  if (← peek) != .ident "pub" then return none
  advance
  if (← peek) == .punct "(" then
    advance
    let scope ← expectIdent
    unless scope == "crate" || scope == "super" do
      failAt "expected `pub(crate)` or `pub(super)`"
    expectPunct ")"
    return some (scope == "super")
  pure (some false)

/-- What follows `use`: a path, perhaps renamed with `as`, `*` for every name
of a module, or names in braces that share what is before them. -/
private partial def parseUseTree (before : List String) : P (List Item) := do
  if ← acceptPunct "{" then
    let mut out : Array Item := #[]
    repeat
      if (← peek) == .punct "}" then break
      out := out ++ (← parseUseTree before).toArray
      if !(← acceptPunct ",") then break
    expectPunct "}"
    pure out.toList
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

/-- A declaration, and with it what was written beside it. -/
private partial def parseItemGroup : P (List Item) := do
  match ← peek with
  | .ident "pub" =>
    let parent := (← acceptPub).getD false
    -- `pub use a::{b, c}` is `pub` for each; with a declaration, for it and
    -- not for what is written out beside it.
    match ← parseItemGroup with
    | items@(.import _ _ _ :: _) => pure (items.map (.pub parent))
    | item :: more => pure (.pub parent item :: more)
    | [] => pure []
  | .ident "mod" =>
    advance
    let name ← expectIdent
    if ← acceptPunct ";" then return [.module name none]
    expectPunct "{"
    let mut items : Array Item := #[]
    repeat
      if (← peek) == .punct "}" then break
      items := items ++ (← parseItemGroup).toArray
    expectPunct "}"
    pure [.module name (some items.toList)]
  | .ident "use" =>
    advance
    let items ← parseUseTree []
    expectPunct ";"
    pure items
  | .ident "struct" =>
    advance
    let name ← expectIdent
    let params ← parseGenerics
    let (fields, names, pubs) ← parseFieldDecls
    let _ ← acceptPunct ";"
    pure [.struct name params fields, .fieldNames name names pubs]
  | .ident "enum" =>
    advance
    let name ← expectIdent
    let params ← parseGenerics
    expectPunct "{"
    let mut ctors : Array (String × List TypeExpr) := #[]
    let mut named : Array Item := #[]
    repeat
      if (← peek) == .punct "}" then break
      let c ← expectIdent
      let (fields, names, _) ← parseFieldDecls
      ctors := ctors.push (c, fields)
      -- A constructor's fields are as visible as the type.
      unless names.isEmpty do named := named.push (.fieldNames c names (fields.map fun _ => true))
      if !(← acceptPunct ",") then break
    expectPunct "}"
    pure (.enum name params ctors.toList :: named.toList)
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
  | _ => pure [← parseItem]

private partial def parseItems : P (List Item) := do
  let mut out : Array Item := #[]
  repeat
    if (← peek) == .eof then break
    out := out ++ (← parseItemGroup).toArray
  pure out.toList

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
  let mut out : List String := []
  for i in [0:toks.size] do
    match tok i, tok (i + 1) with
    | .ident "struct", .ident name =>
      if tok (pastGenerics (i + 2)) == .punct "{" then out := name :: out
    | .ident "enum", .ident _ =>
      -- Each constructor at the top of the enum's braces that has braces.
      let mut j := pastGenerics (i + 2)
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

/-- What a text declares that has to be known before any text of the program
is parsed: its operators, added to `fix`, and its constructors with named
fields. -/
def declaredSyntax (fix : Fixities) (src : String) : Except String (Fixities × List String) := do
  let toks ← lex src
  pure (← collectFixities toks fix, collectRecords toks)

/-- The modules a text says are files of their own, `mod name;`: each as its
path from the module the text is, through the modules written in the text. -/
def fileModules (src : String) : Except String (List (List String)) := do
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

/-- Parse a source text, given the fixities already in scope. Returns the items
and the fixities including those it declares. `base` keeps the identities of
this text's callable literals apart from those of a text parsed before it. -/
def parse (fix : Fixities) (src : String) (base : Nat := 0) (records : List String := []) :
    Except String (List Item × Fixities) := do
  let toks ← lex src
  let fix ← collectFixities toks fix
  let (items, _) ← (parseItems.run ⟨toks, fix, collectRecords toks ++ records, base⟩).run 0
  pure (items, fix)

end Glorious.Syntax
