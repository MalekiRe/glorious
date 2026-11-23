module

public import Glorious.Syntax.Ast
public import Glorious.Syntax.FlatOps
public import Glorious.Syntax.Lexer
public import Glorious.Value

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

public section

namespace Glorious.Syntax.Parse

structure PCtx where
  toks : Array Token
  fix : Fixities
  /-- The constructors declared with named fields, in any module: found
  before parsing, since `Point { x: 1 }` is otherwise a call given a block. -/
  records : List String := []
  /-- Added to the identity of each callable literal, so that the literals of
  texts parsed separately stay distinct. -/
  base : Nat
  /-- The parameters of the function being read that are numbers, `const N:
  Int`: such a name written as a value is the number. -/
  consts : List String := []
  /-- Whether the program has arrays of a length their type says, `[T; N]`:
  `[a, b, c]` is then whichever of the two kinds is wanted of it. -/
  fixed : Bool := false
  /-- The operators of each module of the program, where they are not the
  same in every module, and the module being read. -/
  tables : List (List String × Fixities) := []
  path : List String := []
  /-- The type parameters of the function being read, and what is written of
  them: a `const { .. }` block in it is a function of the module generic in
  them, worked out at compile time at the types each copy is made at. -/
  enclosing : List String × List Bound := ([], [])

/-- What the parser holds as it reads: where it is, the functions written
inside blocks so far (on their way to the module the block is in), and the
body of the declaration being read, which what it reads is put in as it is
read (`Flat.Body`). -/
structure PState where
  pos : Nat
  made : Array Item
  body : Flat.Body

/-- What the parser does: given what it reads from and what it holds, it fails
or gives a value with what it then holds. One monad of its own and not four
stacked: what Lean compiles of this file is a third the size. -/
@[expose] def P (α : Type) : Type := PCtx → PState → Except String (α × PState)

instance : Monad P where
  pure a := fun _ s => .ok (a, s)
  bind x f := fun ctx s =>
    match x ctx s with
    | .ok (a, s) => f a ctx s
    | .error e => .error e

instance : MonadReaderOf PCtx P where
  read := fun ctx s => .ok (ctx, s)

instance : MonadWithReaderOf PCtx P where
  withReader f x := fun ctx s => x (f ctx) s

instance : MonadStateOf (Array Item) P where
  get := fun _ s => .ok (s.made, s)
  set made := fun _ s => .ok ((), { s with made })
  modifyGet f := fun _ s =>
    -- (Taken out first, so that it is changed in place.)
    let made := s.made
    let s := { s with made := #[] }
    let (a, made) := f made
    .ok (a, { s with made })

instance : MonadStateOf Flat.Body P where
  get := fun _ s => .ok (s.body, s)
  set body := fun _ s => .ok ((), { s with body })
  modifyGet f := fun _ s =>
    let body := s.body
    let s := { s with body := {} }
    let (a, body) := f body
    .ok (a, { s with body })

/-- (Declared last: `get` and `set` with nothing said are of where the
parser is.) -/
instance : MonadStateOf Nat P where
  get := fun _ s => .ok (s.pos, s)
  set pos := fun _ s => .ok ((), { s with pos })
  modifyGet f := fun _ s =>
    let (a, pos) := f s.pos
    .ok (a, { s with pos })

/-- What is tried and fails leaves the parser where it was. -/
instance : MonadExceptOf String P where
  throw e := fun _ _ => .error e
  tryCatch x handle := fun ctx s =>
    match x ctx s with
    | .ok r => .ok r
    | .error e => handle e ctx s

instance {α : Type} : Inhabited (P α) := ⟨throw "parser: unreachable"⟩

def peekTok (k : Nat := 0) : P Token := do
  let ctx ← read
  let i ← get
  pure (ctx.toks[i + k]?.getD ⟨.eof, 0, 0⟩)

def peek (k : Nat := 0) : P Tok := do
  pure (← peekTok k).tok

def advance : P Unit := modify (· + 1)

/-- Was what was just closed written with a comma before its closing bracket?
`(x,)` is a tuple of one part, and `(x)` is `x` in brackets. -/
def closedAfterComma : P Bool := do
  let ctx ← read
  let i ← get
  pure (i ≥ 2 && (ctx.toks[i - 2]?.map (·.tok)) == some (.punct ","))

def failAt {α : Type} (msg : String) : P α := do
  let t ← peekTok
  throw s!"{t.line}:{t.col}: {msg}, found {t.tok.describe}"

def expectPunct (s : String) : P Unit := do
  if (← peek) == .punct s then advance else failAt s!"expected `{s}`"

def acceptPunct (s : String) : P Bool := do
  if (← peek) == .punct s then
    advance
    pure true
  else pure false

def expectIdent : P String := do
  match ← peek with
  | .ident s =>
    advance
    pure s
  | _ => failAt "expected a name"

/-- The rest of a path `a::b::c` whose first name was read: all its names. -/
partial def parsePathRest (first : String) : P (List String) := do
  match ← peek, ← peek 1 with
  | .punct "::", .ident y =>
    advance
    advance
    pure (first :: (← parsePathRest y))
  | _, _ => pure [first]

/-- A name, perhaps with the path of the module it is in, as one string. -/
def expectPath : P String := do
  pure ("::".intercalate (← parsePathRest (← expectIdent)))

/-- A path as the name at its end and what is before it. -/
def splitPath (segs : List String) : Option String × String :=
  match segs.reverse with
  | [] => (none, "")
  | [x] => (none, x)
  | x :: before => (some ("::".intercalate before.reverse), x)

/-- A whole number as written, with its sign: it has to fit in 64 bits. -/
def plainInt (neg : Bool) (n : Nat) : P Int := do
  let v : Int := if neg then -(n : Int) else n
  unless Glorious.fits v 64 do failAt s!"`{v}` does not fit in 64 bits"
  pure v

/-- A whole number written with a type, `5u8`: it has to fit, and is then a
value of that type. The name of the type's value and the number. -/
def typedInt (neg : Bool) (n : Nat) (suffix : String) : P (Option String × Int) := do
  let v : Int := if neg then -(n : Int) else n
  if suffix == "i64" || suffix == "Int" then return (none, ← plainInt neg n)
  match scalars.lookup suffix with
  | some (some width) =>
    unless Glorious.fits v width do failAt s!"`{v}` does not fit in `{suffix}`"
    -- 128 bits without a sign are held as the same bits with one.
    let held := if width == -128 && v ≥ 170141183460469231731687303715884105728
      then v - 340282366920938463463374607431768211456 else v
    pure (some (suffix ++ "_of"), held)
  | _ => failAt s!"`{suffix}` is not a type of whole numbers"

/-- A number with a point or an exponent: the nearest number its type holds,
as the name of the type's value and its bits. One too large to hold is an
error. -/
def floatBits (neg : Bool) (digits : Nat) (exp10 : Int) (suffix : String) :
    P (String × Int) := do
  let format ← if suffix == "" || suffix == "f64" then pure Ieee.binary64
    else if suffix == "f32" then pure Ieee.binary32
    else failAt s!"`{suffix}` is not a floating point type"
  let d : Int := if neg then -(digits : Int) else digits
  let bits := if digits == 0 then format.zeroBits neg else Ieee.ofDecimal format d exp10
  if bits == format.infBits neg then failAt "this number is too large for its type"
  pure (if suffix == "f32" then "f32_of" else "f64_of", Ieee.ofBits bits)

/-! ## The body being read

What is read is put in the body of the declaration it is in as it is read:
each expression, statement and clause a node there, named by its place. -/

open Flat (ExprId StmtId ClauseId FExpr FStmt FClause)

/-- Something made with the body being read. -/
def build {α : Type} (x : Flat.Build α) : P α := modifyGetThe Flat.Body fun b => x.run b

def mk (e : FExpr) : P ExprId := build (Flat.pushExpr e)
def mkS (s : FStmt) : P StmtId := build (Flat.pushStmt s)
def mkC (pats : List Pattern) (body : Array StmtId) : P ClauseId := build (Flat.pushClause ⟨pats, body⟩)

/-- What an expression read is. -/
def node (e : ExprId) : P FExpr := do pure ((← getThe Flat.Body).expr e)

def mkName (qual : Option String) (x : String) : P ExprId := mk (.name qual x)

/-- A call of the function named `f`. -/
def callOf (id : Nat) (qual : Option String) (f : String) (args : Array ExprId) : P ExprId := do
  mk (.call id (← mkName qual f) args)

/-- A value written out as a tree: a type among expressions, a scalar. -/
def tree (e : Expr) : P ExprId := build (Flat.flatExpr e)

/-- Another copy of an expression read, for a second place it is written in:
no node is in two places. -/
def copy (e : ExprId) : P ExprId := do tree (Flat.treeExpr (← getThe Flat.Body) e)

/-- A declaration's clauses read into a body of their own. -/
def bodyOf (clauses : P (Array ClauseId)) : P Flat.Body := do
  let outer ← modifyGetThe Flat.Body fun b => (b, {})
  let roots ← clauses
  let b ← modifyGetThe Flat.Body fun b => (b, outer)
  -- (Without what the reading made and left: what is kept is what is
  -- written.)
  pure { b with roots }.compact

/-- An expression read into a body of its own: a constant's value. -/
def valueOf (value : P ExprId) : P (Flat.Body × ExprId) := do
  let outer ← modifyGetThe Flat.Body fun b => (b, {})
  let e ← value
  let b ← modifyGetThe Flat.Body fun b => (b, outer)
  pure (b, e)

/-- A function of the prelude that the compiler writes a literal or an index
with, whatever the program has in scope. -/
def preludeFn (name : String) : P ExprId := mkName (some "%prelude") name

/-- `[a, b, c]` as a value: the empty array with each pushed on. The calls
have identities where they are given, so that they are known to return: an
element computed before the next is then not one that could be left
behind. -/
def arrayValue (elements : List ExprId) (empty : Nat := 0) (pushes : List Nat := []) : P ExprId := do
  let mut acc ← mk (.call empty (← preludeFn "array_empty") #[])
  for (e, i) in elements.zipIdx do
    acc ← mk (.call (pushes.getD i 0) (← preludeFn "push") #[acc, e])
  pure acc

/-- `a[i]`, if this is one: the array and the place. -/
def indexed? (e : ExprId) : P (Option (Nat × ExprId × ExprId)) := do
  match ← node e with
  | .call id f #[a, i] =>
    match ← node f with
    | .name (some "%prelude") "index" => pure (some (id, a, i))
    | _ => pure none
  | _ => pure none

/-- A literal other than a plain whole number, if one is next, perhaps after
a `-` already read. -/
def scalarLiteral (neg : Bool) : P (Option ExprId) := do
  match ← peek with
  | .typed n suffix =>
    let (name, v) ← typedInt neg n suffix
    advance
    some <$> tree (match name with
      | some name => scalarValue name v
      | none => .int v)
  | .float digits exp10 suffix =>
    let (name, bits) ← floatBits neg digits exp10 suffix
    advance
    some <$> tree (scalarValue name bits)
  | .char code =>
    if neg then failAt "a character has no sign"
    advance
    some <$> tree (scalarValue "char_of" code)
  | .str codes =>
    if neg then failAt "a text has no sign"
    advance
    some <$> tree (textValue codes)
  | .bytes codes =>
    if neg then failAt "bytes have no sign"
    -- (Each push numbered, by the text's place, the token and the byte, in
    -- a space of their own.)
    let at_ ← get
    let base := (← read).base
    advance
    let pushes := (List.range codes.length).map fun i =>
      if i < 1000 then 850000000000000000 + (base / 1000000) * 100000000000 + at_ * 1000 + i else 0
    let bytes ← codes.mapM fun (c : Nat) => tree (scalarValue "u8_of" (c : Int))
    some <$> arrayValue bytes 0 pushes
  | _ => pure none

/-- A literal as a pattern: the value it is, to be compared with. -/
partial def literalPattern (e : ExprId) : P (Option Pattern) := do
  match ← node e with
  | .int n => pure (some (.int n))
  | .call _ f args =>
    match ← node f with
    | .name qual name => pure (((← args.toList.mapM literalPattern).mapM id).map (.ctor name qual))
    | _ => pure none
  | .name (some qual) name => pure (some (.ctor name (some qual) []))
  | _ => pure none

/-- A literal read, if one was, as a pattern. -/
def literalOf : Option ExprId → P (Option Pattern)
  | some e => literalPattern e
  | none => pure none

/-- What a field is a field of: a named variable, a named reference written
`(*p)`, or what an expression that gives a reference points to. -/
inductive FieldRoot where
  | named (x : String) (star : Bool)
  | through (base : ExprId)

/-- `root.a.0` as its root and the way to the field, if it is a field. -/
partial def fieldRoot (e : ExprId) : P (Option (FieldRoot × List String)) := do
  match ← node e with
  | .proj e idx => step e (toString idx)
  | .fieldOf _ e name => step e name
  | _ => pure none
where
  step (e : ExprId) (s : String) : P (Option (FieldRoot × List String)) := do
    match ← node e with
    | .name none x => pure (some (.named x false, [s]))
    | .deref inner =>
      match ← node inner with
      | .name none x => pure (some (.named x true, [s]))
      | _ => pure (some (.through inner, [s]))
    | .proj _ _ | .fieldOf _ _ _ => pure ((← fieldRoot e).map fun (root, path) => (root, path ++ [s]))
    | _ => pure (some (.through e, [s]))

/-- A borrow of a field: of a variable or a named reference as it is, of what
an expression points to as a mark for its statement to settle. -/
def fieldBorrow (id : Nat) (uniq : Bool) (root : FieldRoot) (path : List String) : P ExprId := do
  match root with
  | .named x star => mk (.refField id uniq x path star)
  | .through base =>
    let steps ← mk (.tuple (← path.toArray.mapM (mkName none)))
    callOf id none throughMark #[base, steps, ← mk (.int (if uniq then 1 else 0))]

/-- `&a[i]` and `&mut a[i]`: a reference to the element where it is, if `a`
is a place: a variable, a field, what a reference points to, or an element
in turn. Of anything else the element is a value with no name. -/
partial def elementBorrow (uniq : Bool) (e : ExprId) : P (Option ExprId) := do
  let some (id, a, i) ← indexed? e | return none
  let base ← match ← node a with
    | .name none x => some <$> mk (.ref uniq x)
    | .deref r => some <$> mk (.reborrow uniq r)
    | _ =>
      match ← fieldRoot a with
      | some (root, path) => some <$> fieldBorrow (id + 800000) uniq root path
      | none => elementBorrow uniq a
  -- (For writing, the place is worked out before the array is borrowed:
  -- `a[len(a) - 1]` reads `a` to say where.)
  match base with
  | some b =>
    if uniq then some <$> mk (.call id (← preludeFn "place_at") #[i, b])
    else some <$> mk (.call id (← preludeFn "element_at") #[b, i])
  | none => pure none

/-- What a statement's expression leaves to settle: the references to be
named first, whether anything that does something has been come to, and
whether a reference would be computed out of turn. -/
structure Hoist where
  lets : Array (String × ExprId) := #[]
  seen : Bool := false
  bad : Bool := false

/-- Is a borrow through an expression written anywhere in this, outside the
statements of a block or a callable? -/
partial def hasThrough (b : Flat.Body) (e : ExprId) : Bool :=
  match b.expr e with
  | .call _ f args =>
    (match b.expr f with
      | .name none g => g == throughMark
      | _ => hasThrough b f) || args.any (hasThrough b)
  | _ => (b.direct e).any (hasThrough b)

/-- Each borrow through an expression made, in place, a borrow through a
name, the expressions to be given those names noted in the order they are
computed. Nothing that does something may come before one: its reference is
computed before the statement it is in. -/
partial def hoistExpr (h : Hoist) (e : ExprId) : P Hoist := do
  match ← node e with
  | .call id f args =>
    if let .name none g := ← node f then
      if g == throughMark then
        if let #[base, steps, uniq] := args then
          if let (.tuple steps, .int uniq) := (← node steps, ← node uniq) then
            let before := h.seen
            let h ← hoistExpr { h with seen := false } base
            let name := s!"%through{id}"
            let path ← steps.toList.filterMapM fun s => do
              match ← node s with
              | .name none s => pure (some s)
              | _ => pure none
            modifyThe Flat.Body fun b => { b with exprs := b.exprs.set! e (.refField id (uniq == 1) name path true) }
            return { h with lets := h.lets.push (name, base), seen := before, bad := h.bad || before }
        return h
      let h ← args.foldlM hoistExpr h
      return { h with seen := true }
    let h ← hoistExpr h f
    let h ← args.foldlM hoistExpr h
    pure { h with seen := true }
  | .tailCall _ f args =>
    let h ← (#[f] ++ args).foldlM hoistExpr h
    pure { h with seen := true }
  | .tuple es => es.foldlM hoistExpr h
  | .proj e _ | .fieldOf _ e _ | .reborrow _ e => hoistExpr h e
  | .deref e => pure { (← hoistExpr h e) with seen := true }
  | .handle subject _ =>
    -- What is handled is computed under the handler, not before it.
    pure { h with seen := true, bad := h.bad || hasThrough (← getThe Flat.Body) subject }
  | .name _ _ => pure { h with seen := true }
  | _ => pure h

/-- A statement, and before it the references its borrows go through, each
given a name. In an assignment the place is found before the value is
computed. None if a reference would be computed out of turn. -/
def hoistStmt (s : FStmt) : P (Option (List FStmt)) := do
  let h ← match s with
    | .let_ _ e | .letMut _ e | .expr e => hoistExpr {} e
    | .assign target value => do hoistExpr { (← hoistExpr {} target) with seen := true } value
    | .defer e => pure { bad := hasThrough (← getThe Flat.Body) e }
    | .located .. => pure {}
  if h.bad then return none
  pure (some (h.lets.toList.map (fun (name, base) => FStmt.let_ (.var name) base) ++ [s]))

/-- Does the block starting at token `i` have clauses (`... => ...`) rather than statements? -/
partial def scanClauseForm (toks : Array Token) (i depth : Nat) : Bool :=
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

def infixOf (t : Tok) : P (Option (String × Nat × Assoc)) := do
  let fix := (← read).fix
  let name? := match t with
    | .op s => some s
    | .ident s => some s
    | _ => none
  match name? with
  | some s => pure ((fix.infixes.lookup s).map fun (prec, assoc) => (s, prec, assoc))
  | none => pure none

def isOp (s : String) : P Bool := do
  pure ((← peek) == .op s)

def expectOp (s : String) : P Unit := do
  if (← peek) == .op s then advance else failAt s!"expected `{s}`"

/-- Items separated by commas, up to where `closed` says the list ends (not
taken). -/
partial def listUntil {α : Type} (closed : P Bool) (one : P α) : P (List α) := do
  let mut out : Array α := #[]
  repeat
    if ← closed then break
    out := out.push (← one)
    if !(← acceptPunct ",") then break
  pure out.toList

/-- Is the next token the punctuation `s`? -/
def atPunct (s : String) : P Bool := do pure ((← peek) == .punct s)

/-- `<a, b>`, if written. -/
def angledList {α : Type} (one : P α) : P (List α) := do
  if !(← isOp "<") then return []
  advance
  let out ← listUntil (isOp ">") one
  expectOp ">"
  pure out

/-- `<'a, 'b>` after `for`. -/
def parseLifetimes : P (List String) :=
  angledList do
    let l ← expectIdent
    unless l.startsWith "'" do failAt "expected a lifetime: `for<'a>`"
    pure l

mutual

partial def parseType : P TypeExpr := do
  match ← peek with
  | .ident "impl" =>
    failAt "`impl Trait` is a parameter's type, standing for a type parameter of its own with the trait; a result's is not built: write the type"
  | .ident "dyn" =>
    if let .ident _ ← peek 1 then
      failAt "`dyn Trait` is not read: values of several types are an `enum` of them, or the callables that do what is wanted of each"
    pure (.name (← expectPath) [])
  | .op "!" =>
    advance
    pure .never
  | .op "<" =>
    -- `<T as Trait>::Name`: what the trait leaves to `T`'s implementation.
    advance
    let self ← parseType
    unless (← peek) == .ident "as" do failAt "expected `as`: `<Type as Trait>::Name`"
    advance
    let trait ← expectPath
    -- (`<B as Bundle<S>>::Had`: the trait at its arguments.)
    let targs ← angledList parseType
    expectOp ">"
    expectPunct "::"
    let name ← expectIdent
    -- (`<R as Item>::Got<'a>`: what it leaves at its own parameters.)
    let nargs ← angledList parseType
    pure (.name assocOfMark [self, .name trait targs, .name name nargs])
  | .op "&" =>
    advance
    parseRefRest
  | .op "&&" =>
    -- `&&T` (and `&&'a mut T`), which the lexer reads as one symbol.
    advance
    pure (.ref false (← parseRefRest) none)
  | .ident "_" =>
    advance
    pure .hole
  | .ident "fn" =>
    advance
    expectPunct "("
    -- `fn(..P) -> R`: as many arguments as the tuple `P` has.
    let params ← if (← peek) == .punct "." && (← peek 1) == .punct "." then do
        advance
        advance
        let whole ← parseType
        expectPunct ")"
        pure [TypeExpr.name spreadParams [whole]]
      else parseTypeList ")"
    let ret ← if ← acceptPunct "->" then parseResult else pure (.tuple [])
    pure (.fn params ret)
  | .ident x =>
    advance
    if x == "for" && (← isOp "<") then
      -- `for<'a> fn(&'a T) -> R`: a callable for every such lifetime.
      let lifetimes ← parseLifetimes
      return .name rankedMark (lifetimes.map (.name · []) ++ [← parseType])
    let x := "::".intercalate (← parsePathRest x)
    -- (`'_`: a lifetime left to be found, kept in its place: of what a
    -- trait leaves, `Q::Got<'_>`, it says where the lifetime goes.)
    let args ← angledList do
      if (← peek) == .ident "'_" then
        advance
        pure (.name "'_" [])
      else parseType
    pure (.name x args)
  | .int n =>
    -- A whole number where a type is written: the type that stands for it.
    advance
    pure (numberType n)
  | .punct "(" =>
    advance
    -- (`..T` among them: the parts of the tuple `T`, first or last.)
    let mut spread : Option (Nat × TypeExpr) := none
    let mut parts : Array TypeExpr := #[]
    repeat
      if (← peek) == .punct ")" then break
      if (← peek) == .punct "." && (← peek 1) == .punct "." then
        advance
        advance
        if spread.isSome then failAt "a tuple type spreads one list: `(H, ..R)` or `(..G, X)`"
        spread := some (parts.size, ← parseType)
      else
        if let (.ident _, .punct ":") := (← peek, ← peek 1) then
          advance
          advance
        parts := parts.push (← parseType)
      if !(← acceptPunct ",") then break
    expectPunct ")"
    match spread with
    | some (at_, rest) =>
      if at_ == parts.size then
        pure (parts.foldr (fun p acc => TypeExpr.name consHead [p, acc]) rest)
      else if at_ == 0 then
        pure (parts.foldl (fun acc p => TypeExpr.name snocHead [acc, p]) rest)
      else failAt "a tuple type spreads its list first or last: `(H, ..R)` or `(..G, X)`"
    | none =>
    match parts.toList with
    | [t] => if ← closedAfterComma then pure (.tuple [t]) else pure t
    | args => pure (.tuple args)
  | .punct "[" =>
    -- `[T]`: an array of `T`.
    advance
    let element ← parseType
    -- `[T; N]`: an array of exactly `N` of them, `N` a number or a
    -- parameter that stands for one.
    if ← acceptPunct ";" then
      let length ← parseType
      expectPunct "]"
      return .name "%prelude::Fixed" [element, length]
    expectPunct "]"
    pure (.name "%prelude::Array" [element])
  | .op "*" =>
    -- `*const T`, `*mut T`: an address, with what is said to be there.
    advance
    match ← peek with
    | .ident "const" =>
      advance
      pure (.name "%prelude::Ptr" [← parseType])
    | .ident "mut" =>
      advance
      pure (.name "%prelude::PtrMut" [← parseType])
    | _ => failAt "expected `const` or `mut`: `*const T`, `*mut T`"
  | _ => failAt "expected a type"

/-- What follows `->` in a callable: its result, which may be left out when
it is unit, and then `/ {Effect, ...}` if what it performs is to be said. -/
partial def parseResult : P TypeExpr := do
  let startsType := match ← peek with
    | .ident _ => true
    | .punct "(" => true
    | .punct "[" => true
    | .op "!" => true
    | .op "&" => true
    | .op "&&" => true
    | .op "*" => true
    | .op "<" => true
    | _ => false
  let ret ← if startsType then parseType else pure (.tuple [])
  if (← peek) == .op "/" then
    advance
    -- One effect may be written without braces.
    let braced ← acceptPunct "{"
    pure (.performs ret (← parseEffects braced))
  else pure ret

/-- Effects, `E, F<T> | e` up to and including the `}` if `braced`, and
otherwise one. -/
partial def parseEffects (braced : Bool) : P (List (String × List TypeExpr)) := do
  let mut effects : Array (String × List TypeExpr) := #[]
  repeat
    if braced && (← peek) == .punct "}" then break
    -- `| e`: and whatever the row parameter `e` stands for.
    if braced && ((← peek) == .op "|" || (← peek) == .punct "|") then
      advance
      -- (Several, with commas: the row has each of them in it.)
      repeat
        effects := effects.push (rowMark, [← if ← isOp "<" then parseType else do pure (.name (← expectPath) [])])
        if !(← acceptPunct ",") then break
      break
    let name ← expectPath
    effects := effects.push (name, ← parseTypeArgs)
    if !braced then break
    if (← peek) == .op "|" || (← peek) == .punct "|" then continue
    if !(← acceptPunct ",") then break
  if braced then expectPunct "}"
  pure effects.toList

/-- `<A, B>`, if written. -/
partial def parseTypeArgs : P (List TypeExpr) := angledList parseType

/-- What follows `&`: a lifetime, `mut`, and the type. -/
partial def parseRefRest : P TypeExpr := do
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

/-- Types separated by commas up to and including the closing punctuation. An
item may be written `name: Type`. -/
partial def parseTypeList (close : String) : P (List TypeExpr) := do
  let out ← listUntil (atPunct close) do
    if let (.ident _, .punct ":") := (← peek, ← peek 1) then
      advance
      advance
    parseType
  expectPunct close
  pure out

end



def fixityKinds : List String := ["infixl", "infixr", "infix", "prefix"]

/-- `[lower, upper]`: how often something is to be used. `infinity` is no upper
bound. -/
def parseQuantity : P (Nat × Option Nat) := do
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
    | .op "*" => do
      advance
      pure none
    | _ => failAt "expected the most uses, a number, `*` or `infinity`"
  expectPunct "]"
  if let some n := upper then
    if n < lower then failAt "the most uses cannot be fewer than the fewest"
  pure (lower, upper)

/-- A row of effects in braces, `{E, F<T>}`. -/
partial def parseRow : P (List (String × List TypeExpr)) := do
  expectPunct "{"
  parseEffects true

/-- The arguments of a callable as a bound writes them: `()`, `(A,)`,
`(A, B)`. One argument has the comma, so that it is not `A` in brackets. -/
partial def parsePack : P (List TypeExpr) := do
  expectPunct "("
  let mut out : Array TypeExpr := #[]
  let mut comma := false
  repeat
    if (← peek) == .punct ")" then break
    -- `Fn<(..P)>`: as many as the tuple `P` has; `Fn<(H, ..R)>`, as the
    -- tuple of `H` first and the rest `R`.
    if (← peek) == .punct "." && (← peek 1) == .punct "." then
      advance
      advance
      let whole := out.foldr (fun h rest => TypeExpr.name consHead [h, rest]) (← parseType)
      out := #[.name spreadParams [whole]]
      comma := true
      let _ ← acceptPunct ","
      break
    out := out.push (← parseType)
    comma := ← acceptPunct ","
    if !comma then break
  if out.size == 1 && !comma then
    failAt "a callable of one argument is written `Fn<(T,)>`: without the comma `(T)` is `T` in brackets"
  expectPunct ")"
  pure out.toList

/-- `, Name = Type` as often as it is written, up to the closing `>`. -/
partial def parseAssoc : P (List (String × TypeExpr)) := do
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
partial def parseBoundsOf (subject : String) : P (List Bound) := do
  let mut out : Array Bound := #[]
  repeat
    let mut tr ← expectPath
    -- `for<'a>` before a callable: it is asked for at every such lifetime.
    let mut ranked : List String := []
    if tr == "for" && (← isOp "<") then
      ranked ← parseLifetimes
      tr ← expectPath
      unless tr == "Fn" || tr == "RunsIn" do failAt "`for<..>` is written before `Fn` or `RunsIn`"
    if tr == "Fn" then
      if !(← isOp "<") then failAt "expected `<`: `Fn<(A, B), Output = R>`"
      advance
      let pack ← parsePack
      out := out.push { subject, trait := tr, args := pack, assoc := ← parseAssoc, ranked }
    else if tr == "RunsIn" then
      if !(← isOp "<") then failAt "expected `<`: `RunsIn<E, (A, B), Output = R>`"
      advance
      let access ← parseType
      expectPunct ","
      let pack ← parsePack
      out := out.push { subject, trait := tr, args := access :: pack, assoc := ← parseAssoc, ranked }
    else if tr == "Use" then
      if !(← isOp "<") then failAt "expected `<`: `Use<[1, 1]>`"
      advance
      let quantity ← parseQuantity
      if ← isOp ">" then advance else failAt "expected `>`"
      out := out.push { subject, trait := tr, quantity := some quantity }
    else
      let mut args : Array TypeExpr := #[]
      let mut said : Array (String × TypeExpr) := #[]
      if ← isOp "<" then
        advance
        repeat
          if ← isOp ">" then break
          -- `Item = Type`: what the trait leaves to an implementation is
          -- said to be that type.
          match ← peek, ← peek 1 with
          | .ident name, .punct "=" =>
            advance
            advance
            said := said.push (name, ← parseType)
          | _, _ => args := args.push (← parseType)
          if !(← acceptPunct ",") then break
        if ← isOp ">" then advance else failAt "expected `>`"
      out := out.push { subject, trait := tr, args := args.toList, assoc := said.toList }
    if ← isOp "+" then advance else break
  pure out.toList

/-- Generic parameters `<'a, 'b: 'a, T, F: Fn<(T,)>>`, if present: type
parameters and lifetimes, a lifetime perhaps with one it lasts at least as
long as, a type parameter perhaps with what is asked of it. -/
partial def parseGenericsFull :
    P (List String × List Bound × List (Nat × List String × TypeExpr)) := do
  if !(← isOp "<") then return ([], [], [])
  advance
  let mut out : Array String := #[]
  let mut bounds : Array Bound := #[]
  -- `T = Type`: what the parameter is where it is not written, with its
  -- place and the parameters before it, which the type may mention.
  let mut defaults : Array (Nat × List String × TypeExpr) := #[]
  repeat
    if ← isOp ">" then break
    -- `const N: Int`: a parameter that stands for a whole number. It is a
    -- type parameter whose type is known to stand for one.
    if (← peek) == .ident "const" then
      advance
      let x ← expectIdent
      expectPunct ":"
      let _ ← parseType
      out := out.push x
      bounds := bounds.push { subject := x, trait := knownTrait }
      if !(← acceptPunct ",") then break
      continue
    -- `..T`, last: the rest of the arguments a use writes, as one tuple.
    if (← peek) == .punct "." && (← peek 1) == .punct "." then
      advance
      advance
      let x ← expectIdent
      defaults := defaults.push ((genericParams out.toList).length, [variadicMark], .hole)
      out := out.push x
      unless ← isOp ">" do failAt "`..T` takes the rest of the arguments: it is the last parameter"
      break
    let x ← expectIdent
    let before := out.toList
    out := out.push x
    if (← peek) == .punct ":" then
      advance
      if x.startsWith "'" then
        let y ← expectIdent
        unless y.startsWith "'" do failAt "expected a lifetime: `'b: 'a`"
        out := out.push s!"{x}: {y}"
      else if (← peek) == .ident "EffectRow" then
        -- `e: EffectRow`: a parameter that stands for a row of effects.
        advance
        out := out.pop.push s!"{x}: EffectRow"
      else bounds := bounds ++ (← parseBoundsOf x).toArray
    if ← acceptPunct "=" then
      defaults := defaults.push ((genericParams before).length, genericParams before, ← parseType)
    else unless defaults.isEmpty do
      failAt "a parameter that is always written comes before those that need not be"
    if !(← acceptPunct ",") then break
  expectOp ">"
  pure (out.toList, bounds.toList, defaults.toList)

partial def parseGenericsWith : P (List String × List Bound) := do
  let (params, bounds, defaults) ← parseGenericsFull
  unless defaults.isEmpty do
    if defaults.any (·.2.1 == [variadicMark]) then
      failAt "`..T` is a declared type's: a function takes its arguments as it says"
    failAt "what a parameter is where it is not written, `T = Type`, is said of a declared type's"
  pure (params, bounds)

partial def parseGenerics : P (List String) := do
  let (params, bounds) ← parseGenericsWith
  -- (That a `const N: Int` stands for a number is asked where its number
  -- is: `where N: Known` on an implementation that reads it.)
  let bounds := bounds.filter (·.trait != knownTrait)
  unless bounds.isEmpty do failAt "what is asked of a type parameter is written on a function"
  pure params

/-- `where 'b: 'a, F: Fn<(T,)>, ...` after a function's result, if present. -/
partial def parseWhere : P (List String × List Bound) := do
  if (← peek) != .ident "where" then return ([], [])
  advance
  let mut out : Array String := #[]
  let mut bounds : Array Bound := #[]
  repeat
    let mut x ← expectIdent
    -- (`I::Item: Ord`: of what a trait of `I` leaves to its implementation.)
    if (← peek) == .punct "::" then
      advance
      x := x ++ "::" ++ (← expectIdent)
    expectPunct ":"
    if x.startsWith "'" then
      let y ← expectIdent
      unless y.startsWith "'" do failAt "expected a lifetime: `where 'b: 'a`"
      out := out.push s!"{x}: {y}"
    else bounds := bounds ++ (← parseBoundsOf x).toArray
    if !(← acceptPunct ",") then break
  pure (out.toList, bounds.toList)

/-- `pub`, if it is next: whether it is `pub(super)`, which lets only the
module this one is written in see. `pub(crate)` is `pub`: there is one package. -/
def acceptPub : P (Option Bool) := do
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

/-- A pattern of a clause, as one for an array of exactly `j` elements taken
as a tuple of them: nothing if the pattern is for no such array. -/
def asTupleOf (j : Nat) : Pattern → Option Pattern
  | .wild => some .wild
  | .var x => some (.var x)
  | .ctor name none args =>
    match arrayPatLen name, restPatParts name with
    | some n, _ => if n == j then some (.tuple args) else none
    | none, some (k, _, _, _) =>
      let named := args.length - 1
      if named ≤ j then
        some (.tuple (args.take k ++ List.replicate (j - named) Pattern.wild ++ args.drop (k + 1)))
      else none
    | none, none => none
  | _ => none

/-- Clauses with those whose pattern is an array with a rest, `[first,
..rest] => body`, written out. Such a clause takes any array; it asks the
prelude whether the array has as many elements as the pattern names, takes
those off its ends, and the clauses after it are for an array that has not:

    whole => { RestFits(a) => let (first, a) = rest_first(a); let rest = a; body,
               RestShort(back) => { the clauses after, never => .. }(back)
             }(rest_fits(whole, 1))

An array with fewer elements than the pattern names has to be some other
clause's. Whether it is, is the checker's to say, and it cannot of an array:
so for each such length the clauses' patterns for it are written as patterns
of a tuple of so many, in a callable nothing calls, which the checker
refuses if they do not cover every case. With that, `never` is not reached.

The identities of the calls and callables this makes are those of the
pattern's own tokens and the `=>` after it, which nothing else has. -/
partial def restClausesOf (all : List Pattern) : List ClauseId → P (List ClauseId)
  | [] => pure []
  | c :: following => do
    let ⟨pats, body⟩ := (← getThe Flat.Body).clause c
    let some (.ctor name none args) := (match pats with | [p] => some p | _ => none)
      | return c :: (← restClausesOf all following)
    let some (k, id, line, col) := restPatParts name
      | return c :: (← restClausesOf all following)
    let rest := args[k]?.getD .wild
    let first := args.take k
    let last := args.drop (k + 1)
    let count := first.length + last.length
    let named := fun (j : Nat) => s!"%rest{id}:{j}"
    let callPrelude := fun (id : Nat) (f : String) (args : Array ExprId) => do
      mk (.call id (← preludeFn f) args)
    -- Without an element named, the pattern is the array.
    if count == 0 then return (← mkC [rest] body) :: (← restClausesOf all following)
    -- (Each statement has a place of its own in the pattern: what it lets
    -- go of is known by it.)
    let located := fun (col : Nat) (s : FStmt) => do mkS (.located line col (← mkS s))
    let firsts ← first.zipIdx.toArray.mapM fun (p, j) => do
      located (col + 1 + j) (.let_ (.tuple [p, .var (named (j + 1))])
        (← callPrelude (id + 4 + j) "rest_first" #[← mkName none (named j)]))
    -- (The last element comes off first.)
    let lasts ← last.reverse.zipIdx.toArray.mapM fun (p, j) => do
      located (col + 1 + k + j) (.let_ (.tuple [.var (named (k + j + 1)), p])
        (← callPrelude (id + 4 + k + j) "rest_last" #[← mkName none (named (k + j))]))
    let whole := named count
    let fits ← mkC [.ctor "RestFits" none [.var (named 0)]]
      (firsts ++ lasts ++ #[← located (col + 1 + count) (.let_ rest (← mkName none whole))] ++ body)
    let covered ← (List.range count).toArray.mapM fun j => do
      let clauses ← (all.filterMap (asTupleOf j)).toArray.mapM fun p => do
        mkC [p] #[← mkS (.expr (← mk (.tuple #[])))]
      -- (No clause for the length: a callable that covers nothing.)
      let clauses ← if clauses.isEmpty then
          pure #[← mkC [.ctor (arrayPatName 0) none []] #[← mkS (.expr (← mk (.tuple #[])))]]
        else pure clauses
      mkS (.let_ .wild (← mk (.closure (id + 4 + count + j) clauses)))
    let never := s!"%rest{id}:never"
    let unreached ← mkC [.var never]
      (covered.push (← mkS (.expr (← callPrelude (id + 3) "rest_unreached" #[← mkName none never]))))
    let back := s!"%rest{id}:back"
    let after ← mk (.closure (id + 2) ((← restClausesOf all following).toArray.push unreached))
    let short ← mkC [.ctor "RestShort" none [.var back]]
      #[← mkS (.expr (← mk (.call 0 after #[← mkName none back])))]
    let taken := s!"%rest{id}:whole"
    let both ← mk (.closure (id + 1) #[fits, short])
    let fitsCall ← callPrelude id "rest_fits" #[← mkName none taken, ← mk (.int count)]
    pure [← mkC [.var taken] #[← mkS (.expr (← mk (.call 0 both #[fitsCall])))]]

def restClauses (clauses : List ClauseId) : P (List ClauseId) := do
  let b ← getThe Flat.Body
  let pats := clauses.filterMap fun c => match (b.clause c).pats with
    | [p] => some p
    | _ => none
  restClausesOf pats clauses

end Glorious.Syntax.Parse
