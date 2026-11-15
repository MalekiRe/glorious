module

public import Glorious.Syntax.Ast
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

/-- What the parser does: given what it reads from, where it is, and the
functions written inside blocks so far (on their way to the module the block
is in), it fails or gives a value with where it then is and those functions.
One monad of its own and not four stacked: what Lean compiles of this file
is a third the size. -/
@[expose] def P (α : Type) : Type := PCtx → Nat → Array Item → Except String (α × Nat × Array Item)

instance : Monad P where
  pure a := fun _ i made => .ok (a, i, made)
  bind x f := fun ctx i made =>
    match x ctx i made with
    | .ok (a, i, made) => f a ctx i made
    | .error e => .error e

instance : MonadReaderOf PCtx P where
  read := fun ctx i made => .ok (ctx, i, made)

instance : MonadWithReaderOf PCtx P where
  withReader f x := fun ctx i made => x (f ctx) i made

instance : MonadStateOf (Array Item) P where
  get := fun _ i made => .ok (made, i, made)
  set made := fun _ i _ => .ok ((), i, made)
  modifyGet f := fun _ i made =>
    let (a, made) := f made
    .ok (a, i, made)

/-- (Declared last: `get` and `set` with nothing said are of where the
parser is.) -/
instance : MonadStateOf Nat P where
  get := fun _ i made => .ok (i, i, made)
  set i := fun _ _ made => .ok ((), i, made)
  modifyGet f := fun _ i made =>
    let (a, i) := f i
    .ok (a, i, made)

/-- What is tried and fails leaves the parser where it was. -/
instance : MonadExceptOf String P where
  throw e := fun _ _ _ => .error e
  tryCatch x handle := fun ctx i made =>
    match x ctx i made with
    | .ok r => .ok r
    | .error e => handle e ctx i made

instance {α : Type} : Inhabited (P α) := ⟨throw "parser: unreachable"⟩

private def peekTok (k : Nat := 0) : P Token := do
  let ctx ← read
  let i ← get
  pure (ctx.toks[i + k]?.getD ⟨.eof, 0, 0⟩)

private def peek (k : Nat := 0) : P Tok := do
  pure (← peekTok k).tok

private def advance : P Unit := modify (· + 1)

/-- Was what was just closed written with a comma before its closing bracket?
`(x,)` is a tuple of one part, and `(x)` is `x` in brackets. -/
private def closedAfterComma : P Bool := do
  let ctx ← read
  let i ← get
  pure (i ≥ 2 && (ctx.toks[i - 2]?.map (·.tok)) == some (.punct ","))

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
    -- 128 bits without a sign are held as the same bits with one.
    let held := if width == -128 && v ≥ 170141183460469231731687303715884105728
      then v - 340282366920938463463374607431768211456 else v
    pure (some (suffix ++ "_of"), held)
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

/-- A function of the prelude that the compiler writes a literal or an index
with, whatever the program has in scope. -/
private def preludeFn (name : String) : Expr := .name (some "%prelude") name

/-- `[a, b, c]` as a value: the empty array with each pushed on. The calls
have identities where they are given, so that they are known to return: an
element computed before the next is then not one that could be left
behind. -/
private def arrayValue (elements : List Expr) (empty : Nat := 0) (pushes : List Nat := []) : Expr :=
  (elements.zipIdx.foldl (fun acc (e, i) => .call (pushes.getD i 0) (preludeFn "push") [acc, e])
    (.call empty (preludeFn "array_empty") []))

/-- `a[i]`, if this is one: the array and the place. -/
private def indexed? : Expr → Option (Nat × Expr × Expr)
  | .call id (.name (some "%prelude") "index") [a, i] => some (id, a, i)
  | _ => none

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
  | .bytes codes =>
    if neg then failAt "bytes have no sign"
    advance
    pure (some (arrayValue (codes.map fun (c : Nat) => scalarValue "u8_of" (c : Int))))
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

/-- `&a[i]` and `&mut a[i]`: a reference to the element where it is, if `a`
is a place: a variable, a field, what a reference points to, or an element
in turn. Of anything else the element is a value with no name. -/
private partial def elementBorrow (uniq : Bool) (e : Expr) : Option Expr :=
  match indexed? e with
  | none => none
  | some (id, a, i) =>
    let base : Option Expr := match a with
      | .name none x => some (.ref uniq x)
      | .deref r => some (.reborrow uniq r)
      | a =>
        match fieldRoot a with
        | some (root, path) => some (fieldBorrow (id + 800000) uniq root path)
        | none => elementBorrow uniq a
    -- (For writing, the place is worked out before the array is borrowed:
    -- `a[len(a) - 1]` reads `a` to say where.)
    base.map fun b =>
      if uniq then .call id (preludeFn "place_at") [i, b] else .call id (preludeFn "element_at") [b, i]

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

private def isOp (s : String) : P Bool := do
  pure ((← peek) == .op s)

private def expectOp (s : String) : P Unit := do
  if (← peek) == .op s then advance else failAt s!"expected `{s}`"

mutual

private partial def parseType : P TypeExpr := do
  match ← peek with
  | .ident "impl" =>
    failAt "`impl Trait` is not a type: give the function a type parameter with the trait, `fn f<T: Trait>(x: T)`"
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
    if ← isOp ">" then advance else failAt "expected `>`"
    expectPunct "::"
    let name ← expectIdent
    pure (.name assocOfMark [self, .name trait [], .name name []])
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
  | .op "&&" =>
    -- `&&T` (and `&&'a mut T`), which the lexer reads as one symbol.
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
    pure (.ref false (.ref uniq (← parseType) life) none)
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
  | .int n =>
    -- A whole number where a type is written: the type that stands for it.
    advance
    pure (numberType n)
  | .punct "(" =>
    advance
    let args ← parseTypeList ")"
    match args with
    | [t] => if ← closedAfterComma then pure (.tuple [t]) else pure t
    | _ => pure (.tuple args)
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
private partial def parseResult : P TypeExpr := do
  let startsType := match ← peek with
    | .ident _ => true
    | .punct "(" => true
    | .punct "[" => true
    | .op "!" => true
    | .op "&" => true
    | .op "&&" => true
    | .op "*" => true
    | _ => false
  let ret ← if startsType then parseType else pure (.tuple [])
  if (← peek) == .op "/" then
    advance
    -- One effect may be written without braces.
    let braced ← acceptPunct "{"
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
      if !braced then break
      if (← peek) == .op "|" || (← peek) == .punct "|" then continue
      if !(← acceptPunct ",") then break
    if braced then expectPunct "}"
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
    | .op "*" => do
      advance
      pure none
    | _ => failAt "expected the most uses, a number, `*` or `infinity`"
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
    -- `| e`: and whatever the row parameter `e` stands for.
    if (← peek) == .op "|" || (← peek) == .punct "|" then
      advance
      repeat
        effects := effects.push (rowMark, [← if ← isOp "<" then parseType else do pure (.name (← expectPath) [])])
        if !(← acceptPunct ",") then break
      break
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
    if (← peek) == .op "|" || (← peek) == .punct "|" then continue
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
private partial def parseGenericsFull :
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

private partial def parseGenericsWith : P (List String × List Bound) := do
  let (params, bounds, defaults) ← parseGenericsFull
  unless defaults.isEmpty do
    failAt "what a parameter is where it is not written, `T = Type`, is said of a declared type's"
  pure (params, bounds)

private partial def parseGenerics : P (List String) := do
  let (params, bounds) ← parseGenericsWith
  -- (That a `const N: Int` stands for a number is asked where its number
  -- is: `where N: Known` on an implementation that reads it.)
  let bounds := bounds.filter (·.trait != knownTrait)
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

/-- A pattern of a clause, as one for an array of exactly `j` elements taken
as a tuple of them: nothing if the pattern is for no such array. -/
private def asTupleOf (j : Nat) : Pattern → Option Pattern
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
private partial def restClausesOf (all : List Pattern) : List Clause → List Clause
  | [] => []
  | .mk [.ctor name none args] body :: following =>
    match restPatParts name with
    | none => .mk [.ctor name none args] body :: restClausesOf all following
    | some (k, id, line, col) =>
      let rest := args[k]?.getD .wild
      let first := args.take k
      let last := args.drop (k + 1)
      let count := first.length + last.length
      let named := fun (j : Nat) => s!"%rest{id}:{j}"
      let prelude := fun (f : String) => Expr.name (some "%prelude") f
      -- Without an element named, the pattern is the array.
      if count == 0 then .mk [rest] body :: restClausesOf all following
      else
        -- (Each statement has a place of its own in the pattern: what it
        -- lets go of is known by it.)
        let firsts : List Stmt := first.zipIdx.map fun (p, j) =>
          Stmt.located line (col + 1 + j) (.let_ (.tuple [p, .var (named (j + 1))])
            (.call (id + 4 + j) (prelude "rest_first") [.name none (named j)]))
        -- (The last element comes off first.)
        let lasts : List Stmt := last.reverse.zipIdx.map fun (p, j) =>
          Stmt.located line (col + 1 + k + j) (.let_ (.tuple [.var (named (k + j + 1)), p])
            (.call (id + 4 + k + j) (prelude "rest_last") [.name none (named (k + j))]))
        let whole := named count
        let fits := Clause.mk [.ctor "RestFits" none [.var (named 0)]]
          (firsts ++ lasts ++ [Stmt.located line (col + 1 + count) (.let_ rest (.name none whole))] ++ body)
        let covered : List Stmt := (List.range count).map fun j =>
          let clauses := (all.filterMap (asTupleOf j)).map fun p => Clause.mk [p] [.expr (.tuple [])]
          -- (No clause for the length: a callable that covers nothing.)
          let clauses := if clauses.isEmpty then
              [Clause.mk [.ctor (arrayPatName 0) none []] [.expr (.tuple [])]]
            else clauses
          Stmt.let_ .wild (.closure (id + 4 + count + j) clauses)
        let never := s!"%rest{id}:never"
        let unreached := Clause.mk [.var never]
          (covered ++ [.expr (.call (id + 3) (prelude "rest_unreached") [.name none never])])
        let back := s!"%rest{id}:back"
        let short := Clause.mk [.ctor "RestShort" none [.var back]]
          [.expr (.call 0 (.closure (id + 2) (restClausesOf all following ++ [unreached])) [.name none back])]
        let taken := s!"%rest{id}:whole"
        [.mk [.var taken] [.expr (.call 0 (.closure (id + 1) [fits, short])
          [.call id (prelude "rest_fits") [.name none taken, .int count]])]]
  | clause :: following => clause :: restClausesOf all following

private def restClauses (clauses : List Clause) : List Clause :=
  restClausesOf (clauses.filterMap fun
    | .mk [p] _ => some p
    | _ => none) clauses

mutual

private partial def parsePattern : P Pattern := do
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
private partial def parsePatternList : P (List Pattern) := do
  let mut out : Array Pattern := #[]
  repeat
    if (← peek) == .punct ")" then break
    -- `..`: the fields not written, let go.
    if (← peek) == .punct "." && (← peek 1) == .punct "." then
      advance
      advance
      out := out.push (.var restMark)
    else out := out.push (← parsePattern)
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
private partial def parseBinary (minPrec : Nat) (noBlock : Bool)
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
      let rhs ← parseBinary next noBlock (some (prec, assoc))
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

private partial def parseUnary (noBlock : Bool) : P Expr := do
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
          | .name none x => pure (.ref uniq x)
          | e =>
            if let some at_ := elementBorrow uniq e then return at_
            match fieldRoot e with
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

private partial def parsePostfix (noBlock : Bool) : P Expr := do
  let mut e ← parsePrimary noBlock
  repeat
    match ← peek with
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
          let mut tys : Array TypeExpr := #[]
          repeat
            if ← isOp ">" then break
            tys := tys.push (← parseType)
            if !(← acceptPunct ",") then break
          if !(← isOp ">") then pure none
          else
            advance
            if (← peek) != .punct "(" then pure none else pure (some tys.toList)
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
        -- A field of what a name stands for is known by an identity, so
        -- that the checker can say it is read through a reference.
        let id := (← read).base + (← get) + 1
        advance
        advance
        e := match e with
          | .name none _ => .fieldOf id e (toString n)
          | _ => .proj e n
      | .ident field =>
        let id := (← read).base + (← get) + 1
        advance
        advance
        e := .fieldOf id e field
      | _ => failAt "expected a field after `.`"
    | _ => break
  pure e

private partial def parsePrimary (noBlock : Bool) : P Expr := do
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
    expectPunct "{"
    let arms ← parseClauses
    expectPunct "}"
    pure (.handle subject arms)
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
    | [e] => if ← closedAfterComma then pure (.tuple [e]) else pure e
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
  pure (restClauses out.toList)

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
    -- `-> R`, `-> R / {E}`, or `/ {E}` alone for a function that gives `()`.
    let ret ← if (← acceptPunct "->") || (← peek) == .op "/" then some <$> parseResult else pure none
    let (lifetimes, more) ← parseWhere
    expectPunct "{"
    let consts := (bounds.filter (·.trait == knownTrait)).map (·.subject)
    let body ← withReader (fun ctx => { ctx with consts := consts ++ ctx.consts }) parseStmts
    expectPunct "}"
    -- `-> !`: a function that does not come back gives whatever is wanted
    -- of it, which only a body that does not come back can.
    let (params, ret) := match ret with
      | some .never => (params ++ [neverParam], some (TypeExpr.name neverParam []))
      | some (.performs .never effects) =>
        (params ++ [neverParam], some (TypeExpr.performs (.name neverParam []) effects))
      | other => (params, other)
    pure (.fn name (params ++ lifetimes) annots.toList ret [.mk pats.toList body], bounds ++ more)
  else
    expectPunct "{"
    let clauses ← parseClauses
    expectPunct "}"
    pure (.fn name params [] none clauses, bounds)

end

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
    -- `const NAME: Type = value;`: a value with a name, as `let` is here.
    advance
    let name ← expectIdent
    expectPunct ":"
    let ty ← parseType
    expectPunct "="
    let value ← parseBinary 0 false
    expectPunct ";"
    pure (.alias name (Expr.call 0 (.name none ascribeMark) [value, ty.asExpr]))
  | .ident "impl" =>
    advance
    let params ← parseGenerics
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
    if (← peek) == .punct "{" then
      advance
      let self := TypeExpr.name tr selfArgs.toList
      let mut items : Array Item := #[]
      repeat
        if (← peek) == .punct "}" then break
        let vis ← acceptPub
        if (← peek) != .ident "fn" then failAt "expected `fn`: an implementation gives functions"
        let (item, bounds) ← withReader (fun c =>
          if c.records.contains tr then { c with records := "Self" :: c.records } else c) parseFn
        match item with
        | .fn name ps annots ret clauses =>
          let ps := params ++ ps.filter (!params.contains ·)
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
    -- What it is for: a type made with a name, or a tuple, with its
    -- arguments. An argument that is one of the implementation's type
    -- parameters, the first time it is written, is that parameter. Any other
    -- is a type the argument has to be: `impl<T, R> Get<T> for (Column<T>,
    -- R)` is for the pairs whose first part is a `Column<T>`.
    let (head, written) ← match ← parseType with
      | .tuple ts => pure (s!"(tuple{ts.length})", ts)
      | .name h ts => pure (h, ts)
      -- `impl<P, R> System for fn(P) -> R`: for the functions of one
      -- argument that perform nothing. `impl<T> Fetch for &mut T`.
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
    let mut context : Array (String × String) := #[]
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
        methods := methods.push (.typeAlias name takes body)
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
    let written := methods.toList.map fun
      | .fn name ps annots ret clauses =>
        Item.fn name ps (annots.map (·.map (TypeExpr.withSelf self))) (ret.map (TypeExpr.withSelf self))
          (clauses.map (selfClause head (some (tr, (TypeExpr.tuple [self]).asExpr))))
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
      assocs := assocs.push (← expectIdent)
      -- `type Of<T>;`: a type for each type it is asked at. How many it
      -- takes is seen where an implementation says what it is.
      let _ ← parseGenerics
      -- `type Effects: EffectRow;`: what is said of it is read and not kept;
      -- a row is known by where the trait's functions use it.
      if ← acceptPunct ":" then
        let _ ← expectPath
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
    methods := methods.push (m, types.toList, withMethodGenerics ret (genericParams own))
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
    let mut params : Array TypeExpr := #[]
    repeat
      if (← peek) == .punct ")" then break
      let _ ← expectIdent
      expectPunct ":"
      params := params.push (← parseType)
      if !(← acceptPunct ",") then break
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
    for (p, i) in params.toList.zipIdx do
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
    let pats := (List.range params.size).map fun i => Pattern.var s!"%a{i}"
    items := items.push (.fn name [] (declared.toList.map some) (some retTy) [.mk pats body])
    items := items.push (.unsafeFn name)
  expectPunct "}"
  pure items.toList

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
    | item :: more => pure (.pub parent item :: more)
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
      ++ defaults.map fun (i, earlier, ty) => .typeAlias (defaultName name i) earlier ty)
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
      ++ defaults.map fun (i, earlier, ty) => .typeAlias (defaultName name i) earlier ty)
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
    | .module name (some items) => if name == inherentMark then pure items else pure [.module name (some items)]
    | item => pure [item]

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
def textSyntax (base : List String) (src : String) : Except String TextSyntax := do
  let toks ← lex src
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

/-- The same from the texts themselves, each with the module it is. -/
def scopedFixities (prelude : Fixities) (texts : List (List String × String)) :
    Except String (List (List String × Fixities)) := do
  joinFixities prelude (← texts.mapM fun (base, src) => textSyntax base src)

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
      let mut e := j
      let mut braces := 0
      let mut opened := false
      while e < toks.size && !(opened && braces == 0) do
        match tok e with
        | .punct "{" => braces := braces + 1; opened := true
        | .punct "}" => braces := braces - 1
        | _ => pure ()
        e := e + 1
      let body := toks.extract i e
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
        out := out ++ expandOne body all
      i := e
    else
      out := out.push toks[i]!
      i := i + 1
  return out
where
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
            | .punct ")" => depth := depth - 1
            | .punct "]" => depth := depth - 1
            | .punct "}" => depth := depth - 1
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

/-- Parse a source text, given the fixities already in scope. Returns the items
and the fixities including those it declares. `base` keeps the identities of
this text's callable literals apart from those of a text parsed before it.
With `tables`, each module of the text has the operators the table gives it,
and the text is the module `path`. -/
def parse (fix : Fixities) (src : String) (base : Nat := 0) (records : List String := [])
    (tables : List (List String × Fixities) := []) (path : List String := [])
    (fixed : Bool := false) (packs : Nat := 0) :
    Except String (List Item × Fixities) := do
  -- (`packs`: how long lists of types are written out to; by default, as
  -- long as the longest list this text writes.)
  let toks ← lex src
  let toks := expandPacks toks (if packs == 0 then max 2 (longestList toks) else packs)
  let fix ← if tables.isEmpty then collectFixities toks fix else pure ((tables.lookup path).getD fix)
  let (items, _, local_) ← parseItems
    { toks, fix, records := collectRecords toks ++ records, base, tables, path, fixed } 0 #[]
  pure (promoteItems (items ++ local_.toList), fix)

end Glorious.Syntax
