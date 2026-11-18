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

/-- The value a scalar's name makes of an integer. -/
def scalarValue (name : String) (n : Int) : Expr := .call 0 (.name none name) [.int n]

/-- A text as a value: its characters, one after another. -/
def textValue (codes : List Nat) : Expr :=
  codes.foldr (fun (c : Nat) rest =>
      .call 0 (.name (some "%prelude::Str") "StrChar") [scalarValue "char_of" (c : Int), rest])
    (.name (some "%prelude::Str") "StrEnd")

/-- A function of the prelude that the compiler writes a literal or an index
with, whatever the program has in scope. -/
def preludeFn (name : String) : Expr := .name (some "%prelude") name

/-- `[a, b, c]` as a value: the empty array with each pushed on. The calls
have identities where they are given, so that they are known to return: an
element computed before the next is then not one that could be left
behind. -/
def arrayValue (elements : List Expr) (empty : Nat := 0) (pushes : List Nat := []) : Expr :=
  (elements.zipIdx.foldl (fun acc (e, i) => .call (pushes.getD i 0) (preludeFn "push") [acc, e])
    (.call empty (preludeFn "array_empty") []))

/-- `a[i]`, if this is one: the array and the place. -/
def indexed? : Expr → Option (Nat × Expr × Expr)
  | .call id (.name (some "%prelude") "index") [a, i] => some (id, a, i)
  | _ => none

/-- A literal other than a plain whole number, if one is next, perhaps after
a `-` already read. -/
def scalarLiteral (neg : Bool) : P (Option Expr) := do
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
partial def literalPattern : Expr → Option Pattern
  | .int n => some (.int n)
  | .call _ (.name qual name) args => (args.mapM literalPattern).map (.ctor name qual)
  | .name (some qual) name => some (.ctor name (some qual) [])
  | _ => none

/-- What a field is a field of: a named variable, a named reference written
`(*p)`, or what an expression that gives a reference points to. -/
inductive FieldRoot where
  | named (x : String) (star : Bool)
  | through (base : Expr)

/-- `root.a.0` as its root and the way to the field, if it is a field. -/
partial def fieldRoot : Expr → Option (FieldRoot × List String)
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
def fieldBorrow (id : Nat) (uniq : Bool) (root : FieldRoot) (path : List String) : Expr :=
  match root with
  | .named x star => .refField id uniq x path star
  | .through base =>
    .call id (.name none throughMark)
      [base, .tuple (path.map fun s => Expr.name none s), .int (if uniq then 1 else 0)]

/-- `&a[i]` and `&mut a[i]`: a reference to the element where it is, if `a`
is a place: a variable, a field, what a reference points to, or an element
in turn. Of anything else the element is a value with no name. -/
partial def elementBorrow (uniq : Bool) (e : Expr) : Option Expr :=
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
structure Hoist where
  lets : Array (String × Expr) := #[]
  seen : Bool := false
  bad : Bool := false

/-- Is a borrow through an expression written anywhere in this, outside the
statements of a block or a callable? -/
partial def hasThrough : Expr → Bool
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
partial def hoistExpr (h : Hoist) : Expr → Expr × Hoist
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
def hoistStmt (s : Stmt) : Option (List Stmt × Stmt) :=
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
    pure (.name assocOfMark [self, .name trait targs, .name name []])
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
    let params ← parseTypeList ")"
    let ret ← if ← acceptPunct "->" then parseResult else pure (.tuple [])
    pure (.fn params ret)
  | .ident x =>
    advance
    if x == "for" && (← isOp "<") then
      -- `for<'a> fn(&'a T) -> R`: a callable for every such lifetime.
      let lifetimes ← parseLifetimes
      return .name rankedMark (lifetimes.map (.name · []) ++ [← parseType])
    let x := "::".intercalate (← parsePathRest x)
    -- (`'_`: a lifetime left to be found, which is to say not written.)
    let args ← angledList do
      if (← peek) == .ident "'_" then
        advance
        pure none
      else some <$> parseType
    pure (.name x args.reduceOption)
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



/-- The fields of a constructor, struct or operation, if any are written. -/
def parseFields : P (List TypeExpr) := do
  if ← acceptPunct "(" then parseTypeList ")" else pure []

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
partial def restClausesOf (all : List Pattern) : List Clause → List Clause
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

def restClauses (clauses : List Clause) : List Clause :=
  restClausesOf (clauses.filterMap fun
    | .mk [p] _ => some p
    | _ => none) clauses

end Glorious.Syntax.Parse
