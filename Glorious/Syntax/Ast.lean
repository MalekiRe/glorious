/-!
# Surface syntax

What the parser produces. Nothing here is trusted: the elaborator turns it into
Core, and Core is what has a semantics.
-/

namespace Glorious.Syntax

/-- A surface pattern. A bare name is a binder unless it resolves to a
constructor or a declared constant. -/
inductive Pattern where
  | wild
  | var (name : String)
  | int (n : Int)
  | ctor (name : String) (qual : Option String) (args : List Pattern)
  | tuple (args : List Pattern)
  deriving Inhabited

mutual

inductive Expr where
  | int (n : Int)
  /-- A variable, function, constructor, operation or constant, optionally qualified. -/
  | name (qual : Option String) (name : String)
  /-- The label `@name` as a value. -/
  | label (name : String)
  /-- A call. One written in the source has an identity that is not zero, by
  which the checker can tell the elaborator about its arguments. -/
  | call (id : Nat) (f : Expr) (args : List Expr)
  /-- `tail f(args)`. -/
  | tailCall (id : Nat) (f : Expr) (args : List Expr)
  | tuple (args : List Expr)
  /-- `e.N`. -/
  | proj (e : Expr) (idx : Nat)
  /-- A callable literal: one or more clauses. A plain block is one clause with
  no parameters. A literal written in braces has an identity that is not zero,
  by which the checker can tell the elaborator about it. -/
  | closure (id : Nat) (clauses : List Clause)
  /-- `handle subject { arms }`. -/
  | handle (subject : Expr) (arms : List Clause)
  /-- `@name { body }`. -/
  | labelScope (name : String) (body : List Stmt)
  /-- `&x` or `&mut x`: a shared or a unique reference to a mutable variable. -/
  | ref (uniq : Bool) (name : String)
  /-- `*e`: the value a reference points to. -/
  | deref (e : Expr)
  /-- `&mut *e` or `&*e`: a reference borrowed from the reference `e`. -/
  | reborrow (uniq : Bool) (e : Expr)
  /-- `&x.0` or `&mut x.left.0`: a reference to a field of what a mutable
  variable holds, or of what a reference points to, the field found by going
  through `path`, each step a field's number or its name. With `star` it was
  written `&(*x).0`, which only a reference can be. `id` tells this borrow from
  every other. -/
  | refField (id : Nat) (uniq : Bool) (name : String) (path : List String) (star : Bool)
  /-- `e.name`: the field of that name. `id` tells this read from every other. -/
  | fieldOf (id : Nat) (e : Expr) (name : String)

inductive Stmt where
  | let_ (pat : Pattern) (value : Expr)
  | expr (e : Expr)
  /-- `defer e;`: run `e` when the rest of the block is left, by any path. -/
  | defer (e : Expr)
  /-- `let mut x = e;`: a variable that can be assigned and borrowed. -/
  | letMut (name : String) (value : Expr)
  /-- `x = e;` or `*p = e;`. -/
  | assign (target : Expr) (value : Expr)
  /-- A statement together with where it starts in the source. -/
  | located (line col : Nat) (s : Stmt)

inductive Clause where
  | mk (pats : List Pattern) (body : List Stmt)

end

instance : Inhabited Expr := ⟨.int 0⟩

/-- Does a message already begin with a `line:column:` position? -/
def hasPosition (msg : String) : Bool :=
  match msg.splitOn ":" with
  | l :: c :: _ :: _ => !l.isEmpty && l.all Char.isDigit && !c.isEmpty && c.all Char.isDigit
  | _ => false

/-- Give a message a position unless it has a more precise one already. -/
def positioned (line col : Nat) (msg : String) : String :=
  if hasPosition msg then msg else s!"{line}:{col}: {msg}"

/-- Name the function a message is about, keeping its position in front. -/
def inFunction (name : String) (msg : String) : String :=
  if hasPosition msg then
    match msg.splitOn ": " with
    | pos :: rest => s!"{pos}: in `{name}`: {": ".intercalate rest}"
    | [] => msg
  else s!"in `{name}`: {msg}"

instance : Inhabited Clause := ⟨.mk [] []⟩

/-- A type as written in the source. -/
inductive TypeExpr where
  /-- A named type applied to arguments, a generic parameter, or, in a
  declaration, a bare field name whose type is to be inferred. -/
  | name (name : String) (args : List TypeExpr)
  | tuple (args : List TypeExpr)
  /-- `fn(A, B) -> R`. Its effects are inferred, unless the result says them. -/
  | fn (params : List TypeExpr) (ret : TypeExpr)
  /-- `R / {E, F<T>}`, written as the result of a callable: what it gives and
  the effects it performs, all of them. `/ {}` is a callable that performs
  nothing. -/
  | performs (ret : TypeExpr) (effects : List (String × List TypeExpr))
  /-- `&T` or `&mut T`, or with a lifetime `&'a T`, `&'a mut T`. -/
  | ref (uniq : Bool) (t : TypeExpr) (life : Option String)
  /-- `!`. -/
  | never
  /-- `_`: to be inferred. -/
  | hole
  deriving Inhabited

/-! Generic parameters are written in one list: type parameters, lifetimes
(`'a`), and the bounds on lifetimes, each kept as `'b: 'a`, which says `'b`
lasts at least as long as `'a`. -/

/-- Is this generic parameter a lifetime, or a type argument a lifetime's name? -/
def isLifetime (p : String) : Bool := p.startsWith "'" && !p.contains ':'

/-- `'b: 'a` as its two lifetimes, if this entry is a bound. -/
def lifetimeBound (p : String) : Option (String × String) :=
  if p.startsWith "'" then
    match p.splitOn ": " with
    | [longer, shorter] => some (longer, shorter)
    | _ => none
  else none

/-- A parameter list without the bounds: what a use gives arguments for. -/
def genericParams (ps : List String) : List String := ps.filter fun p => !p.contains ':'

/-- An operation of an effect. -/
structure OpDecl where
  name : String
  payload : List TypeExpr
  /-- The type the operation returns to its performer, if written. -/
  result : Option TypeExpr
  /-- Declared `-> !`: the operation never returns. -/
  terminal : Bool
  /-- How often its resumption is to be used, where written before the name:
  the fewest times and the most, none for no limit. -/
  quantity : Option (Nat × Option Nat) := none

inductive Assoc where
  | left
  | right
  | non

/-- Operator fixities declared by the program. -/
structure Fixities where
  infixes : List (String × Nat × Assoc) := []
  prefixes : List (String × Nat) := []

inductive Item where
  /-- An enum: its type parameters and its constructors with their fields. -/
  | enum (name : String) (params : List String) (ctors : List (String × List TypeExpr))
  /-- A struct with positional fields. -/
  | struct (name : String) (params : List String) (fields : List TypeExpr)
  | effect (name : String) (params : List String) (ops : List OpDecl)
  /-- A function: its type parameters, the annotation on each parameter and on
  the result where written, and its clauses. -/
  | fn (name : String) (params : List String) (annots : List (Option TypeExpr))
      (ret : Option TypeExpr) (clauses : List Clause)
  /-- `let Name = expr;`: a constructor alias or a constant. -/
  | alias (name : String) (value : Expr)
  /-- A fixity declaration; already collected before parsing. -/
  | fixity
  /-- `coerce name`: the function `name` is applied without being written, where
  a value of its parameter's type is found and one of its result's type expected. -/
  | coerce (name : String)
  /-- `trait Name { fn method(A, B) -> R; ... }`: functions a type may have.
  `Self` in a method's types is the type that has them. -/
  | trait (name : String) (methods : List (String × List TypeExpr × Option TypeExpr))
  /-- `impl<T, ...> Trait for Head<T, ...> where T: Other, ... { fn ... }`: the
  trait's functions for every type made with `Head`, on the conditions after
  `where`, each a type parameter and a trait it must have. -/
  | impl (params : List String) (trait : String) (head : String) (args : List String)
      (context : List (String × String)) (methods : List Item)
  /-- `impl Use<[lower, upper]> for Head {}`: how often a value of a declared
  type is to be used; no upper bound is `infinity`. -/
  | use (head : String) (lower : Nat) (upper : Option Nat)
  /-- The names of a constructor's fields, if it was declared with names, and
  for each field whether it is `pub`. Written out beside the declaration. -/
  | fieldNames (ctor : String) (names : List String) (pubs : List Bool)
  /-- `type Name<T> = Type;`: another way to write a type, not a new one. -/
  | typeAlias (name : String) (params : List String) (body : TypeExpr)
  /-- `pub item`: the item can be named from outside its module. -/
  | pub (item : Item)

end Glorious.Syntax
