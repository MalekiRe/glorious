/-!
# Surface syntax

What the parser produces. Nothing here is trusted: the elaborator turns it into
Core, and Core is what has a semantics.
-/

namespace Glorious.Syntax

/-- A surface pattern. A bare name is a binder unless it resolves to a
constructor or a declared constant.

A pattern written with field names, `Point { x, y: p, .. }`, leaves the parser
as `Point(%record, %field:x(x), %field:y(p), %rest)`; where the program's names
are resolved, and the declaration known, it becomes `Point(x, p)`. -/
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
  which the checker can tell the elaborator about its arguments.

  A value built by field names, `Point { y: 2, x: 1 }`, leaves the parser as
  the call `Point(%record, %field:y(2), %field:x(1))`; where the program's
  names are resolved it becomes `Point(1, 2)`, computed in the order written. -/
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

/-- `subject is Pattern` leaves the parser as the call `%is(subject, { Pattern
=> })`. Where names are resolved, and so which names of the pattern are new,
it becomes a pattern callable applied to the subject: on a match `Ok` of the
values of those names, else `Err(())`. -/
def isMark : String := "%is"

/-- The values an `is` found, under the names it found them by: `%is:a,b` is
the name of what builds them and of their type. A block that is given them
without naming them has those names. -/
def packName (names : List String) : String := "%is:" ++ ",".intercalate names

/-- The names of a pack, if this is the name of one. -/
def packNames (name : String) : Option (List String) :=
  if name.startsWith "%is:" then some (((name.drop 4).toString.splitOn ",").filter (· != "")) else none

/-- `&mut base.0`, where `base` is not a name but an expression that gives a
reference, leaves the parser's reading of an expression as the call
`%through(base, (steps), uniq)`. Where its statement is done being read, the
reference is given a name of its own first, and the borrow is through that. -/
def throughMark : String := "%through"

/-- `&mut Pattern` and `&Pattern`: what a reference points to is matched, and
the pattern's names are references to its parts. It is the pattern
`%refmut(Pattern)` or `%ref(Pattern)` until names are resolved. -/
def byRefMark (uniq : Bool) : String := if uniq then "%refmut" else "%ref"

/-- A step to a field of one of a type's several constructors, `Circle#0`:
only where a value was just found to be made by that constructor. -/
def ctorStep (ctor : String) (i : Nat) : String := s!"{ctor}#{i}"

/-- The constructor and the field of such a step, if it is one. -/
def splitCtorStep (step : String) : Option (String × Nat) :=
  match step.splitOn "#" with
  | [ctor, i] => i.toNat?.map fun i => (ctor, i)
  | _ => none

/-- The name that marks a call or a pattern as written with field names. -/
def recordMark : String := "%record"

/-- The name that stands for `..` in a pattern written with field names. -/
def restMark : String := "%rest"

/-- The name that wraps the value or pattern given for a field. -/
def fieldMark (field : String) : String := s!"%field:{field}"

/-- The field a marker names, if it is one. -/
def fieldOfMark (name : String) : Option String :=
  if name.startsWith "%field:" then some (name.drop 7).toString else none

/-- The scalar types beside `Int`. A value of each is held as an integer: an
integer type's own value, the code of a character, the bits of a floating
point number. With an integer type is the width `int_fit` is asked whether a
value fits: so many bits with a sign if positive, without one if negative.
A `u128` is held as the integer with the same 128 bits, read with a sign. -/
def scalars : List (String × Option Int) :=
  [("i8", some 8), ("i16", some 16), ("i32", some 32), ("isize", some 64), ("i128", some 128),
   ("u8", some (-8)), ("u16", some (-16)), ("u32", some (-32)), ("u64", some (-64)),
   ("usize", some (-64)), ("u128", some (-128)),
   ("f32", none), ("f64", none), ("char", none)]

def isScalar (name : String) : Bool := (scalars.lookup name).isSome

/-- `i8_of` takes an `Int` to be an `i8` as it is, and `i8_bits` gives the
`Int` an `i8` is held as; so for each scalar type. Neither does anything: they
are how the prelude says what a scalar's operations are. The type, and
whether the name is the one into it. -/
def scalarCast (name : String) : Option (String × Bool) :=
  scalars.findSome? fun (t, _) =>
    if name == t ++ "_of" then some (t, true)
    else if name == t ++ "_bits" then some (t, false)
    else none

/-- A scalar written as a pattern, `'a'` or `5u8`: its type and the integer
it is held as. It is the pattern `char_of(97)`. -/
def scalarPattern : Pattern → Option (String × Int)
  | .ctor name none [.int n] =>
    match scalarCast name with
    | some (t, true) => some (t, n)
    | _ => none
  | _ => none

/-- What the checker is told of a program's modules, which it otherwise does
not see: the module each function is written in, and for each constructor with
fields its module and which fields are `pub`. A field that is not can be read
or borrowed only in the constructor's module. -/
structure ModuleInfo where
  homes : List (String × String) := []
  fieldVis : List (String × String × List Bool) := []
  /-- The two constructors of the prelude's text, the end and a character
  before the rest, by the names they have in the whole program: for showing a
  text as text. -/
  text : Option (String × String) := none
  /-- Does the first module declare a name the prelude has? The prelude's
  own names are then not what they are without the program. -/
  shadowed : Bool := false
  /-- The functions that are `pub`. -/
  pubFns : List String := []
  /-- The types that are not `pub`, each with its module. -/
  privTypes : List (String × String) := []
  /-- For each module, the coercions that apply in it: those it declares, and
  those of functions it brings in with `use`. -/
  coercions : List (String × List String) := []

/-- How the constructors of a text are named where values are shown: no
program can write these names. -/
def textEndName : String := "%end"

/-- The statement a block written `unsafe { .. }` begins with: what follows
it in the block may name what is unsafe. -/
def unsafeMark : String := "%unsafe"

/-- Whether what a reference points to was built by a constructor, at a path
of field numbers: `%ctor_is(r, 0, 1, Some)`. The compiler writes this where a
pattern binds by reference; it reads nothing out of the cell. -/
def ctorIsMark : String := "%ctor_is"

/-- How the resolver says which type is the prelude's type of arrays, whatever
a program has named its own: a list of names under this mark. -/
def arrayMark : String := "%array"

/-- The host operations that are unsafe, by name: a call of a foreign
function, and reading and writing memory at an address. -/
def foreignCall : String := "foreign_call"

def textCharName : String := "%char"

/-- A name without the module it is in: how a value is shown. -/
def lastSegment (name : String) : String :=
  match name.splitOn "::" with
  | [] => name
  | parts => parts.getLast!

/-- The function of an implementation: `method` of `trait` for `head`. -/
def implFnName (trait head method : String) : String := s!"{trait}::{method}@{head}"

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

/-- A type with `Self` written out as the type an implementation is for. -/
partial def TypeExpr.withSelf (self : TypeExpr) : TypeExpr → TypeExpr
  | .name "Self" [] => self
  | .name x args => .name x (args.map (withSelf self))
  | .tuple args => .tuple (args.map (withSelf self))
  | .fn ps r => .fn (ps.map (withSelf self)) (withSelf self r)
  | .performs r effects =>
    .performs (withSelf self r) (effects.map fun (e, args) => (e, args.map (withSelf self)))
  | .ref uniq t life => .ref uniq (withSelf self t) life
  | .never => .never
  | .hole => .hole

/-- A type as it is written in the name of a trait at its arguments,
`From<Option<Int>>`: one spelling for one type. -/
partial def TypeExpr.spell : TypeExpr → String
  | .name x [] => x
  | .name x args => s!"{x}<{", ".intercalate (args.map spell)}>"
  | .tuple args => s!"({", ".intercalate (args.map spell)})"
  | .fn ps r => s!"fn({", ".intercalate (ps.map spell)}) -> {spell r}"
  | .performs r _ => spell r
  | .ref uniq t _ => (if uniq then "&mut " else "&") ++ spell t
  | .never => "!"
  | .hole => "_"

/-- A trait at arguments, as one name: `From<Int>`. Without arguments it is
the trait's own name. -/
def traitAt (trait : String) (args : List String) : String :=
  if args.isEmpty then trait else s!"{trait}<{", ".intercalate args}>"

/-- The trait such a name is of. -/
def traitBase (name : String) : String := (name.splitOn "<").headD name

/-- The name under which an implementation keeps the `i`-th argument it gives
its trait, among what it declares. -/
def traitArgName (i : Nat) : String := s!"%traitArg{i}"

/-- `let x: Type = value` leaves the parser as `let x = %as(value, type)`,
the type written as an expression so that it can sit among expressions: see
`TypeExpr.asExpr`. The checker makes the value that type; after it the value
stands alone. -/
def ascribeMark : String := "%as"

/-- The type parameter a function written `-> !` gives: whatever is wanted. -/
def neverParam : String := "%never"

/-- What the parser wraps the functions of `impl Type { .. }` in, on their way
to the module the implementation is written in. -/
def inherentMark : String := "%inherent"

/-- A type as an expression, for the one place a type sits among expressions. -/
partial def TypeExpr.asExpr : TypeExpr → Expr
  | .name x args => .call 0 (.name none ("%ty:" ++ x)) (args.map asExpr)
  | .tuple args => .call 0 (.name none "%ty(tuple)") (args.map asExpr)
  | .fn ps r => .call 0 (.name none "%ty(fn)") (asExpr r :: ps.map asExpr)
  | .performs r effects =>
    .call 0 (.name none "%ty(performs)")
      (asExpr r :: effects.map fun (e, args) => .call 0 (.name none ("%ty:" ++ e)) (args.map asExpr))
  | .ref uniq t life =>
    .call 0 (.name none (if uniq then "%ty(refmut)" else "%ty(ref)"))
      [asExpr t, .name none ("%ty:" ++ life.getD "")]
  | .never => .name none "%ty(never)"
  | .hole => .name none "%ty(hole)"

/-- The type an expression made by `TypeExpr.asExpr` is. -/
partial def TypeExpr.ofExpr : Expr → TypeExpr
  | .call _ (.name none "%ty(tuple)") args => .tuple (args.map ofExpr)
  | .call _ (.name none "%ty(fn)") (r :: ps) => .fn (ps.map ofExpr) (ofExpr r)
  | .call _ (.name none "%ty(performs)") (r :: effects) =>
    .performs (ofExpr r) (effects.filterMap fun
      | .call _ (.name none e) args => some ((e.drop 4).toString, args.map ofExpr)
      | _ => none)
  | .call _ (.name none "%ty(refmut)") [t, .name none life] =>
    .ref true (ofExpr t) (if life == "%ty:" then none else some (life.drop 4).toString)
  | .call _ (.name none "%ty(ref)") [t, .name none life] =>
    .ref false (ofExpr t) (if life == "%ty:" then none else some (life.drop 4).toString)
  | .call _ (.name none x) args => .name (x.drop 4).toString (args.map ofExpr)
  | .name none "%ty(never)" => .never
  | _ => .hole

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
  deriving BEq

/-- Operator fixities declared by the program. -/
structure Fixities where
  infixes : List (String × Nat × Assoc) := []
  prefixes : List (String × Nat) := []
  /-- The function an operator stands for where a declaration says, `prefix 9
  - = negate`: the operator, whether as a prefix, and the function. One
  symbol can so be one function before a value and another between two. -/
  bound : List (String × Bool × String) := []

/-- The function an operator stands for: itself, unless a declaration says. -/
def Fixities.function (fix : Fixities) (op : String) (asPrefix : Bool) : String :=
  match fix.bound.find? fun (o, p, _) => o == op && p == asPrefix with
  | some (_, _, f) => f
  | none => op

/-- `subject: Trait<args, Name = Type>` written of a type parameter of a
function. The compiler's own: `F: Fn<(A, B), Output = R, Effects = {E}>`, a
callable taking those and giving that, its arguments here taken out of their
tuple; `F: RunsIn<Access, (A, B), Output = R>`, such a callable that runs in
the environment `Access` names (`E`, `&E` or `&mut E`), the access first among
`args`; `E: Environment<'e>`; and `E: Use<[lower, upper]>`, how often the
environment is used. -/
structure Bound where
  subject : String
  trait : String
  args : List TypeExpr := []
  assoc : List (String × TypeExpr) := []
  quantity : Option (Nat × Option Nat) := none
  /-- `for<'a>` before a callable bound: the lifetimes it is asked for at
  every one of. -/
  ranked : List String := []

/-- `for<'a, 'b> fn(&'a T) -> &'a T`, a callable that takes any lifetimes for
those named, is the type `%for<'a, 'b, fn(&'a T) -> &'a T>`. -/
def rankedMark : String := "%for"

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
  /-- What a trait has beside its functions: the traits a type must have to
  have it (`trait Ord: Eq`), the functions it gives a body, which an
  implementation that does not give them gets, its own type parameters
  (`trait From<T>`), and the types an implementation is to say (`type Item;`). -/
  | traitInfo (name : String) (supers : List String) (defaults : List Item)
      (params : List String) (assocs : List String)
  /-- What is written of the type parameters of the function `fn`, beside
  the function. -/
  | bounds (fn : String) (bounds : List Bound)
  /-- `pub item`: the item can be named from outside its module; with
  `pub(super)`, only from the module its module is written in. -/
  | pub (parent : Bool) (item : Item)
  /-- A function that can be named only where `unsafe` is written. -/
  | unsafeFn (name : String)
  /-- `mod name { items }`, or `mod name;` for a module in a file of its own. -/
  | module (name : String) (body : Option (List Item))
  /-- `use a::b::name;`, `use a::b::name as other;` or `use a::b::*;`: names of
  another module, to be written here without their path. `use a::{b, c}` is one
  of these for each. -/
  | import (path : List String) (rename : Option String) (glob : Bool)

end Glorious.Syntax
