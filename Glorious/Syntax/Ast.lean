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

/-- The reference to a field of what a reference points to: the reference, and
the fields to go through by number. -/
def focusMark : String := "%focus"

/-- How the resolver says which type is the prelude's type of arrays, whatever
a program has named its own: a list of names under this mark. -/
def arrayMark : String := "%array"

/-- The constructor an array of exactly `n` elements is taken apart by, in a
pattern `[a, b, c]`. -/
def arrayPatName (n : Nat) : String := s!"%array:{n}"

def arrayPatLen (name : String) : Option Nat :=
  if name.startsWith "%array:" then (name.drop 7).toString.toNat? else none

/-- The host operations that are unsafe, by name: a call of a foreign
function, and reading and writing memory at an address. -/
def foreignCall : String := "foreign_call"

/-- C's names for its types, and the types they are on the one target there
is: x86-64 Linux. -/
def cTypes : List (String × String) :=
  [("c_char", "i8"), ("c_schar", "i8"), ("c_uchar", "u8"), ("c_short", "i16"), ("c_ushort", "u16"),
   ("c_int", "i32"), ("c_uint", "u32"), ("c_long", "i64"), ("c_ulong", "u64"),
   ("c_longlong", "i64"), ("c_ulonglong", "u64"), ("c_size_t", "usize"), ("c_ssize_t", "isize"),
   ("c_float", "f32"), ("c_double", "f64")]

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

/-- The trait every type has of being destroyed, and its one function. The
compiler's own: where a value is let go, its type's function is called, and a
function that lets go of a value of a type it is generic in is given that
type's, as it is given any trait's functions. -/
def destroyTrait : String := "%Destroy"

def destroyFn : String := "%destroy"

/-- The name under which the type a declared type's parameter is, where it is
not written, is kept: an alias beside the declaration. `i` counts the
parameters from none. -/
def defaultName (type : String) (i : Nat) : String := s!"%default:{type}:{i}"

/-- That name for a type known by its whole name, module and all. -/
def defaultKey (global : String) (i : Nat) : String :=
  let segs := global.splitOn "::"
  "::".intercalate (segs.dropLast ++ [defaultName (segs.getLast!) i])

/-- `let name` in a pattern: `name` is a new name there, not the constant or
constructor of that name. -/
def letMark : String := "%let"

/-- Said of a block, as `spreadMark` is: it is written where a value that is
no callable is wanted, so it is run there and is its value. -/
def nowMark : String := "%now"

/-- `move x`: the value of `x`, which is then not to be used again. -/
def moveMark : String := "%move"

/-- Said of a block, where the names of what an `is` found are said: its
clauses each take one tuple, and it is given where a callable of that many
arguments is wanted, so each clause takes the arguments as its tuple's parts. -/
def spreadMark : String := "%spread"

/-- `f<A, B>(args)`: the call, and beside it the types written, as a value
written with its type is: `%inst(f(args), (A, B))`. -/
def instMark : String := "%inst"

/-- In an implementation for another name of a type: the argument of the type
that the name fixes, by its place. -/
def fixedArgName (j : Nat) : String := s!"%fixed:{j}"

/-- `<T as Trait>::Name`, the type or row the trait leaves to `T`'s
implementation under that name, is the type `%assocOf<T, Trait, Name>`. -/
def assocOfMark : String := "%assocOf"

/-- What a name given to a value stands for, apart from the type it was
written with: `let yes: Bool = Ok(());` stands for `Ok(())`. -/
partial def aliasValue : Expr → Expr
  | .call id (.name none mark) (value :: rest) =>
    if mark == ascribeMark then aliasValue value else .call id (.name none mark) (value :: rest)
  | e => e

/-- Was the name given a value written with its type? -/
def aliasTyped : Expr → Bool
  | .call _ (.name none mark) (_ :: _) => mark == ascribeMark
  | _ => false

/-- In an implementation: what one of its conditions says a type left to the
implementations of a trait is, `where I: Iterator<Item = A>`. The name says
which condition, by its place, and which type. -/
def equalArgName (condition : Nat) (name : String) : String := s!"%equal:{condition}:{name}"

/-- The parts of such a name. -/
def equalArgParts (n : String) : Option (Nat × String) :=
  if n.startsWith "%equal:" then
    match (n.drop 7).toString.splitOn ":" with
    | [k, name] => k.toNat?.map (·, name)
    | _ => none
  else none

/-- In a written row, the row parameter that stands for the rest of it. -/
def rowMark : String := "%row"

/-- A generic parameter written `e: EffectRow`: the name of the row. -/
def rowParam (p : String) : Option String :=
  if p.endsWith ": EffectRow" then some (String.ofList (p.toList.take (p.length - ": EffectRow".length))) else none

/-- An attribute, `#[name]` before a declaration or `#![name]` at the top of a
text, is kept beside the declarations as the names of a constructor's fields
are: under this mark and its name, with what it is written of and what it is
given. -/
def attrMark (name : String) : String := "%attr:" ++ name

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

/-- Every name a pattern could bind. -/
partial def patternNames : Pattern → List String
  | .var x => [x]
  | .ctor _ _ args => args.flatMap patternNames
  | .tuple args => args.flatMap patternNames
  | _ => []

mutual

/-- An expression with `x` written `y` wherever it means what it means
outside: not under a pattern, a `let` or a parameter that names `x` anew. -/
partial def renameExpr (x y : String) (bound : List String) : Expr → Expr
  | .name none z => if z == x && !bound.contains x then .name none y else .name none z
  | .call id f args => .call id (renameExpr x y bound f) (args.map (renameExpr x y bound))
  | .tailCall id f args => .tailCall id (renameExpr x y bound f) (args.map (renameExpr x y bound))
  | .tuple args => .tuple (args.map (renameExpr x y bound))
  | .proj e i => .proj (renameExpr x y bound e) i
  | .closure id clauses => .closure id (clauses.map (renameClause x y bound))
  | .handle subject arms => .handle (renameExpr x y bound subject) (arms.map (renameClause x y bound))
  | .labelScope l body => .labelScope l (renameStmts x y bound body)
  | .ref uniq z => .ref uniq (if z == x && !bound.contains x then y else z)
  | .deref e => .deref (renameExpr x y bound e)
  | .reborrow uniq e => .reborrow uniq (renameExpr x y bound e)
  | .refField id uniq z path star =>
    .refField id uniq (if z == x && !bound.contains x then y else z) path star
  | .fieldOf id e name => .fieldOf id (renameExpr x y bound e) name
  | e => e

partial def renameClause (x y : String) (bound : List String) : Clause → Clause
  | .mk pats body => .mk pats (renameStmts x y (pats.flatMap patternNames ++ bound) body)

partial def renameStmts (x y : String) (bound : List String) : List Stmt → List Stmt
  | [] => []
  | .let_ pat value :: rest =>
    .let_ pat (renameExpr x y bound value) :: renameStmts x y (patternNames pat ++ bound) rest
  | .letMut z value :: rest =>
    .letMut z (renameExpr x y bound value) :: renameStmts x y (z :: bound) rest
  | .expr e :: rest => .expr (renameExpr x y bound e) :: renameStmts x y bound rest
  | .defer e :: rest => .defer (renameExpr x y bound e) :: renameStmts x y bound rest
  | .located line col s :: rest =>
    match renameStmts x y bound (s :: rest) with
    | first :: more => .located line col first :: more
    | [] => []
  | .assign target value :: rest =>
    .assign (renameExpr x y bound target) (renameExpr x y bound value) :: renameStmts x y bound rest

end

/-- A pattern with `Self` written out as the type an implementation is for. -/
partial def selfPattern (self : String) : Pattern → Pattern
  | .ctor name qual args =>
    .ctor (if name == "Self" then self else name) (if qual == some "Self" then some self else qual)
      (args.map (selfPattern self))
  | .tuple args => .tuple (args.map (selfPattern self))
  | p => p

mutual

/-- An expression with `Self` written out as the type an implementation is
for: `Self::f`, `Self { .. }` and `Self(..)`. In an implementation of a trait
`Self::f(..)` is the trait's function for that type, `<Self as Trait>::f(..)`. -/
partial def selfExpr (self : String) (trait : Option (String × Expr)) : Expr → Expr
  | .name qual z =>
    .name (if qual == some "Self" then some ((trait.map (·.1)).getD self) else qual)
      (if z == "Self" then self else z)
  | .call id f args =>
    let args := args.map (selfExpr self trait)
    match f, trait with
    | .name (some "Self") z, some (tr, at_) =>
      .call 0 (.name none instMark) [.call id (.name (some tr) z) args, at_]
    | _, _ => .call id (selfExpr self trait f) args
  | .tailCall id f args => .tailCall id (selfExpr self trait f) (args.map (selfExpr self trait))
  | .tuple args => .tuple (args.map (selfExpr self trait))
  | .proj e i => .proj (selfExpr self trait e) i
  | .closure id clauses => .closure id (clauses.map (selfClause self trait))
  | .handle subject arms =>
    .handle (selfExpr self trait subject) (arms.map (selfClause self trait))
  | .labelScope l body => .labelScope l (body.map (selfStmt self trait))
  | .deref e => .deref (selfExpr self trait e)
  | .reborrow uniq e => .reborrow uniq (selfExpr self trait e)
  | .fieldOf id e name => .fieldOf id (selfExpr self trait e) name
  | e => e

partial def selfClause (self : String) (trait : Option (String × Expr)) : Clause → Clause
  | .mk pats body => .mk (pats.map (selfPattern self)) (body.map (selfStmt self trait))

partial def selfStmt (self : String) (trait : Option (String × Expr)) : Stmt → Stmt
  | .let_ pat value => .let_ (selfPattern self pat) (selfExpr self trait value)
  | .letMut z value => .letMut z (selfExpr self trait value)
  | .expr e => .expr (selfExpr self trait e)
  | .defer e => .defer (selfExpr self trait e)
  | .located line col s => .located line col (selfStmt self trait s)
  | .assign target value => .assign (selfExpr self trait target) (selfExpr self trait value)

end


/-- `&value` and `&mut value` where the value has no name. -/
def borrowMark : String := "%borrow"
def borrowMutMark : String := "%borrow_mut"

mutual

/-- A value that is borrowed where it is made, `&f(x)`, is given a name first:
the statement it is in is preceded by the `let` that binds it, and what was
written is a borrow of that name. The value then lasts to the end of the
block the statement is in. -/
partial def nameBorrows : Expr → Expr × List Stmt
  | .call id f args =>
    match f, args with
    | .name none mark, [e] =>
      if mark == borrowMark || mark == borrowMutMark then
        let (e, before) := nameBorrows e
        let x := s!"borrowed%{id}"
        let uniq := mark == borrowMutMark
        (.ref uniq x, before ++ [if uniq then Stmt.letMut x e else .let_ (.var x) e])
      else
        let (e, before) := nameBorrows e
        (.call id f [e], before)
    | _, _ =>
      let (f, before) := nameBorrows f
      let parts := args.map nameBorrows
      (.call id f (parts.map (·.1)), before ++ parts.flatMap (·.2))
  | .tailCall id f args =>
    let (f, before) := nameBorrows f
    let parts := args.map nameBorrows
    (.tailCall id f (parts.map (·.1)), before ++ parts.flatMap (·.2))
  | .tuple args =>
    let parts := args.map nameBorrows
    (.tuple (parts.map (·.1)), parts.flatMap (·.2))
  | .proj e i => let (e, before) := nameBorrows e; (.proj e i, before)
  | .deref e => let (e, before) := nameBorrows e; (.deref e, before)
  | .reborrow uniq e => let (e, before) := nameBorrows e; (.reborrow uniq e, before)
  | .fieldOf id e name => let (e, before) := nameBorrows e; (.fieldOf id e name, before)
  | .closure id clauses => (.closure id (clauses.map nameBorrowsClause), [])
  | .handle subject arms =>
    -- What is handled is run under the handler: so is what it borrows.
    let (subject, before) := nameBorrows subject
    let subject := if before.isEmpty then subject else .labelScope "%block" (before ++ [.expr subject])
    (.handle subject (arms.map nameBorrowsClause), [])
  | .labelScope l body => (.labelScope l (nameBorrowsStmts body), [])
  | e => (e, [])

partial def nameBorrowsClause : Clause → Clause
  | .mk pats body => .mk pats (nameBorrowsStmts body)

partial def nameBorrowsStmt : Stmt → List Stmt
  | .let_ pat e => let (e, before) := nameBorrows e; before ++ [.let_ pat e]
  | .letMut x e => let (e, before) := nameBorrows e; before ++ [.letMut x e]
  | .expr e => let (e, before) := nameBorrows e; before ++ [.expr e]
  | .defer e => let (e, before) := nameBorrows e; before ++ [.defer e]
  | .assign target e =>
    let (target, first) := nameBorrows target
    let (e, second) := nameBorrows e
    first ++ second ++ [.assign target e]
  | .located line col s =>
    match (nameBorrowsStmt s).reverse with
    | last :: before => before.reverse ++ [.located line col last]
    | [] => []

partial def nameBorrowsStmts (body : List Stmt) : List Stmt :=
  body.flatMap nameBorrowsStmt

end

/-- How a name is used in what follows where it is bound: borrowed with `&`,
changed or borrowed with `&mut`, a field of it borrowed, bound again. -/
structure NameUse where
  shared : Bool := false
  changed : Bool := false
  fielded : Bool := false
  rebound : Bool := false
  /-- Its value is used where it is bound: in no callable written there. -/
  valued : Bool := false
  /-- Its value is used in a callable, which may run later, again or never. -/
  valuedInside : Bool := false
  deriving Inhabited

def NameUse.or (a b : NameUse) : NameUse :=
  ⟨a.shared || b.shared, a.changed || b.changed, a.fielded || b.fielded, a.rebound || b.rebound,
    a.valued || b.valued, a.valuedInside || b.valuedInside⟩

/-- What a callable's uses are to the code it is written in. -/
def NameUse.inside (u : NameUse) : NameUse :=
  { u with valued := false, valuedInside := u.valued || u.valuedInside }

/-- The variable a place that is assigned to is a place of, if it is one of a
variable's own and not of what a reference points to. -/
partial def placeRoot : Expr → Option String
  | .name none x => some x
  | .fieldOf _ e _ => placeRoot e
  | .proj e _ => placeRoot e
  | _ => none

mutual

partial def nameUseExpr (x : String) : Expr → NameUse
  | .name none y => if y == x then { valued := true } else {}
  | .ref uniq y => if y != x then {} else if uniq then { changed := true } else { shared := true }
  | .refField _ _ y _ _ => if y == x then { fielded := true } else {}
  | .call _ f args => (f :: args).foldl (fun u e => u.or (nameUseExpr x e)) {}
  | .tailCall _ f args => (f :: args).foldl (fun u e => u.or (nameUseExpr x e)) {}
  | .tuple args => args.foldl (fun u e => u.or (nameUseExpr x e)) {}
  | .proj e _ => nameUseExpr x e
  | .deref e => nameUseExpr x e
  | .reborrow _ e => nameUseExpr x e
  | .fieldOf _ e _ => nameUseExpr x e
  | .closure _ clauses =>
    NameUse.inside (clauses.foldl (fun u c => u.or (nameUseClause x c)) ({} : NameUse))
  | .handle subject arms =>
    (NameUse.inside (arms.foldl (fun u c => u.or (nameUseClause x c)) ({} : NameUse))).or
      (nameUseExpr x subject)
  | .labelScope _ body => nameUseStmts x body
  | _ => {}

partial def nameUseClause (x : String) : Clause → NameUse
  | .mk pats body =>
    let u := nameUseStmts x body
    if (pats.flatMap patternNames).contains x then { u with rebound := true } else u

partial def nameUseStmts (x : String) (body : List Stmt) : NameUse :=
  body.foldl (fun u s => u.or (nameUseStmt x s)) {}

partial def nameUseStmt (x : String) : Stmt → NameUse
  | .let_ pat e =>
    let u := nameUseExpr x e
    if (patternNames pat).contains x then { u with rebound := true } else u
  | .letMut y e =>
    let u := nameUseExpr x e
    if y == x then { u with rebound := true } else u
  | .expr e => nameUseExpr x e
  | .defer e => nameUseExpr x e
  | .located _ _ s => nameUseStmt x s
  | .assign target e =>
    let u := (nameUseExpr x target).or (nameUseExpr x e)
    if placeRoot target == some x then { u with changed := true } else u

end

mutual

/-- Going through an expression in the order it is evaluated: is the name
borrowed once its value has been used? `seen` is whether the value has been
used so far; what comes back is whether it has by the end, and whether a
borrow came after. A callable that borrows the name counts as coming after:
when it runs is not known here. -/
partial def borrowAfterValue (x : String) (seen : Bool) : Expr → Bool × Bool
  | .name none y => (seen || y == x, false)
  | .ref _ y => (seen, seen && y == x)
  | .refField _ _ y _ _ => (seen, seen && y == x)
  | .call _ f args => borrowAfterValues x seen (f :: args)
  | .tailCall _ f args => borrowAfterValues x seen (f :: args)
  | .tuple args => borrowAfterValues x seen args
  | .proj e _ => borrowAfterValue x seen e
  | .deref e => borrowAfterValue x seen e
  | .reborrow _ e => borrowAfterValue x seen e
  | .fieldOf _ e _ => borrowAfterValue x seen e
  | .closure id clauses =>
    -- (One that uses the value may do so whenever it runs: from here on.)
    let u := nameUseExpr x (.closure id clauses)
    (seen || u.valuedInside, u.shared || u.changed || u.fielded)
  | .handle subject arms =>
    let (seen, bad) := borrowAfterValue x seen subject
    let u := arms.foldl (fun u c => u.or (nameUseClause x c)) ({} : NameUse)
    (seen || u.valued || u.valuedInside, bad || u.shared || u.changed || u.fielded)
  | .labelScope _ body =>
    body.foldl (fun (seen, bad) s =>
      let (seen', bad') := borrowAfterValueStmt x seen s
      (seen', bad || bad')) (seen, false)
  | _ => (seen, false)

partial def borrowAfterValues (x : String) (seen : Bool) (es : List Expr) : Bool × Bool :=
  es.foldl (fun (seen, bad) e =>
    let (seen', bad') := borrowAfterValue x seen e
    (seen', bad || bad')) (seen, false)

partial def borrowAfterValueStmt (x : String) (seen : Bool) : Stmt → Bool × Bool
  | .let_ _ e => borrowAfterValue x seen e
  | .letMut _ e => borrowAfterValue x seen e
  | .expr e => borrowAfterValue x seen e
  | .defer e =>
    -- A cleanup runs last of all: what it borrows it borrows after any use
    -- of the value before it, and a use of the value in it comes after
    -- every borrow outside it. A block is gone through in its own order.
    match e with
    | .call _ (.closure _ [.mk [] body]) [] =>
      let (_, bad) := body.foldl (fun (seen, bad) s =>
        let (seen', bad') := borrowAfterValueStmt x seen s
        (seen', bad || bad')) (seen, false)
      (seen, bad)
    | e =>
      let (_, bad) := borrowAfterValue x seen e
      (seen, bad)
  | .located _ _ s => borrowAfterValueStmt x seen s
  | .assign target e => borrowAfterValues x seen [e, target]

end

mutual

/-- The cleanups written in an expression, at any depth, and the expression
without them. -/
partial def splitDefers : Expr → Expr × List Stmt
  | .call id f args =>
    let (f, ds) := splitDefers f
    let parts := args.map splitDefers
    (.call id f (parts.map (·.1)), ds ++ parts.flatMap (·.2))
  | .tailCall id f args =>
    let (f, ds) := splitDefers f
    let parts := args.map splitDefers
    (.tailCall id f (parts.map (·.1)), ds ++ parts.flatMap (·.2))
  | .tuple args =>
    let parts := args.map splitDefers
    (.tuple (parts.map (·.1)), parts.flatMap (·.2))
  | .proj e i => let (e, ds) := splitDefers e; (.proj e i, ds)
  | .deref e => let (e, ds) := splitDefers e; (.deref e, ds)
  | .reborrow u e => let (e, ds) := splitDefers e; (.reborrow u e, ds)
  | .fieldOf id e n => let (e, ds) := splitDefers e; (.fieldOf id e n, ds)
  | .closure id clauses =>
    let parts := clauses.map fun
      | .mk pats body => let (body, ds) := splitDefersStmts body; (Clause.mk pats body, ds)
    (.closure id (parts.map (·.1)), parts.flatMap (·.2))
  | .handle subject arms =>
    let (subject, ds) := splitDefers subject
    let parts := arms.map fun
      | .mk pats body => let (body, ds) := splitDefersStmts body; (Clause.mk pats body, ds)
    (.handle subject (parts.map (·.1)), ds ++ parts.flatMap (·.2))
  | .labelScope l body => let (body, ds) := splitDefersStmts body; (.labelScope l body, ds)
  | e => (e, [])

partial def splitDefersStmts : List Stmt → List Stmt × List Stmt
  | [] => ([], [])
  | s :: rest =>
    let (rest, more) := splitDefersStmts rest
    let rec one : Stmt → List Stmt × List Stmt
      | .defer e => ([], [.defer e])
      | .located l c s => let (kept, ds) := one s; (kept.map (.located l c), ds)
      | .let_ p e => let (e, ds) := splitDefers e; ([.let_ p e], ds)
      | .letMut y e => let (e, ds) := splitDefers e; ([.letMut y e], ds)
      | .expr e => let (e, ds) := splitDefers e; ([.expr e], ds)
      | .assign target e =>
        let (target, d1) := splitDefers target
        let (e, d2) := splitDefers e
        ([.assign target e], d1 ++ d2)
    let (kept, ds) := one s
    (kept ++ rest, ds ++ more)

end

/-- The variable that says whether what a variable held has been given away,
and the name the variable's cleanup is known by where it is one that asks. -/
def movedFlag (x : String) : String := s!"%moved:{x}"
def givenSite (x : String) : String := s!"%given:{x}"

mutual

/-- Every use of a variable's value marked: the flag is set, and then the
value read. Borrows of the variable are left as they are. -/
partial def markMoves (x : String) : Expr → Expr
  | .name none y =>
    if y == x then
      .labelScope "%block" [.assign (.name none (movedFlag x)) (.int 1), .expr (.name none x)]
    else .name none y
  | .call id f args => .call id (markMoves x f) (args.map (markMoves x))
  | .tailCall id f args => .tailCall id (markMoves x f) (args.map (markMoves x))
  | .tuple args => .tuple (args.map (markMoves x))
  | .proj e i => .proj (markMoves x e) i
  | .deref e => .deref (markMoves x e)
  | .reborrow u e => .reborrow u (markMoves x e)
  | .fieldOf id e n => .fieldOf id (markMoves x e) n
  | .closure id clauses => .closure id (clauses.map fun
      | .mk pats body => .mk pats (markMovesStmts x body))
  | .handle subject arms => .handle (markMoves x subject) (arms.map fun
      | .mk pats body => .mk pats (markMovesStmts x body))
  | .labelScope l body => .labelScope l (markMovesStmts x body)
  | e => e

partial def markMovesStmts (x : String) (body : List Stmt) : List Stmt :=
  body.map (markMovesStmt x)

partial def markMovesStmt (x : String) : Stmt → Stmt
  | .let_ p e => .let_ p (markMoves x e)
  | .letMut y e => .letMut y (markMoves x e)
  | .expr e => .expr (markMoves x e)
  | .defer e => .defer (markMoves x e)
  | .located l c s => .located l c (markMovesStmt x s)
  | .assign target e => .assign target (markMoves x e)

end

/-- Is the value a name holds used as it is, with no borrow of the name
after? Then the name gives its value away where it is used. A cleanup runs
after what follows it: one that borrows the name is a borrow after any use
of the value outside it. -/
def givenAway (x : String) (rest : List Stmt) : Bool :=
  let (outside, cleanups) := splitDefersStmts rest
  let late := cleanups.any fun d =>
    let v := nameUseStmt x d
    v.shared || v.fielded || v.changed
  let early := nameUseStmts x outside
  if late && (early.valued || early.valuedInside) then false else
  let u := nameUseStmts x rest
  let (_, bad) := rest.foldl (fun (seen, bad) s =>
    let (seen', bad') := borrowAfterValueStmt x seen s
    (seen', bad || bad')) (false, false)
  !u.changed && !u.fielded && !u.rebound && (u.valued || u.valuedInside) && !bad

/-- Is a name bound here one that what follows borrows with `&` and never
changes? It is then kept where a reference can point: as a variable is. -/
def borrowedOnly (x : String) (after : List Stmt) : Bool :=
  let u := nameUseStmts x after
  !x.startsWith "%" && u.shared && !u.changed && !u.fielded && !u.rebound

mutual

/-- A value that is given a name and then borrowed with `&` has to be
somewhere a reference can point. Where the name is never changed, borrowed
for writing or bound again, the binding is made a variable's, which is such a
place; the checker still sees no assignment to it, since there is none. -/
partial def promoteExpr : Expr → Expr
  | .call id f args => .call id (promoteExpr f) (args.map promoteExpr)
  | .tailCall id f args => .tailCall id (promoteExpr f) (args.map promoteExpr)
  | .tuple args => .tuple (args.map promoteExpr)
  | .proj e i => .proj (promoteExpr e) i
  | .closure id clauses => .closure id (clauses.map promoteClause)
  | .handle subject arms => .handle (promoteExpr subject) (arms.map promoteClause)
  | .labelScope l body => .labelScope l (promoteStmts body)
  | .deref e => .deref (promoteExpr e)
  | .reborrow uniq e => .reborrow uniq (promoteExpr e)
  | .fieldOf id e name => .fieldOf id (promoteExpr e) name
  | e => e

partial def promoteClause : Clause → Clause
  | .mk pats body =>
    let body := promoteStmts body
    let held := ((pats.flatMap patternNames).eraseDups).filter (borrowedOnly · body)
    .mk pats (held.map (fun x => Stmt.letMut x (.name none x)) ++ body)

partial def promoteStmts : List Stmt → List Stmt
  | [] => []
  | s :: rest =>
    let rest := promoteStmts rest
    let rec here : Stmt → List Stmt
      | .located line col s =>
        match here s with
        | first :: more => .located line col first :: more
        | [] => []
      | .let_ (.var x) e =>
        if borrowedOnly x rest then [.letMut x (promoteExpr e)] else [.let_ (.var x) (promoteExpr e)]
      | .let_ pat e =>
        let held := (patternNames pat).eraseDups.filter (borrowedOnly · rest)
        .let_ pat (promoteExpr e) :: held.map fun x => Stmt.letMut x (.name none x)
      | .letMut y e => [.letMut y (promoteExpr e)]
      | .expr e => [.expr (promoteExpr e)]
      | .defer e => [.defer (promoteExpr e)]
      | .assign target e => [.assign (promoteExpr target) (promoteExpr e)]
    here s ++ rest

end

/-- The same for every function of a text. -/
partial def promoteItems (items : List Item) : List Item :=
  items.map fun
    | .fn name ps annots ret clauses =>
      .fn name ps annots ret (clauses.map fun c => promoteClause (nameBorrowsClause c))
    | .pub parent item => .pub parent ((promoteItems [item]).headD item)
    | .module name (some inner) => .module name (some (promoteItems inner))
    | .impl ps tr head args context methods => .impl ps tr head args context (promoteItems methods)
    | item => item

end Glorious.Syntax
