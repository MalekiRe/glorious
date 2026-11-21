module

/-!
# Surface syntax

What the parser produces. Nothing here is trusted: the elaborator turns it into
Core, and Core is what has a semantics.
-/

public section

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
  deriving Inhabited, Hashable

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

deriving instance Hashable for Expr, Stmt, Clause

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
  -- (A constant's function is said as the constant, or as the block.)
  let said := match name.splitOn "$const" with
    | [bare, ""] =>
      if ((bare.splitOn "::").getLastD bare).startsWith "const%" then "a `const { .. }` block (worked out at compile time, from constants and functions alone)"
      else s!"the constant `{bare}`"
    | _ => s!"`{name}`"
  if hasPosition msg then
    match msg.splitOn ": " with
    | pos :: rest => s!"{pos}: in {said}: {": ".intercalate rest}"
    | [] => msg
  else s!"in {said}: {msg}"

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

def isScalar (name : String) : Bool :=
  -- (Asked of every type name there is: told by its first letter before the
  -- table is looked through.)
  match name.front with
  | 'i' | 'u' | 'f' | 'c' => (scalars.lookup name).isSome
  | _ => false

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
  /-- `value.f(a)` where `f` is a function in scope and also the function of
  some type's own: the call and those, by their names in the whole program.
  The checker chooses the type's own where the value is of that type and the
  function in scope does not fit it. -/
  dotAlts : List (Nat × List String) := []
  /-- For each module, by its key, the modules whose names it uses. -/
  unitUses : List (String × List String) := []
  deriving Hashable

/-- What the resolver writes before the items of each module but the
prelude's, with the module's key: each module is a unit of the program,
checked after those it uses (`Driver.unitsOf`). -/
def unitMark : String := "%unit"

/-- How the constructors of a text are named where values are shown: no
program can write these names. -/
def textEndName : String := "%end"

/-- The statement a block written `unsafe { .. }` begins with: what follows
it in the block may name what is unsafe. -/
def unsafeMark : String := "%unsafe"

/-- The first statement of a clause that only looks at a copy of what a
reference points to, to choose itself (`byReference`): what its patterns take
is not the clause's, and nothing of it is destroyed. -/
def observedMark : String := "%observed"

/-- What a dotted call is called on, kept marked until every function's
declaration has been seen: `value.f(a)` borrows `value` if `f` is written to
take a reference first. -/
def receiverMark : String := "%receiver"

/-- A name written through another, `Owner::NAME`, and not called, kept with
a number of its own: if it turns out to be a value a trait leaves to
implementations, it is that trait's function called with nothing. -/
def pathMark : String := "%path"

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

/-- The trait of the prelude a type that stands for a whole number has: the
number is its `VALUE`. -/
def knownTrait : String := "%prelude::Known"

/-- A type parameter of an implementation that says the implementation is
the one a type nothing decides is taken to have: `#[fallback] impl ..`. -/
def fallbackMark : String := "%fallback"

/-- The name `..` has in a tuple pattern until how many parts it stands for
is known: with the identity of the pattern's `(`. -/
def tupleRestName (id : Nat) : String := s!"%tuplerest:{id}"

def tupleRestOf (name : String) : Option Nat :=
  if name.startsWith "%tuplerest:" then (name.drop 11).toString.toNat? else none

/-- The type under which a type left to implementations is asked at types,
`F::Of<Int>`: the type it is asked of, and then those. -/
def gatMark : String := "%gat"

/-- `<T as Trait>::Name` kept as written in what an implementation says one of
its trait's types is, where `T` is one of its type parameters: answered at
each use of the implementation, once `T` is known there. -/
def projMark : String := "%proj"

/-- The implementation, as a value, of a trait with no functions: `()`,
whichever implementation it is. -/
def markerDict : String := "%marker"

/-- The name under which a name bound by the pattern of a `let` is known
where it is destroyed: the place is the statement's, which a clause's own
names are known by too when the statement is its first. -/
def letSite (x : String) : String := s!"%let:{x}"

def letSiteOf (name : String) : Option String :=
  if name.startsWith "%let:" then some (name.drop 5).toString else none

/-- Where a callable written at a statement captures `x`: the site under which
the checker says how what `x` holds is destroyed if the callable is let go
without being called. -/
def captureSite (x : String) : String := s!"%capture:{x}"

def captureSiteOf (name : String) : Option String :=
  if name.startsWith "%capture:" then some (name.drop 9).toString else none

/-- A callable with what destroys it if it is let go: `%destroyed(callable,
{ .. })`, where the block destroys what the callable captured, by its names. -/
def destroyedMark : String := "%destroyed"

/-- The head under which callables are destroyed: by giving them up. -/
def callableHead : String := "(callable)"

/-- The name an array pattern with a rest has until its clause is written
out: how many patterns come before the rest, and the identity of its `[`. -/
def restPatName (before id line col : Nat) : String := s!"%rest:{before}:{id}:{line}:{col}"

def restPatParts (name : String) : Option (Nat × Nat × Nat × Nat) :=
  if name.startsWith "%rest:" then
    match ((name.drop 6).toString.splitOn ":").map String.toNat? with
    | [some k, some id, some line, some col] => some (k, id, line, col)
    | _ => none
  else none

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
  deriving Inhabited, Hashable

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

/-- A type with each of the named parameters replaced. -/
partial def substTypeExpr (m : List (String × TypeExpr)) : TypeExpr → TypeExpr
  | .name x args =>
    match m.lookup x, args with
    | some t, [] => t
    | _, _ => .name x (args.map (substTypeExpr m))
  | .tuple args => .tuple (args.map (substTypeExpr m))
  | .fn ps r => .fn (ps.map (substTypeExpr m)) (substTypeExpr m r)
  | .performs r effects =>
    .performs (substTypeExpr m r) (effects.map fun (e, args) => (e, args.map (substTypeExpr m)))
  | .ref uniq t life =>
    -- A lifetime parameter is replaced by the lifetime it is given.
    let life := match life.bind fun l => m.lookup l with
      | some (TypeExpr.name l []) => some l
      | _ => life
    .ref uniq (substTypeExpr m t) life
  | t => t

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
def traitBase (name : String) : String :=
  -- (`Get#1<T>`: the second of two implementations of `Get` written the
  -- same for one type; see `fillDefaults`.)
  -- (Asked of every implementation for every bound: a name that has neither
  -- is itself, with nothing made.)
  if name.any fun c => c == '<' || c == '#' then (name.takeWhile fun c => c != '<' && c != '#').toString
  else name

/-- What an implementation for every type, `impl<T: Show> Print for T`, is
for, before it is written out for each type (`expandBlankets`). -/
def blanketHead : String := "(any)"

/-- The name under which a copy of such an implementation keeps the type it
is for, as what its type parameter `T` stands for in its functions. -/
def blanketName (param : String) : String := s!"%blanket:{param}"

/-- The name of the type alias that says an implementation is one of the
copies written out for each length of a list of types (`expandPacks`). -/
def packCopyName : String := "%pack"

/-- The type parameter a name made by `blanketName` is for. -/
def blanketParam (name : String) : Option String :=
  if name.startsWith "%blanket:" then some (name.drop 9).toString else none

/-- The type an implementation is for, from the name it is made with and its
arguments: see `Ty.head` in the checker for the names. -/
def selfTypeOf (head : String) (args : List TypeExpr) : TypeExpr :=
  if head.startsWith "(tuple" then .tuple args
  else if head.startsWith "(fn" then .fn args.dropLast (args.getLast?.getD (.tuple []))
  else if head == "(&mut)" then .ref true (args.headD (.tuple [])) none
  else if head == "(&)" then .ref false (args.headD (.tuple [])) none
  else .name head args

/-- The name as it was written: without the number a second implementation
written the same was given. -/
def traitShown (name : String) : String :=
  let whole := (name.splitOn "<").headD name
  traitBase name ++ (name.drop whole.length).toString

/-- The name under which an implementation keeps the `i`-th argument it gives
its trait, among what it declares. -/
def traitArgName (i : Nat) : String := s!"%traitArg{i}"

/-- `let x: Type = value` leaves the parser as `let x = %as(value, type)`,
the type written as an expression so that it can sit among expressions: see
`TypeExpr.asExpr`. The checker makes the value that type; after it the value
stands alone. -/
def ascribeMark : String := "%as"

/-- Said of a constant's value, `const NAME: T = value;`: worked out once, at
compile time, by a function of its own (`constFnName`, `NAME$const`), whose result is then
what every use of the name reads. -/
def comptimeMark : String := "%comptime"

/-- The function that works out the constant `name` at compile time. -/
def constFnName (name : String) : String := name ++ "$const"

/-- Is this the function of a constant? -/
def isConstFn (name : String) : Bool := name.endsWith "$const"

/-- The trait every type has of being destroyed, and its one function. The
compiler's own: where a value is let go, its type's function is called, and a
function that lets go of a value of a type it is generic in is given that
type's, as it is given any trait's functions. -/
def destroyTrait : String := "%Destroy"

/-- The value a scalar's name makes of an integer. -/
def scalarValue (name : String) (n : Int) : Expr := .call 0 (.name none name) [.int n]

/-- A text as a value: its characters, one after another. -/
def textValue (codes : List Nat) : Expr :=
  codes.foldr (fun (c : Nat) rest =>
      .call 0 (.name (some "%prelude::Str") "StrChar") [scalarValue "char_of" (c : Int), rest])
    (.name (some "%prelude::Str") "StrEnd")

/-- `self_name()` in an implementation for every type: in its copy for each
type, the type's name, as a text (what Rust's `type_name::<Self>()` names
the type by, without its path). -/
def selfNameFn : String := "self_name"

/-- The prelude's trait of a type's size and alignment, whose implementation
for every type is written out for each with `self_size()` and `self_align()`
its own (`expandBlankets`). -/
def layoutTrait : String := "Layout"

/-- The prelude's trait of a type with one runtime representation, no
payload and no finalizer (the specification's `nil_represented`): written
out for each type that is (`writeLayouts`). -/
def nilTrait : String := "NilRepresented"

def destroyFn : String := "%destroy"

/-- The name under which the type a declared type's parameter is, where it is
not written, is kept: an alias beside the declaration. `i` counts the
parameters from none. -/
def defaultName (type : String) (i : Nat) : String := s!"%default:{type}:{i}"

/-- That name for a type known by its whole name, module and all. -/
def defaultKey (global : String) (i : Nat) : String :=
  let segs := global.splitOn "::"
  "::".intercalate (segs.dropLast ++ [defaultName (segs.getLast!) i])

/-- The name under which a declared type's last parameter, written `..T`,
is kept as taking the rest of the arguments as one tuple: an alias beside
the declaration whose body is the parameter's place. -/
def variadicName (type : String) : String := s!"%variadic:{type}"

def variadicKey (global : String) : String :=
  let segs := global.splitOn "::"
  "::".intercalate (segs.dropLast ++ [variadicName (segs.getLast!)])

/-- What a parse of type parameters marks `..T` with, among the defaults. -/
def variadicMark : String := "%variadic"

/-- `let name` in a pattern: `name` is a new name there, not the constant or
constructor of that name. -/
def letMark : String := "%let"

/-- `mut name` in a pattern: what it binds is a variable, as `let mut` makes
one (`unmutItems`). -/
def mutPatMark : String := "%mut"

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

/-- The name under which an implementation keeps an argument its condition
gives a trait: `where R: Get<T>` keeps `T` as the first of its condition's. -/
def ctxArgName (condition i : Nat) : String := s!"%ctx:{condition}:{i}"

/-- And the type a condition is of, where that is not one of the
implementation's type parameters: `where (A, B): Apart`. -/
def ctxSubjectName (condition : Nat) : String := s!"%ctxOf:{condition}"

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
  /-- Lifetimes of its own, `read<'a>(Path<'a>)`: each performance has its
  own. -/
  lifetimes : List String := []

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
  deriving BEq

/-- The function an operator stands for: itself, unless a declaration says. -/
def Fixities.function (fix : Fixities) (op : String) (asPrefix : Bool) : String :=
  match fix.bound.find? fun (o, p, _) => o == op && p == asPrefix with
  | some (_, _, f) => f
  | none => op

/-- What a trait's function gives, and the type parameters of its own. -/
def methodGenerics (ret : Option TypeExpr) : Option TypeExpr × List String :=
  match ret with
  | some (.name mark (inner :: generics)) =>
    if mark == "%generic" then
      (some inner, generics.filterMap fun
        | .name g [] => some g
        | _ => none)
    else (ret, [])
  | _ => (ret, [])

def withMethodGenerics (ret : Option TypeExpr) (generics : List String) : Option TypeExpr :=
  if generics.isEmpty then ret
  else some (.name "%generic" ((ret.getD (.tuple [])) :: generics.map fun g => .name g []))

/-- A whole number as a type, for the length of a `[T; N]`: its bits from the
lowest, `B1<B0<B1<Z>>>` for five. Each number is one type. -/
partial def numberType : Nat → TypeExpr
  | 0 => .name "%prelude::Z" []
  | n => .name (if n % 2 == 0 then "%prelude::B0" else "%prelude::B1") [numberType (n / 2)]

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

/-- How often an implementation's functions use a value of its type parameter
`p`, `where T: Use<[lower, upper]>`, kept among its items. -/
def useMark (p : String) (lower : Nat) (upper : Option Nat) : String :=
  s!"%use:{p}:{lower}:{(upper.map toString).getD "*"}"

/-- What `useMark` says. -/
def useMarked (name : String) : Option (String × Nat × Option Nat) :=
  match name.splitOn ":" with
  | ["%use", p, lo, hi] => lo.toNat?.map fun lo => (p, lo, hi.toNat?)
  | _ => none

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

deriving instance Hashable for OpDecl, Bound, Item

/-! ## Rewriting a program

Most passes over a program change one kind of expression, statement or
pattern and rebuild everything else as it was. `Rewrite` is that rebuilding,
once: each hook says what a node is written as, given the rewrite to use
inside it (`Go`), or none to have it rebuilt from its parts. -/

/-- The rewrite, inside a node a hook writes. -/
structure Go where
  ex : Expr → Expr
  st : Stmt → Stmt
  stmts : List Stmt → List Stmt
  clause : Clause → Clause

instance : Inhabited Go := ⟨⟨id, id, id, id⟩⟩

/-- What a rewrite changes. -/
structure Rewrite where
  onExpr : Go → Expr → Option Expr := fun _ _ => none
  /-- A block's statements from the first on. -/
  onStmts : Go → List Stmt → Option (List Stmt) := fun _ _ => none
  onStmt : Go → Stmt → Option Stmt := fun _ _ => none
  onClause : Go → Clause → Option Clause := fun _ _ => none
  onPat : Pattern → Pattern := id

mutual

/-- An expression rewritten. -/
partial def Rewrite.ex (r : Rewrite) (e : Expr) : Expr :=
  match r.onExpr r.go e with
  | some e => e
  | none =>
    match e with
    | .call i f args => .call i (r.ex f) (args.map r.ex)
    | .tailCall i f args => .tailCall i (r.ex f) (args.map r.ex)
    | .tuple args => .tuple (args.map r.ex)
    | .proj e n => .proj (r.ex e) n
    | .closure i clauses => .closure i (clauses.map r.clause)
    | .handle subject arms => .handle (r.ex subject) (arms.map r.clause)
    | .labelScope l body => .labelScope l (r.stmts body)
    | .deref e => .deref (r.ex e)
    | .reborrow uniq e => .reborrow uniq (r.ex e)
    | .fieldOf i e name => .fieldOf i (r.ex e) name
    | e => e

/-- A clause rewritten. -/
partial def Rewrite.clause (r : Rewrite) (c : Clause) : Clause :=
  match r.onClause r.go c with
  | some c => c
  | none =>
    match c with
    | .mk pats body => .mk (pats.map r.onPat) (r.stmts body)

/-- Statements rewritten. -/
partial def Rewrite.stmts (r : Rewrite) (ss : List Stmt) : List Stmt :=
  match r.onStmts r.go ss with
  | some ss => ss
  | none =>
    match ss with
    | [] => []
    | s :: rest => r.st s :: r.stmts rest

/-- A statement rewritten. -/
partial def Rewrite.st (r : Rewrite) (s : Stmt) : Stmt :=
  match r.onStmt r.go s with
  | some s => s
  | none =>
    match s with
    | .let_ pat value => .let_ (r.onPat pat) (r.ex value)
    | .expr e => .expr (r.ex e)
    | .defer e => .defer (r.ex e)
    | .letMut x value => .letMut x (r.ex value)
    | .assign target value => .assign (r.ex target) (r.ex value)
    | .located line col s => .located line col (r.st s)

/-- What a hook rewrites inside a node with. -/
partial def Rewrite.go (r : Rewrite) : Go := ⟨r.ex, r.st, r.stmts, r.clause⟩

end

/-- An expression with each expression directly inside it made by `fe`, and
each block inside it (with the patterns of its clause) by `fb`. -/
def Expr.traverse {m : Type → Type} [Monad m] (fe : Expr → m Expr)
    (fb : List Pattern → List Stmt → m (List Stmt)) : Expr → m Expr
  | .call i g args => do pure (.call i (← fe g) (← args.mapM fe))
  | .tailCall i g args => do pure (.tailCall i (← fe g) (← args.mapM fe))
  | .tuple args => .tuple <$> args.mapM fe
  | .proj e n => (.proj · n) <$> fe e
  | .deref e => .deref <$> fe e
  | .reborrow u e => .reborrow u <$> fe e
  | .fieldOf i e n => (.fieldOf i · n) <$> fe e
  | .closure i clauses => .closure i <$> clauses.mapM fun | .mk ps b => .mk ps <$> fb ps b
  | .handle s arms => do pure (.handle (← fe s) (← arms.mapM fun | .mk ps b => .mk ps <$> fb ps b))
  | .labelScope l b => .labelScope l <$> fb [] b
  | e => pure e

/-- A statement with each expression in it made by `fe`, in order. -/
def Stmt.traverse {m : Type → Type} [Monad m] (fe : Expr → m Expr) : Stmt → m Stmt
  | .let_ p v => .let_ p <$> fe v
  | .expr e => .expr <$> fe e
  | .defer e => .defer <$> fe e
  | .letMut x v => .letMut x <$> fe v
  | .assign t v => do pure (.assign (← fe t) (← fe v))
  | .located l c s => .located l c <$> s.traverse fe

/-- Every function of a program with its clauses made by `f`: in
implementations, traits' defaults and modules too. -/
partial def Item.mapClauses (f : Clause → Clause) : Item → Item
  | .fn name ps annots ret clauses => .fn name ps annots ret (clauses.map f)
  | .impl ps tr head args context methods => .impl ps tr head args context (methods.map (·.mapClauses f))
  | .traitInfo n supers defaults params assocs => .traitInfo n supers (defaults.map (·.mapClauses f)) params assocs
  | .module name (some body) => .module name (some (body.map (·.mapClauses f)))
  | .pub parent item => .pub parent (item.mapClauses f)
  | item => item

/-- A program rewritten. -/
def Rewrite.items (r : Rewrite) (items : List Item) : List Item :=
  items.map (·.mapClauses r.clause)

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
  | .ref uniq z => .ref uniq (if z == x && !bound.contains x then y else z)
  | .refField id uniq z path star =>
    .refField id uniq (if z == x && !bound.contains x then y else z) path star
  | e => Id.run (e.traverse (pure <| renameExpr x y bound ·)
      fun ps b => pure (renameStmts x y (ps.flatMap patternNames ++ bound) b))

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

/-- `Self` written out as the type an implementation is for: `Self::f`,
`Self { .. }` and `Self(..)`. In an implementation of a trait `Self::f(..)`
is the trait's function for that type, `<Self as Trait>::f(..)`. -/
def selfRewrite (self : String) (trait : Option (String × Expr)) : Rewrite where
  onExpr go
    | .name qual z =>
      some (.name (if qual == some "Self" then some ((trait.map (·.1)).getD self) else qual)
        (if z == "Self" then self else z))
    | .call id (.name (some "Self") z) args =>
      trait.map fun (tr, at_) => .call 0 (.name none instMark) [.call id (.name (some tr) z) (args.map go.ex), at_]
    | _ => none
  onPat := selfPattern self

def selfClause (self : String) (trait : Option (String × Expr)) : Clause → Clause := (selfRewrite self trait).clause


/-- `&value` and `&mut value` where the value has no name. -/
def borrowMark : String := "%borrow"
def borrowMutMark : String := "%borrow_mut"

mutual

/-- A value that is borrowed where it is made, `&f(x)`, is given a name first:
the statement it is in is preceded by the `let` that binds it, and what was
written is a borrow of that name. The value then lasts to the end of the
block the statement is in, or, where the statement is an expression, to
the end of the statement. -/
partial def nameBorrowsM : Expr → StateM (List Stmt) Expr
  | .call id (.name none mark) [e] => do
    let e ← nameBorrowsM e
    if mark != borrowMark && mark != borrowMutMark then return .call id (.name none mark) [e]
    let x := s!"borrowed%{id}"
    let uniq := mark == borrowMutMark
    modify (· ++ [if uniq then Stmt.letMut x e else .let_ (.var x) e])
    pure (.ref uniq x)
  | .handle subject arms => do
    -- What is handled is run under the handler: so is what it borrows.
    let (subject, before) := (nameBorrowsM subject).run []
    let subject := if before.isEmpty then subject else .labelScope "%block" (before ++ [.expr subject])
    pure (.handle subject (arms.map nameBorrowsClause))
  | e => e.traverse nameBorrowsM fun _ b => pure (nameBorrowsStmts b)

partial def nameBorrows (e : Expr) : Expr × List Stmt := (nameBorrowsM e).run []

partial def nameBorrowsClause : Clause → Clause
  | .mk pats body => .mk pats (nameBorrowsStmts body)

partial def nameBorrowsStmt : Stmt → List Stmt
  | .let_ pat e => let (e, before) := nameBorrows e; before ++ [.let_ pat e]
  | .letMut x e => let (e, before) := nameBorrows e; before ++ [.letMut x e]
  -- (Of a statement that is an expression, the values named are let go
  -- where it ends: a block of its own.)
  | .expr e =>
    let (e, before) := nameBorrows e
    if before.isEmpty then [.expr e] else [.expr (.labelScope "%block" (before ++ [.expr e]))]
  | .defer e => let (e, before) := nameBorrows e; before ++ [.defer e]
  | .assign target e =>
    let (target, first) := nameBorrows target
    let (e, second) := nameBorrows e
    first ++ second ++ [.assign target e]
  | .located line col s =>
    -- (Each `let` made where the statement is: what a value so named holds
    -- is let go where its block ends, found by that place.)
    (nameBorrowsStmt s).map fun
      | .expr (.labelScope "%block" body) => .located line col (.expr (.labelScope "%block" (body.map (.located line col))))
      | s => .located line col s

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
  /-- A part of it is read where it is, `x.f`: a look at it, as through a
  borrow, and not a use of the whole. -/
  looked : Bool := false
  deriving Inhabited

def NameUse.or (a b : NameUse) : NameUse :=
  ⟨a.shared || b.shared, a.changed || b.changed, a.fielded || b.fielded, a.rebound || b.rebound,
    a.valued || b.valued, a.valuedInside || b.valuedInside, a.looked || b.looked⟩

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
  | .refField _ uniq y _ _ => if y == x then { fielded := true, changed := uniq } else {}
  | .call _ f args => (f :: args).foldl (fun u e => u.or (nameUseExpr x e)) {}
  | .tailCall _ f args => (f :: args).foldl (fun u e => u.or (nameUseExpr x e)) {}
  | .tuple args => args.foldl (fun u e => u.or (nameUseExpr x e)) {}
  -- A part of the variable read where it is: a look at it, as through a
  -- borrow, and not a use of the whole.
  | .proj e _ => if placeRoot e == some x then { looked := true } else nameUseExpr x e
  | .deref e => nameUseExpr x e
  | .reborrow _ e => nameUseExpr x e
  | .fieldOf _ e _ => if placeRoot e == some x then { looked := true } else nameUseExpr x e
  | .closure _ clauses =>
    NameUse.inside (clauses.foldl (fun u c => u.or (nameUseClause x c)) ({} : NameUse))
  | .handle subject arms =>
    (NameUse.inside (arms.foldl (fun u c => u.or (nameUseClause x c)) ({} : NameUse))).or
      (nameUseExpr x subject)
  | .labelScope _ body => nameUseStmts x body
  | _ => {}

partial def nameUseClause (x : String) : Clause → NameUse
  | .mk pats body =>
    -- (A clause that binds the name again: what it does is of that one.)
    if (pats.flatMap patternNames).contains x then { rebound := true } else nameUseStmts x body

partial def nameUseStmts (x : String) (body : List Stmt) : NameUse :=
  -- (What follows a statement that binds the name again is of that one.)
  match body with
  | [] => {}
  | s :: rest =>
    let u := nameUseStmt x s
    if bindsAgain x s then u else u.or (nameUseStmts x rest)

/-- Is this statement itself one that binds the name again? -/
partial def bindsAgain (x : String) : Stmt → Bool
  | .let_ pat _ => (patternNames pat).contains x
  | .letMut y _ => y == x
  | .located _ _ s => bindsAgain x s
  | _ => false

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
    -- (The variable written, or a part of it, is not its value used.)
    if placeRoot target == some x then { nameUseExpr x e with changed := true }
    else (nameUseExpr x target).or (nameUseExpr x e)

end

/-- The variable that says whether what a variable held has been given away,
and the name the variable's cleanup is known by where it is one that asks. -/
def movedFlag (x : String) : String := s!"%moved:{x}"
def givenSite (x : String) : String := s!"%given:{x}"

/-- The place of a field read by name before the type it is read from was
known: found from the name once the type is. -/
def partUnknown : Nat := 1000000000

/-- The name a part of a name's value is destroyed under, where the part is
never read: the name and the part's place among the fields. -/
def partName (x : String) (i : Nat) : String := s!"{x}.%{i}"

/-- The name and the place such a name is of. -/
def partOf (name : String) : Option (String × Nat) :=
  match name.splitOn ".%" with
  | [x, i] => i.toNat?.map (x, ·)
  | _ => none

/-- Is a name bound here one that what follows borrows with `&` and never
changes? It is then kept where a reference can point: as a variable is. -/
def borrowedOnly (x : String) (after : List Stmt) : Bool :=
  let u := nameUseStmts x after
  -- (A field of it may be borrowed too: it is kept where a reference can
  -- point either way.)
  !x.startsWith "%" && u.shared && !u.changed

/-- Is a name bound here one of which what follows borrows a field with `&`,
and never changes? If what it is bound to is a value and not a reference, it
is kept where a reference can point, as one borrowed whole is. -/
def fieldBorrowedOnly (x : String) (after : List Stmt) : Bool :=
  let u := nameUseStmts x after
  !x.startsWith "%" && u.fielded && !u.changed

/-- The label `@f` a function is also known by: the last part of its name,
`f` of `m::f` or `T::f`, and of a function written in a block, `f%12`. -/
def labelShort (name : String) : String :=
  let s := lastSegment name
  match s.splitOn "%" with
  | p :: _ :: _ => if p.isEmpty then s else p
  | _ => s

/-- May what an expression gives be a value and not a reference, by how it is
written: a tuple, what a call gives, or something given a type that is not a
reference's? (A call can give a reference. A name bound to one and kept
where a reference can point holds that reference, and a field is then
borrowed through it: the checker tells the two apart by the type.) -/
def valueLike : Expr → Bool
  | .tuple (_ :: _) => true
  -- (A whole number, or a name written with a capital: a constructor without
  -- fields or a constant.)
  | .int _ => true
  | .name _ x => (lastSegment x).front.isUpper
  | .call _ (.name none mark) [_, ty] =>
    mark != ascribeMark || (match TypeExpr.ofExpr ty with
      | .ref _ _ _ => false
      | _ => true)
  | .call _ _ _ => true
  | _ => false

/-- `&list[i]` of a parameter `list` written with a reference's type: the
element through `list`, as `element_at(list, i)`. -/
def throughParamsRewrite (refs : List String) : Rewrite where
  onExpr go
    | .call id f args =>
      let args := args.map go.ex
      let args := match f, args with
        | .name _ "element_at", [.ref false x, i] => if refs.contains x then [Expr.name none x, i] else args
        | .name _ "place_at", [i, .ref true x] => if refs.contains x then [i, Expr.name none x] else args
        | _, _ => args
      some (.call id (go.ex f) args)
    | _ => none

/-- The names a clause binds that are only borrowed in it, or (of `values`,
the parameters whose written types are not references') only borrowed by
field, each kept in a variable of the same name where the clause starts. -/
def promoteHeld (values : List String) : Clause → Clause
  | .mk pats body =>
    let held := ((pats.flatMap patternNames).eraseDups).filter fun x =>
      borrowedOnly x body || (values.contains x && fieldBorrowedOnly x body)
    -- (Each is where the clause's first statement is: what the variable
    -- holds when the clause is done is destroyed by that place's name.)
    let placed := fun (s : Stmt) => match body with
      | .located line col _ :: _ => Stmt.located line col s
      | _ => s
    .mk pats (held.map (fun x => placed (.letMut x (.name none x))) ++ body)

/-- A value that is given a name and then borrowed with `&` has to be
somewhere a reference can point. Where the name is never changed, borrowed
for writing or bound again, the binding is made a variable's, which is such a
place; the checker still sees no assignment to it, since there is none. -/
def promoteRewrite : Rewrite where
  onExpr go
    | .call id f args =>
      -- (`if(e is Some(n)) { .. &n .. }`: the names an `is` among the
      -- arguments binds are the blocks' after it, and are kept where a
      -- reference can point as a clause's are.)
      let isNames := fun (e : Expr) => match e with
        | .call _ (.name none m) [_, .closure _ [.mk [pat] []]] =>
          if m == isMark then patternNames pat else []
        | .closure _ [.mk [] [.expr (.call _ (.name none m) [_, .closure _ [.mk [pat] []]])]] =>
          if m == isMark then patternNames pat else []
        | _ => []
      let named := args.flatMap isNames
      let args := args.map go.ex
      let args := if named.isEmpty then args else args.map fun
        | .closure cid [.mk [] body] =>
          let held := named.eraseDups.filter (borrowedOnly · body)
          let placed := fun (s : Stmt) => match body with
            | .located line col _ :: _ => Stmt.located line col s
            | _ => s
          .closure cid [.mk [] (held.map (fun x => placed (.letMut x (.name none x))) ++ body)]
        | a => a
      some (.call id (go.ex f) args)
    | _ => none
  onClause go c := some (promoteHeld [] (match c with | .mk pats body => .mk pats (go.stmts body)))
  onStmts go
    | [] => none
    | s :: rest =>
      let rest := go.stmts rest
      let rec here : Stmt → List Stmt
        | .located line col s => (here s).map (.located line col)
        | .let_ (.var x) e =>
          if borrowedOnly x rest || (valueLike e && fieldBorrowedOnly x rest) then [.letMut x (go.ex e)]
          else [.let_ (.var x) (go.ex e)]
        | .let_ pat e =>
          let held := (patternNames pat).eraseDups.filter (borrowedOnly · rest)
          .let_ pat (go.ex e) :: held.map fun x => Stmt.letMut x (.name none x)
        | s => [go.st s]
      some (here s ++ rest)

/-- A clause made so (`promoteRewrite`), with `values` as its parameters
whose written types are not references'. -/
def promoteClause (values : List String) : Clause → Clause
  | .mk pats body => promoteHeld values (.mk pats (promoteRewrite.stmts body))

/-- The names `mut name` binds in a pattern, and the pattern with each a
plain name. -/
partial def unmutPat : Pattern → Pattern × List String
  | .ctor m none [.var x] => if m == mutPatMark then (.var x, [x]) else (.ctor m none [.var x], [])
  | .ctor c q args =>
    let parts := args.map unmutPat
    (.ctor c q (parts.map (·.1)), parts.flatMap (·.2))
  | .tuple args =>
    let parts := args.map unmutPat
    (.tuple (parts.map (·.1)), parts.flatMap (·.2))
  | p => (p, [])

/-- Each name a pattern binds with `mut` a variable of the same name where
what the pattern is of starts: `Some(mut n) => n = n + 1` as `Some(n) => let
mut n = n; n = n + 1`; in a `let`, after it. -/
def unmutRewrite : Rewrite where
  onClause go
    | .mk pats body =>
      let parts := pats.map unmutPat
      let names := parts.flatMap (·.2)
      if names.isEmpty then none
      else some (.mk (parts.map (·.1)) (names.map (fun x => Stmt.letMut x (.name none x)) ++ go.stmts body))
  onStmts go
    | s :: rest =>
      let rec here : Stmt → Option (List Stmt)
        | .located l c s => (here s).map (·.map (.located l c))
        | .let_ pat value =>
          let (pat, names) := unmutPat pat
          if names.isEmpty then none
          else some (.let_ pat (go.ex value) :: names.map fun x => Stmt.letMut x (.name none x))
        | _ => none
      (here s).map (· ++ go.stmts rest)
    | [] => none

def unmutItems (items : List Item) : List Item := unmutRewrite.items items

/-- A clause of a function whose parameters are written with `annots`, made
so (`promoteClause`). -/
def promoteFnClause (annots : List (Option TypeExpr)) (c : Clause) : Clause :=
  -- A parameter written with a type that is no reference's is a value.
  let values := match c with
    | .mk pats _ => (pats.zip annots).filterMap fun
      | (.var _, some (.ref _ _ _)) => none
      | (.var x, some _) => some x
      | _ => none
  -- (One written with a reference's type, `list: &[T]`: `&list[0]` is the
  -- element through that reference, not through one to it.)
  let refs := match c with
    | .mk pats _ => (pats.zip annots).filterMap fun
      | (.var x, some (.ref _ _ _)) => some x
      | _ => none
  let c := if refs.isEmpty then c else match c with
    | .mk pats body => .mk pats ((throughParamsRewrite refs).stmts body)
  promoteClause values (nameBorrowsClause c)

/-- The same for every function of a text. -/
partial def promoteItems (items : List Item) : List Item :=
  items.map fun
    | .fn name ps annots ret clauses => .fn name ps annots ret (clauses.map (promoteFnClause annots))
    | .pub parent item => .pub parent ((promoteItems [item]).headD item)
    | .module name (some inner) => .module name (some (promoteItems inner))
    | .impl ps tr head args context methods => .impl ps tr head args context (promoteItems methods)
    | item => item

end Glorious.Syntax
