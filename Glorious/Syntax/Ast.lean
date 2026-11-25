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

/-- The bits a scalar type is held in, with a sign if positive (Core's
`Ty.scalar`): a float or a `char` as the bits it is held in. (An `f64`'s
bits are held as the integer with the same 64 bits read with a sign, as the
float operations give them: so it is read back from memory.) -/
def scalarBits (t : String) : Int :=
  ((scalars.lookup t).bind id).getD (if t == "f64" then 64 else -32)

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

/-- What a trait's `i`-th type parameter is where a use of the trait does not
write it (`trait Add<R = Self>`), kept among what the trait gives
implementations (`traitInfo`'s), with the parameters before it. -/
def traitParamDefaultName (i : Nat) : String := s!"%traitDefault{i}"

/-- The name of a trait's function where another trait of its module has a
function of the same name: the trait's and its own (`Debug::fmt`). -/
def sharedMethodName (trait m : String) : String := s!"{trait}::{m}"

/-- `[T]` as the parser reads it: a slice's elements, a type only behind a
reference, `&[T]` (`Modules.resolveType` makes it the prelude's
`SliceRef`). -/
def sliceMark : String := "%slice"

/-- `[a, b, c]` as a pattern of a `[T; 3]`, where literals are read with a
length their type says. -/
def fixedPatName (n : Nat) : String := s!"%fixed:{n}"

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

/-- The length of a pattern of a `[T; N]`, `fixedPatName`. -/
def fixedPatLen (name : String) : Option Nat :=
  if name.startsWith "%fixed:" then (name.drop 7).toString.toNat? else none

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

/-- A written type with each type directly in it made by `f`. -/
def TypeExpr.mapParts (f : TypeExpr → TypeExpr) : TypeExpr → TypeExpr
  | .name x args => .name x (args.map f)
  | .tuple args => .tuple (args.map f)
  | .fn ps r => .fn (ps.map f) (f r)
  | .performs r effects => .performs (f r) (effects.map fun (e, args) => (e, args.map f))
  | .ref uniq t life => .ref uniq (f t) life
  | t => t

/-- The types directly in a written type. -/
def TypeExpr.parts : TypeExpr → List TypeExpr
  | .name _ args | .tuple args => args
  | .fn ps r => ps ++ [r]
  | .performs r effects => r :: effects.flatMap (·.2)
  | .ref _ t _ => [t]
  | _ => []

/-- A type with `Self` written out as the type an implementation is for. -/
partial def TypeExpr.withSelf (self : TypeExpr) : TypeExpr → TypeExpr
  | .name "Self" [] => self
  | t => t.mapParts (withSelf self)

/-- A type with each of the named parameters replaced. -/
partial def substTypeExpr (m : List (String × TypeExpr)) : TypeExpr → TypeExpr
  | .name x [] => (m.lookup x).getD (.name x [])
  | .ref uniq t life =>
    -- A lifetime parameter is replaced by the lifetime it is given.
    let life := match life.bind fun l => m.lookup l with
      | some (TypeExpr.name l []) => some l
      | _ => life
    .ref uniq (substTypeExpr m t) life
  | t => t.mapParts (substTypeExpr m)

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

/-- The name of the type alias that says an implementation the compiler
wrote is checked only where something asks it (`reflectionsOf`). -/
def askedOnlyName : String := "%asked"

/-- The type a tuple of one or more is as its first and the tuple of the
rest, `(H, ..R)` (`Traits.consHead`, the same name). -/
def consHead : String := "%Cons"

/-- The type a tuple of one or more is as the tuple of all but its last and
its last, `(..G, X)`. -/
def snocHead : String := "%Snoc"

/-- `..P` as a callable's arguments, `Fn<(..P)>`: as many as the tuple `P`
has, of its types. -/
def spreadParams : String := "%Spread"

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
def scalarValue (name : String) (n : Int) : Expr := .call 0 (.name (some "%prelude") name) [.int n]

/-- A text written out, `"abc"`, as the parser writes it before it is
anything: its characters, one after another, as the constructors of a type
no program can name (`textItem`). Where it is checked it is a `&'static
str`, its bytes where the program has them from its start; a program that
is not checked writes it as its characters. -/
def textValue (codes : List Nat) : Expr :=
  codes.foldr (fun (c : Nat) rest =>
      .call 0 (.name (some "%prelude::%Text") textCharName) [scalarValue "char_of" (c : Int), rest])
    (.name (some "%prelude::%Text") textEndName)

/-- `self_name()` in an implementation for every type: in its copy for each
type, the type's name, as a text (what Rust's `type_name::<Self>()` names
the type by, without its path). -/
def selfNameFn : String := "self_name"

/-- The prelude's trait of a type's size and alignment, whose implementation
for every type is written out for each with `self_size()` and `self_align()`
its own (`expandBlankets`). -/
def layoutTrait : String := "Layout"

/-- The prelude's trait of a value in memory, written out for each type made
of plain data (`writeLayouts`). -/
def reprTrait : String := "Repr"

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

namespace Flat

/-- Where a node is in its body's arrays. -/
abbrev ExprId := Nat
abbrev StmtId := Nat
abbrev ClauseId := Nat

deriving instance BEq for Pattern

/-- An expression, its parts by place (`Syntax.Expr`). -/
inductive FExpr where
  | int (n : Int)
  | name (qual : Option String) (name : String)
  | label (name : String)
  | call (id : Nat) (f : ExprId) (args : Array ExprId)
  | tailCall (id : Nat) (f : ExprId) (args : Array ExprId)
  | tuple (args : Array ExprId)
  | proj (e : ExprId) (idx : Nat)
  | closure (id : Nat) (clauses : Array ClauseId)
  | handle (subject : ExprId) (arms : Array ClauseId)
  | labelScope (name : String) (body : Array StmtId)
  | ref (uniq : Bool) (name : String)
  | deref (e : ExprId)
  | reborrow (uniq : Bool) (e : ExprId)
  | refField (id : Nat) (uniq : Bool) (name : String) (path : List String) (star : Bool)
  | fieldOf (id : Nat) (e : ExprId) (name : String)
  deriving Inhabited, Hashable, BEq

/-- A statement, its parts by place (`Syntax.Stmt`). -/
inductive FStmt where
  | let_ (pat : Pattern) (value : ExprId)
  | expr (e : ExprId)
  | defer (e : ExprId)
  | letMut (name : String) (value : ExprId)
  | assign (target : ExprId) (value : ExprId)
  | located (line col : Nat) (s : StmtId)
  deriving Inhabited, Hashable, BEq

/-- A clause: its patterns, and its body's statements by place. -/
structure FClause where
  pats : List Pattern
  body : Array StmtId
  deriving Inhabited, Hashable, BEq

/-- A declaration's body: its nodes, each kind in an array of its own, and
its own clauses (`roots`). -/
structure Body where
  exprs : Array FExpr := #[]
  stmts : Array FStmt := #[]
  clauses : Array FClause := #[]
  roots : Array ClauseId := #[]
  deriving Hashable, BEq

end Flat

inductive Item where
  /-- An enum: its type parameters and its constructors with their fields. -/
  | enum (name : String) (params : List String) (ctors : List (String × List TypeExpr))
  /-- A struct with positional fields. -/
  | struct (name : String) (params : List String) (fields : List TypeExpr)
  | effect (name : String) (params : List String) (ops : List OpDecl)
  /-- A function: its type parameters, the annotation on each parameter and on
  the result where written, and its clauses, a flat body (`Flat.Body`). -/
  | fn (name : String) (params : List String) (annots : List (Option TypeExpr))
      (ret : Option TypeExpr) (body : Flat.Body)
  /-- `let Name = expr;`: a constructor alias or a constant, its value in a
  body of its own. -/
  | alias (name : String) (body : Flat.Body) (value : Flat.ExprId)
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

/-- The items without the functions declared `#[intrinsic]`: a call of one is
the machine's operation, and its declaration is the checker's alone. -/
def Item.withoutIntrinsics (items : List Item) : List Item :=
  let own := items.filterMap fun
    | .fieldNames mark [n] _ => if mark == attrMark "intrinsic" then some n else none
    | _ => none
  if own.isEmpty then items else items.filter fun
    | .fn n .. => !own.contains n
    | _ => true

/-- Every name a pattern could bind. -/
partial def patternNames : Pattern → List String
  | .var x => [x]
  | .ctor _ _ args => args.flatMap patternNames
  | .tuple args => args.flatMap patternNames
  | _ => []

/-- A pattern with `Self` written out as the type an implementation is for. -/
partial def selfPattern (self : String) : Pattern → Pattern
  | .ctor name qual args =>
    .ctor (if name == "Self" then self else name) (if qual == some "Self" then some self else qual)
      (args.map (selfPattern self))
  | .tuple args => .tuple (args.map (selfPattern self))
  | p => p

/-- `&value` and `&mut value` where the value has no name. -/
def borrowMark : String := "%borrow"
def borrowMutMark : String := "%borrow_mut"


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
  /-- An element of it is read, `x[i]`: through a borrow, where it is not
  used otherwise. -/
  indexed : Bool := false
  deriving Inhabited

def NameUse.or (a b : NameUse) : NameUse :=
  ⟨a.shared || b.shared, a.changed || b.changed, a.fielded || b.fielded, a.rebound || b.rebound,
    a.valued || b.valued, a.valuedInside || b.valuedInside, a.looked || b.looked, a.indexed || b.indexed⟩

/-- The label `@f` a function is also known by: the last part of its name,
`f` of `m::f` or `T::f`, and of a function written in a block, `f%12`. -/
def labelShort (name : String) : String :=
  let s := lastSegment name
  match s.splitOn "%" with
  | p :: _ :: _ => if p.isEmpty then s else p
  | _ => s

/-- A constant expression read as a pattern. -/
partial def exprToPat : Expr → Except String Pattern
  | .int n => pure (.int n)
  | .name q x => pure (if q.isSome then .ctor x q [] else .var x)
  | .call _ (.name q x) args => do
    -- A constant written with its type is its value.
    if q.isNone && x == ascribeMark then
      if let value :: _ := args then return ← exprToPat value
    pure (.ctor x q (← args.mapM exprToPat))
  | .tuple args => do
    pure (.tuple (← args.mapM exprToPat))
  | _ => throw "this constant cannot be used as a pattern"

/-- The name and the place such a name is of. -/
def partOf (name : String) : Option (String × Nat) :=
  match name.splitOn ".%" with
  | [x, i] => i.toNat?.map (x, ·)
  | _ => none

/-- What a callable's uses are to the code it is written in. -/
def NameUse.inside (u : NameUse) : NameUse :=
  -- (A name bound again in a callable is another name there: this one is
  -- still itself after it.)
  { u with valued := false, valuedInside := u.valued || u.valuedInside, rebound := false }


/-- The variable that says whether what a variable held has been given away,
and the name the variable's cleanup is known by where it is one that asks. -/
def movedFlag (x : String) : String := s!"%moved:{x}"

/-- Added to a field read's identity among the reads through a reference
(`derefReads`) where it is through two: a field of the element of a
`Vec<&T>`, read through the element's reference, `names[0].0`. -/
def derefTwice : Nat := 1152921504606846976
def givenSite (x : String) : String := s!"%given:{x}"

/-- The place of a field read by name before the type it is read from was
known: found from the name once the type is. -/
def partUnknown : Nat := 1000000000

/-- The name a part of a name's value is destroyed under, where the part is
never read: the name and the part's place among the fields. -/
def partName (x : String) (i : Nat) : String := s!"{x}.%{i}"

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

/-- The type of a text written out as the parser writes it (`textValue`):
the prelude's, of names no program can write. -/
def textItem : Item :=
  .enum "%Text" [] [(textEndName, []), (textCharName, [.name "char" [], .name "%Text" []])]

end Glorious.Syntax
