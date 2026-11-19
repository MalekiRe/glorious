module

public import Std.Data.HashMap
public import Std.Data.HashSet
public import Glorious.Syntax.Ast
public import Glorious.Syntax.ByRef
public import Glorious.Elab.Base
public import Glorious.Traits
public import Glorious.Trace

public section

namespace Glorious.Check

open Syntax

/-! ## Types -/

inductive Ty where
  /-- A type not yet known. -/
  | var (id : Nat)
  /-- A named type: `Int`, a declared type applied to arguments, or a function's
  own type parameter. -/
  | con (name : String) (args : List Ty)
  | tuple (args : List Ty)
  /-- A callable, with the effects it may perform: the named effects and, if the
  row is open, a variable standing for any others. `cap` identifies what the
  callable has captured, so that the scopes it depends on can be found. -/
  | fn (params : List Ty) (ret : Ty) (effs : List (String × List Ty)) (tail : Option Nat)
      (cap : Nat)
  /-- A reference to a mutable variable; `cap` identifies which it may refer to
  and the borrow it comes from. `how` is `Ty.uniq` for `&mut`, `Ty.shared` for
  `&`, or a variable where a function works with either. -/
  | ref (how : Ty) (t : Ty) (cap : Nat)
  deriving Inhabited

/-- A set of effects, possibly open. -/
structure Row where
  effs : List (String × List Ty)
  tail : Option Nat
  deriving Inhabited

def Ty.int : Ty := .con "Int" []

def Ty.unit : Ty := .tuple []

/-- How a reference borrows: for writing too, with nothing else using the
variable meanwhile, or for reading only, alongside other readers. -/
def Ty.uniq : Ty := .con "&mut" []

def Ty.shared : Ty := .con "&" []

def Ty.func (params : List Ty) (ret : Ty) (row : Row) (cap : Nat) : Ty :=
  .fn params ret row.effs row.tail cap

/-- A lifetime, where a type is expected: as an argument of a declared type.
It is a capture variable, as a reference's is, and says what a value of the
type may be holding borrows of. -/
def Ty.life (cap : Nat) : Ty := .ref (.con "'" []) (.tuple []) cap

/-- Something a callable has captured: a label, by the brand of its scope, or a
value of some type. -/
inductive Captured where
  | brand (id : Nat)
  | ty (t : Ty)
  /-- A resumption: whatever holds it can be used only once. -/
  | once
  /-- A resumption that has to be resumed. -/
  | must
  /-- A borrow of a mutable variable, by its identity: whatever holds it keeps
  the borrow going. -/
  | loan (id : Nat)
  /-- A mutable variable, by the brand of its block, that a callable reads or
  assigns when it runs. -/
  | touch (brand : Nat) (write : Bool)
  /-- A borrow, by its identity, that a callable makes while it runs. The
  callable does not hold it; a computation suspended inside the callable
  does. -/
  | inner (id : Nat)

/-- A type with some of its variables generalised. `edges` records what the
generalised capture variables capture, to be repeated at each use. -/
structure Scheme where
  tvars : List Nat
  rvars : List Nat
  cvars : List Nat
  edges : List (Nat × Captured)
  /-- Types that must be free to use more than once, with the reason. -/
  dups : List (Ty × String)
  ty : Ty
  /-- Types whose values must be free to go unused, with the reason. -/
  drops : List (Ty × String) := []
  /-- Types of callables that must come back when called: they may hold no
  label to jump to. With the reason. -/
  stays : List (Ty × String) := []
  /-- The types that say which instance of an effect each operation performed
  or handled in the function is, and which those of the functions it calls
  are: one after another, in the order of the function's text. A use of the
  function has them at its own types. -/
  sites : List Ty := []
  /-- The traits the function needs of its type parameters, in the order it is
  given the evidence: each a trait and one of `tvars`. -/
  bounds : List (String × Ty) := []
  /-- The callables in the type that are for every lifetime: see `St.ranked`. -/
  ranked : List (Nat × List (Nat × String)) := []
  /-- Types a callable lets go of whatever they are: each use has to be at
  one with nothing to destroy. With what to say where it is not. -/
  quiets : List (Ty × String) := []
  /-- Types left to implementations that the type mentions: see `St.assocUses`. -/
  assocs : List (String × Ty × String × Ty) := []
  /-- Rows of effects the function performs that are left to implementations:
  each, as the type of a callable that performs it, with the row it is
  performed in. A function over two streams performs what both do, and what
  that is is known where the streams are. -/
  incls : List (Ty × Ty) := []

/-- How a type depends on one of its parameters, for telling when a value of
the type at one argument will do where the type at another is wanted. -/
inductive Variance where
  /-- Not at all: the parameter is not used. -/
  | bi
  /-- The same way round: a longer lifetime will do for a shorter. -/
  | co
  /-- The other way round. -/
  | contra
  /-- Neither: the arguments must be the same. -/
  | inv
  deriving BEq, Inhabited

def Variance.flip : Variance → Variance
  | .co => .contra
  | .contra => .co
  | v => v

/-- The dependence through a position that depends `outer` on something that
depends `inner` on the parameter. -/
def Variance.through (outer inner : Variance) : Variance :=
  match outer, inner with
  | .bi, _ => .bi
  | _, .bi => .bi
  | .inv, _ => .inv
  | _, .inv => .inv
  | .co, v => v
  | .contra, v => v.flip

/-- Both dependences at once. -/
def Variance.both : Variance → Variance → Variance
  | .bi, v => v
  | v, .bi => v
  | .co, .co => .co
  | .contra, .contra => .contra
  | _, _ => .inv

structure TypeDecl where
  arity : Nat
  ctors : List String
  /-- Which of its parameters are lifetimes. -/
  kinds : List Bool := []
  /-- How it depends on each parameter, found from its fields. -/
  variances : List Variance := []

structure CtorSig where
  owner : String
  tvars : List Nat
  fields : List Ty
  result : Ty
  /-- The capture variables that stand for the type's lifetime parameters,
  in order, and which of the type's parameters are lifetimes. -/
  cvars : List Nat := []
  kinds : List Bool := []

structure OpSig where
  effect : String
  tvars : List Nat
  payload : List Ty
  /-- What the operation returns to its performer; none if it never returns. -/
  result : Option Ty
  /-- Declared `[1, 1]`: its resumption has to be resumed. -/
  must : Bool := false
  /-- For each parameter of the effect, in order: the capture variable it is
  in the types above if it is a lifetime, none if it is a type. -/
  lifetimes : List (Option Nat) := []
  /-- The lifetimes of its own, written or not (`read<'a>(&'a Path)`,
  `size(&Int)`): each performance and each arm has its own. -/
  caps : List Nat := []

/-- An effect: a variable for each of its parameters, a lifetime's standing
for nothing, and which of them are lifetimes. -/
structure EffectDecl where
  tvars : List Nat
  ops : List String
  lifetimes : List Bool := []

/-- What a local name stands for. -/
inductive Binding where
  /-- A value. `id` tells this binding from any other of the same name. -/
  | val (t : Ty) (id : Nat := 0)
  /-- A mutable variable holding a `t`; `brand` identifies its block. -/
  | cell (t : Ty) (brand : Nat)
  /-- A label whose scope yields a `t`; `brand` identifies the scope. -/
  | label (t : Ty) (brand : Nat)
  /-- A local callable, usable at several types. -/
  | poly (s : Scheme)

abbrev Scope := List (String × Binding)

/-- A borrow. `&x` and `&mut x` borrow a mutable variable; a `&mut` reference
used as a value is not copied but lent, which borrows from the reference. -/
structure Loan where
  id : Nat
  /-- The variable borrowed, by the brand of its block. -/
  root : Option Nat
  uniq : Bool
  /-- For a reference that was lent: its capture variable, and that of the
  reference given in its place. -/
  parent : Option (Nat × Nat)
  /-- The field borrowed, by the way to it through what the variable holds;
  empty for the whole variable. -/
  path : List Nat := []

/-- What is done to a mutable variable. -/
inductive Using where
  | read
  | write
  /-- Given away: what a variable that is never changed holds, taken once. -/
  | move
  /-- `&x`. -/
  | share
  /-- `&mut x`. -/
  | lend

/-- Something that a borrow still in use can forbid. -/
inductive UseKind where
  /-- A mutable variable, or with a `path` the field of it that is used. -/
  | var (brand : Nat) (name : String) (how : Using) (path : List Nat := [])
  /-- Reading or writing through a reference, or lending it; with a `path`,
  only the field of what it points to that is reached that way. -/
  | through (cap : Nat) (name : String) (write : Bool) (path : List Nat := [])
  /-- A call, which may run any callable that these types hold. -/
  | call (what : String) (tys : List Ty)

/-- A use, with what was still to be used when it happened: the names the rest
of the computation mentions, and the values the expression around it had
already computed. -/
structure Use where
  owner : String
  pos : String
  kind : UseKind
  scope : Scope
  later : List String
  temps : List (Ty × Nat)

/-- A coverage check to run once the types involved are known. `what` names the
clauses and ends with the verb of the message. -/
structure Pending where
  /-- Where the clauses are, as a prefix for the message. -/
  pos : String
  what : String
  tys : List Ty
  rows : List (List Pattern)

/-- A trait's function: which trait, which of its functions, and its type with
a variable standing for the type that has the trait. -/
structure MethodSig where
  trait : String
  index : Nat
  self : Nat
  params : List Ty
  ret : Ty
  /-- Its lifetimes as written, by their capture variables; `'_` is the one
  every unwritten lifetime is. -/
  lifetimes : List (Nat × String) := []
  /-- The variables that stand in its types for the trait's own type
  parameters, and for the types the trait leaves to an implementation. -/
  tparams : List Nat := []
  assocs : List (String × Nat) := []
  /-- What the function may perform: nothing, unless the trait says. -/
  row : Row := ⟨[], none⟩
  /-- The rows the trait leaves to an implementation, `type Effects:
  EffectRow;`: each by name, as the row variable that stands for it. Such a
  row is also among `assocs`, as the type of a callable that takes nothing,
  gives nothing and performs the row. -/
  rowAssocs : List (String × Nat) := []
  /-- The type parameters of its own, `fn single<T>(..)`: each by name, as
  the variable that stands for it. A use has each anew. -/
  mparams : List (String × Nat) := []
  /-- Where its types ask a type the trait leaves to implementations at
  types, `Of<T>`: the name, what it is asked at, and the variable that
  stands for the answer there. -/
  gats : List (String × List Ty × Nat) := []

structure ImplDecl where
  trait : String
  head : String
  params : List String
  /-- The conditions: each a trait and which of the head's arguments must have it. -/
  context : List (String × Nat)
  methods : List Item
  dictFn : String
  /-- The arguments it gives its trait, `impl From<Int> for ..`. -/
  targs : List Ty := []
  /-- The types its trait leaves to it, `type Item = ..`, which may mention
  its type parameters: each of those by name, as the variable in `pvars`. -/
  assocs : List (String × Ty) := []
  /-- The arguments of the head that are fixed, where the implementation was
  written for another name of the type: `impl T for Option<A>` is for
  `Result<A, ()>`. -/
  fixed : List (Nat × Ty) := []
  /-- What its conditions say of types left to the implementations of a
  trait, `where I: Iterator<Item = A>`: which of the head's arguments, the
  trait, the type's name, and what it is. -/
  equal : List (Nat × String × String × Ty) := []
  pvars : List (String × Nat) := []
  /-- Whether the arguments it gives its trait mention its own type
  parameters, `impl<T> From<T> for Wrap<T>`: it is then the one
  implementation of the trait for its type, at whatever arguments the
  type's own make them. -/
  generic : Bool := false
  /-- Its conditions that are not a trait of one of the head's arguments
  alone: a trait at arguments, or of a type parameter inside an argument
  (`where R: Get<T>`, `where H: Same<T>`). Each the trait, its arguments and
  the type it is asked of, in the implementation's own type parameters. -/
  extra : List (String × List Ty × Ty) := []
  /-- For a type it says that takes types, `type Of<T> = [T];`: what stands
  in `assocs` for what it takes, each a variable, or for a lifetime
  (`type Item<'a> = &'a T;`, marked `true`) a capture variable. -/
  gatParams : List (String × List (Bool × Nat)) := []
  /-- What its conditions say of a type left to an implementation of a type
  that is not one of the head's arguments, `(A, B): Tuple<Nested = L>`:
  the type asked of, the trait, the name and what it is, in its own type
  parameters. Met where the implementation is used, not assumed in it. -/
  extraEqual : List (Ty × String × String × Ty) := []

/-- A trait needed of a type at a call: of the type a trait's function is used
at, or of a type parameter of the function called. -/
structure Bound where
  trait : String
  ty : Ty
  call : Nat
  slot : Nat
  owner : String
  pos : String
  /-- The arguments the trait is asked at, once the bound is one of an
  implementation's own name (`Get<T>` at `Int`). -/
  args : List Ty := []

/-- Entries numbered from `base` on, in pieces of 64. Where the checker tries
something it may have to take back, it keeps what it knew; a write to a
plain array that is kept elsewhere too copies all of it, and the checker's
arrays are as long as the program and its library together. Here a write
copies one piece, and the list of the pieces. -/
structure Seg (α : Type) where
  base : Nat := 0
  pieces : Array (Array α) := #[]
  count : Nat := 0

namespace Seg

variable {α : Type}

@[inline] def get? (s : Seg α) (i : Nat) : Option α :=
  if i < s.count then (s.pieces.getD (i >>> 6) #[])[i &&& 63]? else none

def push (s : Seg α) (x : α) : Seg α :=
  if s.count &&& 63 == 0 then
    { s with pieces := s.pieces.push ((Array.mkEmpty 64).push x), count := s.count + 1 }
  else { s with pieces := s.pieces.modify (s.count >>> 6) (·.push x), count := s.count + 1 }

def modify (s : Seg α) (i : Nat) (f : α → α) : Seg α :=
  if i < s.count then { s with pieces := s.pieces.modify (i >>> 6) (·.modify (i &&& 63) f) } else s

end Seg

/-- A store of entries numbered as they are made. It is in segments: what is
made after a `jumpTo` starts one of its own, so that two checks that go on
from one state can each number from a place of its own, and what each made
be put together again (`Check.mergeStore`). Mostly there is one. -/
structure Store (α : Type) where
  /-- The segments before the last, in the order of where they start. -/
  older : Array (Seg α) := #[]
  last : Seg α := {}

namespace Store

variable {α : Type}

/-- The number the next entry made has. -/
@[inline] def size (s : Store α) : Nat := s.last.base + s.last.count

@[specialize] def olderGet? (older : Array (Seg α)) (i : Nat) : Option α := Id.run do
  let mut k := older.size
  while k > 0 do
    k := k - 1
    if let some seg := older[k]? then
      if i ≥ seg.base then return seg.get? (i - seg.base)
  return none

@[inline] def get? (s : Store α) (i : Nat) : Option α :=
  if i ≥ s.last.base then s.last.get? (i - s.last.base) else olderGet? s.older i

@[inline] def getD (s : Store α) (i : Nat) (d : α) : α := (s.get? i).getD d

def push (s : Store α) (x : α) : Store α := { s with last := s.last.push x }

def modify (s : Store α) (i : Nat) (f : α → α) : Store α :=
  if i ≥ s.last.base then { s with last := s.last.modify (i - s.last.base) f }
  else
    match (List.range s.older.size).reverse.find? (fun k => (s.older[k]?.map (·.base)).getD 0 ≤ i) with
    | some k => { s with older := s.older.modify k fun seg => seg.modify (i - seg.base) f }
    | none => s

def set! (s : Store α) (i : Nat) (x : α) : Store α := s.modify i fun _ => x

/-- Every segment, the last too, in order. -/
def segs (s : Store α) : Array (Seg α) := s.older.push s.last

def toArray (s : Store α) : Array α :=
  s.segs.foldl (fun acc seg => seg.pieces.foldl (· ++ ·) acc) (Array.mkEmpty s.size)

/-- Each entry with its number. -/
def entries (s : Store α) : List (Nat × α) :=
  s.segs.toList.flatMap fun seg =>
    seg.pieces.toList.zipIdx.flatMap fun (piece, c) =>
      piece.toList.zipIdx.map fun (x, j) => (seg.base + 64 * c + j, x)

/-- What is made next has a number from `n` on, in a segment of its own:
the numbers passed over are never made. -/
def jumpTo (s : Store α) (n : Nat) : Store α :=
  if n ≤ s.size then s
  else if s.last.count == 0 then { s with last := { base := n } }
  else { older := s.older.push s.last, last := { base := n } }

end Store

/-- A use of a function inside the group it is inferred with: its bounds are
not known until the group is done. `call` is zero where it is not called. -/
structure GroupUse where
  call : Nat
  callee : String
  owner : String
  pos : String

structure St where
  tys : Store (Option Ty) := {}
  rows : Store (Option Row) := {}
  /-- Variables standing for the inferred types of declarations: never generalised. -/
  mono : List Nat := []
  monoRows : List Nat := []
  /-- Capture variables of function types written in declarations. -/
  monoCaps : List Nat := []
  /-- Capture variables, merged as function types are unified. -/
  caps : Store (Option Nat) := {}
  /-- What each capture variable is known to capture. -/
  capEdges : Store (Nat × Captured) := {}
  /-- For each capture variable that stands for itself, the places in
  `capEdges` of what it captures, whichever variable of its class the edge
  was made on: so that what one captures is found without going through
  every edge of the program. -/
  capOut : Store (Array Nat) := {}
  /-- For each of `capEdges`, the name captured, where a callable written in
  the program captured a name. -/
  capEdgeNames : Store (Option (String × Nat)) := {}
  brands : Nat := 0
  /-- Capture variables already visited by the search in progress. -/
  seen : List Nat := []
  /-- Types that must be free to use more than once, with the reason; checked
  once the types are known. -/
  dups : Array (Ty × String) := #[]
  /-- The same, for types that later functions can still affect. -/
  lateDups : Array (Ty × String) := #[]
  /-- Types whose values must be free to go unused, with the reason; checked
  once the types are known. -/
  drops : Array (Ty × String) := #[]
  lateDrops : Array (Ty × String) := #[]
  /-- Types of callables that must come back when called, with the reason. -/
  stays : Array (Ty × String) := #[]
  lateStays : Array (Ty × String) := #[]
  /-- What `impl Use<[lower, upper]>` says of a declared type: whether a value
  has to be used, and whether it can be used only once. -/
  useDecls : List (String × Bool × Bool) := []
  /-- Whether the program declares anything that has to be used. Without it
  nothing can have to be, and nothing is checked. -/
  anyMust : Bool := false
  /-- Values the expression being checked has computed, has no name for, and
  has not yet passed on. -/
  anon : List Ty := []
  /-- The lifetimes the function being checked declares: each stands for
  itself there, and is no other. With its name. -/
  rigidCaps : List (Nat × String) := []
  /-- Whether what is being fitted is what a body ends with, to the type the
  body is to give. -/
  givingBack : Bool := false
  /-- The variables, by their blocks' brands, that are never changed and whose
  value is given away where they are: reading one is a use of the value, as
  of a name's, and not a copy. -/
  movedCells : List Nat := []
  /-- Where such variables are, as the count of uses knows a binding: one of
  them may hold a value with `Drop` that some paths use and others do not,
  since its cleanup asks whether it was. -/
  flagged : List String := []
  /-- For each of them, where its cleanup would go: it is put there only if
  some path does not use the value, which is known once the function's
  uses are counted. -/
  givenSites : List (String × Elab.DropSite × Ty × String) := []
  /-- Among what callables hold, by place in `capEdges`: the values of such
  variables. A callable that holds one need not be called for its `drop`'s
  sake, since the variable's cleanup destroys what was not given away. -/
  givenEdges : Std.HashSet Nat := {}
  /-- The callables that are where a variable's value goes: each by what it
  captures with, and the variable. -/
  givers : List (Nat × Nat) := []
  /-- What was read out of such a variable: a value that holds a resumption
  cannot be, since the machine's read is a copy and a resumption is not
  copied. -/
  givenReads : Array (Ty × String) := #[]
  /-- The values a field was taken out of, leaving the rest: their types and
  where. One with `Drop` is taken apart only where it is declared. -/
  aparts : Array (Ty × String × Option Nat) := #[]
  /-- The bounds written between them: the first lasts at least as long as
  the second. -/
  outlives : List (Nat × Nat) := []
  /-- `'static`, once it has been written. -/
  staticCap : Option Nat := none
  /-- What is known of the program's modules: see `ModuleInfo`. -/
  modules : Syntax.ModuleInfo := {}
  /-- The names of the fields of each constructor declared with names. -/
  fieldNames : List (String × List String) := []
  /-- The type parameters of the function being checked, each as what it
  stands for while it is. -/
  rigidParams : List (String × Ty) := []
  /-- Dot calls of a type's own function chosen by the value's type. -/
  dotChosen : List (Nat × String × Nat) := []
  /-- Receivers of dot calls the checker chose to give as other than written,
  by the call and the argument's place: a field borrowed where it is, or a
  reference made where the call is given as it is. -/
  argsChosen : List ((Nat × Nat) × Expr) := []
  /-- What it decided of how the program is read, where it found it
  (`Elab.Decision`). -/
  decided : List Elab.Decision := []
  /-- The result a call is wanted to have, by the call (`applyTy`). -/
  wantResult : Option (Nat × Ty) := none
  /-- For each trait, how many type parameters it has and the names of the
  types it leaves to implementations. -/
  traitShape : List (String × Nat × List String) := []
  /-- A type a trait leaves to its implementations, at a use: the trait, what
  it is asked of (the type, and after it the trait's arguments if it has
  some), which type, the variable that stands for it, the function this is in,
  and where. Once the type asked of is known, the variable is the type its
  implementation says; until then the same question has the same answer. -/
  assocUses : Array (String × Ty × String × Ty × String × String) := #[]
  /-- What is written of each function's type parameters by way of ordinary
  traits, with the trait's arguments as types: the function, the type
  parameter, the trait, the arguments. -/
  writtenArgs : List (String × String × String × List Ty) := []
  /-- For each trait, the traits a type must have to have it. -/
  supers : List (String × List String) := []
  /-- Callable types that are for every lifetime: by the capture variable of
  the callable, the lifetimes it is for, each with its name. Applied, it is
  at new lifetimes each time; given, it must do for any. -/
  ranked : List (Nat × List (Nat × String)) := []
  /-- While a function is read that has no body to find its lifetimes from, a
  trait's: the one lifetime every unwritten lifetime of it is. -/
  elided : Option Nat := none
  /-- The blocks given what an `is` found, each with the names it then has. -/
  packs : Array (Nat × List String) := #[]
  /-- The callables a function is given that run in one environment it is
  given whole: the environment's name, each callable with how many arguments
  it takes, whether one of them has to be called, the other names in scope,
  and the function's body. At most one of them can be called on a path. -/
  envGroups : Array (String × List (String × Nat) × Bool × List String × List Stmt) := #[]
  /-- Environments that are there only once a callable has run, `After = E2`:
  the environment, the callables that leave it, those that run in it, the
  other names in scope, and the function's body. None of those that run in
  it is called before one of those that leave it. -/
  envAfter : Array (String × List (String × Nat) × List (String × Nat) × List String × List Stmt) := #[]
  /-- Environments some callables are given whole and others are lent: the
  environment, those given it, those lent it, the other names in scope, and
  the function's body. None lent it can be called once one given it has been. -/
  envLent : Array (String × List (String × Nat) × List (String × Nat) × List String × List Stmt) := #[]
  /-- For a function whose callables share an environment and take no
  arguments: which of its parameters they are, the first being the one that
  holds the environment; and the same by name. A caller builds the others
  over what the first captured. -/
  fnGroups : List (String × List (List Nat)) := []
  envFns : List (String × List (List String)) := []
  /-- Blocks built over the environment of another block of the same call. -/
  envLinks : Array (Nat × Nat) := #[]
  /-- Calls that give a name where a callable sharing an environment is
  wanted: the call, and which arguments. -/
  envWraps : Array (Nat × List Nat) := #[]
  /-- Of such functions, those of whose callables one is certainly called. -/
  envMust : List String := []
  /-- Blocks given to such a function at one call, of which one certainly
  runs: where, the function, and the capture variable of each block. What
  has to be used and is held by one has to be held by every one. -/
  envHeld : Array (String × String × List Nat) := #[]
  /-- The fields read by name of what a named reference points to. -/
  derefReads : Array Nat := #[]
  /-- The row parameters of the functions checked, each held as the row of a
  callable type: once everything is settled, each is still a row nobody
  knows, and no two of a function's are one. -/
  rowChecks : List (String × List (String × Ty)) := []
  /-- What is asked of the type parameters of a declared type, where a value
  of it is built: for each such type, a trait and which parameter. -/
  typeBounds : List (String × List (String × Nat)) := []
  /-- The type parameters each function of a module declares, in the order
  written, as its type has them; none for one its type does not mention. -/
  typeParams : List (String × List (Option Nat)) := []
  /-- The types a call writes for the type parameters of the function it
  calls, `f<A, B>(..)`, until the function is found. -/
  instWith : Option (List Ty) := none
  /-- For each field read by name, which field it is: for the elaborator. -/
  fieldReads : Array (Nat × Nat) := #[]
  /-- Borrows of a field, to settle once the type is known: the borrow, the
  type of what the variable holds, the way to the field, and where. -/
  fieldSites : Array (Nat × Bool × Ty × List Nat × List (Option String) × String × String) := #[]
  /-- For each, what is gone through to reach the field: at each step the
  constructor, or none for a tuple, and how many fields it has. -/
  fieldTable : Array (Nat × Bool × List Nat × List (Option String × Nat)) := #[]
  /-- What went wrong when a callable was first read, with the types of what
  it is given known, before it was read again without them: said if what is
  then wrong is only that those types were not known. -/
  firstSaid : Option Elab.Said := none
  /-- Every call of a callee with a type, by the call's identity, and whether
  the callee was then seen to perform nothing: its effects were a variable of
  its own that none of its parameters mention. -/
  calls : Array (Nat × Ty × Bool) := #[]
  /-- Effect variables made by using a generalised type: nothing supplies
  effects to one unless a parameter of that type mentions it. -/
  instRows : List Nat := []
  /-- Blocks that do not name what they are given, given a block that was not
  run: the block, the capture variable and type of what it is given, the names
  it mentions, and a message. What the other block held that this one does not
  mention is let go. -/
  unrunGiven : Array (Nat × Nat × Ty × List (String × Nat) × String × Nat) := #[]
  /-- Captures, by their place in `capEdges`, of a block that runs in place of
  another: what both mention is held once, by the other. -/
  sharedEdges : Std.HashSet Nat := {}
  /-- Of those, the ones taken to be given one particular block, to be
  confirmed when the whole program is known. -/
  assumedLinks : Array (Nat × Nat × Ty × String) := #[]
  /-- Values that are let go if a call does not come back: the call, the type,
  and the message. -/
  abandoned : Array (Nat × Ty × String) := #[]
  /-- The calls that certainly come back if they end at all: the callee
  performs nothing and can jump to no label. -/
  sure : Std.HashSet Nat := {}
  /-- Bindings whose use on every path is still to be looked at, once the
  types of the function they are in are known: where, the name, its type, the
  other names in scope, and the code the name is in scope of. -/
  lowerChecks : Array (String × String × Ty × List String × List Stmt) := #[]

  /-- The clauses of every top-level function, for following calls when uses
  are counted. -/
  fnBodies : List (String × List Clause) := []
  /-- What the count of uses reads of what is declared, kept as it is
  declared and found in one look: the bodies of functions, the names of
  constructors, the aliases, whether each operation gives something back,
  the operations whoever handles must resume, and the blocks run where they
  are written. Each is what its list says, the first of a name where the
  list has two. -/
  runFns : Std.HashMap String (List Clause) := {}
  runCtors : Std.HashSet String := {}
  runAliases : Std.HashMap String Expr := {}
  runOps : Std.HashMap String Bool := {}
  runExact : Std.HashSet String := {}
  runNow : Std.HashSet Nat := {}
  /-- Calls whose callee has effects not yet known: the callee's row, the row
  permitted where it is called, and a description of the call. -/
  rowIncl : Array (Row × Row × String) := #[]
  types : List (String × TypeDecl) := []
  ctors : Std.HashMap String CtorSig := {}
  ops : List (String × OpSig) := []
  effects : List (String × EffectDecl) := []
  aliases : Std.HashMap String Expr := {}
  fns : Std.HashMap String Scheme := {}
  /-- The functions being inferred together, with their types so far. -/
  group : List (String × Ty) := []
  pending : Array Pending := #[]
  /-- Field reads whose subject was not yet known: subject, index, field type,
  where the read is, and the read's node where it has one (else 0): one of
  what turns out to be a reference is read through it. -/
  projections : Array (Ty × Nat × Ty × String × Nat) := #[]
  /-- Fields read by name from values whose type was not known yet: the
  value's type, the name, the field's type, the read, and where. -/
  namedReads : Array (Ty × String × Ty × Nat × String) := #[]
  /-- Where the statement being checked starts, as a prefix for messages that
  are only raised later. -/
  pos : String := ""
  /-- The capture variable of each callable literal, by the literal's identity. -/
  blockCaps : Array (Nat × Nat) := #[]
  /-- Blocks written without parameters where a callable taking one argument
  is expected. -/
  given : Array Nat := #[]
  /-- Those of them given a callable that takes no arguments, which is how a
  block that was not run is handed on: the block's identity and the capture
  variable of what it is given. -/
  unrun : Array (Nat × Nat) := #[]
  /-- The functions declared as coercions, in the order declared. -/
  coercing : List String := []
  /-- The coercions applied, each with the place it is applied at. -/
  coercions : Array (Elab.Site × String) := #[]
  /-- The function being checked. -/
  owner : String := ""
  /-- The names the computation still mentions after the expression being checked. -/
  later : List String := []
  /-- Names bound in the blocks being read whose values have a `drop` to run
  where their block ends: what they hold is held till then. -/
  dropLive : List String := []
  /-- The values the expression being checked has computed and not yet used,
  each with how many borrows had been made when it was computed. -/
  temps : List (Ty × Nat) := []
  loans : Store Loan := {}
  /-- Mutable variables, by the brand of their block: the name, and the type held. -/
  cells : Array (Nat × String × Ty) := #[]
  /-- The patterns being looked at are only to say which cases clauses take:
  one for a value may be met by a reference to such a value, which the
  clauses reach through. -/
  shapes : Bool := false
  /-- Where each name was bound, for the cleanup of the parts of its value
  that are never read: the binding, and the place the elaborator knows it
  by. -/
  bindSites : List (Nat × Nat × Nat) := []
  /-- Values let go where nothing destroys them: the fields left when one is
  taken out of a value that has no name to clean up under. One with a `drop`
  is refused. -/
  leftBehind : Array (Ty × String) := #[]
  /-- Values whose parts are read more than once in all, each part a value
  of its own: not one that holds a resumption, of which the machine counts
  every read as a use of the whole. -/
  takenApart : Array (Ty × String) := #[]
  /-- A part of a name's value read, `x.f`: the binding, the value's type,
  which field, as it is written, and where. What it lets go of is seen once
  every part read of that name is known. -/
  partReads : Array (Nat × String × Ty × Nat × String × String) := #[]
  /-- Uses to check against the borrows once the types are known. -/
  uses : Array Use := #[]
  /-- Where a callable that uses a variable's value is written: from there
  on the value may go whenever the callable runs, so nothing that could
  look at the variable may still be callable. -/
  heldMoves : Array Use := #[]
  /-- The functions of each trait, in order. -/
  traits : List (String × List String) := []
  methods : List (String × MethodSig) := []
  impls : Array ImplDecl := #[]
  /-- The implementations of each trait, by the trait's name without its
  arguments: their places in `impls`. -/
  implsByBase : Std.HashMap String (Array Nat) := {}
  /-- The same by the trait's name without its arguments and the type's head. -/
  implsByHead : Std.HashMap (String × String) (Array Nat) := {}
  /-- What fitting found of a trait at a type made of named types and tuples
  alone, while one group's bounds are settled: by the function, the trait,
  the type and arguments spelled, and what the function is given
  (`solveFitting`, `leavesFitting`). -/
  solvedFit : Std.HashMap (String × String × String × Traits.Givens) (Option Traits.Dict) := {}
  leavesFit : Std.HashMap (String × String × String) (List (String × Nat × Ty × List Ty)) := {}
  /-- The implementations as `Traits.solve` sees them, in the same order. -/
  kimpls : Traits.ImplIndex := {}
  /-- The bounds of the scheme last instantiated, at that use. -/
  lastBounds : List (String × Ty) := []
  /-- Has some implementation a condition that is more than a trait of one
  of its head's arguments, or do two implementations of one trait for one
  type differ only in what the arguments have to be? Then which
  implementation meets a bound is found by fitting types, here, and not by
  `Traits.solve`. -/
  patterned : Bool := false
  /-- The traits with an implementation for every type, each with the
  traits it asks of the type (`Syntax.expandBlankets`): a function whose
  type parameter is said to have those has this one too, met where the
  function is used, by the implementation for the type it is used at. -/
  blanketTraits : List (String × List String) := []
  /-- The same of its `sites`. -/
  lastSites : List Ty := []
  /-- Where the function being checked performs or handles an operation of
  an effect that has type parameters, or calls a function that does: the
  function, the call's number, which of the three (`op`, `handle`, `call`),
  the effect or the function called, and the types that say which instance. -/
  instSites : Array (String × Nat × String × String × List Ty) := #[]
  /-- The same once a function is done: for each, its places with where each
  one's types are among the function's `sites`; and those types, where they
  are known without knowing who calls the function. -/
  siteTable : List (String × List (Nat × String × String × Nat × Nat)) := []
  siteTypes : List (String × List (Option Syntax.TypeExpr)) := []
  /-- Bounds to meet once the types of the group being inferred are known. -/
  bounds : Array Bound := #[]
  groupUses : Array GroupUse := #[]
  /-- A function's own type parameters that bounds were needed of, each with
  the number it has for `Traits.solve`. -/
  rigidKeys : Store String := {}
  /-- The number of each of `rigidKeys`, by its name. -/
  rigidAt : Std.HashMap String Nat := {}
  /-- The numbers of the conditions said of a type made from type parameters
  (`'%condition:owner:key:type`), under `key:type`, of every owner. -/
  conditionsAt : Std.HashMap String (List Nat) := {}
  /-- Where the statement being checked starts. -/
  at_ : Nat × Nat := (0, 0)
  /-- Variables whose value is destroyed if its type turns out to have `Drop`:
  the place, the type, and where to report a failure. -/
  dropCands : Array (Elab.DropSite × Ty × String) := #[]
  /-- The functions that can be named only where `unsafe` is written, and
  whether what is being checked is in a block written `unsafe { .. }`. -/
  unsafeFns : List String := []
  unsafeBlock : Bool := false
  /-- The prelude's type of arrays, by its name in this program. -/
  arrayType : Option String := none
  dropSites : Array (Elab.DropSite × Nat) := #[]
  /-- Where the patterns being read are, and how many `_` they have had so
  far: a value a `_` lets go is destroyed, and is known to the elaborator by
  that place and number. None while patterns are read whose `_` are not
  counted the same way there. -/
  wildAt : Option (Nat × Nat) := none
  wildCount : Nat := 0
  /-- Whether the pattern being read is a `let`'s. -/
  wildLet : Bool := false
  /-- The names bound by the pattern of a `let`, by their bindings. -/
  letBinds : List Nat := []
  /-- Names of which parts were read before their type was known: where each
  would be destroyed if it stays whole, its type, the parts read, and where. -/
  lateKeeps : Array (Elab.DropSite × Ty × List (Ty × Nat) × String) := #[]
  /-- Types that have to have nothing to destroy, and what to say if one has. -/
  quiets : Array (Ty × String) := #[]
  /-- While a trait's functions are read: the types it leaves to
  implementations, and where one is asked at types, as `MethodSig.gats`. -/
  gatScope : List String := []
  /-- Reading what an implementation says one of its trait's types is: a type
  that names another trait's type of one of its parameters is kept as written
  (`Syntax.projMark`). -/
  projecting : List Nat := []
  /-- The items being checked are the program's own, after the library's: what
  is asked again with the program rewritten (a value of a type parameter kept
  in a variable) is asked only of these. -/
  ownItems : Bool := false
  /-- While an effect's operations are read: the traits written of each of its
  type parameters, by which `S::Out` is told apart where several traits leave
  an `Out`. -/
  paramTraits : List (String × String × List TypeExpr) := []
  gatOccs : Array (String × List Ty × Nat) := #[]
  /-- A type a trait leaves at a lifetime, not yet known (`L::Item<'a>` where
  `L` is a type parameter): by its variable, the lifetimes it was asked at.
  It may hold whatever they borrow. -/
  gatHolds : Array (Nat × List Nat) := #[]
  /-- A program in which some type has `Drop`: values are destroyed where
  they are let go, each type by its own function, and a function is given
  how to destroy the types it is generic in. Without `Drop` anywhere there
  is nothing to do and none of it is there. -/
  dropMode : Bool := false
  /-- How many `Drop`s have been asked for, to name each. -/
  dropAsked : Nat := 0
  /-- How each call's bounds are met, for the elaborator. -/
  dictTable : Array (Nat × List Elab.DictE) := #[]
  methodCalls : Array (Nat × Nat) := #[]
  fnBounds : List (String × Nat) := []

abbrev M := StateT St (Except Elab.Said)

/-- `act`, its time added to `label`'s where a compile is traced (`Trace`). -/
def timedM {α : Type} (label : String) (act : M α) : M α := fun s => Trace.timed label fun _ => act.run s

/-- A message is what stops the checker, with nothing found. -/
instance : MonadExceptOf String M where
  throw msg := throwThe Elab.Said { msg }
  tryCatch act handle := tryCatchThe Elab.Said act fun e => handle e.msg

/-- Run `act`, and change an error it ends in with `f`. Unlike `try`, which
keeps the state from before to go back to, nothing holds that state while
`act` runs: so what `act` changes is changed in place, and not copied. -/
@[inline] def onError {α : Type} (act : M α) (f : String → String) : M α := fun s =>
  match act s with
  | .ok r => .ok r
  | .error e => .error (e.map f)

/-- The implementations of a trait, by its name without arguments. -/
def implsOfBase (base : String) : M (List ImplDecl) := do
  let s ← get
  pure ((s.implsByBase.getD base #[]).toList.filterMap fun i => s.impls[i]?)

/-- Those for types of this head. -/
def implsOfHead (base head : String) : M (List ImplDecl) := do
  let s ← get
  pure ((s.implsByHead.getD (base, head) #[]).toList.filterMap fun i => s.impls[i]?)

/-- Has a trait more than one implementation for types of this head? -/
def severalFor (base : String) : Option String → M Bool
  | some head => do pure (((← get).implsByHead.getD (base, head) #[]).size > 1)
  | none => pure false

instance {α : Type} : Inhabited (M α) := ⟨throw "checker: unreachable"⟩

def freshTy : M Ty := do
  -- (in one step: the state is not held twice, so the array is not copied)
  modifyGet fun s => (.var s.tys.size, { s with tys := s.tys.push none })

def freshRowVar : M Nat := do
  -- (in one step: the state is not held twice, so the array is not copied)
  modifyGet fun s => (s.rows.size, { s with rows := s.rows.push none })

def freshRow : M Row := do
  pure ⟨[], some (← freshRowVar)⟩

def freshCap : M Nat := do
  -- (in one step: the state is not held twice, so the array is not copied)
  modifyGet fun s => (s.caps.size, { s with caps := s.caps.push none, capOut := s.capOut.push #[] })

def freshBrand : M Nat := do
  modifyGet fun s => (s.brands, { s with brands := s.brands + 1 })

/-- The representative of a capture variable. -/
partial def findCap (c : Nat) : M Nat := do
  match (← get).caps.get? c with
  | some (some parent) => findCap parent
  | _ => pure c

def unifyCap (a b : Nat) : M Unit := do
  let ra ← findCap a
  let rb ← findCap b
  unless ra == rb do
    let s ← get
    -- A lifetime a function declares stays what it is: it can be what an
    -- unknown one turns out to be, but not another declared one.
    match s.rigidCaps.lookup ra, s.rigidCaps.lookup rb with
    | some x, some y =>
      throw s!"lifetime `{x}` is not `{y}`: a reference that lasts for one is used where one that lasts for the other is wanted"
    -- (What the one that gives way captured is the other's from now on.)
    -- (Each array is taken out before the store is written, so that the
    -- store is the only holder of itself and is changed where it is.)
    | some _, none => modify fun s =>
        let moved := s.capOut.getD rb #[]
        let out := s.capOut.set! rb #[]
        { s with caps := s.caps.set! rb (some ra), capOut := out.modify ra (· ++ moved) }
    | _, _ => modify fun s =>
        let moved := s.capOut.getD ra #[]
        let out := s.capOut.set! ra #[]
        { s with caps := s.caps.set! ra (some rb), capOut := out.modify rb (· ++ moved) }

def captures (cap : Nat) (what : Captured) (name : Option (String × Nat) := none) : M Unit := do
  let root ← findCap cap
  modify fun s =>
    let at_ := s.capEdges.size
    { s with capEdges := s.capEdges.push (cap, what), capEdgeNames := s.capEdgeNames.push name,
             capOut := s.capOut.modify root (·.push at_) }

/-- What a capture variable captures: the edges made on any variable of its
class, in the order they were made. `root` stands for itself. -/
def edgesFrom (root : Nat) : M (Array (Nat × Captured)) := do
  let s ← get
  pure ((s.capOut.getD root #[]).filterMap fun i => s.capEdges.get? i)

/-- A function of the library, which is checked once for every program. -/
def libraryOwner (owner : String) : Bool :=
  ["std::", "core::", "alloc::"].any (owner.startsWith ·)

/-- Follow a type variable to what it stands for. -/
partial def find (t : Ty) : M Ty := do
  match t with
  | .var id =>
    match (← get).tys.get? id with
    | some (some t') => find t'
    | _ => pure t
  | _ => pure t

/-- Expand a row's tail as far as it is known. -/
partial def flattenRow (r : Row) : M Row := do
  match r.tail with
  | none => pure r
  | some id =>
    match (← get).rows.get? id with
    | some (some r') => do
      let rest ← flattenRow r'
      pure ⟨r.effs ++ rest.effs, rest.tail⟩
    | _ => pure r

/-- Two types written the same, once what is known of them is filled in. -/
partial def Ty.same : Ty → Ty → Bool
  | .var i, .var j => i == j
  | .con n as, .con m bs => n == m && as.length == bs.length && (as.zip bs).all fun (x, y) => x.same y
  | .tuple as, .tuple bs => as.length == bs.length && (as.zip bs).all fun (x, y) => x.same y
  | .fn ps r _ _ _, .fn qs s _ _ _ =>
    ps.length == qs.length && r.same s && (ps.zip qs).all fun (x, y) => x.same y
  | .ref _ x _, .ref _ y _ => x.same y
  | _, _ => false

/-- The name a type is made with, as an implementation is for one, and its
arguments: a declared type's own; `(tuple2)` and its parts; `(fn2)`, what the
function is given and then what it gives; `(&)` or `(&mut)` and what the
reference is to. -/
def Ty.head : Ty → Option (String × List Ty)
  | .con n args => some (n, args)
  | .tuple parts => some (s!"(tuple{parts.length})", parts)
  | .fn ps r _ _ _ => some (s!"(fn{ps.length})", ps ++ [r])
  | .ref (.con "&mut" []) t _ => some ("(&mut)", [t])
  | .ref _ t _ => some ("(&)", [t])
  | .var _ => none

mutual

/-- Does a pattern fit a type: is there something for each of the pattern's
own variables (`vars`) to be that makes the two the same? Every other
variable, in either, is only itself. What each variable is, is added to
`found`. -/
partial def Ty.fits (vars : List Nat) (pattern term : Ty) (found : List (Nat × Ty)) :
    Option (List (Nat × Ty)) :=
  match pattern, term with
  | .var v, t =>
    if vars.contains v then
      match found.lookup v with
      | some was => if was.same t then some found else none
      | none => some ((v, t) :: found)
    else match t with
      | .var w => if v == w then some found else none
      | _ => none
  | .con n as, .con m bs => if n == m && as.length == bs.length then Ty.fitsAll vars as bs found else none
  | .tuple as, .tuple bs => if as.length == bs.length then Ty.fitsAll vars as bs found else none
  | .fn ps r _ _ _, .fn qs s _ _ _ =>
    if ps.length == qs.length then Ty.fitsAll vars (r :: ps) (s :: qs) found else none
  -- (`&` and `&mut` are two.)
  | .ref h x _, .ref k y _ => (Ty.fits vars h k found).bind (Ty.fits vars x y)
  | _, _ => none

partial def Ty.fitsAll (vars : List Nat) (patterns terms : List Ty) (found : List (Nat × Ty)) :
    Option (List (Nat × Ty)) :=
  match patterns, terms with
  | [], [] => some found
  | p :: ps, t :: ts => (Ty.fits vars p t found).bind (Ty.fitsAll vars ps ts)
  | _, _ => none

end

mutual

/-- Can two types be made the same by what their variables are? What each
would have to be is added to `found`. (Used of two implementations' heads,
to see whether some type could be both's.) -/
partial def Ty.meets (a b : Ty) (found : List (Nat × Ty)) : Option (List (Nat × Ty)) :=
  let rec walk (t : Ty) (fuel : Nat) : Ty :=
    match fuel, t with
    | fuel + 1, .var v => match found.lookup v with
      | some u => walk u fuel
      | none => t
    | _, t => t
  match walk a 64, walk b 64 with
  | .var v, .var w => if v == w then some found else some ((v, .var w) :: found)
  | .var v, t => some ((v, t) :: found)
  | t, .var w => some ((w, t) :: found)
  | .con n as, .con m bs => if n == m && as.length == bs.length then Ty.meetAll as bs found else none
  | .tuple as, .tuple bs => if as.length == bs.length then Ty.meetAll as bs found else none
  | .fn ps r _ _ _, .fn qs s _ _ _ =>
    if ps.length == qs.length then Ty.meetAll (r :: ps) (s :: qs) found else none
  | .ref h x _, .ref k y _ => (Ty.meets h k found).bind (Ty.meets x y)
  | _, _ => none

partial def Ty.meetAll (as bs : List Ty) (found : List (Nat × Ty)) : Option (List (Nat × Ty)) :=
  match as, bs with
  | [], [] => some found
  | a :: as, b :: bs => (Ty.meets a b found).bind (Ty.meetAll as bs)
  | _, _ => none

end

/-- Is everything in a type known: no variable, and no type parameter of the
function it is in? -/
partial def Ty.ground : Ty → Bool
  | .var _ => false
  | .con n args => !n.startsWith "'" && args.all Ty.ground
  | .tuple args => args.all Ty.ground
  | .fn ps r _ _ _ => r.ground && ps.all Ty.ground
  | .ref _ t _ => t.ground

/-- The type parameters of a function a type mentions, by name. -/
partial def Ty.rigidNames : Ty → List String
  | .con n [] => if n.startsWith "'" then [n] else []
  | .con _ args | .tuple args => args.flatMap Ty.rigidNames
  | .fn ps r _ _ _ => (r :: ps).flatMap Ty.rigidNames
  | .ref h x _ => h.rigidNames ++ x.rigidNames
  | .var _ => []

/-- A type with each of those that `named` says a variable in its place. -/
partial def Ty.openRigids (named : List (String × Ty)) : Ty → Ty
  | .con n [] => (named.lookup n).getD (.con n [])
  | .con n args => .con n (args.map (Ty.openRigids named))
  | .tuple args => .tuple (args.map (Ty.openRigids named))
  | .fn ps r effs tail cap => .fn (ps.map (Ty.openRigids named)) (r.openRigids named) effs tail cap
  | .ref h x cap => .ref (h.openRigids named) (x.openRigids named) cap
  | .var v => .var v

/-- Could a pattern come to fit a type, once what is not yet known of the
type is, and whatever a function's own type parameters in it are? Yes
unless the two are made with different names somewhere. -/
partial def Ty.mayFit (pattern term : Ty) : Bool :=
  match pattern, term with
  | .var _, _ => true
  | _, .var _ => true
  | .con n as, .con m bs =>
    (m.startsWith "'" && bs.isEmpty) || (n.startsWith "'" && as.isEmpty)
      || (n == m && as.length == bs.length && (as.zip bs).all fun (x, y) => x.mayFit y)
  | _, .con m [] => m.startsWith "'"
  | .con n [], _ => n.startsWith "'"
  | .tuple as, .tuple bs => as.length == bs.length && (as.zip bs).all fun (x, y) => x.mayFit y
  | .fn ps r _ _ _, .fn qs s _ _ _ =>
    ps.length == qs.length && r.mayFit s && (ps.zip qs).all fun (x, y) => x.mayFit y
  | .ref h x _, .ref k y _ => h.mayFit k && x.mayFit y
  | _, _ => false

/-- A type as it would be written, if nothing in it is unknown or a type
parameter: the instance of an effect it names can then be an effect of its
own. -/
partial def Ty.written : Ty → Option Syntax.TypeExpr
  | .var _ => none
  | .con n args =>
    if n.startsWith "'" then none
    else (args.mapM Ty.written).map (Syntax.TypeExpr.name n)
  | .tuple args => (args.mapM Ty.written).map .tuple
  | .fn ps r _ _ _ => do pure (.fn (← ps.mapM Ty.written) (← r.written))
  | .ref how t _ =>
    match how with
    | .con "&mut" [] => t.written.map (.ref true · none)
    | _ => t.written.map (.ref false · none)

/-- A row with each instance of an effect once (of types filled in). -/
def dedupe (effs : List (String × List Ty)) : List (String × List Ty) :=
  effs.foldl (fun acc e =>
    if acc.any (fun o => o.1 == e.1 && o.2.length == e.2.length && (o.2.zip e.2).all fun (x, y) => x.same y)
    then acc else acc ++ [e]) []

mutual

/-- Replace every known variable in a type. -/
partial def zonk (t : Ty) : M Ty := do
  match ← find t with
  | .var id => pure (.var id)
  | .con n args => do
    pure (.con n (← args.mapM zonk))
  | .tuple args => do
    pure (.tuple (← args.mapM zonk))
  | .fn ps r effs tail cap => do
    let row ← zonkRow ⟨effs, tail⟩
    pure (.fn (← ps.mapM zonk) (← zonk r) row.effs row.tail (← findCap cap))
  | .ref how t cap => do
    pure (.ref (← zonk how) (← zonk t) (← findCap cap))

partial def zonkRow (r : Row) : M Row := do
  let r ← flattenRow r
  let effs ← r.effs.mapM fun (n, args) => do
    pure (n, ← args.mapM zonk)
  pure ⟨dedupe effs, r.tail⟩

end

/-! ## Printing -/

/-- A function's own type parameter is stored with a mark and its owner; show
only the name as written. -/
def bareName (n : String) : String :=
  let base := (n.splitOn "@").headD n
  if base.startsWith "'" then (base.drop 1).toString else base

/-- The whole number a type of the prelude stands for, if it is one of those:
`B1<B0<B1<Z>>>` is five. -/
partial def numberOf : Ty → Option Nat
  | .con "Z" [] => some 0
  | .con "B0" [n] => (numberOf n).map (2 * ·)
  | .con "B1" [n] => (numberOf n).map (2 * · + 1)
  | _ => none

mutual

partial def showTy : Ty → String
  | .var _ => "_"
  | .con n [] => if bareName n == Syntax.neverParam then "!" else if n == "Z" then "0" else bareName n
  | .con n args =>
    -- (A length is shown as the number, and an array with one as written.)
    match numberOf (.con n args), n, args with
    | some k, _, _ => toString k
    | none, "Fixed", [element, length] => s!"[{showTy element}; {showTy length}]"
    | none, "Array", [element] => s!"[{showTy element}]"
    | none, _, _ => s!"{bareName n}<{", ".intercalate (args.map showTy)}>"
  | .tuple [one] => s!"({showTy one},)"
  | .tuple args => s!"({", ".intercalate (args.map showTy)})"
  | .fn ps r effs _ _ =>
    let sig := s!"fn({", ".intercalate (ps.map showTy)}) -> {showTy r}"
    if effs.isEmpty then sig else s!"{sig} / {showEffs effs}"
  | .ref (.con "&mut" []) t _ => s!"&mut {showTy t}"
  | .ref (.con "'" []) _ _ => "'_"
  | .ref _ t _ => s!"&{showTy t}"

partial def showEffs (effs : List (String × List Ty)) : String :=
  let one := fun (e : String × List Ty) =>
    if e.2.isEmpty then e.1 else s!"{e.1}<{", ".intercalate (e.2.map showTy)}>"
  "{" ++ ", ".intercalate (effs.map one) ++ "}"

end

/-! ## Free variables, substitution, generalisation -/

mutual

partial def freeTys : Ty → List Nat
  | .var id => [id]
  | .con _ args => args.flatMap freeTys
  | .tuple args => args.flatMap freeTys
  | .fn ps r effs _ _ =>
    ps.flatMap freeTys ++ freeTys r ++ effs.flatMap (fun e => e.2.flatMap freeTys)
  | .ref how t _ => freeTys how ++ freeTys t

partial def freeRows : Ty → List Nat
  | .var _ => []
  | .con _ args => args.flatMap freeRows
  | .tuple args => args.flatMap freeRows
  | .fn ps r effs tail _ =>
    ps.flatMap freeRows ++ freeRows r ++ effs.flatMap (fun e => e.2.flatMap freeRows)
      ++ tail.toList
  | .ref _ t _ => freeRows t

end

partial def freeCaps : Ty → List Nat
  | .var _ => []
  | .con _ args => args.flatMap freeCaps
  | .tuple args => args.flatMap freeCaps
  | .fn ps r effs _ cap =>
    cap :: (ps.flatMap freeCaps ++ freeCaps r ++ effs.flatMap (fun e => e.2.flatMap freeCaps))
  | .ref _ t cap => cap :: freeCaps t

/-- Replace variables: type variables by types, row and capture variables by
variables of their own kind. -/
partial def subst (tm : List (Nat × Ty)) (rm cm : List (Nat × Nat)) : Ty → Ty
  | .var id => (tm.lookup id).getD (.var id)
  | .con n args => .con n (args.map (subst tm rm cm))
  | .tuple args => .tuple (args.map (subst tm rm cm))
  | .fn ps r effs tail cap =>
    .fn (ps.map (subst tm rm cm)) (subst tm rm cm r)
      (effs.map fun (n, args) => (n, args.map (subst tm rm cm)))
      (tail.map fun id => (rm.lookup id).getD id)
      ((cm.lookup cap).getD cap)
  | .ref how t cap => .ref (subst tm rm cm how) (subst tm rm cm t) ((cm.lookup cap).getD cap)

/-- A constructor's field types in a value of its type applied to `args`,
which are types and, where the type has lifetime parameters, lifetimes. -/
def CtorSig.fieldsAt (sig : CtorSig) (args : List Ty) : List Ty :=
  if sig.cvars.isEmpty then sig.fields.map (subst (sig.tvars.zip args) [] [])
  else
    let paired := sig.kinds.zip args
    let types := paired.filterMap fun (life, a) => if life then none else some a
    let caps := (paired.filter (·.1)).map fun (_, a) =>
      match a with
      | .ref _ _ cap => some cap
      | _ => none
    let cm := (sig.cvars.zip caps).filterMap fun (c, cap) => cap.map fun cap => (c, cap)
    sig.fields.map (subst (sig.tvars.zip types) [] cm)

/-- Arguments for an effect, all new: a type for each type parameter, a
lifetime for each lifetime. -/
def EffectDecl.fresh (d : EffectDecl) : M (List Ty) := do
  (d.tvars.zip (d.lifetimes ++ d.tvars.map fun _ => false)).mapM fun (_, life) => do
    if life then pure (Ty.life (← freshCap)) else freshTy

/-- What a type a trait leaves at types is, `said` with what it takes,
`takes`, as `asked`: types for its type parameters, and for a lifetime the
lifetime asked. `own` is the implementation's own type parameters. -/
def gatAt (own : List (Nat × Ty)) (takes : List (Bool × Nat)) (asked : List Ty) (said : Ty) : Ty :=
  let pairs := takes.zip asked
  let tm := pairs.filterMap fun ((life, id), t) => if life then none else some (id, t)
  let cm := pairs.filterMap fun ((life, id), t) =>
    match life, t with
    | true, .ref _ _ c => some (id, c)
    | _, _ => none
  subst (own ++ tm) [] cm said

/-- A type with each `Syntax.projMark` in it a new variable, asked of its
trait for the type it names: what an implementation says one of its trait's
types is, at one use of it. -/
partial def unproject : Ty → M Ty
  | .con n args => do
    if n == Syntax.projMark then
      match args with
      | [self, .con tr [], .con name []] =>
        let self ← unproject self
        let a ← freshTy
        modify fun s => { s with assocUses := s.assocUses.push (tr, self, name, a, s.owner, s.pos) }
        pure a
      | _ => pure (.con n args)
    else pure (.con n (← args.mapM unproject))
  | .tuple ps => do pure (.tuple (← ps.mapM unproject))
  | .fn ps r effs tail cap => do
    pure (.fn (← ps.mapM unproject) (← unproject r)
      (← effs.mapM fun (e, args) => do pure (e, ← args.mapM unproject)) tail cap)
  | .ref how t cap => do pure (.ref how (← unproject t) cap)
  | t => pure t

/-- A type with every capture variable replaced by a new one. -/
def freshenCaps (t : Ty) : M Ty := do
  let t ← zonk t
  let cm ← (freeCaps t).eraseDups.mapM fun c => do pure (c, ← freshCap)
  pure (subst [] [] cm t)

def instantiate (s : Scheme) (via : Option String := none) (fixed : List (Nat × Ty) := []) :
    M Ty := do
  -- (`fixed`: the type parameters the call wrote types for.)
  let tm ← s.tvars.mapM fun id => do
    match fixed.lookup id with
    | some t => pure (id, t)
    | none => pure (id, ← freshTy)
  let rm ← s.rvars.mapM fun id => do
    pure (id, ← freshRowVar)
  if (← get).anyMust then
    modify fun st => { st with instRows := rm.map (·.2) ++ st.instRows }
  let cm ← s.cvars.mapM fun id => do
    pure (id, ← freshCap)
  for (cap, what) in s.edges do
    captures ((cm.lookup cap).getD cap) (match what with
      | .ty t => .ty (subst tm rm cm t)
      | .brand b => .brand b
      | .once => .once
      | .must => .must
      | .loan l => .loan l
      | .touch b w => .touch b w
      | .inner l => .inner l)
  let pos := (← get).pos
  for (t, why) in s.drops do
    let why := match via with
      | some f => s!"{pos}`{f}` may leave what it is given unused"
      | none => why
    modify fun st => { st with drops := st.drops.push (subst tm rm cm t, why) }
  for (t, why) in s.stays do
    let why := match via with
      | some f => s!"{pos}`{f}` holds a value that has to be used while it calls what it is given"
      | none => why
    modify fun st => { st with stays := st.stays.push (subst tm rm cm t, why) }
  for (t, why) in s.quiets do
    modify fun st => { st with quiets := st.quiets.push (subst tm rm cm t, pos ++ why) }
  for (t, why) in s.dups do
    -- At a use, the reason is the function's need rather than its inner detail.
    let why := match via with
      | some f => s!"{pos}`{f}` may use what it is given more than once"
      | none => why
    modify fun st => { st with dups := st.dups.push (subst tm rm cm t, why) }
  modify fun st => { st with lastBounds := s.bounds.map fun (tr, t) => (tr, subst tm rm cm t)
                             lastSites := s.sites.map (subst tm rm cm) }
  for (cap, lifetimes) in s.ranked do
    let here := ((cm.lookup cap).getD cap, lifetimes.map fun (q, name) => ((cm.lookup q).getD q, name))
    modify fun st => { st with ranked := here :: st.ranked }
  for (tr, subject, name, a) in s.assocs do
    let use := (tr, subst tm rm cm subject, name, subst tm rm cm a)
    modify fun st =>
      { st with assocUses := st.assocUses.push (use.1, use.2.1, use.2.2.1, use.2.2.2, st.owner, st.pos) }
  for (callee, amb) in s.incls do
    if let (.fn _ _ effs tail _, .fn _ _ effs' tail' _) := (subst tm rm cm callee, subst tm rm cm amb) then
      let what := match via with
        | some f => s!"`{f}`"
        | none => "this"
      modify fun st => { st with rowIncl := st.rowIncl.push (⟨effs, tail⟩, ⟨effs', tail'⟩, st.pos ++ what) }
  pure (subst tm rm cm s.ty)

/-- Replace a function's own type parameters, which stood for themselves while
its body was checked, by variables. -/
partial def openParams (seen : List (String × Ty)) : Ty → M (Ty × List (String × Ty))
  | .var id => pure (.var id, seen)
  | .con n [] =>
    if n.startsWith "'" then
      match seen.lookup n with
      | some t => pure (t, seen)
      | none => do
        let t ← freshTy
        pure (t, (n, t) :: seen)
    else pure (.con n [], seen)
  | .con n args => do
    let (args, seen) ← openAll seen args
    pure (.con n args, seen)
  | .tuple args => do
    let (args, seen) ← openAll seen args
    pure (.tuple args, seen)
  | .fn ps r effs tail cap => do
    let (ps, seen) ← openAll seen ps
    let (r, seen) ← openParams seen r
    let mut seen := seen
    let mut effs' : Array (String × List Ty) := #[]
    for (n, args) in effs do
      let (args, s) ← openAll seen args
      seen := s
      effs' := effs'.push (n, args)
    pure (.fn ps r effs'.toList tail cap, seen)
  | .ref how t cap => do
    let (t, seen) ← openParams seen t
    pure (.ref how t cap, seen)
where
  openAll (seen : List (String × Ty)) (ts : List Ty) : M (List Ty × List (String × Ty)) := do
    let mut seen := seen
    let mut out : Array Ty := #[]
    for t in ts do
      let (t, s) ← openParams seen t
      seen := s
      out := out.push t
    pure (out.toList, seen)

/-- Generalise every variable of a type that nothing else depends on: not a
declaration's inferred type, and not any of the types in `keep`. The capture
variables generalised are those of the type and those they capture in turn,
together with what each captures. -/
def generalize (t : Ty) (keep : List Ty := []) (top : Bool := true) : M Scheme := do
  -- A function's own type parameters become variables only once the whole
  -- function is done; inside it they stay fixed.
  let t ← if top then (·.1) <$> openParams [] (← zonk t) else pure t
  let t ← zonk t
  let s ← get
  -- (Sets, and nothing appended to a list: what declarations fix is as much
  -- as the program and its library declare, and this runs for every
  -- function and every callable written in one.)
  let mut fixedTys : Std.HashSet Nat := {}
  let mut fixedRows : Std.HashSet Nat := {}
  let mut fixedCaps : Std.HashSet Nat := {}
  for id in s.monoCaps do
    fixedCaps := fixedCaps.insert (← findCap id)
  -- A local callable is used at one type where a trait is needed of it: the
  -- evidence is found for the function it is written in, once.
  let bounded := if top then [] else s.bounds.toList.map (·.ty)
  for m in keep ++ bounded ++ s.mono.map Ty.var do
    let m ← zonk m
    fixedTys := (freeTys m).foldl (·.insert ·) fixedTys
    fixedRows := (freeRows m).foldl (·.insert ·) fixedRows
    fixedCaps := (freeCaps m).foldl (·.insert ·) fixedCaps
  for id in s.monoRows do
    let r ← zonkRow ⟨[], some id⟩
    fixedRows := r.tail.toList.foldl (·.insert ·) fixedRows
    for (_, args) in r.effs do
      for a in args do
        fixedTys := (freeTys a).foldl (·.insert ·) fixedTys
        fixedRows := (freeRows a).foldl (·.insert ·) fixedRows
        fixedCaps := (freeCaps a).foldl (·.insert ·) fixedCaps
  -- What must be free to use more than once is part of the function's
  -- contract, so the capture variables it mentions are generalised too.
  let mut dups : Array (Ty × String) := #[]
  for (d, why) in s.dups do
    dups := dups.push (← zonk d, why)
  let mut drops : Array (Ty × String) := #[]
  for (d, why) in s.drops do
    drops := drops.push (← zonk d, why)
  let mut stays : Array (Ty × String) := #[]
  for (d, why) in s.stays do
    stays := stays.push (← zonk d, why)
-- Capture variables reachable from the type through what they capture,
  -- and what each captures: found from the type outwards, not by going
  -- through every edge of the program.
  --
  -- What is needed of a type is part of the function's contract only where
  -- it is about something whoever uses the function decides: one of the
  -- type variables the function is general in, or something its type
  -- holds. The capture variables such a need mentions are then the
  -- function's too. A need about what the function made for itself was
  -- settled when the function was checked: passed on, every use of the
  -- function would ask it again, with a copy of all it mentions, and so
  -- would every use of whatever used it.
  let general := (freeTys t).eraseDups.filter (!fixedTys.contains ·)
  let generalSet : Std.HashSet Nat := general.foldl (·.insert ·) {}
  let needs := (dups.toList ++ drops.toList ++ stays.toList).map (·.1)
  let mut pending := needs.map fun d => (freeTys d, freeCaps d)
  -- (`reach` in the order found, and the same as a set to ask of: what a
  -- type holds can be a great deal, and each was looked for in a list.)
  let mut reach : List Nat := (freeCaps t).eraseDups
  let mut reached : Std.HashSet Nat := reach.foldl (·.insert ·) {}
  let mut todo := reach
  let mut found : Array (Nat × Nat × Captured) := #[]
  let mut more := true
  while more do
    more := false
    while !todo.isEmpty do
      let mut next : List Nat := []
      let mut nextSet : Std.HashSet Nat := {}
      for c in todo do
        let root ← findCap c
        for i in s.capOut.getD root #[] do
          match s.capEdges.get? i with
          | some (_, .ty target) =>
            -- What a block shares with the block it runs in place of, the
            -- other holds: it is no part of what this one's type says it holds.
            if s.sharedEdges.contains i then continue
            let target ← zonk target
            found := found.push (i, root, .ty target)
            for c in freeCaps target do
              unless reached.contains c || nextSet.contains c do
                next := c :: next
                nextSet := nextSet.insert c
          | some (_, what) => found := found.push (i, root, what)
          | none => pure ()
      reach := reach ++ next
      reached := next.foldl (·.insert ·) reached
      todo := next
    -- The needs that are about what has been reached so far.
    let mut rest : List (List Nat × List Nat) := []
    let mut todoSet : Std.HashSet Nat := {}
    for (tys, caps) in pending do
      if tys.any generalSet.contains || caps.any reached.contains then
        for c in caps do
          unless reached.contains c || todoSet.contains c do
            todo := c :: todo
            todoSet := todoSet.insert c
        more := true
      else rest := (tys, caps) :: rest
    pending := rest
    reach := reach ++ todo
    reached := todo.foldl (·.insert ·) reached
  -- (In the order the edges were made.)
  let all := (found.qsort fun a b => a.1 < b.1).map fun (_, root, what) => (root, what)
  let cvars := reach.filter (!fixedCaps.contains ·)
  let cset : Std.HashSet Nat := cvars.foldl (·.insert ·) {}
  let tvars := general
  let mine := dups.toList.filter fun (d, _) =>
    (freeTys d).any generalSet.contains || (freeCaps d).any cset.contains
  let unused := drops.toList.filter fun (d, _) =>
    (freeTys d).any generalSet.contains || (freeCaps d).any cset.contains
  pure { tvars, rvars := (freeRows t).eraseDups.filter (!fixedRows.contains ·), cvars,
         edges := all.toList.filter (cset.contains ·.1), dups := mine, ty := t,
         drops := unused,
         stays := stays.toList.filter fun (d, _) =>
           (freeTys d).any generalSet.contains || (freeCaps d).any cset.contains }

/-- Does the type have one of a function's own type parameters in it? -/
partial def Ty.hasRigid : Ty → Bool
  | .con n args => n.startsWith "'" || args.any Ty.hasRigid
  | .tuple args => args.any Ty.hasRigid
  | .ref _ t _ => Ty.hasRigid t
  | _ => false

/-- The functions of their own of the types a dot call may be of, as the
resolver found them. (A call in a function an implementation takes from its
trait is the trait's, its number moved on by `10000000000` times one more
than the implementation's place: its alternatives are the trait's call's.) -/
def dotAltsOf (modules : Syntax.ModuleInfo) (call : Nat) : Option (List String) :=
  modules.dotAlts.lookup call <|> (if call ≥ 10000000000 then modules.dotAlts.lookup (call % 10000000000) else none)

end Glorious.Check
