import Glorious.Syntax.Ast
import Glorious.Elab
import Glorious.Traits

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
  /-- A resumption that has to be resumed or cancelled. -/
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
  /-- The traits the function needs of its type parameters, in the order it is
  given the evidence: each a trait and one of `tvars`. -/
  bounds : List (String × Ty) := []
  /-- The callables in the type that are for every lifetime: see `St.ranked`. -/
  ranked : List (Nat × List (Nat × String)) := []
  /-- Types left to implementations that the type mentions: see `St.assocUses`. -/
  assocs : List (String × Ty × String × Ty) := []

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
  /-- Declared `[1, 1]`: its resumption has to be resumed or cancelled. -/
  must : Bool := false
  /-- For each parameter of the effect, in order: the capture variable it is
  in the types above if it is a lifetime, none if it is a type. -/
  lifetimes : List (Option Nat) := []

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
  pvars : List (String × Nat) := []

/-- A trait needed of a type at a call: of the type a trait's function is used
at, or of a type parameter of the function called. -/
structure Bound where
  trait : String
  ty : Ty
  call : Nat
  slot : Nat
  owner : String
  pos : String

/-- A use of a function inside the group it is inferred with: its bounds are
not known until the group is done. `call` is zero where it is not called. -/
structure GroupUse where
  call : Nat
  callee : String
  owner : String
  pos : String

structure St where
  tys : Array (Option Ty) := #[]
  rows : Array (Option Row) := #[]
  /-- Variables standing for the inferred types of declarations: never generalised. -/
  mono : List Nat := []
  monoRows : List Nat := []
  /-- Capture variables of function types written in declarations. -/
  monoCaps : List Nat := []
  /-- Capture variables, merged as function types are unified. -/
  caps : Array (Option Nat) := #[]
  /-- What each capture variable is known to capture. -/
  capEdges : Array (Nat × Captured) := #[]
  /-- For each of `capEdges`, the name captured, where a callable written in
  the program captured a name. -/
  capEdgeNames : Array (Option (String × Nat)) := #[]
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
  /-- The borrows of a field made through a reference in the function being
  checked: what each holds, and where. Such a borrow is a variable of the
  function's while it lasts, so it cannot leave the function. -/
  fieldCaps : Array (Nat × String) := #[]
  /-- For each field read by name, which field it is: for the elaborator. -/
  fieldReads : Array (Nat × Nat) := #[]
  /-- Borrows of a field, to settle once the type is known: the borrow, the
  type of what the variable holds, the way to the field, and where. -/
  fieldSites : Array (Nat × Bool × Ty × List Nat × List (Option String) × String × String) := #[]
  /-- For each, what is gone through to reach the field: at each step the
  constructor, or none for a tuple, and how many fields it has. -/
  fieldTable : Array (Nat × Bool × List Nat × List (Option String × Nat)) := #[]
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
  sharedEdges : List Nat := []
  /-- Of those, the ones taken to be given one particular block, to be
  confirmed when the whole program is known. -/
  assumedLinks : Array (Nat × Nat × Ty × String) := #[]
  /-- Values that are let go if a call does not come back: the call, the type,
  and the message. -/
  abandoned : Array (Nat × Ty × String) := #[]
  /-- The calls that certainly come back if they end at all: the callee
  performs nothing and can jump to no label. -/
  sure : List Nat := []
  /-- Bindings whose use on every path is still to be looked at, once the
  types of the function they are in are known: where, the name, its type, the
  other names in scope, and the code the name is in scope of. -/
  lowerChecks : Array (String × String × Ty × List String × List Stmt) := #[]

  /-- The clauses of every top-level function, for following calls when uses
  are counted. -/
  fnBodies : List (String × List Clause) := []
  /-- Calls whose callee has effects not yet known: the callee's row, the row
  permitted where it is called, and a description of the call. -/
  rowIncl : Array (Row × Row × String) := #[]
  types : List (String × TypeDecl) := []
  ctors : List (String × CtorSig) := []
  ops : List (String × OpSig) := []
  effects : List (String × EffectDecl) := []
  aliases : List (String × Expr) := []
  fns : List (String × Scheme) := []
  /-- The functions being inferred together, with their types so far. -/
  group : List (String × Ty) := []
  pending : Array Pending := #[]
  /-- Field reads whose subject was not yet known: subject, index, field type,
  and where the read is. -/
  projections : Array (Ty × Nat × Ty × String) := #[]
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
  /-- The values the expression being checked has computed and not yet used,
  each with how many borrows had been made when it was computed. -/
  temps : List (Ty × Nat) := []
  loans : Array Loan := #[]
  /-- Mutable variables, by the brand of their block: the name, and the type held. -/
  cells : Array (Nat × String × Ty) := #[]
  /-- Uses to check against the borrows once the types are known. -/
  uses : Array Use := #[]
  /-- The functions of each trait, in order. -/
  traits : List (String × List String) := []
  methods : List (String × MethodSig) := []
  impls : Array ImplDecl := #[]
  /-- The implementations as `Traits.solve` sees them, in the same order. -/
  kimpls : List Traits.Impl := []
  /-- The bounds of the scheme last instantiated, at that use. -/
  lastBounds : List (String × Ty) := []
  /-- Bounds to meet once the types of the group being inferred are known. -/
  bounds : Array Bound := #[]
  groupUses : Array GroupUse := #[]
  /-- A function's own type parameters that bounds were needed of, each with
  the number it has for `Traits.solve`. -/
  rigidKeys : Array String := #[]
  /-- What the implementation being checked assumes of its type parameters. -/
  implGivens : Option (List (String × Ty)) := none
  /-- Where the statement being checked starts. -/
  at_ : Nat × Nat := (0, 0)
  /-- Variables whose value is destroyed if its type turns out to have `Drop`:
  the place, the type, and where to report a failure. -/
  dropCands : Array (Elab.DropSite × Ty × String) := #[]
  dropSites : Array (Elab.DropSite × Nat) := #[]
  /-- How each call's bounds are met, for the elaborator. -/
  dictTable : Array (Nat × List Elab.DictE) := #[]
  methodCalls : Array (Nat × Nat) := #[]
  fnBounds : List (String × Nat) := []

abbrev M := StateT St (Except String)

instance {α : Type} : Inhabited (M α) := ⟨throw "checker: unreachable"⟩

def freshTy : M Ty := do
  let s ← get
  set { s with tys := s.tys.push none }
  pure (.var s.tys.size)

def freshRowVar : M Nat := do
  let s ← get
  set { s with rows := s.rows.push none }
  pure s.rows.size

def freshRow : M Row := do
  pure ⟨[], some (← freshRowVar)⟩

def freshCap : M Nat := do
  let s ← get
  set { s with caps := s.caps.push none }
  pure s.caps.size

def freshBrand : M Nat := do
  let s ← get
  set { s with brands := s.brands + 1 }
  pure s.brands

/-- The representative of a capture variable. -/
partial def findCap (c : Nat) : M Nat := do
  match (← get).caps[c]? with
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
    | some _, none => modify fun s => { s with caps := s.caps.set! rb (some ra) }
    | _, _ => modify fun s => { s with caps := s.caps.set! ra (some rb) }

def captures (cap : Nat) (what : Captured) (name : Option (String × Nat) := none) : M Unit :=
  modify fun s =>
    { s with capEdges := s.capEdges.push (cap, what), capEdgeNames := s.capEdgeNames.push name }

/-- Follow a type variable to what it stands for. -/
partial def find (t : Ty) : M Ty := do
  match t with
  | .var id =>
    match (← get).tys[id]? with
    | some (some t') => find t'
    | _ => pure t
  | _ => pure t

/-- Expand a row's tail as far as it is known. -/
partial def flattenRow (r : Row) : M Row := do
  match r.tail with
  | none => pure r
  | some id =>
    match (← get).rows[id]? with
    | some (some r') => do
      let rest ← flattenRow r'
      pure ⟨r.effs ++ rest.effs, rest.tail⟩
    | _ => pure r

def dedupe (effs : List (String × List Ty)) : List (String × List Ty) :=
  effs.foldl (fun acc e => if acc.any (·.1 == e.1) then acc else acc ++ [e]) []

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

mutual

partial def showTy : Ty → String
  | .var _ => "_"
  | .con n [] => bareName n
  | .con n args => s!"{bareName n}<{", ".intercalate (args.map showTy)}>"
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

/-- A type with every capture variable replaced by a new one. -/
def freshenCaps (t : Ty) : M Ty := do
  let t ← zonk t
  let cm ← (freeCaps t).eraseDups.mapM fun c => do pure (c, ← freshCap)
  pure (subst [] [] cm t)

def instantiate (s : Scheme) (via : Option String := none) : M Ty := do
  let tm ← s.tvars.mapM fun id => do
    pure (id, ← freshTy)
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
  for (t, why) in s.dups do
    -- At a use, the reason is the function's need rather than its inner detail.
    let why := match via with
      | some f => s!"{pos}`{f}` may use what it is given more than once"
      | none => why
    modify fun st => { st with dups := st.dups.push (subst tm rm cm t, why) }
  modify fun st => { st with lastBounds := s.bounds.map fun (tr, t) => (tr, subst tm rm cm t) }
  for (cap, lifetimes) in s.ranked do
    let here := ((cm.lookup cap).getD cap, lifetimes.map fun (q, name) => ((cm.lookup q).getD q, name))
    modify fun st => { st with ranked := here :: st.ranked }
  for (tr, subject, name, a) in s.assocs do
    let use := (tr, subst tm rm cm subject, name, subst tm rm cm a)
    modify fun st =>
      { st with assocUses := st.assocUses.push (use.1, use.2.1, use.2.2.1, use.2.2.2, st.owner, st.pos) }
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
  let mut fixedTys : List Nat := []
  let mut fixedRows : List Nat := []
  let mut fixedCaps : List Nat := []
  for id in s.monoCaps do
    fixedCaps := (← findCap id) :: fixedCaps
  -- A local callable is used at one type where a trait is needed of it: the
  -- evidence is found for the function it is written in, once.
  let bounded := if top then [] else s.bounds.toList.map (·.ty)
  for m in keep ++ bounded ++ s.mono.map Ty.var do
    let m ← zonk m
    fixedTys := fixedTys ++ freeTys m
    fixedRows := fixedRows ++ freeRows m
    fixedCaps := fixedCaps ++ freeCaps m
  for id in s.monoRows do
    let r ← zonkRow ⟨[], some id⟩
    fixedRows := fixedRows ++ r.tail.toList
    for (_, args) in r.effs do
      for a in args do
        fixedTys := fixedTys ++ freeTys a
        fixedRows := fixedRows ++ freeRows a
        fixedCaps := fixedCaps ++ freeCaps a
  -- Capture variables reachable from the type through what they capture.
  let mut edges : Array (Nat × Ty) := #[]
  let mut all : Array (Nat × Captured) := #[]
  for ((cap, what), i) in s.capEdges.zipIdx do
    let root ← findCap cap
    match what with
    | .ty target =>
      -- What a block shares with the block it runs in place of, the other
      -- holds: it is no part of what this one's type says it holds.
      if s.sharedEdges.contains i then continue
      let target ← zonk target
      edges := edges.push (root, target)
      all := all.push (root, .ty target)
    | .brand b => all := all.push (root, .brand b)
    | .once => all := all.push (root, .once)
    | .must => all := all.push (root, .must)
    | .loan l => all := all.push (root, .loan l)
    | .touch b w => all := all.push (root, .touch b w)
    | .inner l => all := all.push (root, .inner l)
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
  let mut reach : List Nat := (freeCaps t ++ dups.toList.flatMap (freeCaps ·.1)
    ++ drops.toList.flatMap (freeCaps ·.1) ++ stays.toList.flatMap (freeCaps ·.1)).eraseDups
  let mut todo := reach
  while !todo.isEmpty do
    let mut next : List Nat := []
    for (cap, target) in edges do
      if todo.contains cap then
        for c in freeCaps target do
          unless reach.contains c || next.contains c do next := c :: next
    reach := reach ++ next
    todo := next
  let cvars := reach.filter (!fixedCaps.contains ·)
  let tvars := (freeTys t).eraseDups.filter (!fixedTys.contains ·)
  let mine := dups.toList.filter fun (d, _) =>
    (freeTys d).any tvars.contains || (freeCaps d).any cvars.contains
  let unused := drops.toList.filter fun (d, _) =>
    (freeTys d).any tvars.contains || (freeCaps d).any cvars.contains
  pure { tvars, rvars := (freeRows t).eraseDups.filter (!fixedRows.contains ·), cvars,
         edges := all.toList.filter (cvars.contains ·.1), dups := mine, ty := t,
         drops := unused,
         stays := stays.toList.filter fun (d, _) =>
           (freeTys d).any tvars.contains || (freeCaps d).any cvars.contains }

end Glorious.Check
