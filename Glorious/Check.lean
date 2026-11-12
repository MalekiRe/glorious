import Glorious.Syntax.Ast
import Glorious.Elab
import Glorious.Traits

/-!
# Type and effect inference

Checks a program before it is elaborated. Types and effects are inferred:
annotations on functions are optional, and a field of a data or operation
declaration written as a bare name has its type inferred from how the program
uses it. A declaration with type parameters is polymorphic; one with inferred
fields has a single type throughout the program.

The checker establishes that values are used at consistent types, that calls
supply the right number of arguments, that pattern clauses cover every case,
that every effect a program performs is handled before it reaches `main`, that
no callable able to jump to a label can be called after the label's scope has
ended, that nothing able to reach a mutable variable outlives the block the
variable is declared in, that a variable is not used against a borrow of it
that is still held, and that nothing holding a resumption is used more than
once. This pass is not proved.

A trait's function is used at a type that has the trait. Which implementation
a use needs is found by `Traits.solve`, which is proved to find only evidence
that the bound is met, and evidence that is the only evidence there is.
-/

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

structure TypeDecl where
  arity : Nat
  ctors : List String

structure CtorSig where
  owner : String
  tvars : List Nat
  fields : List Ty
  result : Ty

structure OpSig where
  effect : String
  tvars : List Nat
  payload : List Ty
  /-- What the operation returns to its performer; none if it never returns. -/
  result : Option Ty
  /-- Declared `[1, 1]`: its resumption has to be resumed or cancelled. -/
  must : Bool := false

structure EffectDecl where
  tvars : List Nat
  ops : List String

/-- What a local name stands for. -/
inductive Binding where
  | val (t : Ty)
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
  | var (brand : Nat) (name : String) (how : Using)
  /-- Reading or writing through a reference, or lending it. -/
  | through (cap : Nat) (name : String) (write : Bool)
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

structure ImplDecl where
  trait : String
  head : String
  params : List String
  /-- The conditions: each a trait and which of the head's arguments must have it. -/
  context : List (String × Nat)
  methods : List Item
  dictFn : String

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
  capEdgeNames : Array (Option String) := #[]
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
  unrunGiven : Array (Nat × Nat × Ty × List String × String × Nat) := #[]
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
    modify fun s => { s with caps := s.caps.set! ra (some rb) }

def captures (cap : Nat) (what : Captured) (name : Option String := none) : M Unit :=
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

private def dedupe (effs : List (String × List Ty)) : List (String × List Ty) :=
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
private def bareName (n : String) : String :=
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

/-! ## Unification -/

private def bindTy (id : Nat) (t : Ty) : M Unit := do
  if (freeTys (← zonk t)).contains id then
    throw "this would need a type that contains itself"
  modify fun s => { s with tys := s.tys.set! id (some t) }

private def bindRow (id : Nat) (r : Row) : M Unit :=
  modify fun s => { s with rows := s.rows.set! id (some r) }

mutual

partial def unify (a b : Ty) : M Unit := do
  let a ← find a
  let b ← find b
  match a, b with
  | .var i, .var j => if i == j then pure () else bindTy i b
  | .var i, _ => bindTy i b
  | _, .var j => bindTy j a
  | .con n as, .con m bs =>
    if n == m && as.length == bs.length then unifyAll as bs else mismatch a b
  | .tuple as, .tuple bs => if as.length == bs.length then unifyAll as bs else mismatch a b
  | .fn ps r e1 t1 c1, .fn qs s e2 t2 c2 =>
    if ps.length == qs.length then do
      unifyAll ps qs
      unify r s
      unifyRow ⟨e1, t1⟩ ⟨e2, t2⟩
      unifyCap c1 c2
    else mismatch a b
  | .ref h1 x c1, .ref h2 y c2 => do
    try unify h1 h2
    catch _ => mismatch a b
    unify x y
    unifyCap c1 c2
  | _, _ => mismatch a b

partial def mismatch (a b : Ty) : M Unit := do
  throw s!"`{showTy (← zonk a)}` is not `{showTy (← zonk b)}`"

partial def unifyAll (as bs : List Ty) : M Unit := do
  for (a, b) in as.zip bs do
    unify a b

/-- Unify two effect rows as sets of effects. -/
partial def unifyRow (r1 r2 : Row) : M Unit := do
  let r1 ← flattenRow r1
  let r2 ← flattenRow r2
  let e1 ← collapse r1.effs
  let e2 ← collapse r2.effs
  for (n, args) in e1 do
    match e2.lookup n with
    | some args' => unifyAll args args'
    | none => pure ()
  let only1 := e1.filter fun e => (e2.lookup e.1).isNone
  let only2 := e2.filter fun e => (e1.lookup e.1).isNone
  let unhandled := fun (e : String × List Ty) =>
    (throw s!"effect `{e.1}` is not handled here" : M Unit)
  match r1.tail, r2.tail with
  | none, none =>
    match only1 ++ only2 with
    | e :: _ => unhandled e
    | [] => pure ()
  | some i, none =>
    match only1 with
    | e :: _ => unhandled e
    | [] => bindRow i ⟨only2, none⟩
  | none, some j =>
    match only2 with
    | e :: _ => unhandled e
    | [] => bindRow j ⟨only1, none⟩
  | some i, some j =>
    if i == j then
      match only1 ++ only2 with
      | e :: _ => unhandled e
      | [] => pure ()
    else do
      let k ← freshRowVar
      bindRow i ⟨only2, some k⟩
      bindRow j ⟨only1, some k⟩

/-- A row names each effect once: unify the arguments of repeated names. -/
partial def collapse (effs : List (String × List Ty)) : M (List (String × List Ty)) := do
  let mut out : List (String × List Ty) := []
  for (n, args) in effs do
    match out.lookup n with
    | some args' => unifyAll args args'
    | none => out := out ++ [(n, args)]
  pure out

end

/-- Unify, reporting a failure as a mismatch between what was expected and found. -/
def unifyAt (what : String) (expected actual : Ty) : M Unit := do
  try unify expected actual
  catch e =>
    let detail := if e.startsWith "effect" || e.startsWith "this would" then s!" ({e})" else ""
    throw s!"{what}: expected `{showTy (← zonk expected)}`, found `{showTy (← zonk actual)}`{detail}"

/-! ## The effects of a callee

A callee may perform fewer effects than are permitted where it is called. Its
named effects are required of the caller at once. If the rest of its effects is
still unknown, the call is remembered, and at the end of the function each
unknown is given the most that every place it is called from permits. Making a
callee's effects equal to its caller's instead would wrongly tie together two
calls of one function value made under different handlers.
-/

/-- The named effects of a callee must be permitted where it is called. -/
def includeNamed (callee amb : Row) (what : String) : M Unit := do
  let c ← flattenRow callee
  for (e, args) in dedupe c.effs do
    let a ← flattenRow amb
    try
      match a.effs.lookup e with
      | some args' => unifyAll args args'
      | none => unifyRow amb ⟨[(e, args)], some (← freshRowVar)⟩
    catch err => throw s!"{what} cannot be called here: {err}"

/-- The callee's unknown remaining effects, unless they are the caller's own. -/
def openTail (callee amb : Row) : M (Option Nat) := do
  let c ← flattenRow callee
  let a ← flattenRow amb
  match c.tail with
  | none => pure none
  | some ρ => pure (if a.tail == some ρ then none else some ρ)

def includeRow (callee amb : Row) (what : String) : M Unit := do
  includeNamed callee amb what
  if (← openTail callee amb).isSome then
    modify fun s => { s with rowIncl := s.rowIncl.push (callee, amb, s.pos ++ what) }

/--
Work through the remembered calls. Named effects are always passed on. With
`bind`, an unknown that `bind` accepts is then decided, newest first, since an
inner unknown should give way before an outer one: if every place it is called
from has the same remaining effects, it gets the named effects common to them
all; otherwise, and only when `final`, it is made equal to each in turn.
-/
partial def settleRows (bind : Option (Nat → Bool)) (final : Bool) : M Unit := do
  let pending := (← get).rowIncl
  modify fun s => { s with rowIncl := #[] }
  let mut left : Array (Row × Row × String × Nat) := #[]
  for (callee, amb, what) in pending do
    includeNamed callee amb what
    if let some ρ ← openTail callee amb then left := left.push (callee, amb, what, ρ)
  let restore : M Unit :=
    modify fun s => { s with rowIncl := left.map (fun (c, a, w, _) => (c, a, w)) ++ s.rowIncl }
  match bind with
  | none => restore
  | some ok =>
    let candidates := ((left.toList.map (·.2.2.2)).eraseDups.filter ok).mergeSort (· ≥ ·)
    for ρ in candidates do
      let mine := left.toList.filter (·.2.2.2 == ρ)
      let ambs ← mine.mapM fun (_, amb, _, _) => flattenRow amb
      match ambs with
      | [] => pure ()
      | first :: _ =>
        if ambs.all (·.tail == first.tail) && first.tail != some ρ then
          let common := (dedupe first.effs).filter fun (n, _) =>
            ambs.all fun a => a.effs.any (·.1 == n)
          modify fun s => { s with rows := s.rows.set! ρ (some ⟨common, first.tail⟩) }
          restore
          return ← settleRows bind final
        else if final then
          for (callee, amb, what, _) in mine do
            try unifyRow callee amb
            catch err => throw s!"{what} cannot be called here: {err}"
          restore
          return ← settleRows bind final
    restore

/-! ## Declarations -/

/-- A type left to be inferred from how the program uses a declaration. -/
private def inferredTy : M Ty := do
  let t ← freshTy
  match t with
  | .var id => modify fun s => { s with mono := id :: s.mono }
  | _ => pure ()
  pure t

mutual

/-- Read a type as written. In a declaration, a bare unknown name is a field
whose type is inferred; elsewhere it is an error. -/
partial def resolveType (params : List (String × Ty)) (decl : Bool) : TypeExpr → M Ty
  | .name x args => do
    match params.lookup x with
    | some t =>
      if args.isEmpty then pure t else throw s!"type parameter `{x}` takes no arguments"
    | none =>
      if x == "Int" then
        if args.isEmpty then pure .int else throw "`Int` takes no arguments"
      else
        match (← get).types.lookup x with
        | some d =>
          if d.arity != args.length then
            throw s!"type `{x}` takes {d.arity} arguments, but is given {args.length}"
          pure (.con x (← args.mapM (resolveType params decl)))
        | none =>
          if decl && args.isEmpty then inferredTy
          else throw s!"unknown type `{x}`"
  | .tuple args => do
    pure (.tuple (← args.mapM (resolveType params decl)))
  | .fn ps r => do
    let ps ← ps.mapM (resolveType params decl)
    let cap ← freshCap
    match r with
    | .performs r effects =>
      -- What it performs is said: these effects and no others.
      let r ← resolveType params decl r
      let effs ← resolveEffects params decl effects
      if decl then modify fun s => { s with monoCaps := cap :: s.monoCaps }
      pure (.fn ps r effs none cap)
    | _ =>
      let r ← resolveType params decl r
      let tail ← freshRowVar
      if decl then
        modify fun s => { s with monoRows := tail :: s.monoRows, monoCaps := cap :: s.monoCaps }
      pure (.fn ps r [] (some tail) cap)
  | .performs _ _ =>
    throw "what a callable performs is written after its result: `fn(A) -> R / {Effect}`"
  | .ref uniq t => do
    let cap ← freshCap
    if decl then modify fun s => { s with monoCaps := cap :: s.monoCaps }
    pure (.ref (if uniq then .uniq else .shared) (← resolveType params decl t) cap)
  | .never => throw "`!` can only be the result of an operation"
  | .hole => if decl then inferredTy else freshTy

/-- The effects written after a callable's result. An effect's arguments may
be left out, to be inferred. -/
partial def resolveEffects (params : List (String × Ty)) (decl : Bool)
    (effects : List (String × List TypeExpr)) : M (List (String × List Ty)) := do
  effects.mapM fun (name, args) => do
    match (← get).effects.lookup name with
    | none => throw s!"unknown effect `{name}`"
    | some d =>
      if args.isEmpty then
        pure (name, ← d.tvars.mapM fun _ => freshTy)
      else
        unless d.tvars.length == args.length do
          throw s!"effect `{name}` takes {d.tvars.length} arguments, but is given {args.length}"
        pure (name, ← args.mapM (resolveType params decl))

end

private def freshParams (names : List String) : M (List (String × Ty) × List Nat) := do
  let mut pairs : Array (String × Ty) := #[]
  let mut ids : Array Nat := #[]
  for n in names do
    match ← freshTy with
    | .var id =>
      pairs := pairs.push (n, .var id)
      ids := ids.push id
    | _ => pure ()
  pure (pairs.toList, ids.toList)

/-- A type with every callable in it performing nothing: what a trait's
function is given performs nothing its caller would have to handle. -/
partial def closeRows : Ty → Ty
  | .var id => .var id
  | .con n args => .con n (args.map closeRows)
  | .tuple args => .tuple (args.map closeRows)
  | .fn ps r _ _ cap => .fn (ps.map closeRows) (closeRows r) [] none cap
  | .ref how t cap => .ref how (closeRows t) cap

/-- Read the traits and their implementations. Types are declared by now. -/
def declareTraits (items : List Item) : M Unit := do
  -- `Drop` is the compiler's: its function is run on what a variable holds
  -- when the variable's block ends.
  let dropSelf ← match ← freshTy with
    | .var id => pure id
    | _ => pure 0
  let dropCap ← freshCap
  modify fun s =>
    { s with
      traits := ("Drop", ["drop"]) :: s.traits
      methods := ("drop", ⟨"Drop", 0, dropSelf, [.ref .uniq (.var dropSelf) dropCap], .unit⟩)
        :: s.methods }
  for item in items do
    if let .trait name methods := item then
      if ((← get).traits.lookup name).isSome then throw s!"trait `{name}` is declared twice"
      let self ← match ← freshTy with
        | .var id => pure id
        | _ => pure 0
      let mut index := 0
      for (m, params, ret) in methods do
        if ((← get).methods.lookup m).isSome then
          throw s!"`{m}` is declared twice as a function of a trait"
        let ps ← params.mapM fun p => closeRows <$> resolveType [("Self", .var self)] false p
        let r ← match ret with
          | some r => closeRows <$> resolveType [("Self", .var self)] false r
          | none => pure .unit
        let sig : MethodSig := ⟨name, index, self, ps, r⟩
        modify fun s => { s with methods := (m, sig) :: s.methods }
        index := index + 1
      modify fun s => { s with traits := (name, methods.map (·.1)) :: s.traits }
  for item in items do
    if let .impl params tr head args context methods := item then
      let what := s!"`impl {tr} for {head}`"
      let names ← match (← get).traits.lookup tr with
        | some ns => pure ns
        | none => throw s!"{what}: unknown trait `{tr}`"
      let arity ← if head == "Int" then pure 0
        else match (← get).types.lookup head with
          | some d => pure d.arity
          | none => throw s!"{what}: unknown type `{head}`"
      unless args.length == arity do
        throw s!"{what}: `{head}` takes {arity} type arguments, but is given {args.length}"
      unless args.eraseDups.length == args.length && args.all params.contains
          && params.all args.contains do
        throw s!"{what}: the arguments of `{head}` must be the type parameters after `impl`, each once"
      let ctx ← context.mapM fun (p, t') => do
        unless ((← get).traits.lookup t').isSome do throw s!"{what}: unknown trait `{t'}`"
        match args.idxOf? p with
        | some j => pure (t', j)
        | none => throw s!"{what}: `{p}` is not one of its type parameters"
      let given := methods.filterMap fun
        | .fn m _ _ _ _ => some m
        | _ => none
      for m in names do
        unless given.contains m do throw s!"{what} lacks the function `{m}`"
      for m in given do
        unless names.contains m do throw s!"{what}: `{m}` is not a function of `{tr}`"
      unless given.eraseDups.length == given.length do
        throw s!"{what} gives a function twice"
      if (← get).kimpls.any fun I => I.trait == tr && I.head == head then
        throw s!"`{tr}` is implemented twice for `{head}`"
      modify fun s =>
        { s with
          impls := s.impls.push ⟨tr, head, args, ctx, methods, Elab.implDictName tr head⟩
          kimpls := s.kimpls ++ [⟨tr, head, arity, ctx⟩] }
  -- What `Traits.coherent` asks of the implementations.
  unless Traits.noOverlap (← get).kimpls do
    throw "two implementations are for the same trait and type"

def declare (items : List Item) : M Unit := do
  -- Names first, so that declarations may refer to each other.
  for item in items do
    match item with
    | .enum name params ctors =>
      if ((← get).types.lookup name).isSome then throw s!"type `{name}` is declared twice"
      modify fun s =>
        { s with types := (name, ⟨params.length, ctors.map (·.1)⟩) :: s.types }
    | .struct name params _ =>
      if ((← get).types.lookup name).isSome then throw s!"type `{name}` is declared twice"
      modify fun s => { s with types := (name, ⟨params.length, [name]⟩) :: s.types }
    | .alias name value => modify fun s => { s with aliases := (name, value) :: s.aliases }
    | .coerce name => modify fun s => { s with coercing := s.coercing ++ [name] }
    | _ => pure ()
  for item in items do
    match item with
    | .enum name params ctors =>
      let (pmap, ids) ← freshParams params
      let result := Ty.con name (pmap.map (·.2))
      for (c, fields) in ctors do
        let fields ← fields.mapM (resolveType pmap true)
        modify fun s => { s with ctors := (c, ⟨name, ids, fields, result⟩) :: s.ctors }
    | .struct name params fields =>
      let (pmap, ids) ← freshParams params
      let fields ← fields.mapM (resolveType pmap true)
      modify fun s =>
        { s with ctors := (name, ⟨name, ids, fields, .con name (pmap.map (·.2))⟩) :: s.ctors }
    | .effect name params ops =>
      let (pmap, ids) ← freshParams params
      for op in ops do
        let payload ← op.payload.mapM (resolveType pmap true)
        let result ← if op.terminal then pure none
          else match op.result with
            | some t => some <$> resolveType pmap true t
            | none => some <$> resolveType pmap true .hole
        -- A resumption is resumed at most once, so the most uses is one; the
        -- fewest says whether it may simply be let go.
        let must ← match op.quantity with
          | none => pure false
          | some (lower, upper) =>
            if op.terminal then
              throw s!"operation `{op.name}` does not return, so it has no resumption to say this of"
            unless upper == some 1 do
              throw s!"operation `{op.name}`: a resumption is used at most once, so write `[0, 1]` or `[1, 1]`"
            pure (lower == 1)
        if must then modify fun s => { s with anyMust := true }
        modify fun s => { s with ops := (op.name, ⟨name, ids, payload, result, must⟩) :: s.ops }
      modify fun s => { s with effects := (name, ⟨ids, ops.map (·.name)⟩) :: s.effects }
    | .use head lower upper =>
      unless ((← get).types.lookup head).isSome do
        throw s!"`impl Use` for `{head}`: there is no such declared type"
      if ((← get).useDecls.lookup head).isSome then
        throw s!"`impl Use` for `{head}` is written twice"
      -- Counting stops at one: the bounds a type can ask for are none or one
      -- use at least, and one use or any number at most.
      unless lower ≤ 1 && (upper == some 1 || upper == none) do
        throw s!"`impl Use` for `{head}`: the fewest uses can be 0 or 1 and the most 1 or `infinity`; other bounds are not counted yet"
      if lower == 1 then modify fun s => { s with anyMust := true }
      modify fun s => { s with useDecls := (head, lower == 1, upper == some 1) :: s.useDecls }
    | _ => pure ()

/-- A constructor's field types and result type at fresh type arguments. -/
def instCtor (sig : CtorSig) : M (List Ty × Ty) := do
  let tm ← sig.tvars.mapM fun id => do
    pure (id, ← freshTy)
  pure (sig.fields.map (subst tm [] []), subst tm [] [] sig.result)

/-- An operation's payload and result types at the given effect arguments. -/
def instOp (sig : OpSig) (inst : List Ty) : List Ty × Option Ty :=
  let tm := sig.tvars.zip inst
  (sig.payload.map (subst tm [] []), sig.result.map (subst tm [] []))

/-- Resolve a name to a constructor, following constructor aliases. -/
partial def resolveCtor (name : String) (qual : Option String) : M (Option (String × CtorSig)) := do
  let s ← get
  match s.ctors.lookup name with
  | some sig =>
    match qual with
    | some q =>
      if q == sig.owner then pure (some (name, sig))
      else throw s!"`{name}` is not a constructor of `{q}`"
    | none => pure (some (name, sig))
  | none =>
    match s.aliases.lookup name with
    | some (.name q y) => resolveCtor y q
    | _ => pure none

/-- Read a constant expression as a pattern. -/
partial def exprToPat : Expr → M Pattern
  | .int n => pure (.int n)
  | .name q x => pure (if q.isSome then .ctor x q [] else .var x)
  | .call _ (.name q x) args => do
    pure (.ctor x q (← args.mapM exprToPat))
  | .tuple args => do
    pure (.tuple (← args.mapM exprToPat))
  | _ => throw "this constant cannot be used as a pattern"

/-! ## Coverage of pattern clauses -/

/-- A pattern with its names resolved. -/
inductive NPat where
  | any
  | int (n : Int)
  | ctor (name : String) (args : List NPat)
  | tuple (args : List NPat)
  deriving Inhabited

partial def normPat : Pattern → M NPat
  | .wild => pure .any
  | .int n => pure (.int n)
  | .tuple ps => do
    pure (.tuple (← ps.mapM normPat))
  | .var x => do
    match ← resolveCtor x none with
    | some (name, _) => pure (.ctor name [])
    | none =>
      match (← get).aliases.lookup x with
      | some e => do normPat (← exprToPat e)
      | none => pure .any
  | .ctor x q ps => do
    match ← resolveCtor x q with
    | some (name, _) => do
      pure (.ctor name (← ps.mapM normPat))
    | none => throw s!"unknown constructor `{x}` in a pattern"

/-- Do the rows of patterns cover every value of the column types? -/
partial def exhaustive (tys : List Ty) (rows : List (List NPat)) : M Bool := do
  match tys with
  | [] => pure !rows.isEmpty
  | t :: rest =>
    let fallback : M Bool := exhaustive rest (rows.filterMap fun
      | .any :: tl => some tl
      | _ => none)
    match ← find t with
    | .tuple ts =>
      exhaustive (ts ++ rest) (rows.filterMap fun
        | .tuple ps :: tl => some (ps ++ tl)
        | .any :: tl => some (List.replicate ts.length .any ++ tl)
        | _ => none)
    | .con name args =>
      match (← get).types.lookup name with
      | some decl =>
        -- Split by constructor only where some clause tests for one; a recursive
        -- type would otherwise be unfolded for ever.
        let tested := rows.any fun
          | .ctor _ _ :: _ => true
          | _ => false
        if !tested then fallback
        else decl.ctors.allM fun c => do
          match (← get).ctors.lookup c with
          | none => pure false
          | some sig =>
            let fields := sig.fields.map (subst (sig.tvars.zip args) [] [])
            exhaustive (fields ++ rest) (rows.filterMap fun
              | .ctor c' ps :: tl => if c' == c then some (ps ++ tl) else none
              | .any :: tl => some (List.replicate fields.length .any ++ tl)
              | _ => none)
      | none => fallback
    | _ => fallback

/-- The type of field `idx` of a value of type `t`, if `t` is known. -/
def fieldType (t : Ty) (idx : Nat) : M (Option Ty) := do
  match ← find t with
  | .var _ => pure none
  | .tuple ts =>
    match ts[idx]? with
    | some t => pure (some t)
    | none => throw s!"a tuple of {ts.length} values has no field {idx}"
  | .con name args =>
    match (← get).ctors.lookup name with
    | some sig =>
      match (sig.fields.map (subst (sig.tvars.zip args) [] []))[idx]? with
      | some t => pure (some t)
      | none => throw s!"`{name}` has no field {idx}"
    | none => throw s!"`{bareName name}` has no fields to read with `.{idx}`"
  | t => throw s!"`.{idx}` reads a field, but `{showTy (← zonk t)}` has none"

/-- Settle the field reads that were waiting for their subject's type. When
`final`, one that still cannot be settled is an error. -/
partial def runProjections (final : Bool) : M Unit := do
  let waiting := (← get).projections
  modify fun s => { s with projections := #[] }
  let mut left : Array (Ty × Nat × Ty × String) := #[]
  for (subject, idx, result, pos) in waiting do
    match ← fieldType subject idx with
    | some t =>
      try unifyAt s!"the field `.{idx}`" result t
      catch e => throw (pos ++ e)
    | none => left := left.push (subject, idx, result, pos)
  if left.isEmpty then pure ()
  else if left.size < waiting.size then
    modify fun s => { s with projections := left ++ s.projections }
    runProjections final
  else if !final then
    modify fun s => { s with projections := left ++ s.projections }
  else
    match left[0]? with
    | some (_, idx, _, pos) =>
      throw s!"{pos}`.{idx}` reads a field of a value whose type is not known here; \
        annotate the value it is read from"
    | none => pure ()

def runPending : M Unit := do
  runProjections true
  settleRows (some fun _ => true) true
  let pending := (← get).pending
  modify fun s => { s with pending := #[] }
  for p in pending do
    let rows ← p.rows.mapM (·.mapM normPat)
    unless ← exhaustive p.tys rows do
      throw s!"{p.pos}{p.what} not cover every case"

/-! ## Scopes that values cannot outlive

A label is only meaningful while its scope is running. A callable that mentions
a label captures the scope's brand, as does any callable that captures such a
value. When a scope ends, no type that is still visible may mention a callable
holding its brand: not the scope's result, not a variable declared outside, not
a payload sent to a handler outside, and not a declaration's shared field type.

This is deliberately conservative. A function type mentions every callable
type in its parameters and result, so handing a callable that holds the brand
to a *variable* of function type counts as an escape: nothing says that
function will not keep it. Top-level functions are generalised, so passing such
a callable to one of them is fine.
-/

mutual

partial def capHolds (brand : Nat) (cap : Nat) : M Bool := do
  let root ← findCap cap
  if (← get).seen.contains root then return false
  modify fun s => { s with seen := root :: s.seen }
  for (src, what) in (← get).capEdges do
    if (← findCap src) == root then
      match what with
      | .brand b => if b == brand then return true
      | .ty t => if ← tyHolds brand t then return true
      | .once => pure ()
      | .must => pure ()
      | .loan _ => pure ()
      | .touch _ _ => pure ()
      | .inner _ => pure ()
  return false

/-- Does the type mention a callable that holds the brand? -/
partial def tyHolds (brand : Nat) (t : Ty) : M Bool := do
  match ← find t with
  | .var _ => pure false
  | .con _ args => args.anyM (tyHolds brand)
  | .tuple args => args.anyM (tyHolds brand)
  | .fn ps r effs tail cap => do
    if ← capHolds brand cap then return true
    if ← ps.anyM (tyHolds brand) then return true
    if ← tyHolds brand r then return true
    let row ← flattenRow ⟨effs, tail⟩
    row.effs.anyM fun e => e.2.anyM (tyHolds brand)
  | .ref _ t cap => do
    if ← capHolds brand cap then return true
    tyHolds brand t

end

/-- Reject a scope whose label could still be reached after the scope has ended.
`roots` are the types that outlive the scope, each with a description. -/
def checkEscape (brand : Nat) (what : String) (roots : List (String × Ty)) (amb : Row) :
    M Unit := do
  runProjections false
  settleRows none false
  let holds := fun (t : Ty) => do
    modify fun s => { s with seen := [] }
    tyHolds brand t
  let escape := fun (how : String) =>
    (throw s!"{what}: {how}" : M Unit)
  for (how, t) in roots do
    if ← holds t then escape how
  let row ← flattenRow amb
  for (e, args) in row.effs do
    for a in args do
      if ← holds a then escape s!"it is passed to a handler of `{e}` outside"
  let s ← get
  for id in s.mono do
    if ← holds (.var id) then
      escape "it is stored in a declaration whose field types are inferred; \
        give that declaration a type parameter"
  for cap in s.monoCaps do
    modify fun s => { s with seen := [] }
    if ← capHolds brand cap then
      escape "it is stored in a declaration's `fn` field; give that declaration a \
        type parameter for the field"

def jumpsAfter (label : String) : String :=
  s!"a callable that jumps to `@{label}` could be called after `@{label}` has ended"

/-- The types of the bindings in scope, described for an escape message. -/
def scopeRoots (scope : Scope) : List (String × Ty) :=
  scope.map fun (name, b) =>
    match b with
    | .val t => (s!"`{name}`, which outlives the scope, could hold it", t)
    | .cell t _ => (s!"`{name}`, which outlives the scope, could hold it", t)
    | .label t _ => (s!"it can be passed out through `{name}`", t)
    | .poly s => (s!"`{name}`, which outlives the scope, could hold it", s.ty)

/-! ## Values that can be used only once

A resumption can be used once. So can anything that holds one: a tuple or data
value with a resumption inside, and a callable that has captured one. A
reference holds nothing, and neither does a function merely because it accepts
or returns such a value.

A binding used more than once must therefore be of a type that holds no
resumption. The requirement is recorded when the uses are counted and checked
once types are known; for a type that depends on a function's parameters it
becomes part of the function's contract and is checked at each call.

Uses are counted from the shape of the program. Clauses of one callable are
alternatives. A callable that mentions a binding uses it once, by capturing it.
The arm of an operation that can be resumed may run any number of times, so a
binding from outside used in one counts as used repeatedly. The count knows
nothing about which callables a function goes on to call, so two callables that
each use a resumption count as two uses even if only one of them ever runs.
-/

mutual

partial def capOwnsOnce (cap : Nat) : M Bool := do
  let root ← findCap cap
  if (← get).seen.contains root then return false
  modify fun s => { s with seen := root :: s.seen }
  for (src, what) in (← get).capEdges do
    if (← findCap src) == root then
      match what with
      | .once => return true
      | .must => pure ()
      | .ty t => if ← tyOwnsOnce [] t then return true
      | .brand _ => pure ()
      | .loan _ => pure ()
      | .touch _ _ => pure ()
      | .inner _ => pure ()
  return false

/-- Can a value of this type be used only once? One that holds a resumption,
and one of a declared type that says so. -/
partial def tyOwnsOnce (visiting : List String) (t : Ty) : M Bool := do
  match ← find t with
  | .var _ => pure false
  | .tuple args => args.anyM (tyOwnsOnce visiting)
  | .fn _ _ _ _ cap => capOwnsOnce cap
  | .ref _ _ _ => pure false
  | .con name args => do
    if let some (_, once) := (← get).useDecls.lookup name then
      if once then return true
    if ← args.anyM (tyOwnsOnce visiting) then return true
    if visiting.contains name then return false
    match (← get).types.lookup name with
    | none => pure false
    | some decl =>
      decl.ctors.anyM fun c => do
        match (← get).ctors.lookup c with
        | none => pure false
        | some sig =>
          (sig.fields.map (subst (sig.tvars.zip args) [] [])).anyM
            (tyOwnsOnce (name :: visiting))

end

/-- Require that values of a type may be used more than once. -/
def mustDup (t : Ty) (why : String) : M Unit :=
  modify fun s => { s with dups := s.dups.push (t, s.pos ++ why) }

/-- The declared type, if any, that makes a type one whose values are used
only once. Only to say why. -/
partial def onceBy (visiting : List String) (t : Ty) : M (Option String) := do
  match ← find t with
  | .tuple args => args.findSomeM? (onceBy visiting)
  | .con name args => do
    if let some (_, once) := (← get).useDecls.lookup name then
      if once then return some name
    if let some n ← args.findSomeM? (onceBy visiting) then return some n
    if visiting.contains name then return none
    match (← get).types.lookup name with
    | none => pure none
    | some decl =>
      decl.ctors.findSomeM? fun c => do
        match (← get).ctors.lookup c with
        | none => pure none
        | some sig =>
          (sig.fields.map (subst (sig.tvars.zip args) [] [])).findSomeM?
            (onceBy (name :: visiting))
  | _ => pure none

def checkDups (dups : Array (Ty × String)) : M Unit := do
  for (t, why) in dups do
    modify fun s => { s with seen := [] }
    if ← tyOwnsOnce [] t then
      if let some name ← onceBy [] t then
        throw s!"{why}, but a `{name}` can be used only once"
      throw s!"{why}, but a value that holds a resumption can be used only once"

/-! ## Values that have to be used

A type may say that its values have to be used: `impl Use<[1, 1]> for T {}`.
An operation may say it of its resumption: `[1, 1] op()`. A value that holds
one of either has to be used too. Wherever a value is let go without being
used, its type is recorded, and once types are known none of them may be such
a type. For a type that depends on a function's parameters the requirement is
part of the function's contract, as for use more than once.

A callable that mentions such a value does not thereby have to be called: the
value's own uses are counted along the paths the program can take, through the
callables that mention it.
-/

/-- What the capture variables say about having to be used, gathered once. -/
structure MustInfo where
  /-- Those that are a resumption which has to be used. -/
  roots : List Nat := []
  /-- Those that are a resumption at all. What one mentions is the computation
  it suspended, not something it holds. -/
  resumptions : List Nat := []
  /-- Those of callables written in the program. -/
  blocks : List Nat := []
  /-- The types of what each captures. -/
  held : Array (Nat × Ty) := #[]

def mustInfo : M MustInfo := do
  let s ← get
  let mut info : MustInfo := {}
  unless s.anyMust do return info
  for ((src, what), i) in s.capEdges.zipIdx do
    let root ← findCap src
    match what with
    | .must => unless info.roots.contains root do info := { info with roots := root :: info.roots }
    | .once =>
      unless info.resumptions.contains root do
        info := { info with resumptions := root :: info.resumptions }
    | .ty t => unless s.sharedEdges.contains i do info := { info with held := info.held.push (root, t) }
    | _ => pure ()
  for (_, c) in s.blockCaps do
    let root ← findCap c
    unless info.blocks.contains root do info := { info with blocks := root :: info.blocks }
  pure info

/-- What in a type has to be used, if anything: said for the message. A
callable has to be called if it holds something that has to be used. -/
partial def tyMustUse (info : MustInfo) (visiting : List String) (t : Ty) :
    M (Option String) := do
  match ← find t with
  | .var _ => pure none
  | .tuple args => args.findSomeM? (tyMustUse info visiting)
  | .fn _ _ _ _ cap => do
    let root ← findCap cap
    if info.roots.contains root then
      return some "a resumption of an operation declared `[1, 1]`"
    if info.resumptions.contains root && !info.blocks.contains root then return none
    if (← get).seen.contains root then return none
    modify fun s => { s with seen := root :: s.seen }
    for (r, held) in info.held do
      if r == root then
        if let some what ← tyMustUse info visiting held then
          return some s!"a callable that holds {what}"
    return none
  | .ref _ _ _ => pure none
  | .con name args => do
    if let some (must, _) := (← get).useDecls.lookup name then
      if must then return some s!"a `{bareName name}`"
    if let some w ← args.findSomeM? (tyMustUse info visiting) then return some w
    if visiting.contains name then return none
    match (← get).types.lookup name with
    | none => pure none
    | some decl =>
      decl.ctors.findSomeM? fun c => do
        match (← get).ctors.lookup c with
        | none => pure none
        | some sig =>
          (sig.fields.map (subst (sig.tvars.zip args) [] [])).findSomeM?
            (tyMustUse info (name :: visiting))

/-- Record that a value of this type is let go unused here. -/
def mustDrop (t : Ty) (why : String) : M Unit := do
  unless (← get).anyMust do return
  match ← find t with
  | .con "Int" [] => pure ()
  | .tuple [] => pure ()
  | .ref _ _ _ => pure ()
  | _ => modify fun s => { s with drops := s.drops.push (t, s.pos ++ why) }

def checkDrops (drops : Array (Ty × String)) : M Unit := do
  if drops.isEmpty then return
  let info ← mustInfo
  for (t, why) in drops do
    modify fun s => { s with seen := [] }
    if let some what ← tyMustUse info [] t then
      throw s!"{why}, but {what} has to be used"

private def addUses (a b : Nat) : Nat := min 2 (a + b)

mutual

/-- How often an expression uses the binding `x`: 0, 1, or 2 for more.
`resumptive` says which operation names have arms that may run repeatedly. -/
partial def usesExpr (resumptive : String → Bool) (x : String) : Expr → Nat
  | .int _ => 0
  | .name q y => if q.isNone && y == x then 1 else 0
  | .label _ => 0
  | .call _ f args =>
    (args.map (usesExpr resumptive x)).foldl addUses (usesExpr resumptive x f)
  | .tailCall _ f args =>
    (args.map (usesExpr resumptive x)).foldl addUses (usesExpr resumptive x f)
  | .tuple args => (args.map (usesExpr resumptive x)).foldl addUses 0
  | .proj e _ => usesExpr resumptive x e
  | .closure _ clauses => (clauses.map (usesClause resumptive x)).foldl max 0
  | .handle subject arms =>
    let repeated := fun (arm : Clause) =>
      match arm with
      | .mk [.ctor name _ _] _ => resumptive name
      | _ => false
    let once := ((arms.filter (!repeated ·)).map (usesClause resumptive x)).foldl max 0
    let many := if (arms.filter repeated).any (usesClause resumptive x · > 0) then 2 else 0
    addUses (addUses (usesExpr resumptive x subject) once) many
  | .labelScope _ body => usesStmts resumptive x body
  | .ref _ _ => 0
  | .deref e => usesExpr resumptive x e

partial def usesClause (resumptive : String → Bool) (x : String) : Clause → Nat
  | .mk pats body =>
    if (pats.flatMap Elab.patVars).contains x then 0 else usesStmts resumptive x body

partial def usesStmts (resumptive : String → Bool) (x : String) : List Stmt → Nat
  | [] => 0
  | .expr e :: rest => addUses (usesExpr resumptive x e) (usesStmts resumptive x rest)
  | .let_ pat value :: rest =>
    addUses (usesExpr resumptive x value)
      (if (Elab.patVars pat).contains x then 0 else usesStmts resumptive x rest)
  | .letMut y value :: rest =>
    addUses (usesExpr resumptive x value) (if y == x then 0 else usesStmts resumptive x rest)
  | .assign target value :: rest =>
    let inTarget := match target with
      | .deref e => usesExpr resumptive x e
      | _ => 0
    addUses (addUses inTarget (usesExpr resumptive x value)) (usesStmts resumptive x rest)
  | .defer e :: rest => addUses (usesExpr resumptive x e) (usesStmts resumptive x rest)
  | .located _ _ s :: rest => usesStmts resumptive x (s :: rest)

end


/-! ### Counting uses along the paths a program can take

The count above treats every callable that mentions a binding as one use. That
is too coarse where a function runs only one of several callables it is given,
which is how every conditional is written. So before a binding is held to
"used more than once", its uses are counted again by running the program
abstractly: constructors, callables and top-level functions are followed,
clauses are chosen by the constructor of the value they are applied to, and
anything not understood is treated as opaque, in which case every callable
handed to it counts as called.

This is an upper bound on the uses along any one path. If the analysis runs out
of budget it gives no answer and the coarse count stands.
-/

/-- What is known about a value during the count. -/
inductive AVal where
  | unknown
  /-- The binding whose uses are being counted. -/
  | tracked
  /-- A constructed value; a tuple has the empty tag. -/
  | data (tag : String) (args : List AVal)
  | clo (clauses : List Clause) (env : List (String × AVal))
  | fn (name : String)
  /-- No value: the path left for somewhere else, an operation's handler
  (named by the operation), a label's scope (`@name`), or somewhere unknown. -/
  | gone (target : String)
  deriving Inhabited

structure ACtx where
  fns : List (String × List Clause)
  ctors : List String
  aliases : List (String × Expr)
  ops : List (String × Bool)
  /-- Count the fewest uses along any path instead of the most. Then a call
  that cannot be followed may also not come back, a callable that leaves the
  count may never be called, and a path that leaves ends with what it has. -/
  lower : Bool := false
  /-- Names whose calls only compute: they always come back. -/
  quiet : List String := []
  /-- Calls, by identity, whose types say they come back. -/
  sure : List Nat := []

private def isGone : AVal → Bool
  | .gone _ => true
  | _ => false

/-- The target of the first value that is no value, if any is. -/
private def goneOf (vs : List AVal) : Option String :=
  vs.findSome? fun
    | .gone t => some t
    | _ => none

/-- The most, or in the other direction the fewest, of some counts. -/
private def ACtx.fold (ctx : ACtx) : List Nat → Nat
  | [] => 0
  | n :: ns => if ctx.lower then ns.foldl min n else ns.foldl max n

/-- A budget of steps; running out abandons the count. -/
abbrev A := StateT Nat Option

private def tick : A Unit := do
  match ← get with
  | 0 => failure
  | n + 1 => set n

/-- The outcomes of a computation: its value and the uses so far, per path. -/
abbrev Alts := List (AVal × Nat)

partial def ACtx.ctorOf (ctx : ACtx) (name : String) : Option String :=
  if ctx.ctors.contains name then some name
  else
    match ctx.aliases.lookup name with
    | some (.name _ y) => ctx.ctorOf y
    | _ => none

private partial def constPat : Expr → Option Pattern
  | .int n => some (.int n)
  | .name q x => some (if q.isSome then .ctor x q [] else .var x)
  | .call _ (.name q x) args => do
    some (.ctor x q (← args.mapM constPat))
  | .tuple args => do
    some (.tuple (← args.mapM constPat))
  | _ => none

/-- The names a pattern binds, leaving out constructors and constants. -/
partial def binders (ctx : ACtx) : Pattern → List String
  | .wild => []
  | .int _ => []
  | .var x =>
    if (ctx.ctorOf x).isSome || (ctx.aliases.lookup x).isSome then [] else [x]
  | .ctor _ _ ps => ps.flatMap (binders ctx)
  | .tuple ps => ps.flatMap (binders ctx)

inductive Fit where
  | yes
  | no
  | maybe
  deriving Inhabited

def Fit.and : Fit → Fit → Fit
  | .no, _ => .no
  | _, .no => .no
  | .yes, .yes => .yes
  | _, _ => .maybe

mutual

/-- Does a value match a pattern, and what does the pattern bind? -/
partial def fit (ctx : ACtx) : Pattern → AVal → Fit × List (String × AVal)
  | .wild, _ => (.yes, [])
  | .int _, _ => (.maybe, [])
  | .var x, v =>
    match ctx.ctorOf x with
    | some c => fitData ctx c [] v
    | none =>
      match ctx.aliases.lookup x with
      | some e =>
        match constPat e with
        | some p => fit ctx p v
        | none => (.maybe, [])
      | none => (.yes, [(x, v)])
  | .ctor x _ ps, v =>
    match ctx.ctorOf x with
    | some c => fitData ctx c ps v
    | none => (.maybe, (ps.flatMap (binders ctx)).map (·, AVal.unknown))
  | .tuple ps, v => fitData ctx "" ps v

partial def fitData (ctx : ACtx) (tag : String) (ps : List Pattern) (v : AVal) :
    Fit × List (String × AVal) :=
  match v with
  | .data tag' args =>
    if tag' == tag && args.length == ps.length then fitAll ctx ps args else (.no, [])
  | _ => (.maybe, (ps.flatMap (binders ctx)).map (·, AVal.unknown))

partial def fitAll (ctx : ACtx) (ps : List Pattern) (vs : List AVal) :
    Fit × List (String × AVal) :=
  (ps.zip vs).foldl (fun (acc : Fit × List (String × AVal)) (p, v) =>
    let (f, binds) := fit ctx p v
    (acc.1.and f, binds ++ acc.2)) (.yes, [])

end

private def maxUses (alts : Alts) : Nat := (alts.map (·.2)).foldl max 0

/-- Uses made by matching a value against a pattern: a binding taken apart by a
pattern that looks inside it is used. A plain name or `_` does not look. -/
partial def takenApart (ctx : ACtx) : Pattern → AVal → Nat
  | .wild, _ => 0
  | .var x, v =>
    if (binders ctx (.var x)).isEmpty then
      match v with
      | .tracked => 1
      | _ => 0
    else 0
  | _, .tracked => 1
  | .ctor _ _ ps, .data _ args =>
    ((ps.zip args).map fun (p, v) => takenApart ctx p v).foldl (· + ·) 0
  | .tuple ps, .data _ args =>
    ((ps.zip args).map fun (p, v) => takenApart ctx p v).foldl (· + ·) 0
  | _, _ => 0

/-- Can a use of the binding come of this value? -/
partial def holdsTracked : AVal → Bool
  | .tracked => true
  | .data _ args => args.any holdsTracked
  | .clo clauses env =>
    (clauses.flatMap (Elab.fvClause [])).eraseDups.any fun y =>
      match env.lookup y with
      | some v => holdsTracked v
      | none => false
  | _ => false

mutual

/-- The uses made if a value goes somewhere the count cannot follow. For the
most uses, every callable in it is taken to be called; for the fewest, none. -/
partial def escapes (ctx : ACtx) (depth : Nat) : AVal → A Nat
  | .tracked => pure 1
  | .data _ args => do
    let ns ← args.mapM (escapes ctx depth)
    pure (ns.foldl (· + ·) 0)
  | .clo clauses env => do
    -- For the fewest uses: a callable that mentions the binding has to be
    -- called, since the binding has to be used; one that does not, need not.
    if ctx.lower && !holdsTracked (.clo clauses env) then return 0
    tick
    let mut ns : List Nat := []
    for clause in clauses do
      match clause with
      | .mk pats body =>
        let params := (pats.flatMap (binders ctx)).map (·, AVal.unknown)
        let found ← runStmts ctx depth (params ++ env) body
        for (v, n) in found do
          ns := (n + (← escapes ctx depth v)) :: ns
    pure (ctx.fold ns)
  | _ => pure 0

/-- The paths that go on merged into one count, with what each yields going
where the count cannot follow; and the paths that have left. -/
partial def settle (ctx : ACtx) (depth : Nat) (alts : Alts) (leaves : Bool := true) :
    A (Option Nat × Alts) := do
  let mut ns : List Nat := []
  let mut left : Alts := []
  for (v, n) in alts do
    if isGone v then left := (v, n) :: left
    else if leaves then ns := (n + (← escapes ctx depth v)) :: ns
    else ns := n :: ns
  pure (if ns.isEmpty then none else some (ctx.fold ns), left)

/-- Keep the number of paths small: beyond a limit, merge them into one whose
value is unknown and whose uses are the most any of them made. -/
partial def cap (ctx : ACtx) (depth : Nat) (alts : Alts) : A Alts := do
  if alts.length ≤ 16 then pure alts
  else
    let (on, left) ← settle ctx depth alts
    let merged : Alts := match on with
      | some n => [(.unknown, n)]
      | none => []
    pure (merged ++ (if left.isEmpty then [] else [(.gone "*", ctx.fold (left.map (·.2)))]))

/-- A call the count cannot follow: its arguments escape. -/
partial def unfollowed (ctx : ACtx) (depth : Nat) (args : List AVal) (quiet : Bool := false) :
    A Alts := do
  let mut n := 0
  for a in args do
    n := n + (← escapes ctx depth a)
  -- What is called may not come back.
  pure (if ctx.lower && !quiet then [(.unknown, n), (.gone "*", n)] else [(.unknown, n)])

partial def applyClauses (ctx : ACtx) (depth : Nat) (clauses : List Clause)
    (env : List (String × AVal)) (args : List AVal) : A Alts := do
  let mut out : Alts := []
  for clause in clauses do
    match clause with
    | .mk pats body =>
      -- A block without parameters that is given one argument drops it.
      let pats := if pats.isEmpty && args.length == 1 then [Pattern.wild] else pats
      if pats.length == args.length then
        let (fitness, binds) := fitAll ctx pats args
        let taken := ((pats.zip args).map fun (p, v) => takenApart ctx p v).foldl (· + ·) 0
        let run : A Alts := do
          let alts ← runStmts ctx depth (binds ++ env) body
          pure (alts.map fun (v, n) => (v, n + taken))
        match fitness with
        | .no => pure ()
        | .maybe => out := out ++ (← run)
        | .yes =>
          out := out ++ (← run)
          break
  if out.isEmpty then unfollowed ctx depth args else cap ctx depth out

partial def callValue (ctx : ACtx) (depth : Nat) (f : AVal) (args : List AVal) : A Alts := do
  tick
  match f with
  | .tracked => do
    -- Calling the binding uses it.
    let alts ← unfollowed ctx depth args
    pure (alts.map fun (v, n) => (v, n + 1))
  | .clo clauses env => applyClauses ctx depth clauses env args
  | .fn name =>
    match depth, ctx.fns.lookup name with
    | d + 1, some clauses => applyClauses ctx d clauses [] args
    | _, _ => unfollowed ctx depth args
  | _ => unfollowed ctx depth args

/-- Evaluate expressions left to right, over every combination of paths. A
path that left on the way has only the value that says so. -/
partial def runList (ctx : ACtx) (depth : Nat) (env : List (String × AVal)) :
    List Expr → A (List (List AVal × Nat))
  | [] => pure [([], 0)]
  | e :: es => do
    let heads ← runExpr ctx depth env e
    let mut out : List (List AVal × Nat) := []
    for (v, n) in heads do
      if isGone v then out := ([v], n) :: out
    let on := heads.filter fun (v, _) => !isGone v
    unless on.isEmpty do
      let tails ← runList ctx depth env es
      out := out ++ on.flatMap fun (v, n) => tails.map fun (vs, m) =>
        if (goneOf vs).isSome then (vs, n + m) else (v :: vs, n + m)
    if out.length ≤ 16 then pure out
    else
      let mut ns : List Nat := []
      let mut left : List Nat := []
      for (vs, n) in out do
        if (goneOf vs).isSome then left := n :: left
        else
          let mut total := n
          for v in vs do
            total := total + (← escapes ctx depth v)
          ns := total :: ns
      let merged := if ns.isEmpty then [] else [((e :: es).map fun _ => AVal.unknown, ctx.fold ns)]
      pure (merged ++ (if left.isEmpty then [] else [([AVal.gone "*"], ctx.fold left)]))

partial def runExpr (ctx : ACtx) (depth : Nat) (env : List (String × AVal)) : Expr → A Alts
  | .int _ => pure [(.unknown, 0)]
  | .name q x => do
    tick
    -- Naming the binding is not yet a use; calling it, taking it apart, or
    -- letting it go where the count cannot follow is.
    match (if q.isNone then env.lookup x else none) with
    | some v => pure [(v, 0)]
    | none =>
      if let some c := ctx.ctorOf x then pure [(.data c [], 0)]
      else if (ctx.ops.lookup x).isSome then pure [(.unknown, 0)]
      else if (ctx.fns.lookup x).isSome then pure [(.fn x, 0)]
      else
        match ctx.aliases.lookup x with
        | some e => runExpr ctx depth [] e
        | none => pure [(.unknown, 0)]
  | .label _ => pure [(.unknown, 0)]
  | .tuple es => do
    let alts ← runList ctx depth env es
    pure (alts.map fun (vs, n) =>
      match goneOf vs with
      | some t => (.gone t, n)
      | none => (.data "" vs, n))
  | .proj e idx => do
    let alts ← runExpr ctx depth env e
    pure (alts.map fun (v, n) =>
      match v with
      | .data _ args => (args.getD idx .unknown, n)
      | .tracked => (.unknown, n + 1)
      | .gone t => (.gone t, n)
      | _ => (.unknown, n))
  | .call id f args => runCall ctx depth env f args id
  | .tailCall id f args => runCall ctx depth env f args id
  | .closure _ clauses => pure [(.clo clauses env, 0)]
  | .handle subject arms => do
    let subject ← runExpr ctx depth env subject
    let mut completions : List Clause := []
    let mut repeated := 0
    let mut terminal : Alts := []
    let mut handled : List String := []
    for arm in arms do
      match arm with
      | .mk [.ctor name q ps] body =>
        match ctx.ops.lookup name with
        | some resumptive =>
          handled := name :: handled
          let params := (ps.flatMap (binders ctx)).map (·, AVal.unknown)
          let alts ← runStmts ctx depth (params ++ env) body
          if resumptive then
            -- May run any number of times: one use there is already too many,
            -- and none there can be relied on.
            unless ctx.lower do
              for (v, n) in alts do
                if n + (← escapes ctx depth v) > 0 then repeated := 2
          else terminal := terminal ++ alts
        | none => completions := completions ++ [.mk [.ctor name q ps] body]
      | other => completions := completions ++ [other]
    -- A path that left for an operation handled here goes on from here.
    let subject := subject.map fun (v, n) =>
      match v with
      | .gone t => if handled.contains t then (AVal.unknown, n) else (v, n)
      | _ => (v, n)
    let mut done : Alts := []
    for (v, n) in subject do
      if isGone v || completions.isEmpty then done := (v, n) :: done
      else
        let found ← applyClauses ctx depth completions env [v]
        for (v', n') in found do
          done := (v', n + n') :: done
    -- How much of the subject ran before an arm that does not resume is not
    -- known: for the fewest uses, none of it.
    let before := if ctx.lower then 0 else maxUses subject
    let all := done ++ terminal.map fun (v, n) => (v, n + before)
    cap ctx depth (all.map fun (v, n) => (v, n + repeated))
  | .labelScope l body => do
    let alts ← runStmts ctx depth env body
    if ctx.lower then
      -- A path that left for this label goes on from here.
      pure (alts.map fun (v, n) =>
        match v with
        | .gone t => if t == "@" ++ l then (AVal.unknown, n) else (v, n)
        | _ => (v, n))
    else
      -- Leaving through the label gives a value the count does not follow.
      pure (alts ++ [(.unknown, maxUses alts)])
  | .ref _ _ => pure [(.unknown, 0)]
  | .deref e => do
    let alts ← runExpr ctx depth env e
    let (on, left) ← settle ctx depth alts
    pure ((match on with
      | some n => [(AVal.unknown, n)]
      | none => []) ++ left)

partial def runCall (ctx : ACtx) (depth : Nat) (env : List (String × AVal)) (f : Expr)
    (args : List Expr) (id : Nat) : A Alts := do
  tick
  let sure := ctx.lower && ctx.sure.contains id
  let alts ← runCallee ctx depth env f args sure
  -- A call whose type says it comes back does, whatever was lost track of
  -- inside it.
  if sure then
    pure (alts.map fun (v, n) => if isGone v then (AVal.unknown, n) else (v, n))
  else pure alts

partial def runCallee (ctx : ACtx) (depth : Nat) (env : List (String × AVal)) (f : Expr)
    (args : List Expr) (sure : Bool) : A Alts := do
  let general : A Alts := do
    let mut out : Alts := []
    let found ← runExpr ctx depth env f
    for (fv, n) in found do
      if isGone fv then out := (fv, n) :: out
      else
        let found ← runList ctx depth env args
        for (vs, m) in found do
          match goneOf vs with
          | some t => out := (.gone t, n + m) :: out
          | none =>
            -- A call that comes back and is given nothing a use could come
            -- of need not be followed.
            if sure && !holdsTracked fv && !vs.any holdsTracked then
              out := (.unknown, n + m) :: out
            else
              let found ← callValue ctx depth fv vs
              for (v, k) in found do
                out := (v, n + m + k) :: out
    cap ctx depth out
  -- The arguments go to something that is not followed; `after` says what
  -- becomes of the path once they have.
  let handedOn := fun (after : Nat → Alts) => (do
    let mut out : Alts := []
    let found ← runList ctx depth env args
    for (vs, n) in found do
      match goneOf vs with
      | some t => out := (.gone t, n) :: out
      | none =>
        let mut k := n
        for v in vs do
          k := k + (← escapes ctx depth v)
        out := out ++ after k
    cap ctx depth out : A Alts)
  match f with
  | .label l =>
    -- Applying a label leaves for its scope.
    if ctx.lower then handedOn fun n => [(.gone ("@" ++ l), n)] else general
  | .name q x =>
    if q.isNone && (env.lookup x).isSome then general
    else if let some c := ctx.ctorOf x then
      let alts ← runList ctx depth env args
      pure (alts.map fun (vs, n) =>
        match goneOf vs with
        | some t => (.gone t, n)
        | none => (.data c vs, n))
    else if let some resumptive := ctx.ops.lookup x then
      -- Performing an operation hands its payload to a handler.
      if ctx.lower then
        -- The handler need not resume: the path may end here.
        handedOn fun n => (if resumptive then [(AVal.unknown, n)] else []) ++ [(.gone x, n)]
      else
        let mut worst := 0
        let found ← runList ctx depth env args
        for (vs, n) in found do
          let found ← unfollowed ctx depth vs
          for (_, k) in found do
            worst := max worst (n + k)
        pure [(.unknown, worst)]
    else if ctx.lower && ctx.quiet.contains x && (ctx.fns.lookup x).isNone then
      handedOn fun n => [(.unknown, n)]
    else general
  | _ => general

partial def runStmts (ctx : ACtx) (depth : Nat) (env : List (String × AVal)) :
    List Stmt → A Alts
  | [] => pure [(.data "" [], 0)]
  | .located _ _ s :: rest => runStmts ctx depth env (s :: rest)
  | [.expr e] => runExpr ctx depth env e
  | .expr e :: rest => do
    -- The value is dropped, so the rest does not depend on which path was taken.
    let (on, left) ← settle ctx depth (← runExpr ctx depth env e) (leaves := false)
    match on with
    | none => pure left
    | some first =>
      let alts ← runStmts ctx depth env rest
      pure ((alts.map fun (v, n) => (v, n + first)) ++ left)
  | .let_ pat value :: rest => do
    let mut out : Alts := []
    let found ← runExpr ctx depth env value
    for (v, n) in found do
      if isGone v then out := (v, n) :: out
      else
        let (_, binds) := fit ctx pat v
        let bound := binds.map (·.1)
        let others := ((binders ctx pat).filter (!bound.contains ·)).map (·, AVal.unknown)
        let taken := takenApart ctx pat v
        let found ← runStmts ctx depth (binds ++ others ++ env) rest
        for (v', n') in found do
          out := (v', n + n' + taken) :: out
    cap ctx depth out
  | .letMut x value :: rest => do
    -- The value goes into a cell, where the count does not follow it.
    let (on, left) ← settle ctx depth (← runExpr ctx depth env value)
    match on with
    | none => pure left
    | some first =>
      let alts ← runStmts ctx depth ((x, .unknown) :: env) rest
      pure ((alts.map fun (v, n) => (v, n + first)) ++ left)
  | .assign target value :: rest => do
    let (on, left) ← settle ctx depth (← runExpr ctx depth env value)
    match on with
    | none => pure left
    | some first =>
      let (inTarget, left') ← match target with
        | .deref e => settle ctx depth (← runExpr ctx depth env e)
        | _ => pure (some 0, [])
      match inTarget with
      | none => pure (left ++ left'.map fun (v, n) => (v, n + first))
      | some inTarget =>
        let alts ← runStmts ctx depth env rest
        pure ((alts.map fun (v, n) => (v, n + first + inTarget)) ++ left
          ++ left'.map fun (v, n) => (v, n + first))
  | .defer e :: rest => do
    -- A cleanup runs however the rest is left.
    let mut ns : List Nat := []
    for (v, n) in ← runExpr ctx depth env e do
      ns := (n + (← escapes ctx depth v)) :: ns
    let first := ctx.fold ns
    let alts ← runStmts ctx depth env rest
    pure (alts.map fun (v, n) => (v, n + first))

end

/-- The most uses of `x` along any path through `body`, or with `ctx.lower` the
fewest, if the count finishes. `outer` are the other local names in scope,
about which nothing is known. -/
def pathUses (ctx : ACtx) (outer : List String) (x : String) (body : List Stmt) : Option Nat :=
  let env := (x, AVal.tracked) :: outer.map (·, AVal.unknown)
  let count : A Nat := do
    let mut ns : List Nat := []
    let found ← runStmts ctx 8 env body
    for (v, n) in found do
      -- What the body yields leaves the region being counted.
      ns := (n + (← escapes ctx 8 v)) :: ns
    pure (ctx.fold ns)
  (count.run 20000).map (·.1)

/-- Does evaluating this run nothing at all? `quiet` names what only builds a
value. -/
private partial def stillExpr (quiet : String → Bool) : Expr → Bool
  | .int _ => true
  | .name _ _ => true
  | .label _ => true
  | .closure _ _ => true
  | .ref _ _ => true
  | .tuple es => es.all (stillExpr quiet)
  | .call _ (.name _ f) args => quiet f && args.all (stillExpr quiet)
  | _ => false

private def isName (x : String) : Expr → Bool
  | .name none y => y == x
  | _ => false

mutual

/-- Whether `x` is used by this expression before anything in it could fail to
come back: `some true` if so, `some false` if something that may not come back
runs first, `none` if neither happens. -/
private partial def firstUse (quiet : String → Bool) (x : String) : Expr → Option Bool
  | .tuple es => firstParts quiet x true false es
  | .call _ f args =>
    firstParts quiet x (match f with
      | .name _ g => quiet g
      | _ => false) false (f :: args)
  | .tailCall _ f args =>
    firstParts quiet x (match f with
      | .name _ g => quiet g
      | _ => false) false (f :: args)
  | .proj e _ => if isName x e then some true else firstUse quiet x e
  | .deref e => if isName x e then none else firstUse quiet x e
  | .handle _ _ => some false
  | .labelScope _ _ => some false
  | _ => none

/-- The parts of a tuple or call, in order. `x` among them is handed on once
all are computed, so nothing after it may fail to come back. `builds` says the
whole only builds a value; otherwise it is a call that may not come back. -/
private partial def firstParts (quiet : String → Bool) (x : String) (builds pending : Bool) :
    List Expr → Option Bool
  | [] => if pending then some true else if builds then none else some false
  | e :: rest =>
    if isName x e then firstParts quiet x builds true rest
    else if stillExpr quiet e then firstParts quiet x builds pending rest
    else
      match firstUse quiet x e with
      | some true => if pending then some false else some true
      | some false => some false
      | none => if pending then some false else firstParts quiet x builds pending rest

end

/-- Is `x` certainly used before anything in these statements could fail to
come back? Decided from their shape, in the order they are evaluated: a quick
yes that saves counting along paths. -/
partial def usedFirst (quiet : String → Bool) (x : String) : List Stmt → Bool
  | [] => false
  | .located _ _ s :: rest => usedFirst quiet x (s :: rest)
  | [.expr e] => isName x e || firstUse quiet x e == some true
  | .expr e :: rest =>
    match firstUse quiet x e with
    | some b => b
    | none => usedFirst quiet x rest
  | .let_ pat value :: rest =>
    if isName x value then true
    else
      match firstUse quiet x value with
      | some b => b
      | none => !(Elab.patVars pat).contains x && usedFirst quiet x rest
  | .letMut y value :: rest =>
    if isName x value then true
    else
      match firstUse quiet x value with
      | some b => b
      | none => y != x && usedFirst quiet x rest
  | .assign _ value :: rest =>
    if isName x value then true
    else
      match firstUse quiet x value with
      | some b => b
      | none => usedFirst quiet x rest
  | .defer _ :: rest => usedFirst quiet x rest

/-- Record, for each binding used more than once in `body`, that its type must
allow that. `outer` is the scope the bindings are added to. A binding whose
type is already known to allow it needs no count; one that fails the coarse
count is counted again along the paths the program can take. -/
def checkUses (pos : String) (outer : Scope) (binds : Scope) (body : List Stmt) : M Unit := do
  -- Report at the statement the bindings belong to, not the last one checked.
  modify fun st => { st with pos := pos }
  let s ← get
  let resumptive := fun (name : String) =>
    match s.ops.lookup name with
    | some sig => sig.result.isSome
    | none => false
  -- What only computes: the machine's own operations and what builds a value.
  let intrinsics := Elab.prims.map (·.1) ++ Elab.hosts.map (·.1) ++ ["cancel", "replace"]
  let ctx : ACtx :=
    { fns := s.fnBodies, ctors := s.ctors.map (·.1), aliases := s.aliases,
      ops := s.ops.map fun (name, sig) => (name, sig.result.isSome), quiet := intrinsics }
  let names := (binds ++ outer).map (·.1)
  for (x, b) in binds do
    let t := match b with
      | .val t => some t
      | .poly p => some p.ty
      | _ => none
    if let some t := t then
      let mentions := usesStmts resumptive x body
      if mentions ≥ 2 then
        let t ← zonk t
        modify fun st => { st with seen := [] }
        let settled := (freeTys t).isEmpty && (freeCaps t).isEmpty && !(← tyOwnsOnce [] t)
        unless settled do
          match pathUses ctx (names.filter (· != x)) x body with
          | some n => if n ≥ 2 then mustDup t s!"`{x}` is used more than once"
          | none => mustDup t s!"`{x}` is used more than once"
      -- A value that has to be used: is it, however the body goes? Looked at
      -- once the function's types are known. A name the compiler made up
      -- stands for nothing the program wrote.
      if s.anyMust && !x.startsWith "%" then
        modify fun st =>
          { st with lowerChecks := st.lowerChecks.push (pos, x, t, names.filter (· != x), body) }

/-- Does a value of this type hold a callable that can jump to a label? -/
partial def tyJumps (t : Ty) : M Bool := do
  match ← find t with
  | .var _ => pure false
  | .con _ args => args.anyM tyJumps
  | .tuple args => args.anyM tyJumps
  | .ref _ inner _ => tyJumps inner
  | .fn ps r _ _ cap => do
    if ← ps.anyM tyJumps then return true
    if ← tyJumps r then return true
    let root ← findCap cap
    if (← get).seen.contains root then return false
    modify fun s => { s with seen := root :: s.seen }
    for (src, what) in (← get).capEdges do
      if (← findCap src) == root then
        match what with
        | .brand b => unless (← get).cells.any (·.1 == b) do return true
        | .ty t => if ← tyJumps t then return true
        | _ => pure ()
    return false

/-- A callable that has to come back when called may hold no label. -/
def checkStays (stays : Array (Ty × String)) : M Unit := do
  for (t, why) in stays do
    modify fun s => { s with seen := [] }
    if ← tyJumps t then
      throw s!"{why}, but what it is given here can jump to a label and not come back"

/-- With the types of a function known: note which of its calls certainly come
back, and look at each binding that may have to be used. `fnTy` is the
function's type.

A call comes back if its callee performs no operation and can jump to no
label. Effects not yet named are none at all unless something can supply
them: a callable the function was given, or one kept in a declared type. -/
def runLowerChecks (fnTy : Ty) : M Unit := do
  let s ← get
  modify fun st => { st with calls := #[], lowerChecks := #[], abandoned := #[] }
  unless s.anyMust do return
  let mut sources : List Nat := []
  if let .fn ps _ _ _ _ ← zonk fnTy then
    sources := ps.flatMap freeRows
  for id in s.monoRows do
    sources := sources ++ (← zonkRow ⟨[], some id⟩).tail.toList
  -- A callable the function was given holds whatever its caller gave it: it
  -- comes back only if that holds no label.
  let mut given : List Nat := []
  if let .fn ps _ _ _ _ ← zonk fnTy then
    for c in ps.flatMap freeCaps do
      given := (← findCap c) :: given
  let mut sure := s.sure
  let mut conditional : List (Nat × Ty) := []
  for (id, callee, silent) in s.calls do
    let callee ← zonk callee
    if let .fn _ _ effs tail _ := callee then
      modify fun st => { st with seen := [] }
      let silent := silent || (effs.isEmpty && match tail with
        | none => true
        | some ρ => !sources.contains ρ)
      if silent && !(← tyJumps callee) then
        let mut theirs := false
        for c in freeCaps callee do
          if given.contains (← findCap c) then theirs := true
        if theirs then conditional := (id, callee) :: conditional
        else sure := id :: sure
  modify fun st => { st with sure := sure }
  for (id, t, why) in s.abandoned do
    unless sure.contains id do
      modify fun st => { st with drops := st.drops.push (t, why) }
  let resumptive := fun (name : String) =>
    match s.ops.lookup name with
    | some sig => sig.result.isSome
    | none => false
  let intrinsics := Elab.prims.map (·.1) ++ Elab.hosts.map (·.1) ++ ["cancel", "replace"]
  let ctx : ACtx :=
    { fns := s.fnBodies, ctors := s.ctors.map (·.1), aliases := s.aliases,
      ops := s.ops.map fun (name, sig) => (name, sig.result.isSome), quiet := intrinsics,
      lower := true, sure := sure }
  let quiet := fun (f : String) =>
    (ctx.ctorOf f).isSome || (intrinsics.contains f && (ctx.fns.lookup f).isNone)
  let roots ← mustInfo
  -- What is found here is said first: it names the binding.
  let earlier := (← get).drops
  modify fun st => { st with drops := #[] }
  let mut relied := false
  for (pos, x, t, names, body) in s.lowerChecks do
    let t ← zonk t
    -- Only a type that has to be used, or one not yet known, needs the count.
    let free := !(freeTys t).isEmpty || !(freeCaps t).isEmpty
    modify fun st => { st with seen := [] }
    unless free || (← tyMustUse roots [] t).isSome do continue
    let mut unused := false
    if usesStmts resumptive x body == 0 then unused := true
    else if usedFirst quiet x body then unused := false
    else
      let counted := fun (c : ACtx) =>
        match pathUses c names x body with
        | some n => n == 0
        | none => true
      unused := counted ctx
      -- Used on every path if the callables the function was given come
      -- back: then that is asked of whoever gives them.
      if unused && !conditional.isEmpty then
        unless counted { ctx with sure := conditional.map (·.1) ++ sure } do
          unused := false
          relied := true
    if unused then
      modify fun st => { st with pos := pos }
      mustDrop t s!"`{x}` is not used on every path"
  modify fun st => { st with drops := st.drops ++ earlier }
  if relied then
    for (_, callee) in conditional do
      modify fun st => { st with stays := st.stays.push (callee,
        "a value that has to be used is held while a callable the function was given is called") }
  -- A block given a block that was not run. If only one block of the program
  -- so far can be that one, the second runs in its place: what the first held
  -- under a name the second also mentions is the second's to use, and is held
  -- once, by the first; the rest of what the first held is let go. Otherwise
  -- all of it is.
  modify fun st => { st with unrunGiven := #[] }
  for (id, cap, input, mentioned, why, own) in s.unrunGiven do
    let root ← findCap cap
    let mut owners : List (Nat × Nat) := []
    for (owner, c) in s.blockCaps do
      if owner != id && owner != 0 && (← findCap c) == root && !owners.any (·.1 == owner) then
        owners := (owner, c) :: owners
    match owners with
    | [(owner, c)] =>
      let mut theirs : List String := []
      for ((src, what), name) in s.capEdges.zip s.capEdgeNames do
        if src == c then
          if let .ty held := what then
            if let some n := name then theirs := n :: theirs
            let covered := match name with
              | some n => mentioned.contains n
              | none => false
            unless covered do
              modify fun st => { st with drops := st.drops.push (held,
                why ++ ", and the block it is given was not run and holds a value this one does not mention") }
      for (((src, what), name), i) in (s.capEdges.zip s.capEdgeNames).zipIdx do
        if src == own then
          if let .ty _ := what then
            if let some n := name then
              if theirs.contains n then
                modify fun st => { st with sharedEdges := i :: st.sharedEdges }
      modify fun st => { st with assumedLinks := st.assumedLinks.push (id, owner, input, why) }
    | _ => modify fun st => { st with drops := st.drops.push (input, why) }

/-- Can this pattern fail to match? Decided from its shape alone. -/
partial def irrefutable : Pattern → M Bool
  | .wild => pure true
  | .int _ => pure false
  | .tuple ps => ps.allM irrefutable
  | .var x => do
    if (← resolveCtor x none).isSome then return false
    return ((← get).aliases.lookup x).isNone
  | .ctor _ _ _ => pure false

/-! ## Borrows

`&x` borrows a mutable variable for reading, `&mut x` for writing too. A
borrow lasts for as long as something that holds it may still be used: the
reference itself, a value it was put in, a callable that captured it, a
variable it was assigned to. While a `&mut` borrow lasts, the variable can be
used only through it; while a `&` borrow lasts, the variable cannot be assigned
or borrowed with `&mut`.

A callable that mentions a mutable variable does not borrow it. It uses the
variable when it runs, so what a borrow forbids is calling it. This is what
lets a condition and a body, or the arms of a handler, be separate callables
over the same variables, with no rule that knows what `while` or `if` is.

A `&mut` reference used as a value is lent rather than copied: what receives it
borrows from it, and the reference cannot be used again until that is over.

Each use is recorded with what was still to be used when it happened, and
checked once the types say what holds which borrow.
-/

def withLater {α : Type} (names : List String) (act : M α) : M α := do
  let outer := (← get).later
  modify fun s => { s with later := names ++ outer }
  let r ← act
  modify fun s => { s with later := outer }
  pure r

/-- Run a part of an expression, forgetting the values it computed on the way. -/
def withTemps {α : Type} (act : M α) : M α := do
  let outer := (← get).temps
  let anon := (← get).anon
  let r ← act
  modify fun s => { s with temps := outer, anon := anon }
  pure r

def pushTemp (t : Ty) : M Unit := modify fun s => { s with temps := (t, s.loans.size) :: s.temps }

/-- A value just computed that has no name: until it is passed on, nothing
but the expression holds it. A name's value is the name's to account for. -/
def pushAnon (e : Expr) (t : Ty) : M Unit := do
  unless (← get).anyMust do return
  match e with
  | .name _ _ => pure ()
  | .int _ => pure ()
  | .label _ => pure ()
  | .closure _ _ => pure ()
  | .ref _ _ => pure ()
  | _ => modify fun s => { s with anon := t :: s.anon }

/-- Something that may not come back is about to run: the values still waiting
are let go if it does not. -/
def abandons (waiting : List Ty) (what : String) (call : Nat := 0) : M Unit := do
  unless (← get).anyMust do return
  for t in waiting do
    let why := s!"a value computed before {what} is let go if that does not return (give it a name first)"
    -- A call with an identity is looked at again once its type is known.
    if call == 0 then mustDrop t why
    else modify fun s => { s with abandoned := s.abandoned.push (call, t, s.pos ++ why) }

def use (scope : Scope) (kind : UseKind) : M Unit :=
  modify fun s =>
    { s with uses := s.uses.push ⟨s.owner, s.pos, kind, scope, s.later, s.temps⟩ }

def freshLoan (root : Option Nat) (uniq : Bool) (parent : Option (Nat × Nat)) : M Nat := do
  let id := (← get).loans.size
  modify fun s => { s with loans := s.loans.push ⟨id, root, uniq, parent⟩ }
  pure id

mutual

partial def capHoldsLoan (loan : Nat) (cap : Nat) (suspended : Bool := false)
    (plain : Bool := false) : M Bool := do
  let root ← findCap cap
  let s ← get
  -- A resumption is a computation set aside: the borrows its callables make
  -- while they run are borrows it holds. `plain` asks only for what a value
  -- holds as a value.
  let mut suspended := suspended
  unless suspended || plain do
    for (src, what) in s.capEdges do
      if let .once := what then
        if (← findCap src) == root then suspended := true
  let mark := 2 * root + (if suspended then 1 else 0)
  if s.seen.contains mark then return false
  modify fun s => { s with seen := mark :: s.seen }
  for (src, what) in s.capEdges do
    if (← findCap src) == root then
      match what with
      | .loan l => if l == loan then return true
      | .inner l => if suspended && l == loan then return true
      | .ty t => if ← tyHoldsLoan loan t suspended plain then return true
      | .brand b => if ← cellHoldsLoan loan b suspended plain then return true
      | .touch b _ => if ← cellHoldsLoan loan b suspended plain then return true
      | .once => pure ()
      | .must => pure ()
  return false

/-- A callable that uses a mutable variable can reach what the variable holds. -/
partial def cellHoldsLoan (loan : Nat) (brand : Nat) (suspended : Bool := false)
    (plain : Bool := false) : M Bool := do
  for (b, _, t) in (← get).cells do
    if b == brand then
      if ← tyHoldsLoan loan t suspended plain then return true
  return false

/-- Does a value of this type hold the borrow? What a callable takes and gives
back is not what it holds: only what it captured is. -/
partial def tyHoldsLoan (loan : Nat) (t : Ty) (suspended : Bool := false)
    (plain : Bool := false) : M Bool := do
  match ← find t with
  | .var _ => pure false
  | .con _ args => args.anyM (tyHoldsLoan loan · suspended plain)
  | .tuple args => args.anyM (tyHoldsLoan loan · suspended plain)
  | .fn _ _ _ _ cap => capHoldsLoan loan cap suspended plain
  | .ref _ t cap => do
    if ← capHoldsLoan loan cap suspended plain then return true
    tyHoldsLoan loan t suspended plain

end

mutual

partial def capTouches (cap : Nat) (out : List (Nat × Bool)) : M (List (Nat × Bool)) := do
  let root ← findCap cap
  if (← get).seen.contains root then return out
  modify fun s => { s with seen := root :: s.seen }
  let mut out := out
  for (src, what) in (← get).capEdges do
    if (← findCap src) == root then
      match what with
      | .touch b w => unless out.contains (b, w) do out := (b, w) :: out
      | .ty t => out ← tyTouches t out
      | _ => pure ()
  return out

/-- The mutable variables that running the callables a value holds may read or
assign. -/
partial def tyTouches (t : Ty) (out : List (Nat × Bool)) : M (List (Nat × Bool)) := do
  match ← find t with
  | .var _ => pure out
  | .con _ args => args.foldlM (fun o a => tyTouches a o) out
  | .tuple args => args.foldlM (fun o a => tyTouches a o) out
  | .fn _ _ _ _ cap => capTouches cap out
  | .ref _ t _ => tyTouches t out

end

/-- Whether doing this to a variable is forbidden by a borrow of it. -/
def Using.forbiddenBy (how : Using) (uniq : Bool) : Bool :=
  match how with
  | .read => uniq
  | .share => uniq
  | .write => true
  | .lend => true

/-- The types a binding's value has, for looking into what it holds. -/
private def Binding.held : Binding → Option Ty
  | .val t => some t
  | .cell t _ => some t
  | .poly s => some s.ty
  | .label _ _ => none

def holdsLoan (loan : Nat) (t : Ty) : M Bool := do
  modify fun s => { s with seen := [] }
  tyHoldsLoan loan t

def touchesVar (brand : Nat) (write : Bool) (t : Ty) : M Bool := do
  modify fun s => { s with seen := [] }
  let touched ← tyTouches t []
  pure (touched.any fun (b, w) => b == brand && (w || !write))

/-- A value computed before a borrow was first made cannot hold it, unless it
came from something that was there before and does: a variable that keeps what
an earlier run of the same code borrowed. -/
def tempHolds (loan : Nat) (u : Use) (t : Ty) (made : Nat) : M Bool := do
  unless ← holdsLoan loan t do return false
  if loan < made then return true
  for (_, b) in u.scope do
    if let some t := b.held then
      if ← holdsLoan loan t then return true
  return false

/-- What still holds a borrow where a use happens, if anything does. -/
def holderOf (loan : Nat) (u : Use) : M (Option String) := do
  for name in u.later.eraseDups do
    if let some t := (u.scope.lookup name).bind Binding.held then
      if ← holdsLoan loan t then
        if name == "%resumed" then return some "the computation this arm resumes"
        return some s!"`{name}`"
  for (t, made) in u.temps do
    if ← tempHolds loan u t made then return some "a value this expression is still using"
  return none

/-- One value both holds a borrow of a variable and holds a callable that uses
the variable. That is a conflict only if it can be both at once: the fields of
one constructor are, the alternatives of a type are not. This is what lets a
value be either what a body gave or the body that was not run. -/
partial def bothAtOnce (loan brand : Nat) (write : Bool) (t : Ty) : M Bool := do
  unless (← holdsLoan loan t) && (← touchesVar brand write t) do return false
  let together := fun (fields : List Ty) => (do
    let mut holding : List Nat := []
    let mut touching : List Nat := []
    for (f, i) in fields.zipIdx do
      if ← holdsLoan loan f then holding := i :: holding
      if ← touchesVar brand write f then touching := i :: touching
    if holding.any fun i => touching.any (· != i) then return true
    for (f, i) in fields.zipIdx do
      if holding.contains i && touching.contains i then
        if ← bothAtOnce loan brand write f then return true
    return false : M Bool)
  match ← find t with
  | .tuple fields => together fields
  | .con name args =>
    match (← get).types.lookup name with
    | none => pure true
    | some decl =>
      for c in decl.ctors do
        match (← get).ctors.lookup c with
        | none => return true
        | some sig =>
          if ← together (sig.fields.map (subst (sig.tvars.zip args) [] [])) then return true
      return false
  | _ => pure true

/-- Check the uses recorded against the borrows, now that types are known. -/
def checkLoans : M Unit := do
  let s ← get
  modify fun st => { st with uses := #[] }
  if s.loans.isEmpty then return
  let fail := fun (u : Use) (msg : String) => (throw (inFunction u.owner (u.pos ++ msg)) : M Unit)
  for u in s.uses do
    match u.kind with
    | .var brand x how =>
      for l in s.loans do
        if l.root == some brand && how.forbiddenBy l.uniq then
          if let some who ← holderOf l.id u then
            let kind := if l.uniq then "`&mut` reference" else "reference"
            fail u (match how with
              | .read => s!"`{x}` is read while {who} holds a {kind} to it"
              | .write => s!"`{x}` is assigned while {who} holds a {kind} to it"
              | .share => s!"`{x}` is borrowed while {who} holds a {kind} to it"
              | .lend => s!"`{x}` is borrowed with `&mut` while {who} holds a {kind} to it")
    | .through cap name write =>
      let root ← findCap cap
      for l in s.loans do
        if let some (parent, own) := l.parent then
          -- A reference lent to the function it is a parameter of, from inside
          -- it, has become the same as what was lent from it: nothing to tell apart.
          if (l.uniq || write) && (← findCap parent) == root && (← findCap own) != root then
            if let some who ← holderOf l.id u then
              fail u s!"{name} is used while {who}, which borrows from it, is still in use"
    | .call what tys =>
      -- The values of the call are the last of the values computed: the
      -- callee and its arguments, each of which may hold callables.
      let mine := (u.temps.take tys.length).reverse
      let outer := { u with temps := u.temps.drop tys.length }
      for (t, i) in tys.zipIdx do
        modify fun st => { st with seen := [] }
        for (brand, write) in ← tyTouches t [] do
          for l in s.loans do
            if l.root == some brand && (write || l.uniq) then
              let mut found ← holderOf l.id outer
              for ((t', made), j) in mine.zipIdx do
                if found.isNone then
                  if ← tempHolds l.id u t' made then
                    -- A resumption both holds the borrows of the computation
                    -- it suspended and uses what that computation uses:
                    -- resuming it is that computation going on.
                    modify fun st => { st with seen := [] }
                    let own ← if i == j then tyHoldsLoan l.id t' false true else pure true
                    if i != j || (own && (← bothAtOnce l.id brand write t')) then
                      found := some "a value this expression is still using"
              if let some who := found then
                let x := ((s.cells.toList.find? (·.1 == brand)).map (·.2.1)).getD "a variable"
                let kind := if l.uniq then "`&mut` reference" else "reference"
                let does := if write then "assign or borrow" else "read"
                fail u s!"calling {what} may {does} `{x}` while {who} holds a {kind} to it"

mutual

/-- Does the code assign the mutable variable `x`, or borrow it with `&mut`? -/
partial def assignsExpr (x : String) : Expr → Bool
  | .int _ => false
  | .name _ _ => false
  | .label _ => false
  | .call _ f args => assignsExpr x f || args.any (assignsExpr x)
  | .tailCall _ f args => assignsExpr x f || args.any (assignsExpr x)
  | .tuple args => args.any (assignsExpr x)
  | .proj e _ => assignsExpr x e
  | .closure _ clauses => clauses.any (assignsClause x)
  | .handle subject arms => assignsExpr x subject || arms.any (assignsClause x)
  | .labelScope _ body => assignsStmts x body
  | .ref uniq y => uniq && y == x
  | .deref e => assignsExpr x e

partial def assignsClause (x : String) : Clause → Bool
  | .mk _ body => assignsStmts x body

partial def assignsStmts (x : String) : List Stmt → Bool
  | [] => false
  | .let_ _ value :: rest => assignsExpr x value || assignsStmts x rest
  | .expr e :: rest => assignsExpr x e || assignsStmts x rest
  | .defer e :: rest => assignsExpr x e || assignsStmts x rest
  | .located _ _ s :: rest => assignsStmts x (s :: rest)
  | .letMut _ value :: rest => assignsExpr x value || assignsStmts x rest
  | .assign target value :: rest =>
    (match target with
      | .name none y => y == x
      | e => assignsExpr x e) || assignsExpr x value || assignsStmts x rest

end

/-- A `&mut` reference used as a value is lent: what is given is a reference
that borrows from it. Anything else is given as it is. -/
def lend (scope : Scope) (x : String) (t : Ty) : M Ty := do
  match ← find t with
  | .ref how inner cap =>
    match ← find how with
    | .con "&mut" [] =>
      use scope (.through cap s!"`{x}`" true)
      let cap' ← freshCap
      captures cap' (.loan (← freshLoan none true (some (cap, cap'))))
      captures cap' (.ty t)
      pure (.ref how inner cap')
    | _ => pure t
  | _ => pure t

/-! ## Expressions -/

/-- What a name in an expression refers to. -/
inductive Head where
  | local (b : Binding)
  /-- A function: its type at this use, the traits that use needs, and whether
  it is one of the group being inferred, whose needs are not yet known. -/
  | fn (t : Ty) (bounds : List (String × Ty)) (inGroup : Bool)
  | method (sig : MethodSig)
  | ctor (sig : CtorSig)
  | op (sig : OpSig)
  | prim
  | host (id : Nat)
  | cancel
  | replace
  | const (e : Expr)

def resolveName (scope : Scope) (qual : Option String) (x : String) : M Head := do
  if qual.isNone then
    if let some b := scope.lookup x then return .local b
  if let some (_, sig) ← resolveCtor x qual then return .ctor sig
  let s ← get
  if let some sig := s.ops.lookup x then
    if let some q := qual then
      unless q == sig.effect do throw s!"`{x}` is not an operation of `{q}`"
    return .op sig
  if let some sig := s.methods.lookup x then
    if let some q := qual then
      unless q == sig.trait do throw s!"`{x}` is not a function of `{q}`"
    return .method sig
  if let some t := s.group.lookup x then return .fn t [] true
  if let some scheme := s.fns.lookup x then
    let t ← instantiate scheme (some x)
    return .fn t (← get).lastBounds false
  if (Elab.prims.lookup x).isSome then return .prim
  if let some (id, _) := Elab.hosts.lookup x then return .host id
  if x == "cancel" then return .cancel
  if x == "replace" then return .replace
  if let some e := s.aliases.lookup x then return .const e
  throw s!"unknown name `{x}`"

/-- A call needs these traits of these types: to be met when the types are known. -/
def needBounds (call : Nat) (bs : List (String × Ty)) : M Unit := do
  if bs.isEmpty then return
  if call == 0 then
    throw "a trait is needed at a call the checker has no name for; this is a compiler defect"
  let s ← get
  let news := (bs.zip (List.range bs.length)).map fun ((tr, ty), k) =>
    (⟨tr, ty, call, k, s.owner, s.pos⟩ : Bound)
  set { s with bounds := s.bounds ++ news.toArray }

/-- Record that `cap` captures the named bindings: a value by its type, a label
or a mutable variable by the brand of its scope as well. -/
def captureAll (scope : Scope) (cap : Nat) (names : List String) (assigns : String → Bool) :
    M Unit := do
  -- Capturing a mutable variable holds the variable, not what is in it; and
  -- the callable reads or assigns the variable when it runs.
  for name in names.eraseDups do
    match scope.lookup name with
    | some (.val t) => captures cap (.ty t) (some name)
    | some (.cell _ brand) =>
      captures cap (.brand brand)
      captures cap (.touch brand (assigns name))
    | some (.label _ brand) => captures cap (.brand brand)
    | some (.poly s) => captures cap (.ty s.ty) (some name)
    | none => pure ()

private def placeName : Expr → String
  | .name _ x => s!"`{x}`"
  | _ => "this reference"

/-- A label is a callable that never returns: it accepts the value its scope
yields, and holds the scope's brand. -/
private def labelType (t : Ty) (brand : Nat) : M Ty := do
  let cap ← freshCap
  captures cap (.brand brand)
  pure (.func [t] (← freshTy) (← freshRow) cap)

private def readsCell (x : String) : String :=
  s!"reading the mutable variable `{x}` copies its value (`replace` takes it out instead)"

private def arguments (n : Nat) : String :=
  if n == 1 then "1 argument" else s!"{n} arguments"

private def arityError (what : String) (expected found : Nat) : M Unit :=
  throw s!"{what} takes {arguments expected}, but is given {found}"

/-! ## Coercions

A program declares a function a coercion with `coerce name`. Where a value does
not have the type expected of it, and exactly one declared coercion takes what
was found to what is expected, that function is applied, as if the call had
been written. Nothing is converted in more than one step, and a coercion is not
applied where its name means something else.
-/

/-- The declared coercions that take what was found to what is expected. If
there is exactly one, the types are made to fit it: it is applied. -/
def coerceTo (scope : Scope) (amb : Row) (expected actual : Ty) : M (List String) := do
  let s ← get
  let mut fits : List String := []
  for name in s.coercing do
    if (scope.lookup name).isNone then
      if let some scheme := s.fns.lookup name then
        let saved ← get
        let ok ← try
            (do
              match ← find (← instantiate scheme (some name)) with
              | .fn [a] b _ _ _ => do
                unify a actual
                unify b expected
                pure true
              | _ => pure false)
          catch _ => pure false
        set saved
        if ok then fits := name :: fits
  match fits with
  | [name] =>
    match s.fns.lookup name with
    | some scheme =>
      match ← find (← instantiate scheme (some name)) with
      | .fn [a] b effs tail _ => do
        unify a actual
        unify b expected
        includeRow ⟨effs, tail⟩ amb s!"`{name}`"
        pure [name]
      | _ => pure []
    | none => pure []
  | several => pure several.reverse

/-- A `&mut` reference where a `&` reference is wanted is lent for reading:
what is given borrows from it, as a reader. -/
def shareRef (scope : Scope) (expected actual : Ty) : M Bool := do
  match ← find expected, ← find actual with
  | .ref how inner cap, .ref how' inner' cap' =>
    match ← find how, ← find how' with
    | .con "&" [], .con "&mut" [] =>
      let fits ← try (do unify inner inner'; pure true) catch _ => pure false
      unless fits do return false
      use scope (.through cap' "a reference" false)
      captures cap (.loan (← freshLoan none false (some (cap', cap))))
      captures cap (.ty actual)
      pure true
    | _, _ => pure false
  | _, _ => pure false

/-- Marks a failure as a body's result not being the type wanted, which the
clause the body belongs to can still answer by looking at its clauses in
another order. -/
def resultMark : String := "\x01"

/-- Make what was found the type expected, by a declared coercion at `site` if
the two differ. Gives the mismatch if neither works. -/
def fitAt (scope : Scope) (amb : Row) (what : String) (site : Option Elab.Site)
    (expected actual : Ty) : M (Option String) := do
  try
    unifyAt what expected actual
    pure none
  catch e =>
    if ← shareRef scope expected actual then return none
    match site with
    | none => pure (some e)
    | some site =>
      match ← coerceTo scope amb expected actual with
      | [name] =>
        modify fun s => { s with coercions := s.coercions.push (site, name) }
        pure none
      | [] => pure (some e)
      | several =>
        let names := ", ".intercalate (several.map fun name => s!"`{name}`")
        pure (some s!"{e} (the coercions {names} all apply here, so none is chosen)")

mutual

partial def inferExpr (scope : Scope) (amb : Row) : Expr → M Ty
  | .int _ => pure .int
  | .name q x => do
    match ← resolveName scope q x with
    | .local (.val t) => lend scope x t
    | .local (.cell t brand) => do
      mustDup t (readsCell x)
      use scope (.var brand x .read)
      pure t
    | .local (.label t brand) => labelType t brand
    | .local (.poly s) => instantiate s (some x)
    | .fn t bounds inGroup => do
      unless bounds.isEmpty do
        throw s!"`{x}` needs a trait of a type it is used at, so it is called where it is named: write a block that calls it"
      if inGroup then
        modify fun s => { s with groupUses := s.groupUses.push ⟨0, x, s.owner, s.pos⟩ }
      pure t
    | .method sig =>
      throw s!"`{x}` is a function of the trait `{sig.trait}`, so it is called where it is named: write a block that calls it"
    | .ctor sig => do
      let (fields, result) ← instCtor sig
      unless fields.isEmpty do arityError s!"constructor `{x}`" fields.length 0
      pure result
    | .op _ => throw s!"operation `{x}` must be called"
    | .prim => throw s!"intrinsic `{x}` must be called"
    | .host _ => throw s!"host operation `{x}` must be called"
    | .cancel => throw "`cancel` must be applied to a resumption"
    | .replace => throw "`replace` must be called"
    | .const e => inferExpr [] amb e
  | .label l =>
    match scope.lookup ("@" ++ l) with
    | some (.label t brand) => labelType t brand
    | _ => throw s!"unknown label `@{l}`"
  | .tuple es => withTemps do
    let mut ts : Array Ty := #[]
    for e in es do
      let t ← inferExpr scope amb e
      pushTemp t
      pushAnon e t
      ts := ts.push t
    pure (.tuple ts.toList)
  | .proj e idx => do
    let subject ← inferExpr scope amb e
    mustDrop subject "taking one field of a value lets go of the rest"
    match ← fieldType subject idx with
    | some t => pure t
    | none => do
      -- Not known yet: settle it once the rest of the function is inferred.
      let t ← freshTy
      modify fun s => { s with projections := s.projections.push (subject, idx, t, s.pos) }
      pure t
  | .call id f args => withTemps (inferCall scope amb f args id)
  | .tailCall id f args => withTemps (inferCall scope amb f args id)
  | .closure id clauses => do
    let t ← inferCallable scope [] none none clauses "the clauses of this callable do" id
    if let .fn _ _ _ _ cap := t then
      modify fun s => { s with blockCaps := s.blockCaps.push (id, cap) }
    pure t
  | .handle subject arms => inferHandle scope amb subject arms
  | .labelScope l body => do
    let t ← freshTy
    let brand ← freshBrand
    let found ← inferStmts (("@" ++ l, .label t brand) :: scope) amb body
    unifyAt s!"the result of the scope `@{l}`" t found
    checkEscape brand (jumpsAfter l) (("it is the result of the scope", t) :: scopeRoots scope) amb
    pure t
  | .ref uniq x =>
    match scope.lookup x with
    | some (.cell t brand) => do
      use scope (.var brand x (if uniq then .lend else .share))
      let cap ← freshCap
      captures cap (.brand brand)
      captures cap (.loan (← freshLoan (some brand) uniq none))
      pure (.ref (if uniq then .uniq else .shared) t cap)
    | some _ => throw s!"`{x}` is not a mutable variable, so it cannot be borrowed"
    | none => throw s!"unknown name `{x}`"
  | .deref e => do
    let t ← inferPlace scope amb e
    let inner ← freshTy
    let cap ← freshCap
    unifyAt "`*` reads through a reference" (.ref (← freshTy) inner cap) t
    use scope (.through cap (placeName e) false)
    mustDup inner "reading through a reference copies the value (`replace` takes it out instead)"
    pure inner

/-- The reference that `*e` goes through. A name is the reference it stands
for, not one lent from it. -/
partial def inferPlace (scope : Scope) (amb : Row) : Expr → M Ty
  | .name none x => do
    match scope.lookup x with
    | some (.val t) => pure t
    | _ => inferExpr scope amb (.name none x)
  | e => inferExpr scope amb e

/-- Check one argument. Gives the mismatch if it does not fit. -/
partial def checkArg (scope : Scope) (amb : Row) (what : String) (p : Ty) (a : Expr)
    (site : Option Elab.Site) : M (Option String) := do
  match Elab.plainBlock a, ← find p with
  | some (id, body), .fn [input] _ _ _ _ =>
    -- A callable taking one argument is expected, and a block is written
    -- without parameters: it takes the argument without naming it.
    let t ← inferCallable scope [some input] none none [.mk [.var "%given"] body]
      "the clauses of this callable do" id
    let own := match t with
      | .fn _ _ _ _ c => c
      | _ => 0
    match ← fitAt scope amb what none p t with
    | some e => pure (some e)
    | none =>
      modify fun s => { s with given := s.given.push id }
      -- What it is given and does not name, it lets go. Given a block that
      -- was not run, it lets go of what that block held and it does not
      -- itself mention: looked at once the types are known.
      let why := "a block that does not name what it is given lets it go"
      match ← find input with
      | .fn [] _ _ _ cap =>
        if (← get).anyMust then
          modify fun s =>
            { s with unrunGiven :=
                s.unrunGiven.push (id, cap, input, Elab.fvStmts [] body, s.pos ++ why, own) }
      | _ => mustDrop input why
      -- A callable that takes no arguments, given to a block: a block that was
      -- not run, whose environment this one can take over.
      if let .fn [] _ _ _ cap ← find input then
        modify fun s => { s with unrun := s.unrun.push (id, cap) }
      pure none
  | _, _ => do
    -- A name whose type is not known yet, where a `&mut` reference is wanted:
    -- it is one, so it is lent rather than handed over.
    if let .name none x := a then
      if let some (.val t) := scope.lookup x then
        if let .var _ ← find t then
          if let .ref how inner _ ← find p then
            if let .con "&mut" [] ← find how then
              unify t (.ref how inner (← freshCap))
    fitAt scope amb what site p (← inferExpr scope amb a)

/-- Check arguments in the given order. Gives the first that does not fit. -/
partial def checkArgsIn (scope : Scope) (amb : Row) (what : String) (params : List Ty)
    (args : List Expr) (call : Nat) (order : List Nat) : M (Option (Nat × String)) := do
  for i in order do
    match params[i]?, args[i]? with
    | some p, some a =>
      let site := if call == 0 then none else some (Elab.Site.arg call i)
      if let some e ← checkArg scope amb s!"argument {i + 1} of {what}" p a site then
        return some (i, e)
      pushTemp p
      pushAnon a p
    | _, _ => pure ()
  return none

/-- Check the arguments of a call against the parameter types. An argument that
does not fit is converted by a coercion the program declares, if one applies.
If none does, the arguments are checked once more with that one first: what it
needs is then known when the others are looked at, and one of them may be what
has to be converted. -/
partial def checkArgs (scope : Scope) (amb : Row) (what : String) (params : List Ty)
    (args : List Expr) (call : Nat := 0) : M Unit := do
  unless params.length == args.length do arityError what params.length args.length
  let order := List.range args.length
  let saved ← get
  match ← checkArgsIn scope amb what params args call order with
  | none => pure ()
  | some (i, e) =>
    set saved
    if saved.coercing.isEmpty then throw e
    match ← checkArgsIn scope amb what params args call (i :: order.erase i) with
    | none => pure ()
    | some _ =>
      set saved
      throw e

/-- Apply a callee of a given type in the ambient effects. -/
partial def applyTy (scope : Scope) (amb : Row) (what : String) (callee : Ty) (args : List Expr)
    (call : Nat := 0) : M Ty := do
  abandons (← get).anon what call
  pushTemp callee
  match ← find callee with
  | .fn ps r effs tail _ => do
    checkArgs scope amb what ps args call
    if call != 0 && (← get).anyMust then
      let row ← flattenRow ⟨effs, tail⟩
      let silent ← match row.effs.isEmpty, row.tail with
        | true, none => pure true
        | true, some ρ => do
          if (← get).instRows.contains ρ then
            pure !((← ps.mapM zonk).flatMap freeRows).contains ρ
          else pure false
        | false, _ => pure false
      modify fun s => { s with calls := s.calls.push (call, callee, silent) }
    use scope (.call what (callee :: ps))
    includeRow ⟨effs, tail⟩ amb what
    pure r
  | t => do
    let mut argTys : Array Ty := #[]
    for a in args do
      let ty ← inferExpr scope amb a
      pushTemp ty
      argTys := argTys.push ty
    let r ← freshTy
    let row ← freshRow
    unifyAt s!"{what} is called with {arguments args.length}"
      (.func argTys.toList r row (← freshCap)) t
    use scope (.call what (callee :: argTys.toList))
    includeRow row amb what
    pure r

partial def inferCall (scope : Scope) (amb : Row) (f : Expr) (args : List Expr)
    (call : Nat := 0) : M Ty := do
  match f with
  | .name q x =>
    match ← resolveName scope q x with
    | .ctor sig => do
      let (fields, result) ← instCtor sig
      checkArgs scope amb s!"constructor `{x}`" fields args call
      pure result
    | .op sig => do
      abandons (← get).anon s!"operation `{x}`"
      let decl := ((← get).effects.lookup sig.effect).getD ⟨[], []⟩
      let inst ← decl.tvars.mapM fun _ => freshTy
      let (payload, result) := instOp sig inst
      try unifyRow amb ⟨[(sig.effect, inst)], some (← freshRowVar)⟩
      catch e => throw s!"operation `{x}` cannot be performed here: {e}"
      checkArgs scope amb s!"operation `{x}`" payload args call
      -- The handler may run a callable it is given, there and then.
      use scope (.call s!"operation `{x}`" payload)
      match result with
      | some r => pure r
      | none => freshTy
    | .prim => do
      checkArgs scope amb s!"intrinsic `{x}`" [.int, .int] args call
      pure .int
    | .host id => do
      if id == 0 then
        checkArgs scope amb s!"`{x}`" [← freshTy] args call
        pure .unit
      else
        checkArgs scope amb s!"`{x}`" [] args call
        pure (.tuple [.int, .int])
    | .cancel => do
      -- Giving up a callable: a resumption, or anything else applied to one value.
      let row ← freshRow
      let given := Ty.func [← freshTy] (← freshTy) row (← freshCap)
      checkArgs scope amb "`cancel`" [given] args call
      -- A cleanup of a cancelled computation may jump to a label inside it, and
      -- the computation then runs on from there, where it is being cancelled.
      -- So what it may perform must be handled here, as if it were called.
      includeRow row amb "`cancel`"
      pure .unit
    | .replace => do
      let t ← freshTy
      let cap ← freshCap
      checkArgs scope amb "`replace`" [.ref .uniq t cap, t] args call
      use scope (.through cap "the reference given to `replace`" true)
      pure t
    | .local (.val t) => applyTy scope amb s!"`{x}`" t args call
    | .local (.cell t brand) => do
      mustDup t (readsCell x)
      use scope (.var brand x .read)
      applyTy scope amb s!"`{x}`" t args call
    | .local (.label t brand) => do
      applyTy scope amb s!"the label `{x}`" (← labelType t brand) args call
    | .local (.poly s) => do
      applyTy scope amb s!"`{x}`" (← instantiate s (some x)) args call
    | .fn t bounds inGroup => do
      let r ← applyTy scope amb s!"`{x}`" t args call
      needBounds call bounds
      if inGroup then
        modify fun s => { s with groupUses := s.groupUses.push ⟨call, x, s.owner, s.pos⟩ }
      pure r
    | .method sig => do
      if sig.trait == "Drop" then
        throw s!"`{x}` is run when what holds a value ends; a program does not call it"
      -- A trait's function at the type it is used at, which must have the trait.
      let self ← freshTy
      let tm := [(sig.self, self)]
      let callee ← freshenCaps
        (.func (sig.params.map (subst tm [] [])) (subst tm [] [] sig.ret) ⟨[], none⟩ (← freshCap))
      let r ← applyTy scope amb s!"`{x}`" callee args call
      needBounds call [(sig.trait, self)]
      modify fun s => { s with methodCalls := s.methodCalls.push (call, sig.index) }
      pure r
    | .const e => do
      applyTy scope amb s!"`{x}`" (← inferExpr [] amb e) args call
  | .label l => do
    applyTy scope amb s!"the label `@{l}`" (← inferExpr scope amb f) args call
  | _ => do
    applyTy scope amb "this callee" (← inferExpr scope amb f) args call

/-- The type of a block: that of its last expression, or unit. -/
partial def inferStmts (scope : Scope) (amb : Row) (stmts : List Stmt)
    (want : Option (Ty × Option Elab.Site) := none) : M Ty := do
  -- The value a body ends with is made the type wanted of it where it is
  -- computed, inside whatever the body's statements have put around it.
  let finish := fun (t : Ty) (convertible : Bool) => (do
    match want with
    | none => pure t
    | some (expected, site) =>
      let site := if convertible then site else none
      match ← fitAt scope amb "the result of a clause" site expected t with
      | none => pure expected
      | some e => throw (resultMark ++ e) : M Ty)
  match stmts with
  | [] => finish .unit false
  | .located line col s :: rest => do
    modify fun st => { st with pos := s!"{line}:{col}: ", at_ := (line, col) }
    try inferStmts scope amb (s :: rest) want
    catch e => throw (positioned line col e)
  | [.expr e] => do finish (← inferExpr scope amb e) true
  | .expr e :: rest => do
    let t ← withLater (Elab.fvStmts [] rest) (inferExpr scope amb e)
    mustDrop t "the value of a statement is let go"
    inferStmts scope amb rest want
  | .let_ (.var x) (.closure id clauses) :: rest => do
    let t ← withLater (Elab.fvStmts [x] rest) (inferExpr scope amb (.closure id clauses))
    if (← resolveCtor x none).isSome || ((← get).aliases.lookup x).isSome then
      let binds ← inferPat (.var x) t
      inferStmts (binds ++ scope) amb rest want
    else
      -- A callable bound by `let` is a value, so it can be used at several types.
      -- Everything its surroundings already depend on stays fixed.
      let s ← get
      let mut keep : List Ty := [.func [] .unit amb (← freshCap)]
      for (_, b) in scope do
        keep := (match b with
          | .val t => t
          | .cell t _ => t
          | .label t _ => t
          | .poly p => p.ty) :: keep
      for (_, t) in s.group do
        keep := t :: keep
      for (subject, _, result, _) in s.projections do
        keep := subject :: result :: keep
      -- Decide the effects of what the callable calls, where nothing outside
      -- depends on them; calls still undecided keep their effects fixed.
      let mut fixedRows : List Nat := []
      for k in keep do
        fixedRows := fixedRows ++ freeRows (← zonk k)
      settleRows (some fun ρ => !fixedRows.contains ρ) false
      for (callee, permitted, _) in (← get).rowIncl do
        keep := .func [] .unit callee (← freshCap) :: .func [] .unit permitted (← freshCap) :: keep
      let scheme ← generalize t keep (top := false)
      let here := (← get).pos
      let result ← inferStmts ((x, .poly scheme) :: scope) amb rest want
      checkUses here scope [(x, .poly scheme)] rest
      pure result
  | .let_ pat value :: rest => do
    let (at_, pos) := ((← get).at_, (← get).pos)
    let t ← withLater (Elab.fvStmts (Elab.patVars pat) rest) (inferExpr scope amb value)
    -- A value given a name that nothing then uses is owned by the name: if it
    -- is one to destroy, that happens when the block ends.
    if let .var x := pat then
      unless (Elab.fvStmts [] rest).contains x || (← resolveCtor x none).isSome
          || ((← get).aliases.lookup x).isSome do
        modify fun s =>
          { s with dropCands := s.dropCands.push (⟨s.owner, at_.1, at_.2, x, false⟩, t, pos) }
    let binds ← inferPat pat t
    let check : Pending := ⟨(← get).pos, "the pattern of this `let` does", [t], [[pat]]⟩
    modify fun s => { s with pending := s.pending.push check }
    let here := (← get).pos
    let result ← inferStmts (binds ++ scope) amb rest want
    checkUses here scope binds rest
    pure result
  | .letMut x value :: rest => do
    let (at_, pos) := ((← get).at_, (← get).pos)
    let t ← withLater (Elab.fvStmts [x] rest) (inferExpr scope amb value)
    -- The variable lives until the end of this block: nothing that can reach
    -- it may be left over afterwards.
    let brand ← freshBrand
    modify fun s =>
      { s with
        cells := s.cells.push (brand, x, t)
        -- A variable owns what it holds.
        dropCands := s.dropCands.push (⟨s.owner, at_.1, at_.2, x, false⟩, t, pos) }
    -- Nothing says the variable is empty when its block ends, or when it is
    -- assigned: what it holds then is let go.
    mustDrop t s!"the mutable variable `{x}` lets go of what it holds when it is assigned or its block ends"
    let result ← inferStmts ((x, .cell t brand) :: scope) amb rest want
    checkEscape brand s!"`{x}` could be used after its block has ended"
      (("something that uses it is the block's result", result) :: scopeRoots scope) amb
    pure result
  | .assign target value :: rest => do
    withLater (Elab.fvStmts [] rest) do
      -- The value is computed first, and then the place is written.
      let (expected, written) ← match target with
        | .name none x =>
          match scope.lookup x with
          | some (.cell t brand) => do
            -- What the variable held is destroyed.
            modify fun s =>
              { s with dropCands :=
                  s.dropCands.push (⟨s.owner, s.at_.1, s.at_.2, x, true⟩, t, s.pos) }
            pure (t, UseKind.var brand x .write)
          | some _ => throw s!"`{x}` is not a mutable variable"
          | none => throw s!"unknown name `{x}`"
        | .deref e => do
          let inner ← freshTy
          let cap ← freshCap
          unifyAt "`*` assigns through a reference" (.ref .uniq inner cap)
            (← inferPlace scope amb e)
          mustDrop inner "assigning through a reference lets go of what was there"
          pure (inner, UseKind.through cap (placeName e) true)
        | _ => throw "only a mutable variable or `*reference` can be assigned"
      unifyAt "the assigned value" expected (← inferExpr scope amb value)
      use scope written
    inferStmts scope amb rest want
  | .defer e :: rest => do
    -- A cleanup performs no effects: it may run while its surroundings are
    -- being left, when no handler should be asked to do anything.
    try
      let t ← withLater (Elab.fvStmts [] rest) (inferExpr scope ⟨[], none⟩ e)
      mustDrop t "what a `defer` gives is let go"
    catch err => throw s!"a `defer` cannot perform effects: {err}"
    -- It runs when the rest is left, so what it mentions is still to be used
    -- throughout the rest.
    withLater (Elab.fvExpr [] e) (inferStmts scope amb rest want)

/-- Check a pattern against a type; the names it binds. -/
partial def inferPat (p : Pattern) (t : Ty) : M Scope := do
  match p with
  | .wild => do
    mustDrop t "`_` lets go of a value"
    pure []
  | .int _ => do
    unifyAt "an integer pattern" .int t
    pure []
  | .tuple ps => do
    let ts ← ps.mapM fun _ => freshTy
    unifyAt "a tuple pattern" (.tuple ts) t
    inferPats ps ts
  | .var x => do
    match ← resolveCtor x none with
    | some (_, sig) => do
      let (fields, result) ← instCtor sig
      unless fields.isEmpty do arityError s!"constructor `{x}`" fields.length 0
      unifyAt s!"the pattern `{x}`" result t
      pure []
    | none =>
      match (← get).aliases.lookup x with
      | some e => do inferPat (← exprToPat e) t
      | none => pure [(x, .val t)]
  | .ctor x q ps => do
    match ← resolveCtor x q with
    | some (_, sig) => do
      let (fields, result) ← instCtor sig
      unless fields.length == ps.length do arityError s!"constructor `{x}`" fields.length ps.length
      unifyAt s!"the pattern `{x}(..)`" result t
      inferPats ps fields
    | none => throw s!"unknown constructor `{x}` in a pattern"

partial def inferPats (ps : List Pattern) (ts : List Ty) : M Scope := do
  let mut out : Scope := []
  for (p, t) in ps.zip ts do
    out := (← inferPat p t) ++ out
  pure out

/-- The type of a callable given by clauses. Parameter and result annotations
are checked if present; the clauses must cover every argument. -/
partial def inferCallable (scope : Scope) (annots : List (Option Ty)) (ret : Option Ty)
    (self : Option String) (clauses : List Clause) (what : String) (id : Nat := 0) : M Ty := do
  let arity := match clauses with
    | .mk pats _ :: _ => pats.length
    | [] => 0
  let params ← (List.range arity).mapM fun i => do
    match annots[i]? with
    | some (some t) => pure t
    | _ => freshTy
  let result ← match ret with
    | some t => pure t
    | none => freshTy
  let row ← freshRow
  -- The body runs when the callable is called, perhaps again and again: what
  -- it mentions from outside is still to be used wherever the body has got to,
  -- and the values the expression around it has computed are not its concern.
  let outerLater := (← get).later
  let outerTemps := (← get).temps
  let outerAnon := (← get).anon
  modify fun s =>
    { s with later := (clauses.flatMap (Elab.fvClause [])).eraseDups, temps := [], anon := [] }
  -- What the callable captures from the scope it is written in.
  let cap ← freshCap
  captureAll scope cap (clauses.flatMap (Elab.fvClause [])) fun x => clauses.any (assignsClause x)
  let loansBefore := (← get).loans.size
  let brand ← freshBrand
  let scope := match self with
    | some name => ("@" ++ name, Binding.label result brand) :: scope
    | none => scope
  -- Where the result of clause `j` can be converted, if this callable is one
  -- the elaborator can be told about.
  let site := fun (j : Nat) => match self with
    | some name => some (Elab.Site.fnResult name j)
    | none => if id == 0 then none else some (Elab.Site.result id j)
  let checkClause := fun (j : Nat) => (do
    match clauses[j]? with
    | none => pure none
    | some (.mk pats body) =>
      unless pats.length == arity do
        throw "the clauses of a callable take different numbers of arguments"
      let binds ← inferPats pats params
      let here := (← get).pos
      let at_ := if (Elab.wrapResult "" body).isSome then site j else none
      let failure ← try
          (do
            let _ ← inferStmts (binds ++ scope) row body (some (result, at_))
            pure none)
        catch e =>
          if (e.splitOn resultMark).length > 1 then pure (some (e.replace resultMark ""))
          else throw e
      match failure with
      | some e => pure (some e)
      | none =>
        -- Uses are counted in the body as it will be elaborated.
        let cs := (← get).coercions.toList
        let body := if cs.isEmpty then body else
          match Elab.coerceClause cs ((site j).bind fun k => List.lookup k cs) (.mk pats body) with
          | .mk _ body => body
        checkUses here scope binds body
        pure none : M (Option String))
  -- As with arguments: a clause whose result does not fit is looked at first
  -- on a second attempt, so that the others can be converted to what it gives.
  let order := List.range clauses.length
  let saved ← get
  let mut failed : Option (Nat × String) := none
  for j in order do
    if let some e ← checkClause j then
      failed := some (j, e)
      break
  if let some (j, e) := failed then
    set saved
    if saved.coercing.isEmpty then throw e
    for k in j :: order.erase j do
      if (← checkClause k).isSome then
        set saved
        throw e
  let check : Pending := ⟨(← get).pos, what, params, clauses.map fun
    | .mk pats _ => pats⟩
  modify fun s => { s with pending := s.pending.push check }
  -- A function's own label returns from it, so nothing holding that label may
  -- be handed back to the caller.
  if let some name := self then
    let roots := ("it is returned from the function", result) ::
      params.map fun p => ("the caller could hold it through a parameter", p)
    checkEscape brand (jumpsAfter name) roots row
  -- The borrows made while it runs: a computation suspended inside it holds
  -- them.
  for id in [loansBefore:(← get).loans.size] do
    captures cap (.inner id)
  modify fun s => { s with later := outerLater, temps := outerTemps, anon := outerAnon }
  pure (.func params result row cap)

/--
`handle subject { arms }`. The subject may perform the handled effects on top
of the ambient ones. An effect whose every operation has an arm that cannot
fail to match is handled completely; any other handled effect may still reach
an outer handler, so it must be permitted outside as well.
-/
partial def inferHandle (scope : Scope) (amb : Row) (subject : Expr) (arms : List Clause) :
    M Ty := do
  let s ← get
  let mut completions : Array (Pattern × List Stmt) := #[]
  let mut opArms : Array (String × OpSig × List Pattern × List Stmt) := #[]
  for arm in arms do
    match arm with
    | .mk [.ctor x q ps] body =>
      match s.ops.lookup x with
      | some sig =>
        if let some owner := q then
          unless owner == sig.effect do throw s!"`{x}` is not an operation of `{owner}`"
        opArms := opArms.push (x, sig, ps, body)
      | none => completions := completions.push (.ctor x q ps, body)
    | .mk [p] body => completions := completions.push (p, body)
    | .mk _ _ => throw "a handler arm has exactly one head pattern"
  -- One instance of each handled effect.
  let mut insts : List (String × List Ty) := []
  for e in (opArms.toList.map (·.2.1.effect)).eraseDups do
    let decl := (s.effects.lookup e).getD ⟨[], []⟩
    insts := insts ++ [(e, ← decl.tvars.mapM fun _ => freshTy)]
  let ambFlat ← flattenRow amb
  -- An arm can run whenever the subject performs, and the subject goes on
  -- when an arm resumes it: what either mentions is still to be used
  -- throughout the other.
  let outerLater := (← get).later
  modify fun st => { st with later := Elab.fvExpr [] (.handle subject arms) ++ outerLater }
  let loansBefore := (← get).loans.size
  let subjectTy ← inferExpr scope ⟨insts ++ ambFlat.effs, ambFlat.tail⟩ subject
  -- The borrows the handled computation makes. While it is suspended in an
  -- arm, its resumption holds them: the arm must not use what they exclude.
  let suspendedLoans := (List.range (← get).loans.size).drop loansBefore
  let result ← freshTy
  if completions.isEmpty then unify result subjectTy
  else
    for (p, body) in completions do
      let binds ← inferPat p subjectTy
      let here := (← get).pos
      unifyAt "the result of a completion clause" result
        (← inferStmts (binds ++ scope) amb body)
      checkUses here scope binds body
    let check : Pending := ⟨(← get).pos, "the completion clauses of this handler do", [subjectTy],
      completions.toList.map fun (p, _) => [p]⟩
    modify fun st => { st with pending := st.pending.push check }
  let mut covered : List String := []
  for (x, sig, ps, body) in opArms do
    let inst := (insts.lookup sig.effect).getD []
    let (payload, opResult) := instOp sig inst
    match opResult with
    | none =>
      unless ps.length == payload.length do
        arityError s!"an arm for the operation `{x}`" payload.length ps.length
      let binds ← inferPats ps payload
      let here := (← get).pos
      unifyAt s!"the result of the arm for `{x}`" result (← inferStmts (binds ++ scope) amb body)
      checkUses here scope binds body
      if ← ps.allM irrefutable then covered := x :: covered
    | some o =>
      if ps.length == payload.length + 1 then
        -- The resumption holds the handled computation and, because resuming
        -- reinstalls the handler, the arms too: everything either of them uses.
        let held ← freshCap
        captures held .once
        if sig.must then captures held .must
        for id in suspendedLoans do
          captures held (.inner id)
        captureAll scope held (Elab.fvExpr [] (.handle subject arms)) fun x =>
          assignsExpr x (.handle subject arms)
        let binds ← inferPats ps (payload ++ [.func [o] result amb held])
        let here := (← get).pos
        unifyAt s!"the result of the arm for `{x}`" result
          (← inferStmts (binds ++ scope) amb body)
        checkUses here scope binds body
        if ← (ps.take payload.length).allM irrefutable then covered := x :: covered
      else if ps.length == payload.length then
        let binds ← inferPats ps payload
        let here := (← get).pos
        -- The arm resumes with what it gives: the computation is suspended,
        -- holding its borrows, for as long as the arm runs.
        let held ← freshCap
        captures held .once
        for id in suspendedLoans do
          captures held (.inner id)
        captureAll scope held (Elab.fvExpr [] (.handle subject arms)) fun x =>
          assignsExpr x (.handle subject arms)
        let resumption := ("%resumed", Binding.val (.func [o] result amb held))
        unifyAt s!"the value the arm for `{x}` resumes with" o
          (← withLater ["%resumed"] (inferStmts (binds ++ resumption :: scope) amb body))
        checkUses here scope binds body
        if ← ps.allM irrefutable then covered := x :: covered
      else arityError s!"an arm for the operation `{x}`" payload.length ps.length
  for (e, inst) in insts do
    let decl := (s.effects.lookup e).getD ⟨[], []⟩
    unless decl.ops.all covered.contains do
      try unifyRow amb ⟨[(e, inst)], some (← freshRowVar)⟩
      catch err =>
        throw s!"this handler does not handle every `{e}` operation, and the rest cannot \
          be passed on: {err}"
  modify fun st => { st with later := outerLater }
  pure result

end

/-! ## Programs -/

structure FnDecl where
  name : String
  params : List String
  annots : List (Option TypeExpr)
  ret : Option TypeExpr
  clauses : List Clause
  /-- For a function an implementation gives: the implementation, and the
  trait's function it is. -/
  impl : Option (ImplDecl × MethodSig) := none

/-! ## Traits

A bound is a trait needed of a type. Where the type is made with a name, an
implementation meets it, on its conditions; where it is one the function is
generic in, the function is given the evidence, and so needs the bound of
whoever calls it. -/

/-- The number `Traits.solve` knows a type by, if it is one a function is
generic in: a type nothing has decided, or one of the function's own type
parameters. -/
def keyOf (t : Ty) : M (Option Nat) := do
  match ← find t with
  | .var id => pure (some (2 * id))
  | .con n [] =>
    if n.startsWith "'" then
      let keys := (← get).rigidKeys
      match keys.toList.idxOf? n with
      | some i => pure (some (2 * i + 1))
      | none =>
        modify fun s => { s with rigidKeys := s.rigidKeys.push n }
        pure (some (2 * keys.size + 1))
    else pure none
  | _ => pure none

partial def toSTy (t : Ty) : M Traits.STy := do
  let t ← find t
  match ← keyOf t with
  | some k => pure (.var k)
  | none =>
    match t with
    | .con n args => pure (.con n (← args.mapM toSTy))
    | .tuple args => pure (.con "(tuple)" (← args.mapM toSTy))
    | .fn _ _ _ _ _ => pure (.con "(callable)" [])
    | .ref _ _ _ => pure (.con "(reference)" [])
    | .var _ => pure (.var 0)

/-- The bounds on types a function is generic in that a bound comes down to,
each with the number of its type. This is only to say what a function needs
and to explain a failure: the evidence itself is `Traits.solve`'s. -/
partial def leaves (pos trait : String) (t : Ty) : M (List (String × Nat × Ty)) := do
  let t ← find t
  match ← keyOf t with
  | some k => pure [(trait, k, t)]
  | none =>
    let missing : M (List (String × Nat × Ty)) := do
      throw s!"{pos}`{showTy (← zonk t)}` does not implement `{trait}`"
    match t with
    | .con n args =>
      match Traits.findImpl trait n args.length (← get).kimpls with
      | some (_, I) =>
        let mut out : List (String × Nat × Ty) := []
        for (tr', j) in I.context do
          out := out ++ (← leaves pos tr' (args[j]?.getD .unit))
        pure out
      | none => missing
    | _ => missing

partial def toDictE (impls : Array ImplDecl) : Traits.Dict → Elab.DictE
  | .given k => .param k
  | .impl i subs => .impl ((impls[i]?.map (·.dictFn)).getD "") (subs.map (toDictE impls))

/-- The types a value of this type directly holds. -/
def partsOf (t : Ty) : M (List Ty) := do
  match ← find t with
  | .tuple args => pure args
  | .con name args =>
    match (← get).types.lookup name with
    | none => pure []
    | some decl =>
      decl.ctors.flatMapM fun c => do
        match (← get).ctors.lookup c with
        | none => pure []
        | some sig => pure (sig.fields.map (subst (sig.tvars.zip args) [] []))
  | _ => pure []

/-- Meet the bounds of the group just inferred, and give each of its functions
its type. A bound on a type the function is generic in becomes something the
function is given; every other is met by `Traits.solve`. -/
def settleBounds (decls : List FnDecl) (defs : List (String × Ty)) : M Unit := do
  let mut pending := (← get).bounds
  let uses := (← get).groupUses
  let cands := (← get).dropCands
  modify fun s => { s with bounds := #[], groupUses := #[], dropCands := #[] }
  -- A variable whose value's type has `Drop` needs the implementation, to run
  -- its function when the value is destroyed.
  for (site, ty, pos) in cands do
    if let .con n _ ← find ty then
      if (← get).kimpls.any fun I => I.trait == "Drop" && I.head == n then
        let id := 2000000000 + (← get).dropSites.size
        pending := pending.push ⟨"Drop", ty, id, 0, site.owner, pos⟩
        modify fun s => { s with dropSites := s.dropSites.push (site, id) }
  -- What the group's functions need of the types they are generic in.
  let mut leafs : Array (String × Nat × Ty) := #[]
  for b in pending do
    let ls ← try leaves b.pos b.trait b.ty catch e => throw (inFunction b.owner e)
    for l in ls do
      unless leafs.any (fun x => x.1 == l.1 && x.2.1 == l.2.1) do leafs := leafs.push l
  let mut givensOf : List (String × List (String × Nat)) := []
  for d in decls do
    let t0 ← zonk ((defs.lookup d.name).getD .unit)
    let (t1, seen) ← openParams [] t0
    let scheme ← generalize t1 [] false
    let mine : List (String × Nat × Ty) ← match d.impl with
      | some (im, _) =>
        -- An implementation says what it assumes.
        im.context.mapM fun (tr, j) => do
          let t := Ty.con s!"'{(im.params[j]?).getD ""}@{d.name}" []
          pure (tr, ((← keyOf t).getD 0), t)
      | none =>
        pure (leafs.toList.filter fun (_, _, k) =>
          match k with
          | .var id => scheme.tvars.contains id
          | .con n [] => (seen.lookup n).isSome
          | _ => false)
    let bounds := mine.map fun (tr, _, k) =>
      (tr, match k with
        | .con n [] => (seen.lookup n).getD k
        | k => k)
    givensOf := (d.name, mine.map fun (tr, k, _) => (tr, k)) :: givensOf
    modify fun s =>
      { s with
        fns := (d.name, { scheme with bounds := bounds }) :: s.fns
        fnBounds := (d.name, mine.length) :: s.fnBounds }
  let impls := (← get).impls
  let kimpls := (← get).kimpls
  let mut table : List (Nat × List Elab.DictE) := []
  let record := fun (table : List (Nat × List Elab.DictE)) (call : Nat) (d : Elab.DictE) =>
    match table.lookup call with
    | some ds => (call, ds ++ [d]) :: table.filter (·.1 != call)
    | none => (call, [d]) :: table
  for b in pending do
    let givens := (givensOf.lookup b.owner).getD []
    -- What `Traits.coherent` asks of the assumptions.
    unless Traits.distinct givens do
      throw (inFunction b.owner s!"{b.pos}a bound is assumed twice; this is a compiler defect")
    match Traits.solve kimpls givens 100000 b.trait (← toSTy b.ty) with
    | some d => table := record table b.call (toDictE impls d)
    | none =>
      for (tr, k, t) in ← leaves b.pos b.trait b.ty do
        unless givens.contains (tr, k) do
          match t with
          | .con n [] =>
            let hint := if (decls.find? (·.name == b.owner)).any (·.impl.isSome) then
              s!": add `where {bareName n}: {tr}` to the implementation" else ""
            throw (inFunction b.owner
              s!"{b.pos}`{bareName n}` is not known to implement `{tr}`{hint}")
          | _ =>
            throw (inFunction b.owner
              s!"{b.pos}`{tr}` is needed of a type that nothing here decides")
      throw (inFunction b.owner s!"{b.pos}no implementation of `{b.trait}` was found; this is a compiler defect")
  -- A use of one of the group's functions inside the group passes on what the
  -- function it is in was given.
  for u in uses do
    let theirs := (givensOf.lookup u.callee).getD []
    unless theirs.isEmpty do
      if u.call == 0 then
        throw (inFunction u.owner s!"{u.pos}`{u.callee}` needs a trait of a type it is used at, so it is called where it is named: write a block that calls it")
      let mine := (givensOf.lookup u.owner).getD []
      for g in theirs do
        match mine.idxOf? g with
        | some i => table := record table u.call (.param i)
        | none =>
          throw (inFunction u.owner
            s!"{u.pos}`{u.callee}` needs `{g.1}` of a type that `{u.owner}` is not given")
  modify fun s => { s with dictTable := s.dictTable ++ table.toArray }

/-- What a type says of its own uses may only narrow what its fields allow. -/
def checkUseDecls : M Unit := do
  for (head, must, once) in (← get).useDecls do
    let arity := (((← get).types.lookup head).map (·.arity)).getD 0
    let args ← (List.range arity).mapM fun _ => freshTy
    for part in ← partsOf (.con head args) do
      unless must do
        if let some what ← tyMustUse {} [head] part then
          throw s!"`impl Use` for `{head}`: it holds {what}, which has to be used, so the fewest uses of a `{head}` cannot be 0"
      unless once do
        modify fun s => { s with seen := [] }
        if ← tyOwnsOnce [head] part then
          throw s!"`impl Use` for `{head}`: it holds a value that can be used only once, so the most uses of a `{head}` cannot be `infinity`"

/-- Strongly connected components of the call graph, callees first. -/
partial def components (names : List String) (deps : String → List String) : List (List String) :=
  let rec visit (v : String) (st : Nat × List String × List (String × Nat × Nat) × List (List String)) :
      Nat × List String × List (String × Nat × Nat) × List (List String) :=
    let (index, stack, info, out) := st
    let info := (v, index, index) :: info
    let st := (index + 1, v :: stack, info, out)
    let st := (deps v).foldl (fun st w =>
      let (index, stack, info, out) := st
      match info.lookup w with
      | none =>
        let (index, stack, info, out) := visit w (index, stack, info, out)
        let lowW := ((info.lookup w).map (·.2)).getD 0
        (index, stack, lower info v lowW, out)
      | some (idxW, _) =>
        if stack.contains w then (index, stack, lower info v idxW, out) else st) st
    let (index, stack, info, out) := st
    match info.lookup v with
    | some (idx, low) =>
      if idx == low then
        let comp := (stack.takeWhile (· != v)) ++ [v]
        (index, stack.drop comp.length, info, out ++ [comp])
      else st
    | none => st
  let (_, _, _, out) := names.foldl (fun st v =>
    if (st.2.2.1.lookup v).isSome then st else visit v st) (0, [], [], [])
  out
where
  lower (info : List (String × Nat × Nat)) (v : String) (bound : Nat) : List (String × Nat × Nat) :=
    info.map fun (n, idx, low) => if n == v then (n, idx, min low bound) else (n, idx, low)

/-- Infer one group of mutually recursive functions and generalise their types. -/
def checkGroup (decls : List FnDecl) : M Unit := do
  let mut group : List (String × Ty) := []
  for d in decls do
    group := (d.name, ← freshTy) :: group
  modify fun s => { s with group := group }
  let mut defs : List (String × Ty) := []
  let mut reused : List (String × Ty) := []
  for d in decls do
    try
      modify fun s => { s with pos := "", owner := d.name, later := [], temps := [], anon := [] }
      let rigid := d.params.map fun p => (p, Ty.con s!"'{p}@{d.name}" [])
      let annots ← d.annots.mapM fun
        | some t => some <$> resolveType rigid false t
        | none => pure none
      -- The result may say what the function performs: that, and no more.
      let (retExpr, declared) := match d.ret with
        | some (.performs t effects) => (some t, some effects)
        | other => (other, none)
      let ret ← match retExpr with
        | some t => some <$> resolveType rigid false t
        | none => pure none
      let t ← inferCallable [] annots ret (some d.name) d.clauses s!"the clauses of `{d.name}` do"
      if let some effects := declared then
        let effects ← resolveEffects rigid false effects
        if let .fn _ _ effs tail _ ← find t then
          try unifyRow ⟨effs, tail⟩ ⟨effects, none⟩
          catch e =>
            let said := if effects.isEmpty then "nothing" else showEffs effects
            throw s!"`{d.name}` says it performs {said}, and that is not what it performs: {e}"
      -- A function an implementation gives is the function its trait declares,
      -- at the implementation's type.
      if let some (im, sig) := d.impl then
        let tm := [(sig.self, Ty.con im.head (rigid.map (·.2)))]
        let want ← freshenCaps
          (.func (sig.params.map (subst tm [] [])) (subst tm [] [] sig.ret) ⟨[], none⟩ (← freshCap))
        try unify t want
        catch e =>
          throw s!"this is not the function `{sig.trait}` declares, which takes its arguments, gives its result and performs nothing: {e}"
      -- A use of the function inside its group has the function's type, but
      -- what it is given there need not be what the function itself was given:
      -- the captures of the two are kept apart, and related below.
      let used := (group.lookup d.name).getD t
      if let .var _ ← find used then unify used t
      else
        unifyAt s!"`{d.name}` is used recursively at a different type" (← freshenCaps used) t
        reused := (d.name, used) :: reused
      defs := (d.name, t) :: defs
      runPending
      runLowerChecks t
      checkDups (← get).dups
      checkDrops (← get).drops
      checkStays (← get).stays
    catch e =>
      -- The usual cause: the body ends in an expression run only for its effect,
      -- whose value has become the function's result.
      let recursive := (e.splitOn "is used recursively").length > 1
        && (e.splitOn "contains itself").length > 1
      let hint := if recursive then
        "; if the last expression of the body is not meant as the result, end it with `;`"
        else ""
      throw (inFunction d.name (e ++ hint))
  -- Each use inside the group is a use like any other: of the function's type
  -- with captures of its own, which capture what the function's do.
  for (name, used) in reused do
    if let some t := defs.lookup name then
      try unify (← instantiate (← generalize t) (some name)) used
      catch e => throw (inFunction name s!"`{name}` is used recursively at a different type: {e}")
  checkLoans
  settleBounds decls defs
  -- Later functions follow calls into these as they will be elaborated.
  let cs := (← get).coercions.toList
  unless cs.isEmpty do
    modify fun s =>
      { s with fnBodies := s.fnBodies.map fun (name, clauses) =>
          if decls.any (·.name == name) then (name, Elab.coerceFn cs name clauses)
          else (name, clauses) }
  -- A later function can still decide a requirement made here, through a
  -- declaration whose field types are inferred, so each is checked again at
  -- the end of the program.
  let owner := (decls.head?.map (·.name)).getD "the program"
  let late := (← get).dups.map fun (t, why) => (t, inFunction owner why)
  let lateDrops := (← get).drops.map fun (t, why) => (t, inFunction owner why)
  let lateStays := (← get).stays.map fun (t, why) => (t, inFunction owner why)
  modify fun s =>
    { s with group := [], dups := #[], lateDups := s.lateDups ++ late, drops := #[],
             lateDrops := s.lateDrops ++ lateDrops, stays := #[],
             lateStays := s.lateStays ++ lateStays }

/-- Check a whole program. Gives what the elaborator needs to know about its
blocks: which take an argument they do not name, and for each that is handed a
block which was not run, the identity of that block if it can only be one. The
elaborator then lets those two share what they capture. -/
def checkProgram (items : List Item) : Except String Elab.Blocks := do
  let decls : List FnDecl := items.filterMap fun
    | .fn name params annots ret clauses => some { name, params, annots, ret, clauses }
    | _ => none
  let names := decls.map (·.name)
  let mentions := fun (name : String) =>
    match decls.find? (·.name == name) with
    | some d => ((d.clauses.flatMap (Elab.fvClause [])).filter names.contains).eraseDups
    | none => []
  let coercing := items.filterMap fun
    | .coerce name => some name
    | _ => none
  for c in coercing do
    unless names.contains c do throw s!"`coerce {c}`: there is no function `{c}`"
  -- A coercion can be applied in any function, so the coercions are checked
  -- before all the others: all, that is, but the functions the coercions are
  -- themselves built from, in which none is applied.
  let builtFrom := Id.run do
    let mut seen := coercing
    for _ in [0:names.length] do
      seen := (seen ++ seen.flatMap mentions).eraseDups
    pure seen
  let deps := fun (name : String) =>
    if builtFrom.contains name then mentions name else (mentions name ++ coercing).eraseDups
  let action : M Elab.Blocks := do
    modify fun s => { s with fnBodies := decls.map fun d => (d.name, d.clauses) }
    declare items
    declareTraits items
    checkUseDecls
    for comp in components names deps do
      checkGroup (comp.filterMap fun n => decls.find? (·.name == n))
    -- The functions implementations give, each on its own: any function may
    -- call them, but only through a trait, whose types are declared.
    for im in (← get).impls do
      for item in im.methods do
        if let .fn m _ annots ret clauses := item then
          if let some sig := (← get).methods.lookup m then
            checkGroup [{ name := Elab.implFnName im.trait im.head m, params := im.params, annots,
                          ret, clauses, impl := some (im, sig) }]
    for c in coercing do
      unless (((← get).fnBounds.lookup c).getD 0) == 0 do
        throw s!"`coerce {c}`: a coercion cannot need a trait of a type it is used at"
    unless (((← get).fnBounds.lookup "main").getD 0) == 0 do
      throw "`main` needs a trait of a type that nothing decides"
    checkDups (← get).lateDups
    checkDrops (← get).lateDrops
    checkStays (← get).lateStays
    match (← get).fns.lookup "main" with
    | none => pure ()
    | some scheme =>
      match ← zonk (← instantiate scheme) with
      | .fn ps r effs _ _ =>
        unless ps.isEmpty do throw "`main` takes no arguments"
        unless effs.isEmpty do
          throw s!"`main` performs effects that nothing handles: {showEffs effs}"
        -- Nothing uses what the program gives.
        modify fun s => { s with pos := "", drops := #[] }
        mustDrop r "the result of `main` is let go when the program ends"
        checkDrops (← get).drops
      | _ => pure ()
    let s ← get
    let mut links : List (Nat × Nat) := []
    for (id, cap) in s.unrun do
      let root ← findCap cap
      let mut owners : List Nat := []
      for (owner, c) in s.blockCaps do
        if owner != id && owner != 0 && (← findCap c) == root && !owners.contains owner then
          owners := owner :: owners
      if let [owner] := owners then links := (id, owner) :: links
    -- A block taken to be given one particular block, where in the end it
    -- may be given another, lets go of whatever it is given.
    let mut unlinked : Array (Ty × String) := #[]
    for (id, owner, input, why) in s.assumedLinks do
      unless links.contains (id, owner) do unlinked := unlinked.push (input, why)
    checkDrops unlinked
    let implEs := s.impls.toList.map fun im =>
      let names := (s.traits.lookup im.trait).getD []
      (⟨im.dictFn, im.context.length, names.map fun m =>
        (Elab.implFnName im.trait im.head m, ((s.methods.lookup m).map (·.params.length)).getD 0)⟩ :
        Elab.ImplE)
    pure ⟨s.given.toList, links, s.coercions.toList,
      ⟨s.dictTable.toList, s.methodCalls.toList, s.fnBounds, implEs, s.dropSites.toList⟩⟩
  let (blocks, _) ← action.run {}
  pure blocks

end Glorious.Check
