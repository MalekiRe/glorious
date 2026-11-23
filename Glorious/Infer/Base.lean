module

public import Std.Data.HashMap
public import Std.Data.HashSet
public import Glorious.Syntax.Ast
public import Glorious.Elab
public import Glorious.Typing.Certify

/-!
# Finding a certificate for a Core program

The Core type checker in `Glorious/Typing` needs to be told the signatures of
each function and a few types the program text leaves open. This pass finds
them, by unification over the Core program the elaborator produced. It is not
proved and does not need to be: whatever it produces goes to `checkProgram`,
which accepts it only if it is a valid typing.

It works in two steps. First each group of mutually recursive functions is
inferred once, callees before callers, giving the group a general type together
with the conditions a user of the group must also meet. A reference to a
function from outside its group takes a fresh copy of that type. Then, starting
from `main`, each function is given a signature for every ground type it is
actually used at, and its hints are read off at that type.
-/

public section

namespace Glorious.Infer

open Syntax
open Glorious.Typing (Ty FnSig Hint Cert SigEntry DataInst OpInst)

/-- Whether a callable can be called only once, while that is being inferred. -/
inductive ICls where
  | var (id : Nat)
  | lit (once : Bool)
  deriving BEq, Hashable

/-- A region while it is being inferred: the same as another, or the cell of one
scope. A region nothing is known about has neither. -/
inductive IRg where
  | link (id : Nat)
  | atom

/-- What a callable may touch, while that is being inferred: some regions, and
whatever some other callables may touch. -/
structure IAcc where
  link : Option Nat := none
  rgns : List Nat := []
  /-- Those of the regions that it may write. -/
  wrs : List Nat := []
  /-- Included sets, each without one region if one is given. -/
  subs : List (Nat × Option Nat) := []
  /-- The region the callable is polymorphic in, if a cell's scope runs it. -/
  binder : Option Nat := none
  /-- The further regions its type binds, if it is one given references to
  more than one. -/
  more : List Nat := []
  /-- Callables called at regions of the caller's choosing: what each
  touches, and for each region its type binds the region chosen. What it
  touches of the first is touched of the second. -/
  insts : List (Nat × List (Nat × Nat)) := []
  /-- Nothing will be added to it: it is of a group of functions whose types
  are settled, and what it includes has been worked out and written here in
  its own `rgns` and `wrs`. A copy of it copies those and nothing further. -/
  final : Bool := false
  deriving BEq, Hashable

/-- A type while it is being inferred. -/
inductive ITy where
  /-- Not yet known. -/
  | var (id : Nat)
  /-- A type parameter of the declaration this type was written in. -/
  | param (i : Nat)
  | int
  /-- A scalar of so many bits (`Typing.Ty.scalar`). -/
  | scalar (bits : Int)
  | tuple (fs : List ITy)
  | data (name : Nat) (args : List ITy)
  /-- A callable; its operations, each with the type arguments of its effect,
  and a variable for any others if the row is open. `env` is a tuple of what it
  captured if its type is to state that, `never` if it cannot, and otherwise
  not yet known. `acc` stands for the regions a call may touch. -/
  | fn (ps : List ITy) (ret : ITy) (ops : List (Nat × List ITy)) (tail : Option Nat) (cls : ICls)
      (env : ITy) (acc : Nat)
  | ref (ρ : Nat) (t : ITy)
  /-- The result of a call that does not return. -/
  | never
  deriving BEq, Hashable

abbrev IOps := List (Nat × List ITy)

structure IRow where
  ops : IOps
  tail : Option Nat
  deriving BEq, Hashable

def ITy.unit : ITy := .tuple []

/-- A type with each of its parts made anew: the types directly in it by `ty`,
and its regions, classes, accesses and row tail each by its own. -/
@[specialize] def ITy.mapM {m : Type → Type} [Monad m] (ty : ITy → m ITy) (rg : Nat → m Nat := pure)
    (cls : ICls → m ICls := pure) (acc : Nat → m Nat := pure)
    (tail : Option Nat → m (Option Nat) := pure) : ITy → m ITy
  | .tuple fs => do pure (.tuple (← fs.mapM ty))
  | .data n args => do pure (.data n (← args.mapM ty))
  | .fn ps r ops t c env a => do
    pure (.fn (← ps.mapM ty) (← ty r) (← ops.mapM fun (op, ts) => do pure (op, ← ts.mapM ty))
      (← tail t) (← cls c) (← ty env) (← acc a))
  | .ref ρ t => do pure (.ref (← rg ρ) (← ty t))
  | t => pure t

/-- The types directly in a type, a callable's operations' last. -/
def ITy.parts : ITy → List ITy
  | .tuple fs | .data _ fs => fs
  | .fn ps r ops _ _ env _ => ps ++ [r, env] ++ ops.flatMap (·.2)
  | .ref _ t => [t]
  | _ => []

def ITy.func (ps : List ITy) (ret : ITy) (row : IRow) (cls : ICls) (env : ITy) (acc : Nat) : ITy :=
  .fn ps ret row.ops row.tail cls env acc

/-- A function's signature while it is being inferred. -/
structure ISig where
  caps : List ITy
  params : List ITy
  ret : ITy
  row : IRow
  acc : Nat
  deriving Hashable

inductive IHint where
  | ty (t : ITy)
  /-- A closure, and the signature its function is used at. -/
  | clo (t : ITy) (sig : ISig)
  /-- A handler: what it yields, its operations, what it may touch, and the
  signatures of its functions, the one for a result first. -/
  | handler (ρ : ITy) (H : IOps) (Φ : Nat) (sigs : List ISig)
  /-- A call: what the callee gives back, and what the code after it takes the
  result to be. The checker is told the second only if the first is `never`. -/
  | result (r b : ITy)
  /-- A call of a callable whose type binds a region: what the callable
  touches, by which its type is known, and the region the call chooses. -/
  | rgns (acc : Nat) (actuals : List Nat)
  deriving Hashable

/-- A lifetime a declared type or an effect is given is one of its arguments
in Core: a type that carries the region, `&ρ ()`. In the declaration's own
types the region of its `i`-th parameter is written as this plus `i`, which
no region of a program is; `subst` puts the argument's region there. -/
def lifetimeBase : Nat := 1099511627776

structure CtorDecl where
  owner : Nat
  arity : Nat
  fields : List ITy
  /-- Which of the type's parameters are lifetimes. -/
  lifetimes : List Bool := []

structure OpDecl where
  effect : Nat
  arity : Nat
  payload : List ITy
  result : Option ITy
  /-- Which of the effect's parameters are lifetimes. -/
  lifetimes : List Bool := []

/-- Every operation of `sub` must be served at the same type: by `under` if it
lists the operation, and by `sup` otherwise. -/
structure Incl where
  sub : IRow
  under : IOps
  sup : IRow
  deriving Hashable

/-- A function of an inferred group: its signature, the hints of each clause,
and the functions outside the group it refers to, each at the type it uses. -/
structure Member where
  fn : Nat
  sig : ISig
  hints : Array (Array IHint)
  refs : Array (Nat × ISig)
  deriving Hashable

/-- A call whose callable was not yet known when it was met: the callable,
what it is given, what it gives and performs here, what it touches, the
region this call chooses if the callable's type binds one, and what the
calling code touches. -/
structure Call where
  callee : ITy
  given : List ITy
  result : ITy
  row : IRow
  acc : Nat
  /-- Regions for this call to choose, as many as a callable type may bind. -/
  actuals : List Nat
  self : Nat
  deriving Hashable

/-- The general type of a group of mutually recursive functions. Variables made
while the group was inferred stand for anything, except those in `fixed`, which
declarations share with the rest of the program. -/
structure Scheme where
  startTy : Nat
  startRow : Nat
  startCls : Nat
  startRg : Nat
  startAcc : Nat
  fixedTys : Std.HashSet Nat
  fixedRows : Std.HashSet Nat
  fixedClss : Std.HashSet Nat
  fixedRgs : Std.HashSet Nat
  fixedAccs : Std.HashSet Nat
  members : List Member
  /-- Everything the group's own typing depends on. -/
  incls : Array Incl
  places : Array (ITy × Nat × ITy)
  coerces : Array (ITy × ITy × Bool)
  nevers : Array ITy
  onces : Array (ICls × List ITy)
  shows : Array (ITy × List ITy)
  opens : Array (ITy × ITy × List (Nat × Nat)) := #[]
  calls : Array Call := #[]
  /-- Callables given up whose types the group does not fix (a parameter of
  any callable type): what giving one up touches is known at each use. -/
  givenUpOpen : Array (ITy × IRow × Nat) := #[]
  /-- The part of it a user of the group can still affect, and so must meet too. -/
  exported : Array Incl
  exportedPlaces : Array (ITy × Nat × ITy)
  exportedCoerces : Array (ITy × ITy × Bool)
  exportedNevers : Array ITy
  exportedOnces : Array (ICls × List ITy)
  exportedShows : Array (ITy × List ITy)

/-- What instantiating a function at a signature gave, kept for a later
compile: the signature and hints of each function of its group (each by its
key), and the uses of other functions it then asked for (each by its key,
with what the use said: the signature, its regions, and the regions it
binds). What a function and the functions it refers to are made of is in its
key, so a later compile that finds the same key at the same signature takes
this instead of working it out. The proved checker checks what comes of it
like anything else. -/
structure Remembered where
  entries : List (UInt64 × FnSig × List (List Hint))
  wanted : List (UInt64 × FnSig × List Nat × Option Nat × List Nat)

/-- A group's scheme, kept for a later compile: its own variables numbered
from `frozenBase`, those of the declarations as they are; how many of each it
has; which of its regions are cells, and which callables bind; what is known
of its records of what callables touch and of what regions stand for; and the
records the program's other groups may still add to. -/
structure Frozen where
  scheme : Scheme
  counts : Nat × Nat × Nat × Nat × Nat
  atoms : List Nat
  ranks : List Nat
  nodes : List (Nat × IAcc)
  lows : List (Nat × List Nat)
  kept : List Nat
  /-- The callables of the group whose regions are decided once what they
  are given is known. -/
  waiting : List (List ITy × List ITy × Nat) := []

/-- What a kept scheme is, to the groups that use it: two that are the same
give the same hash. -/
def Frozen.face (fz : Frozen) : UInt64 :=
  let s := fz.scheme
  let set := fun (h : Std.HashSet Nat) => h.toList.mergeSort (· ≤ ·)
  [hash s.members, hash s.incls, hash s.places, hash s.coerces, hash s.nevers, hash s.onces,
    hash s.shows, hash s.opens, hash s.calls, hash s.givenUpOpen, hash s.exported,
    hash s.exportedPlaces, hash s.exportedCoerces, hash s.exportedNevers, hash s.exportedOnces,
    hash s.exportedShows, hash (set s.fixedTys), hash (set s.fixedRows), hash (set s.fixedClss),
    hash (set s.fixedRgs), hash (set s.fixedAccs), hash fz.counts, hash fz.atoms, hash fz.ranks,
    hash fz.nodes, hash fz.lows, hash fz.kept, hash fz.waiting].foldl mixHash 7

/-- What certificate inference keeps between compiles: instantiations, by
the key of the function and the signature, and groups' schemes, by key. -/
structure Memo where
  inst : Std.HashMap UInt64 (List (FnSig × Remembered)) := {}
  schemes : Std.HashMap UInt64 Frozen := {}
  /-- What each group showed those that use it (`faceOf`), by its key. -/
  faces : Std.HashMap UInt64 UInt64 := {}

def Memo.isEmpty (m : Memo) : Bool := m.inst.isEmpty && m.schemes.isEmpty && m.faces.isEmpty

instance : Nonempty Memo := ⟨{}⟩

/-- What a compile made of that. -/
structure Made where
  inst : Array (UInt64 × FnSig × Remembered) := #[]
  schemes : Array (UInt64 × Frozen) := #[]
  faces : Array (UInt64 × UInt64) := #[]

structure St where
  fns : Array Core.Fn
  /-- The types of numbers written out: a whole number's, or a scalar's, as
  what they are given to says; `Int` where nothing does. -/
  numeric : Std.HashSet Nat := {}
  /-- Counts the changes to what callables touch and to which regions are
  one: what was worked out from them is kept until the next. -/
  accVer : Nat := 0
  /-- The regions each callable may touch (`false`) or write (`true`), as
  worked out when `accVer` was `accMemoAt`. -/
  accMemo : Std.HashMap (Nat × Bool) (List Nat) := {}
  accMemoAt : Nat := 0
  /-- The records of what callables touch that settled groups' own types and
  unsettled questions name: each use of such a group copies them and adds to
  the copy, so what they include is never written into them. -/
  kept : Std.HashSet Nat := {}
  /-- For each function, an identity shared by the functions it is mutually recursive with. -/
  scc : Array Nat := #[]
  /-- How many values each function captures. -/
  ncaps : Array Nat := #[]
  /-- For a function given the environment of a block: how many arguments
  that block took. -/
  givenUp : List (Nat × Nat) := []
  ctors : Array (Option CtorDecl) := #[]
  ops : Array (Option OpDecl) := #[]
  /-- The constructor tags of each declared type. -/
  types : Array (List Nat) := #[]
  tys : Array (Option ITy) := #[]
  rows : Array (Option IRow) := #[]
  clss : Array (Option ICls) := #[]
  rgs : Array (Option IRg) := #[]
  accs : Array IAcc := #[]
  /-- Whether the region rules are to hold. If not, regions are not looked at. -/
  regions : Bool := false
  /-- Whether the rules for borrows are to hold. If not, writing is not told
  from reading, and a lent reference is the reference it was lent from. -/
  loans : Bool := false
  /-- Whether the ownership rules are to hold: a function that captures
  something that cannot be duplicated can then be called only once. -/
  strict : Bool := true
  /-- Counts bindings, so that a pass over the constraints can tell whether it learnt anything. -/
  gen : Nat := 0
  /-- Variables below these belong to declarations. -/
  globalTys : Nat := 0
  globalRows : Nat := 0
  globalClss : Nat := 0
  globalAccs : Nat := 0
  schemes : Std.HashMap Nat Scheme := {}
  /-- The prelude's type of arrays, by its name in this program. -/
  arrayType : Option String := none
  /-- For each declared type, which of its parameters are lifetimes. -/
  typeLifetimes : Array (List Bool) := #[]
  /-- The declared types by name, in the order of their numbers. -/
  typeNames : List String := []
  /-- What each function a program wrote says of its parameters: its type
  parameters, and the written type of each parameter where it is written.
  A function's signature starts from these (`declaredParams`). -/
  declared : Std.HashMap Nat (List String × List (Option TypeExpr)) := {}
  /-- The group being inferred, and the signatures of its functions. -/
  curScc : Option Nat := none
  /-- Callables made where what they are given was not yet known: whether
  each binds the region of a reference it is given is decided once it is. -/
  closureRanks : Array (List ITy × List ITy × Nat) := #[]
  cur : List (Nat × ISig) := []
  incls : Array Incl := #[]
  /-- Field reads whose subject was not yet known: subject, index, field. -/
  places : Array (ITy × Nat × ITy) := #[]
  /-- Calls whose callee's result is not yet known: the result, and what the
  code after the call takes it to be. They are the same type unless the result
  turns out to be `never`. -/
  coerces : Array (ITy × ITy × Bool) := #[]
  /-- Result types of labels: `never`, unless something needs them to be a type. -/
  nevers : Array ITy := #[]
  /-- Callables given up whose type was not yet known: the type, and the
  effects and regions where they were given up. Settled once the function's
  body is read. -/
  cancels : Array (ITy × IRow × Nat × Bool) := #[]
  /-- Of those, the ones whose types the group being inferred left open. -/
  pending : Array (ITy × IRow × Nat) := #[]
  /-- The functions that give up a callable of whatever type they are given:
  how callables are destroyed, and what destroys the captures of a closure.
  What a use gives them is checked of each use. -/
  anyCallable : List Nat := []
  /-- How many arguments the callable a function captured at a place takes,
  where that is known (`captureArities`). -/
  capArities : Std.HashMap (Nat × Nat) Nat := {}
  /-- The functions that are a handler's arms: what they give up without its
  type known is their resumption. -/
  armFns : Std.HashSet Nat := {}
  /-- Functions and what they captured: one that captured something that cannot
  be duplicated can be called only once. -/
  onces : Array (ICls × List ITy) := #[]
  /-- Functions and what they captured: if a function's type comes to state its
  environment, these are the types it states. -/
  shows : Array (ITy × List ITy) := #[]
  /-- Whether a callable may be taken to bind a region: one it is called at a
  reference to a cell with, where nothing else says what it is. -/
  ranked : Bool := false
  /-- The regions callable types bind for whoever calls them: no cells, but
  like cells in that a function inside one that binds such a region has to
  be told which it is. -/
  rankBinders : Std.HashSet Nat := {}
  /-- Calls of such callables: what the callable gives as its type has it,
  what this call gives, the region the type binds and the one the call
  chooses. One is the other with the region changed, whichever is known first. -/
  opens : Array (ITy × ITy × List (Nat × Nat)) := #[]
  /-- Calls of callables not yet known, to be settled when they are. -/
  calls : Array Call := #[]
  /-- The hints of the clause being inferred. -/
  hints : Array IHint := #[]
  /-- The outside functions the function being inferred refers to. -/
  refs : Array (Nat × ISig) := #[]
  /-- Renaming in progress while a scheme is copied. -/
  renTy : Std.HashMap Nat Nat := {}
  renRow : Std.HashMap Nat Nat := {}
  renCls : Std.HashMap Nat Nat := {}
  renRg : Std.HashMap Nat Nat := {}
  renAcc : Std.HashMap Nat Nat := {}
  /-- The signatures given out so far, by function. -/
  emitted : Std.HashMap Nat (List FnSig) := {}
  entries : Array SigEntry := #[]
  /-- Whether an operand whose type is a reference may be used as one of a
  region of more places: one of several cells. -/
  widen : Bool := false
  /-- For a region standing for several places, by what stands for it: the
  regions of the references used as it. -/
  lows : Std.HashMap Nat (List Nat) := {}
  /-- Whether functions are keyed, for what is kept (`groupKeyOf`): what
  each function is made of and what is known of it, each group's functions
  and the groups outside it they refer to, and what the program declares. -/
  keyed : Bool := false
  ownKeys : Array UInt64 := #[]
  members : Std.HashMap Nat (List Nat) := {}
  outside : Std.HashMap Nat (List Nat) := {}
  keyBase : UInt64 := 0
  /-- Groups' keys and what each shows those that use it, once worked out,
  what an earlier compile found each key to show, and the function with each
  key. -/
  groupKeys : Std.HashMap Nat UInt64 := {}
  faces : Std.HashMap Nat UInt64 := {}
  keptFaces : Std.HashMap UInt64 UInt64 := {}
  facesMade : Array (UInt64 × UInt64) := #[]
  byKey : Std.HashMap UInt64 Nat := {}
  /-- What an earlier compile kept, and what this one made. -/
  memo : Std.HashMap UInt64 (List (FnSig × Remembered)) := {}
  made : Array (UInt64 × FnSig × Remembered) := #[]
  /-- Whether what this compile infers is to be kept. -/
  remember : Bool := false
  /-- Groups' schemes an earlier compile kept, by key, and those this one
  made that can be kept. -/
  frozen : Std.HashMap UInt64 Frozen := {}
  frozenMade : Array (UInt64 × Frozen) := #[]

/-- (One result made at each step, not a pair inside an `Except`: most of
inference is small steps. What fails goes back to the state it began
with, `try` as over `Except`: the whole state is what is saved.) -/
abbrev M := EStateM String St

instance {α : Type} : Inhabited (M α) := ⟨throw "certificate: unreachable"⟩

def freshTy : M ITy := do
  -- (in one step: the state is not held twice, so the array is not copied)
  modifyGet fun s => (.var s.tys.size, { s with tys := s.tys.push none })

def freshTys (n : Nat) : M (List ITy) := (List.range n).mapM fun _ => freshTy

def freshRow : M IRow := do
  -- (in one step: the state is not held twice, so the array is not copied)
  modifyGet fun s => (⟨[], some s.rows.size⟩, { s with rows := s.rows.push none })

def freshCls : M ICls := do
  -- (in one step: the state is not held twice, so the array is not copied)
  modifyGet fun s => (.var s.clss.size, { s with clss := s.clss.push none })

/-! ## Regions and what callables touch -/

def freshRg : M Nat := do
  -- (in one step: the state is not held twice, so the array is not copied)
  modifyGet fun s => (s.rgs.size, { s with rgs := s.rgs.push none })

/-- A region that is a cell of its own: no other such region is the same. -/
def freshAtom : M Nat := do
  -- (in one step: the state is not held twice, so the array is not copied)
  modifyGet fun s => (s.rgs.size, { s with rgs := s.rgs.push (some .atom) })

partial def findRg (id : Nat) : M Nat := do
  match (← get).rgs[id]? with
  | some (some (.link j)) => findRg j
  | _ => pure id

def isAtom (root : Nat) : M Bool := do
  match (← get).rgs[root]? with
  | some (some .atom) => pure true
  | _ => pure false

/-- Make two regions the same. Two different cells cannot be: a reference that
may point to one cell or another has no type here. -/
def unifyRg (a b : Nat) : M Unit := do
  unless (← get).regions do return
  let a ← findRg a
  let b ← findRg b
  if a == b then return
  if ← isAtom a then
    if ← isAtom b then
      throw "region: references to two different mutable variables are used as one"
    modify fun s => { s with accVer := s.accVer + 1, rgs := s.rgs.set! b (some (.link a))
                             rankBinders := joined s.rankBinders b a, lows := moved s.lows b a }
  else if ← isAtom b then
    modify fun s => { s with accVer := s.accVer + 1, rgs := s.rgs.set! a (some (.link b))
                             rankBinders := joined s.rankBinders a b, lows := moved s.lows a b }
  else
    let (lo, hi) := if a < b then (a, b) else (b, a)
    modify fun s => { s with accVer := s.accVer + 1, rgs := s.rgs.set! hi (some (.link lo))
                             rankBinders := joined s.rankBinders hi lo, lows := moved s.lows hi lo }
where
  /-- The regions callables bind, once `gone` is the same region as `kept`. -/
  joined (ranked : Std.HashSet Nat) (gone kept : Nat) : Std.HashSet Nat :=
    if ranked.contains gone then ranked.insert kept else ranked
  /-- What is used as `gone` is used as `kept`. -/
  moved (lows : Std.HashMap Nat (List Nat)) (gone kept : Nat) : Std.HashMap Nat (List Nat) :=
    match lows[gone]? with
    | some ls => (lows.erase gone).insert kept (ls ++ (lows[kept]?.getD []))
    | none => lows

/-- The places a region stands for: itself if it is a cell's or one a callable
type binds, or nothing is used as it; otherwise the places of what is used as
it, a reference to one of several cells. -/
partial def leavesOf (ρ : Nat) (seen : List Nat := []) : M (List Nat) := do
  let r ← findRg ρ
  if seen.contains r then return []
  if (← isAtom r) || (← get).rankBinders.contains r then return [r]
  match (← get).lows[r]? with
  | some ls =>
    let mut out : List Nat := []
    for l in ls do
      for x in ← leavesOf l (r :: seen) do
        unless out.contains x do out := out ++ [x]
    pure (if out.isEmpty then [r] else out)
  | none => pure [r]


def freshAcc : M Nat := do
  -- (in one step: the state is not held twice, so the array is not copied)
  modifyGet fun s => (s.accs.size, { s with accs := s.accs.push {} })

partial def findAcc (id : Nat) : M Nat := do
  match (← get).accs[id]? with
  | some { link := some j, .. } => findAcc j
  | _ => pure id

def accNode (root : Nat) : M IAcc := do pure ((← get).accs[root]?.getD {})

/-- Make two callables touch the same regions. The older stands for both. -/
def unifyAcc (a b : Nat) : M Unit := do
  unless (← get).regions do return
  let a ← findAcc a
  let b ← findAcc b
  if a == b then return
  let (lo, hi) := if a < b then (a, b) else (b, a)
  let x ← accNode lo
  let y ← accNode hi
  if let (some p, some q) := (x.binder, y.binder) then unifyRg p q
  for (p, q) in x.more.zip y.more do
    unifyRg p q
  modify fun s =>
    { s with
      accVer := s.accVer + 1
      accs := (s.accs.set! lo
        { rgns := x.rgns ++ y.rgns, wrs := x.wrs ++ y.wrs, subs := x.subs ++ y.subs
          binder := x.binder <|> y.binder, more := if x.more.isEmpty then y.more else x.more
          insts := x.insts ++ y.insts }).set!
          hi { link := some lo } }

/-- The callable touches this region. -/
def accRgn (a ρ : Nat) : M Unit := do
  unless (← get).regions do return
  let a ← findAcc a
  let x ← accNode a
  unless x.rgns.contains ρ do
    modify fun s => { s with accVer := s.accVer + 1, accs := s.accs.set! a { x with rgns := ρ :: x.rgns } }

/-- The callable writes this region. -/
def accWr (a ρ : Nat) : M Unit := do
  unless (← get).regions do return
  accRgn a ρ
  unless (← get).loans do return
  let a ← findAcc a
  let x ← accNode a
  unless x.wrs.contains ρ do
    modify fun s => { s with accVer := s.accVer + 1, accs := s.accs.set! a { x with wrs := ρ :: x.wrs } }

/-- The callable touches whatever `b` does, except region `ex` if given. -/
def accSub (a b : Nat) (ex : Option Nat := none) : M Unit := do
  unless (← get).regions do return
  let a ← findAcc a
  let x ← accNode a
  modify fun s => { s with accVer := s.accVer + 1, accs := s.accs.set! a { x with subs := (b, ex) :: x.subs } }

/-- The callable calls one that touches what `sub` does, with `actual` for the
region `bound` that one's type binds. -/
def accInst (a sub : Nat) (chosen : List (Nat × Nat)) : M Unit := do
  unless (← get).regions do return
  let a ← findAcc a
  let x ← accNode a
  modify fun s => { s with accVer := s.accVer + 1, accs := s.accs.set! a { x with insts := (sub, chosen) :: x.insts } }

/-- Every region a callable may touch, or may write: its own and those of
what it includes. What a callable called at a region of the caller's
choosing touches is touched with that region for the one its type binds.

The callables reached are found first, and then each one's regions are
worked out from the others' until nothing more is added: a callable that
calls itself, or two that call each other, are gone round as often as that
takes and no oftener. (Going down every chain of calls separately, as this
did, took a time that grew with the number of chains, which for a handful of
functions that call each other is very many.) -/
def accSolve (writes : Bool) (a : Nat) : M (List Nat) := do
  let a ← findAcc a
  -- (Asked again for every type a certificate writes out: what was worked
  -- out is kept while nothing it was worked out from has changed.)
  if (← get).accMemoAt != (← get).accVer then
    modify fun s => { s with accMemo := {}, accMemoAt := s.accVer }
  if let some known := (← get).accMemo[(a, writes)]? then return known
  -- The callables reached, by what each includes and calls.
  let mut nodes : Array Nat := #[a]
  let mut seen : Std.HashSet Nat := ({} : Std.HashSet Nat).insert a
  let mut at_ := 0
  while at_ < nodes.size do
    let x ← accNode (nodes[at_]!)
    at_ := at_ + 1
    for next in x.subs.map (·.1) ++ x.insts.map (·.1) do
      let n ← findAcc next
      unless seen.contains n do
        seen := seen.insert n
        nodes := nodes.push n
  let mut sets : Std.HashMap Nat (Std.HashSet Nat) := {}
  let mut changed := true
  while changed do
    changed := false
    -- (From the last found back: what is included is mostly found later.)
    for n in nodes.reverse do
      let x ← accNode n
      let mut mine := sets.getD n {}
      let before := mine.size
      for ρ in (if writes then x.wrs else x.rgns) do
        for l in ← leavesOf ρ do
          mine := mine.insert l
      for (b, e) in x.subs do
        let ex ← e.mapM findRg
        for r in (sets.getD (← findAcc b) {}).toList do
          unless ex == some r do mine := mine.insert r
      for (sub, chosen) in x.insts do
        let chosen ← chosen.mapM fun (bound, actual) => do pure (← findRg bound, actual)
        for r in (sets.getD (← findAcc sub) {}).toList do
          match chosen.lookup r with
          | some to =>
            for l in ← leavesOf to do
              mine := mine.insert l
          | none => mine := mine.insert r
      if mine.size != before then
        sets := sets.insert n mine
        changed := true
  -- (Every callable reached was worked out on the way.)
  -- (Taken out of the state first: held twice, the whole map would be
  -- copied at the first insert, each time.)
  let mut memo ← modifyGet fun s => (s.accMemo, { s with accMemo := {} })
  for n in nodes do
    memo := memo.insert (n, writes) (sets.getD n {}).toList
  modify fun s => { s with accMemo := memo }
  pure (sets.getD a {}).toList

/-- Every region a callable may touch. -/
def accSet (a : Nat) : M (List Nat) := accSolve false a

/-- Every region a callable may write. -/
def accWrSet (a : Nat) : M (List Nat) := accSolve true a

/-- A region is one a callable type binds for whoever calls it. -/
def markRank (r : Nat) : M Unit :=
  -- (Kept by what stands for the region: where two are made one, what
  -- stands for both is one if either was. So asking is one look.)
  do
    let root ← findRg r
    modify fun s => { s with rankBinders := s.rankBinders.insert root }

def isRank (r : Nat) : M Bool := do
  pure ((← get).rankBinders.contains (← findRg r))

/-- Every region a callable type binds, the first first. -/
def bindersOf (a : Nat) : M (List Nat) := do
  unless (← get).regions do return []
  let x ← accNode (← findAcc a)
  (x.binder.toList ++ x.more).mapM findRg

/-- The region a callable type binds, if a cell's scope runs it. -/
def binderOf (a : Nat) : M (Option Nat) := do
  unless (← get).regions do return none
  match (← accNode (← findAcc a)).binder with
  | some ρ => some <$> findRg ρ
  | none => pure none

partial def findCls (c : ICls) : M ICls := do
  match c with
  | .var id =>
    match (← get).clss[id]? with
    | some (some c') => findCls c'
    | _ => pure c
  | .lit _ => pure c

def unifyCls (a b : ICls) : M Unit := do
  match ← findCls a, ← findCls b with
  | .var i, .var j =>
    unless i == j do
      modify fun s => { s with clss := s.clss.set! i (some (.var j)), gen := s.gen + 1 }
  | .var i, c => modify fun s => { s with clss := s.clss.set! i (some c), gen := s.gen + 1 }
  | c, .var j => modify fun s => { s with clss := s.clss.set! j (some c), gen := s.gen + 1 }
  | .lit x, .lit y =>
    unless x == y do
      throw "a callable that can be called only once is used where it may be called again"

partial def find (t : ITy) : M ITy := do
  match t with
  | .var id =>
    match (← get).tys[id]? with
    | some (some t') => find t'
    | _ => pure t
  | _ => pure t

partial def flattenRow (r : IRow) : M IRow := do
  match r.tail with
  | none => pure r
  | some id =>
    match (← get).rows[id]? with
    | some (some r') => do
      let rest ← flattenRow r'
      pure ⟨r.ops ++ rest.ops, rest.tail⟩
    | _ => pure r

/-- The types directly in a type, a callable's operations as its row now is. -/
def partsOf : ITy → M (List ITy)
  | t@(.fn _ _ _ tail ..) => do pure (t.parts ++ (← flattenRow ⟨[], tail⟩).ops.flatMap (·.2))
  | t => pure t.parts

partial def occurs (id : Nat) (t : ITy) : M Bool := do
  match ← find t with
  | .var j => pure (id == j)
  | t => (← partsOf t).anyM (occurs id)

partial def showTy (t : ITy) : M String := do
  match ← find t with
  | .var id => pure s!"?{id}"
  | .param i => pure s!"'{i}"
  | .int => pure "Int"
  | .scalar b => pure s!"scalar{b}"
  | .tuple fs => do pure s!"({", ".intercalate (← fs.mapM showTy)})"
  | .data n args => do pure s!"#{n}<{", ".intercalate (← args.mapM showTy)}>"
  | .fn ps r ops tail _ _ _ => do
    let row ← flattenRow ⟨ops, tail⟩
    let shown := row.ops.map fun (op, _) => toString op
    let open_ := if row.tail.isSome then ["…"] else []
    pure s!"fn({", ".intercalate (← ps.mapM showTy)}) -> {← showTy r} / \{{", ".intercalate (shown ++ open_)}}"
  | .ref _ t => do pure s!"&{← showTy t}"
  | .never => pure "!"

def bindTy (id : Nat) (t : ITy) : M Unit := do
  if ← occurs id t then throw s!"a type would contain itself: ?{id} in {← showTy t}"
  modify fun s => { s with tys := s.tys.set! id (some t), gen := s.gen + 1 }
  -- (A number written out is still one where its type is another unknown.)
  if let .var j := t then
    if (← get).numeric.contains id then modify fun s => { s with numeric := s.numeric.insert j }

def bindRow (id : Nat) (r : IRow) : M Unit :=
  modify fun s => { s with rows := s.rows.set! id (some r), gen := s.gen + 1 }

mutual

partial def unify (a b : ITy) : M Unit := do
  let a ← find a
  let b ← find b
  match a, b with
  | .var i, .var j => if i == j then pure () else bindTy i b
  | .var i, t => bindTy i t
  | t, .var j => bindTy j t
  | .param i, .param j =>
    unless i == j do throw "two different type parameters do not match"
  | .int, .int => pure ()
  | .scalar a, .scalar b => unless a == b do throw s!"scalar{a} does not match scalar{b}"
  | .tuple as, .tuple bs => unifyList as bs
  | .data n as, .data m bs =>
    if n == m then unifyList as bs
    else throw s!"{← showTy a} does not match {← showTy b}"
  | .fn ps r ops tail cls env acc, .fn ps' r' ops' tail' cls' env' acc' => do
    unifyList ps ps'
    unify r r'
    unifyRow ⟨ops, tail⟩ ⟨ops', tail'⟩
    unifyCls cls cls'
    unify env env'
    unifyAcc acc acc'
  | .ref ρ x, .ref ρ' y => do
    unifyRg ρ ρ'
    unify x y
  | .never, .never => pure ()
  | _, _ => throw s!"{← showTy a} does not match {← showTy b}"

partial def unifyList (as bs : List ITy) : M Unit := do
  unless as.length == bs.length do
    throw s!"{as.length} types do not match {bs.length}"
  for (x, y) in as.zip bs do
    unify x y

/-- Make two rows the same: each gets the other's operations, and the same tail. -/
partial def unifyRow (a b : IRow) : M Unit := do
  let a ← flattenRow a
  let b ← flattenRow b
  let mut onlyA : IOps := []
  for (op, targs) in a.ops do
    match b.ops.lookup op with
    | some targs' => unifyList targs targs'
    | none => onlyA := onlyA ++ [(op, targs)]
  let onlyB := b.ops.filter fun (op, _) => (a.ops.lookup op).isNone
  match a.tail, b.tail with
  | none, none =>
    unless onlyA.isEmpty && onlyB.isEmpty do
      throw "two closed sets of operations differ"
  | some va, none =>
    unless onlyA.isEmpty do throw "a closed set of operations lacks an operation"
    bindRow va ⟨onlyB, none⟩
  | none, some vb =>
    unless onlyB.isEmpty do throw "a closed set of operations lacks an operation"
    bindRow vb ⟨onlyA, none⟩
  | some va, some vb =>
    if va == vb then
      unless onlyA.isEmpty && onlyB.isEmpty do
        throw "a set of operations would contain itself"
    else if onlyA.isEmpty && onlyB.isEmpty then bindRow va ⟨[], some vb⟩
    else
      let rest ← freshRow
      bindRow va ⟨onlyB, rest.tail⟩
      bindRow vb ⟨onlyA, rest.tail⟩

end

/-- The row must serve `op` at these type arguments: it does already, or it is
open and now does. -/
def requireOp (r : IRow) (op : Nat) (targs : List ITy) : M Unit := do
  let r ← flattenRow r
  match r.ops.lookup op with
  | some targs' => unifyList targs targs'
  | none =>
    match r.tail with
    | some v =>
      let rest ← freshRow
      bindRow v ⟨[(op, targs)], rest.tail⟩
    | none => throw s!"operation {op} is performed where nothing handles it"

/-- Replace a declaration's type parameters by arguments. -/
partial def subst (args : List ITy) : ITy → ITy
  | .param i => args[i]?.getD (.param i)
  | .ref ρ t =>
    -- The region of a lifetime parameter is its argument's.
    if lifetimeBase ≤ ρ then
      match args[ρ - lifetimeBase]? with
      | some (.ref ρ' _) => .ref ρ' (subst args t)
      | _ => .ref ρ (subst args t)
    else .ref ρ (subst args t)
  | t => Id.run (t.mapM (pure ∘ subst args))

def ctorDecl (tag : Nat) : M CtorDecl := do
  match (← get).ctors[tag]? with
  | some (some d) => pure d
  | _ => throw s!"constructor {tag} has no declaration"

def opDecl (op : Nat) : M OpDecl := do
  match (← get).ops[op]? with
  | some (some d) => pure d
  | _ => throw s!"operation {op} has no declaration"

/-- Arguments not yet known for a declaration's parameters: a type for each,
and for a lifetime a type that carries a region. -/
def argsFor (arity : Nat) (lifetimes : List Bool) : M (List ITy) :=
  (List.range arity).mapM fun i => do
    if lifetimes.getD i false then pure (.ref (← freshRg) (.tuple [])) else freshTy

/-- The type a constructor builds and its field types, at fresh type arguments. -/
def instCtor (tag : Nat) : M (ITy × List ITy) := do
  -- The constructor that builds an array of so many elements.
  if arrayBase ≤ tag then
    let t ← freshTy
    return (.data arrayName [t], List.replicate (tag - arrayBase) t)
  let d ← ctorDecl tag
  let args ← argsFor d.arity d.lifetimes
  pure (.data d.owner args, d.fields.map (subst args))

/-- An operation at type arguments: those arguments, what it takes, and what it
is resumed with. Operations of one effect met in the same place share the
effect's type arguments. -/
def instOp (shared : List (Nat × List ITy)) (op : Nat) :
    M ((List ITy × List ITy × Option ITy) × List (Nat × List ITy)) := do
  let d ← opDecl op
  let (args, shared) ← match shared.lookup d.effect with
    | some args => pure (args, shared)
    | none => do
      let args ← argsFor d.arity d.lifetimes
      pure (args, (d.effect, args) :: shared)
  pure ((args, d.payload.map (subst args), d.result.map (subst args)), shared)

/-- The type of field `i` of a value of type `t`, if `t` is known well enough. -/
def fieldNow (t : ITy) (i : Nat) : M (Option ITy) := do
  match ← find t with
  | .tuple fs =>
    match fs[i]? with
    | some f => pure (some f)
    | none => throw s!"a tuple of {fs.length} has no field {i}"
  | .data name args =>
    match (← get).types[name]? with
    | some [tag] =>
      let d ← ctorDecl tag
      match d.fields[i]? with
      | some f => pure (some (subst args f))
      | none => throw s!"type {name} has no field {i}"
    | _ => throw s!"a field is read from type {name}, which does not have exactly one constructor"
  | .var _ => pure none
  | t => throw s!"a field is read from {← showTy t}"

def field (t : ITy) (i : Nat) : M ITy := do
  match ← fieldNow t i with
  | some f => pure f
  | none =>
    let r ← freshTy
    modify fun s => { s with places := s.places.push (t, i, r) }
    pure r

def atomTy (Γ : Array ITy) : Atom → M ITy
  | .var i =>
    match Γ[i]? with
    | some t => pure t
    | none => throw s!"local {i} does not exist"
  | .int _ => pure .int

def hint (h : IHint) : M Unit := modify fun s => { s with hints := s.hints.push h }

/-- A call gives back an `r` and the code after it expects a `b`: the same type,
unless the call does not return. Decided now if `r` is known. -/
def coerce (r b : ITy) (widen : Bool := false) : M Unit := do
  match ← find r with
  | .never => pure ()
  | .var v =>
    -- Already the same unknown: nothing is left to decide.
    if let .var w ← find b then
      if v == w then return
    modify fun s => { s with coerces := s.coerces.push (r, b, widen) }
  -- (An operand used where a reference of a region of more places is
  -- wanted: what it is used as is one of the places of that.)
  | .ref ρ s =>
    if widen && (← get).widen && (← get).regions then
      let u ← freshRg
      modify fun st => { st with lows := st.lows.insert u [ρ] }
      unify b (.ref u s)
    else unify r b
  | _ => unify r b

/-- An operand's type as it is used where a type is wanted: a reference may be
used as one of a region of more places. -/
def widenTy (t : ITy) : M ITy := do
  unless (← get).widen && (← get).regions do return t
  -- (A number written out is no callable to widen.)
  if let .var id ← find t then
    if (← get).numeric.contains id then return t
  let b ← freshTy
  coerce t b (widen := true)
  pure b

def needs (sub : IRow) (under : IOps) (sup : IRow) : M Unit :=
  modify fun s => { s with incls := s.incls.push ⟨sub, under, sup⟩ }

mutual

/-- The types a pattern binds from a value of type `t`. -/
partial def inferPat (p : Core.Pat) (t : ITy) : M (List ITy) := do
  match p with
  | .wild => pure []
  | .bind => pure [t]
  | .int _ => do
    -- (A number is a pattern of a scalar too, `5u8`: of a type not known yet,
    -- a number's.)
    match ← find t with
    | .scalar _ => pure ()
    | .var id => modify fun s => { s with numeric := s.numeric.insert id }
    | _ => unify t .int
    pure []
  | .ctor tag ps =>
    if tag == 0 then
      let fs ← freshTys ps.length
      unify t (.tuple fs)
      inferPats ps fs
    else
      let (result, fields) ← instCtor tag
      unify t result
      unless fields.length == ps.length do
        throw s!"a pattern for constructor {tag} has {ps.length} fields"
      inferPats ps fields

partial def inferPats (ps : List Core.Pat) (ts : List ITy) : M (List ITy) := do
  let mut out : List ITy := []
  for (p, t) in ps.zip ts do
    out := out ++ (← inferPat p t)
  pure out

end

end Glorious.Infer
