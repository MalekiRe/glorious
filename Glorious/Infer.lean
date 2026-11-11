import Std.Data.HashMap
import Std.Data.HashSet
import Glorious.Syntax.Ast
import Glorious.Elab
import Glorious.Typing.Certify

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

namespace Glorious.Infer

open Syntax
open Glorious.Typing (Ty FnSig Hint Cert SigEntry DataInst OpInst)

/-- Whether a callable can be called only once, while that is being inferred. -/
inductive ICls where
  | var (id : Nat)
  | lit (once : Bool)
  deriving Inhabited

/-- A type while it is being inferred. -/
inductive ITy where
  /-- Not yet known. -/
  | var (id : Nat)
  /-- A type parameter of the declaration this type was written in. -/
  | param (i : Nat)
  | int
  | tuple (fs : List ITy)
  | data (name : Nat) (args : List ITy)
  /-- A callable; its operations, each with the type arguments of its effect,
  and a variable for any others if the row is open. `env` is a tuple of what it
  captured if its type is to state that, `never` if it cannot, and otherwise
  not yet known. -/
  | fn (ps : List ITy) (ret : ITy) (ops : List (Nat × List ITy)) (tail : Option Nat) (cls : ICls)
      (env : ITy)
  | ref (t : ITy)
  /-- The result of a call that does not return. -/
  | never
  deriving Inhabited

abbrev IOps := List (Nat × List ITy)

structure IRow where
  ops : IOps
  tail : Option Nat
  deriving Inhabited

def ITy.unit : ITy := .tuple []

def ITy.func (ps : List ITy) (ret : ITy) (row : IRow) (cls : ICls) (env : ITy) : ITy :=
  .fn ps ret row.ops row.tail cls env

inductive IHint where
  | ty (t : ITy)
  | handler (ρ : ITy) (H : IOps)
  /-- A call: what the callee gives back, and what the code after it takes the
  result to be. The checker is told the second only if the first is `never`. -/
  | result (r b : ITy)

structure CtorDecl where
  owner : Nat
  arity : Nat
  fields : List ITy

structure OpDecl where
  effect : Nat
  arity : Nat
  payload : List ITy
  result : Option ITy

/-- A function's signature while it is being inferred. -/
structure ISig where
  caps : List ITy
  params : List ITy
  ret : ITy
  row : IRow
  deriving Inhabited

/-- Every operation of `sub` must be served at the same type: by `under` if it
lists the operation, and by `sup` otherwise. -/
structure Incl where
  sub : IRow
  under : IOps
  sup : IRow

/-- A function of an inferred group: its signature, the hints of each clause,
and the functions outside the group it refers to, each at the type it uses. -/
structure Member where
  fn : Nat
  sig : ISig
  hints : Array (Array IHint)
  refs : Array (Nat × ISig)

/-- The general type of a group of mutually recursive functions. Variables made
while the group was inferred stand for anything, except those in `fixed`, which
declarations share with the rest of the program. -/
structure Scheme where
  startTy : Nat
  startRow : Nat
  startCls : Nat
  fixedTys : Std.HashSet Nat
  fixedRows : Std.HashSet Nat
  fixedClss : Std.HashSet Nat
  members : List Member
  /-- Everything the group's own typing depends on. -/
  incls : Array Incl
  places : Array (ITy × Nat × ITy)
  coerces : Array (ITy × ITy)
  nevers : Array ITy
  onces : Array (ICls × List ITy)
  shows : Array (ITy × List ITy)
  /-- The part of it a user of the group can still affect, and so must meet too. -/
  exported : Array Incl
  exportedPlaces : Array (ITy × Nat × ITy)
  exportedCoerces : Array (ITy × ITy)
  exportedNevers : Array ITy
  exportedOnces : Array (ICls × List ITy)
  exportedShows : Array (ITy × List ITy)

structure St where
  fns : Array Core.Fn
  /-- For each function, an identity shared by the functions it is mutually recursive with. -/
  scc : Array Nat := #[]
  /-- How many values each function captures. -/
  ncaps : Array Nat := #[]
  ctors : Array (Option CtorDecl) := #[]
  ops : Array (Option OpDecl) := #[]
  /-- The constructor tags of each declared type. -/
  types : Array (List Nat) := #[]
  tys : Array (Option ITy) := #[]
  rows : Array (Option IRow) := #[]
  clss : Array (Option ICls) := #[]
  /-- Whether the ownership rules are to hold: a function that captures
  something that cannot be duplicated can then be called only once. -/
  strict : Bool := true
  /-- Counts bindings, so that a pass over the constraints can tell whether it learnt anything. -/
  gen : Nat := 0
  /-- Variables below these belong to declarations. -/
  globalTys : Nat := 0
  globalRows : Nat := 0
  globalClss : Nat := 0
  schemes : Std.HashMap Nat Scheme := {}
  /-- The group being inferred, and the signatures of its functions. -/
  curScc : Option Nat := none
  cur : List (Nat × ISig) := []
  incls : Array Incl := #[]
  /-- Field reads whose subject was not yet known: subject, index, field. -/
  places : Array (ITy × Nat × ITy) := #[]
  /-- Calls whose callee's result is not yet known: the result, and what the
  code after the call takes it to be. They are the same type unless the result
  turns out to be `never`. -/
  coerces : Array (ITy × ITy) := #[]
  /-- Result types of labels: `never`, unless something needs them to be a type. -/
  nevers : Array ITy := #[]
  /-- Functions and what they captured: one that captured something that cannot
  be duplicated can be called only once. -/
  onces : Array (ICls × List ITy) := #[]
  /-- Functions and what they captured: if a function's type comes to state its
  environment, these are the types it states. -/
  shows : Array (ITy × List ITy) := #[]
  /-- The hints of the clause being inferred. -/
  hints : Array IHint := #[]
  /-- The outside functions the function being inferred refers to. -/
  refs : Array (Nat × ISig) := #[]
  /-- Renaming in progress while a scheme is copied. -/
  renTy : Std.HashMap Nat Nat := {}
  renRow : Std.HashMap Nat Nat := {}
  renCls : Std.HashMap Nat Nat := {}
  /-- The signatures given out so far, by function. -/
  emitted : Std.HashMap Nat (List FnSig) := {}
  entries : Array SigEntry := #[]

abbrev M := StateT St (Except String)

instance {α : Type} : Inhabited (M α) := ⟨throw "certificate: unreachable"⟩

def freshTy : M ITy := do
  let s ← get
  set { s with tys := s.tys.push none }
  pure (.var s.tys.size)

def freshTys (n : Nat) : M (List ITy) := (List.range n).mapM fun _ => freshTy

def freshRow : M IRow := do
  let s ← get
  set { s with rows := s.rows.push none }
  pure ⟨[], some s.rows.size⟩

def freshCls : M ICls := do
  let s ← get
  set { s with clss := s.clss.push none }
  pure (.var s.clss.size)

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

partial def occurs (id : Nat) (t : ITy) : M Bool := do
  match ← find t with
  | .var j => pure (id == j)
  | .param _ => pure false
  | .int => pure false
  | .tuple fs => fs.anyM (occurs id)
  | .data _ args => args.anyM (occurs id)
  | .fn ps r ops tail _ env => do
    if ← ps.anyM (occurs id) then return true
    if ← occurs id r then return true
    if ← occurs id env then return true
    let row ← flattenRow ⟨ops, tail⟩
    row.ops.anyM fun (_, targs) => targs.anyM (occurs id)
  | .ref t => occurs id t
  | .never => pure false

partial def showTy (t : ITy) : M String := do
  match ← find t with
  | .var id => pure s!"?{id}"
  | .param i => pure s!"'{i}"
  | .int => pure "Int"
  | .tuple fs => do pure s!"({", ".intercalate (← fs.mapM showTy)})"
  | .data n args => do pure s!"#{n}<{", ".intercalate (← args.mapM showTy)}>"
  | .fn ps r ops tail _ _ => do
    let row ← flattenRow ⟨ops, tail⟩
    let shown := row.ops.map fun (op, _) => toString op
    let open_ := if row.tail.isSome then ["…"] else []
    pure s!"fn({", ".intercalate (← ps.mapM showTy)}) -> {← showTy r} / \{{", ".intercalate (shown ++ open_)}}"
  | .ref t => do pure s!"&{← showTy t}"
  | .never => pure "!"

def bindTy (id : Nat) (t : ITy) : M Unit := do
  if ← occurs id t then throw s!"a type would contain itself: ?{id} in {← showTy t}"
  modify fun s => { s with tys := s.tys.set! id (some t), gen := s.gen + 1 }

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
  | .tuple as, .tuple bs => unifyList as bs
  | .data n as, .data m bs =>
    if n == m then unifyList as bs
    else throw s!"{← showTy a} does not match {← showTy b}"
  | .fn ps r ops tail cls env, .fn ps' r' ops' tail' cls' env' => do
    unifyList ps ps'
    unify r r'
    unifyRow ⟨ops, tail⟩ ⟨ops', tail'⟩
    unifyCls cls cls'
    unify env env'
  | .ref x, .ref y => unify x y
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
  | .var id => .var id
  | .param i => args[i]?.getD (.param i)
  | .int => .int
  | .tuple fs => .tuple (fs.map (subst args))
  | .data n as => .data n (as.map (subst args))
  | .fn ps r ops tail cls env =>
    .fn (ps.map (subst args)) (subst args r)
      (ops.map fun (op, targs) => (op, targs.map (subst args))) tail cls (subst args env)
  | .ref t => .ref (subst args t)
  | .never => .never

def ctorDecl (tag : Nat) : M CtorDecl := do
  match (← get).ctors[tag]? with
  | some (some d) => pure d
  | _ => throw s!"constructor {tag} has no declaration"

def opDecl (op : Nat) : M OpDecl := do
  match (← get).ops[op]? with
  | some (some d) => pure d
  | _ => throw s!"operation {op} has no declaration"

/-- The type a constructor builds and its field types, at fresh type arguments. -/
def instCtor (tag : Nat) : M (ITy × List ITy) := do
  let d ← ctorDecl tag
  let args ← freshTys d.arity
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
      let args ← freshTys d.arity
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
def coerce (r b : ITy) : M Unit := do
  match ← find r with
  | .never => pure ()
  | .var v =>
    -- Already the same unknown: nothing is left to decide.
    if let .var w ← find b then
      if v == w then return
    modify fun s => { s with coerces := s.coerces.push (r, b) }
  | _ => unify r b

def needs (sub : IRow) (under : IOps) (sup : IRow) : M Unit :=
  modify fun s => { s with incls := s.incls.push ⟨sub, under, sup⟩ }

mutual

/-- The types a pattern binds from a value of type `t`. -/
partial def inferPat (p : Core.Pat) (t : ITy) : M (List ITy) := do
  match p with
  | .wild => pure []
  | .bind => pure [t]
  | .int _ => do
    unify t .int
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

/-! ## General types of groups -/

/-- A type with everything known about it written out. -/
partial def resolve (t : ITy) : M ITy := do
  match ← find t with
  | .var id => pure (.var id)
  | .param i => pure (.param i)
  | .int => pure .int
  | .tuple fs => do pure (.tuple (← fs.mapM resolve))
  | .data n args => do pure (.data n (← args.mapM resolve))
  | .fn ps r ops tail cls env => do
    let row ← flattenRow ⟨ops, tail⟩
    let ops ← row.ops.mapM fun (op, targs) => do pure (op, ← targs.mapM resolve)
    pure (.fn (← ps.mapM resolve) (← resolve r) ops row.tail (← findCls cls) (← resolve env))
  | .ref t => do pure (.ref (← resolve t))
  | .never => pure .never

def resolveRow (r : IRow) : M IRow := do
  let r ← flattenRow r
  pure ⟨← r.ops.mapM fun (op, targs) => do pure (op, ← targs.mapM resolve), r.tail⟩

def resolveSig (s : ISig) : M ISig := do
  pure ⟨← s.caps.mapM resolve, ← s.params.mapM resolve, ← resolve s.ret, ← resolveRow s.row⟩

def resolveIncl (c : Incl) : M Incl := do
  pure ⟨← resolveRow c.sub, ← c.under.mapM fun (op, targs) => do pure (op, ← targs.mapM resolve),
    ← resolveRow c.sup⟩

def resolveHint : IHint → M IHint
  | .ty t => do pure (.ty (← resolve t))
  | .handler ρ H => do
    pure (.handler (← resolve ρ) (← H.mapM fun (op, targs) => do pure (op, ← targs.mapM resolve)))
  | .result r b => do pure (.result (← resolve r) (← resolve b))

/-- The variables of a resolved type: of types, of rows and of classes. -/
structure Vars where
  tys : Std.HashSet Nat := {}
  rows : Std.HashSet Nat := {}
  clss : Std.HashSet Nat := {}

def Vars.size (v : Vars) : Nat := v.tys.size + v.rows.size + v.clss.size

partial def varsOf (t : ITy) (acc : Vars) : Vars :=
  match t with
  | .var id => { acc with tys := acc.tys.insert id }
  | .param _ => acc
  | .int => acc
  | .tuple fs => fs.foldl (fun a f => varsOf f a) acc
  | .data _ args => args.foldl (fun a f => varsOf f a) acc
  | .fn ps r ops tail cls env =>
    let acc := ps.foldl (fun a f => varsOf f a) acc
    let acc := varsOf r acc
    let acc := varsOf env acc
    let acc := ops.foldl (fun a e => e.2.foldl (fun a f => varsOf f a) a) acc
    let acc := match tail with
      | some v => { acc with rows := acc.rows.insert v }
      | none => acc
    match cls with
    | .var c => { acc with clss := acc.clss.insert c }
    | .lit _ => acc
  | .ref t => varsOf t acc
  | .never => acc

def varsOfRow (r : IRow) (acc : Vars) : Vars :=
  varsOf (.fn [] .int r.ops r.tail (.lit false) .never) acc

def varsOfSig (s : ISig) (acc : Vars) : Vars :=
  varsOf (.fn (s.caps ++ s.params) s.ret s.row.ops s.row.tail (.lit false) .never) acc

/-- Does a type mention a variable in the set? -/
def Vars.touches (live : Vars) (t : ITy) : Bool :=
  let v := varsOf t {}
  v.tys.toList.any live.tys.contains || v.rows.toList.any live.rows.contains
    || v.clss.toList.any live.clss.contains

def copyCls (sch : Scheme) (c : ICls) : M ICls := do
  match c with
  | .lit _ => pure c
  | .var id =>
    if id < sch.startCls || sch.fixedClss.contains id then pure c
    else
      match (← get).renCls[id]? with
      | some id' => pure (.var id')
      | none =>
        match ← freshCls with
        | .var id' =>
          modify fun s => { s with renCls := s.renCls.insert id id' }
          pure (.var id')
        | c' => pure c'

mutual

/-- A copy of a scheme's type with its general variables renamed. -/
partial def copyTy (sch : Scheme) (t : ITy) : M ITy := do
  match t with
  | .var id =>
    if id < sch.startTy || sch.fixedTys.contains id then pure t
    else
      match (← get).renTy[id]? with
      | some id' => pure (.var id')
      | none =>
        match ← freshTy with
        | .var id' =>
          modify fun s => { s with renTy := s.renTy.insert id id' }
          pure (.var id')
        | t' => pure t'
  | .param i => pure (.param i)
  | .int => pure .int
  | .tuple fs => do pure (.tuple (← fs.mapM (copyTy sch)))
  | .data n args => do pure (.data n (← args.mapM (copyTy sch)))
  | .fn ps r ops tail cls env => do
    let row ← copyRow sch ⟨ops, tail⟩
    pure (.fn (← ps.mapM (copyTy sch)) (← copyTy sch r) row.ops row.tail (← copyCls sch cls)
      (← copyTy sch env))
  | .ref t => do pure (.ref (← copyTy sch t))
  | .never => pure .never

partial def copyRow (sch : Scheme) (r : IRow) : M IRow := do
  let ops ← r.ops.mapM fun (op, targs) => do pure (op, ← targs.mapM (copyTy sch))
  match r.tail with
  | none => pure ⟨ops, none⟩
  | some v =>
    if v < sch.startRow || sch.fixedRows.contains v then pure ⟨ops, some v⟩
    else
      match (← get).renRow[v]? with
      | some v' => pure ⟨ops, some v'⟩
      | none =>
        let fresh ← freshRow
        match fresh.tail with
        | some v' =>
          modify fun s => { s with renRow := s.renRow.insert v v' }
          pure ⟨ops, some v'⟩
        | none => pure ⟨ops, none⟩

end

def copySig (sch : Scheme) (s : ISig) : M ISig := do
  pure ⟨← s.caps.mapM (copyTy sch), ← s.params.mapM (copyTy sch), ← copyTy sch s.ret,
    ← copyRow sch s.row⟩

def copyIncl (sch : Scheme) (c : Incl) : M Incl := do
  pure ⟨← copyRow sch c.sub, (← copyRow sch ⟨c.under, none⟩).ops, ← copyRow sch c.sup⟩

def copyPlace (sch : Scheme) (p : ITy × Nat × ITy) : M (ITy × Nat × ITy) := do
  pure (← copyTy sch p.1, p.2.1, ← copyTy sch p.2.2)

def copyHint (sch : Scheme) : IHint → M IHint
  | .ty t => do pure (.ty (← copyTy sch t))
  | .handler ρ H => do pure (.handler (← copyTy sch ρ) (← copyRow sch ⟨H, none⟩).ops)
  | .result r b => do pure (.result (← copyTy sch r) (← copyTy sch b))

def startCopy : M Unit := modify fun s => { s with renTy := {}, renRow := {}, renCls := {} }

def copyOnce (sch : Scheme) (o : ICls × List ITy) : M (ICls × List ITy) := do
  pure (← copyCls sch o.1, ← o.2.mapM (copyTy sch))

def copyShow (sch : Scheme) (o : ITy × List ITy) : M (ITy × List ITy) := do
  pure (← copyTy sch o.1, ← o.2.mapM (copyTy sch))

/-- Is this type known to hold something that cannot be duplicated? -/
partial def nonDup (seen : List Nat) (t : ITy) : M Bool := do
  match ← find t with
  | .var _ => pure false
  | .param _ => pure false
  | .int => pure false
  | .tuple fs => fs.anyM (nonDup seen)
  | .data name args =>
    if seen.contains name then pure false
    else
      let tags := (← get).types[name]?.getD []
      tags.anyM fun tag => do
        let d ← ctorDecl tag
        d.fields.anyM fun f => nonDup (name :: seen) (subst args f)
  | .fn _ _ _ _ cls _ => do
    match ← findCls cls with
    | .lit once => pure once
    | .var _ => pure false
  | .ref _ => pure false
  | .never => pure false

/-- Enforce the inclusions and the field reads until nothing more is learnt. -/
partial def settle : M Unit := do
  let before := (← get).gen
  for c in (← get).incls do
    let sub ← flattenRow c.sub
    for (op, targs) in sub.ops do
      match c.under.lookup op with
      | some targs' => unifyList targs targs'
      | none => requireOp c.sup op targs
  let waiting := (← get).places
  modify fun s => { s with places := #[] }
  for (t, i, r) in waiting do
    match ← fieldNow t i with
    | some f => unify f r
    | none => modify fun s => { s with places := s.places.push (t, i, r) }
  let pending := (← get).coerces
  modify fun s => { s with coerces := #[] }
  for (r, b) in pending do
    coerce r b
  let waitingOnce := (← get).onces
  modify fun s => { s with onces := #[] }
  for (c, tys) in waitingOnce do
    if ← tys.anyM (nonDup []) then unifyCls c (.lit true)
    else modify fun s => { s with onces := s.onces.push (c, tys) }
  let waitingShow := (← get).shows
  modify fun s => { s with shows := #[] }
  for (env, caps) in waitingShow do
    match ← find env with
    | .var _ => modify fun s => { s with shows := s.shows.push (env, caps) }
    | .tuple stated => unifyList stated caps
    | _ => pure ()
  if (← get).gen != before then settle

mutual

/-- The general type of the group of `fn`, inferring the group if this is its first use. -/
partial def schemeOf (scc : Nat) : M Scheme := do
  if let some sch := (← get).schemes[scc]? then return sch
  let outer ← get
  let startTy := outer.tys.size
  let startRow := outer.rows.size
  let startCls := outer.clss.size
  let fns := (List.range outer.fns.size).filter fun f => outer.scc[f]?.getD f == scc
  -- A signature for each function of the group, before any body is looked at.
  let mut cur : List (Nat × ISig) := []
  for f in fns do
    let arity := match outer.fns[f]? with
      | some ⟨c :: _⟩ => c.pats.length
      | _ => 0
    let sig : ISig :=
      ⟨← freshTys (outer.ncaps[f]?.getD 0), ← freshTys arity, ← freshTy, ← freshRow⟩
    cur := cur ++ [(f, sig)]
  modify fun s =>
    { s with
      curScc := some scc, cur := cur, incls := #[], places := #[], coerces := #[], nevers := #[]
      onces := #[], shows := #[] }
  let mut raw : List Member := []
  for (f, sig) in cur do
    let F := (outer.fns[f]?).getD ⟨[]⟩
    modify fun s => { s with refs := #[] }
    let mut hints : Array (Array IHint) := #[]
    for c in F.clauses do
      modify fun s => { s with hints := #[] }
      unless c.pats.length == sig.params.length do
        throw s!"the clauses of function {f} take different numbers of arguments"
      let binds ← inferPats c.pats sig.params
      inferTm sig.row sig.ret (sig.params ++ sig.caps ++ binds).toArray c.body
      hints := hints.push (← get).hints
    raw := raw ++ [⟨f, sig, hints, (← get).refs⟩]
  settle
  -- Write out what was learnt, and separate what is general from what is shared.
  let members ← raw.mapM fun m => do
    pure { m with
      sig := ← resolveSig m.sig
      hints := ← m.hints.mapM fun hs => hs.mapM resolveHint
      refs := ← m.refs.mapM fun (g, s) => do pure (g, ← resolveSig s) }
  let incls ← (← get).incls.mapM resolveIncl
  let places ← (← get).places.mapM fun (t, i, r) => do pure (← resolve t, i, ← resolve r)
  let coerces ← (← get).coerces.mapM fun (r, b) => do pure (← resolve r, ← resolve b)
  let nevers ← (← get).nevers.mapM resolve
  let onces ← (← get).onces.mapM fun (c, tys) => do pure (← findCls c, ← tys.mapM resolve)
  let shows ← (← get).shows.mapM fun (env, caps) => do pure (← resolve env, ← caps.mapM resolve)
  let s ← get
  let mut fixed : Vars := {}
  for g in [0:s.globalTys] do
    fixed := varsOf (← resolve (.var g)) fixed
  for g in [0:s.globalRows] do
    fixed := varsOfRow (← resolveRow ⟨[], some g⟩) fixed
  for g in [0:s.globalClss] do
    if let .var c ← findCls (.var g) then fixed := { fixed with clss := fixed.clss.insert c }
  -- A variable can still be bound if a user can reach it, or if something that
  -- can still change decides it.
  let liveTy (live : Vars) (t : ITy) : Bool :=
    match t with
    | .var v => v < s.globalTys || live.tys.contains v
    | _ => false
  let liveRow (live : Vars) (r : IRow) : Bool :=
    match r.tail with
    | some v => v < s.globalRows || live.rows.contains v
    | none => false
  let liveCls (live : Vars) (c : ICls) : Bool :=
    match c with
    | .var v => v < s.globalClss || live.clss.contains v
    | .lit _ => false
  let mut live := members.foldl (fun acc m => varsOfSig m.sig acc) fixed
  let mut size := 0
  while live.size != size do
    size := live.size
    for c in incls do
      if liveRow live c.sub then live := varsOfRow ⟨c.under, none⟩ (varsOfRow c.sup live)
    for (r, b) in coerces do
      if liveTy live r then live := varsOf b live
    for (t, _, r) in places do
      if liveTy live t then live := varsOf r live
    for (c, tys) in onces do
      if tys.any live.touches then
        if let .var v := c then live := { live with clss := live.clss.insert v }
    for (env, caps) in shows do
      if liveTy live env then live := caps.foldl (fun acc c => varsOf c acc) live
  let sch : Scheme :=
    { startTy, startRow, startCls, fixedTys := fixed.tys, fixedRows := fixed.rows
      fixedClss := fixed.clss, members, incls, places, coerces, nevers, onces, shows
      exported := incls.filter fun c => liveRow live c.sub
      exportedPlaces := places.filter fun (t, _, _) => liveTy live t
      exportedCoerces := coerces.filter fun (r, _) => liveTy live r
      exportedNevers := nevers.filter (liveTy live)
      exportedOnces := onces.filter fun (c, tys) => liveCls live c || tys.any live.touches
      exportedShows := shows.filter fun (env, _) => liveTy live env }
  modify fun s =>
    { s with
      schemes := s.schemes.insert scc sch
      curScc := outer.curScc, cur := outer.cur, incls := outer.incls, places := outer.places
      coerces := outer.coerces, nevers := outer.nevers, onces := outer.onces, shows := outer.shows
      hints := outer.hints, refs := outer.refs }
  pure sch

/-- The signature to use for a reference to `fn`: the group's own inside its
group, and otherwise a fresh copy of its general type, whose conditions the
referring function takes on. -/
partial def refSig (fn : Nat) : M ISig := do
  let s ← get
  let scc := s.scc[fn]?.getD fn
  if s.curScc == some scc then
    match s.cur.lookup fn with
    | some sig => pure sig
    | none => throw s!"certificate: function {fn} is missing from its group"
  else
    let sch ← schemeOf scc
    match sch.members.find? (·.fn == fn) with
    | none => throw s!"certificate: function {fn} is missing from its group"
    | some m =>
      startCopy
      let sig ← copySig sch m.sig
      let incls ← sch.exported.mapM (copyIncl sch)
      let places ← sch.exportedPlaces.mapM (copyPlace sch)
      let coerces ← sch.exportedCoerces.mapM fun (r, b) => do
        pure (← copyTy sch r, ← copyTy sch b)
      let nevers ← sch.exportedNevers.mapM (copyTy sch)
      let onces ← sch.exportedOnces.mapM (copyOnce sch)
      let shows ← sch.exportedShows.mapM (copyShow sch)
      modify fun s =>
        { s with
          incls := s.incls ++ incls, places := s.places ++ places
          coerces := s.coerces ++ coerces, nevers := s.nevers ++ nevers
          onces := s.onces ++ onces, shows := s.shows ++ shows, refs := s.refs.push (fn, sig) }
      pure sig

partial def inferRhs (Γ : Array ITy) : Rhs → M ITy
  | .atom a => atomTy Γ a
  | .prim _ args => do
    for a in args do
      unify (← atomTy Γ a) .int
    pure .int
  | .construct tag args => do
    let ts ← args.mapM (atomTy Γ)
    if tag == 0 then pure (.tuple ts)
    else
      let (result, fields) ← instCtor tag
      unifyList ts fields
      pure result
  | .place pl => do
    let mut t ← atomTy Γ (.var pl.var)
    for i in pl.path do
      t ← field t i
    pure t
  | .closure fn captures => do
    let ts ← captures.mapM (atomTy Γ)
    let sig ← refSig fn
    unifyList ts sig.caps
    let cls ← freshCls
    if (← get).strict then modify fun s => { s with onces := s.onces.push (cls, sig.caps) }
    let env ← freshTy
    modify fun s => { s with shows := s.shows.push (env, sig.caps) }
    pure (.func sig.params sig.ret sig.row cls env)
  -- The elaborator gives another function only the environment of a block,
  -- which takes no arguments, so that is the only shape looked for.
  | .rebind a fn => do
    let sig ← refSig fn
    unify (← atomTy Γ a) (.func [] (← freshTy) (← freshRow) (← freshCls) (.tuple sig.caps))
    let cls ← freshCls
    if (← get).strict then modify fun s => { s with onces := s.onces.push (cls, sig.caps) }
    let env ← freshTy
    modify fun s => { s with shows := s.shows.push (env, sig.caps) }
    pure (.func sig.params sig.ret sig.row cls env)

/-- Infer a handler's functions. Gives its operations, in the order of `ops`. -/
partial def inferHandler (amb : IRow) (Γ : Array ITy) (ret : Nat) (ops : List (Nat × Nat))
    (captures : List Atom) (σ ρ : ITy) : M IOps := do
  let Cs ← captures.mapM (atomTy Γ)
  let retSig ← refSig ret
  unifyList Cs retSig.caps
  unifyList [σ] retSig.params
  unify ρ retSig.ret
  needs retSig.row [] amb
  let mut H : IOps := []
  let mut shared : List (Nat × List ITy) := []
  for (op, arm) in ops do
    let ((targs, payload, result), shared') ← instOp shared op
    shared := shared'
    H := H ++ [(op, targs)]
    let armSig ← refSig arm
    unifyList Cs armSig.caps
    let params := match result with
      | some o => payload ++ [.func [o] ρ amb (.lit true) .never]
      | none => payload
    unifyList params armSig.params
    unify ρ armSig.ret
    needs armSig.row [] amb
  pure H

/-- Infer a computation that must give a `τ` and may perform what `amb` serves. -/
partial def inferTm (amb : IRow) (τ : ITy) (Γ : Array ITy) : Core.Tm → M Unit
  | .ret a => do unify (← atomTy Γ a) τ
  | .let_ rhs body => do
    let σ ← inferRhs Γ rhs
    hint (.ty σ)
    inferTm amb τ (Γ.push σ) body
  | .call f args body => do
    let r ← applied Γ amb f args
    let b ← freshTy
    coerce r b
    hint (.result r b)
    inferTm amb τ (Γ.push b) body
  | .tail f args => do
    let r ← applied Γ amb f args
    coerce r τ
  | .handle ret ops captures thunk body => do
    let σ ← freshTy
    let ρ ← freshTy
    let εt ← freshRow
    unify (← atomTy Γ thunk) (.func [] σ εt (← freshCls) (← freshTy))
    let H ← inferHandler amb Γ ret ops captures σ ρ
    needs εt H amb
    hint (.handler ρ H)
    inferTm amb τ (Γ.push ρ) body
  | .handleTail ret ops captures thunk => do
    let σ ← freshTy
    let εt ← freshRow
    unify (← atomTy Γ thunk) (.func [] σ εt (← freshCls) (← freshTy))
    let H ← inferHandler amb Γ ret ops captures σ τ
    needs εt H amb
    hint (.handler τ H)
  | .raise op args => do
    let ((targs, payload, result), _) ← instOp [] op
    unifyList (← args.mapM (atomTy Γ)) payload
    if result.isSome then throw s!"operation {op} is raised, but it can be resumed"
    requireOp amb op targs
  | .perform op args body => do
    let ((targs, payload, result), _) ← instOp [] op
    unifyList (← args.mapM (atomTy Γ)) payload
    match result with
    | some σ =>
      requireOp amb op targs
      inferTm amb τ (Γ.push σ) body
    | none => throw s!"operation {op} is performed for a result, but it never returns"
  | .label thunk body => do
    let σ ← scope Γ amb thunk
    inferTm amb τ (Γ.push σ) body
  | .labelTail thunk => do
    let σ ← scope Γ amb thunk
    unify σ τ
  | .guard cleanup thunk body => do
    let σ ← guarded Γ amb cleanup thunk
    inferTm amb τ (Γ.push σ) body
  | .guardTail cleanup thunk => do
    let σ ← guarded Γ amb cleanup thunk
    unify σ τ
  | .cancel k body => do
    let ε' ← freshRow
    unify (← atomTy Γ k) (.func [← freshTy] (← freshTy) ε' (← freshCls) (← freshTy))
    needs ε' [] amb
    inferTm amb τ (Γ.push .unit) body
  | .mem op args body => do
    let ts ← args.mapM (atomTy Γ)
    let σ ← match op, ts with
      | .alloc, [t] => pure (ITy.ref t)
      | .load, [t] => do
        let σ ← freshTy
        unify t (.ref σ)
        pure σ
      | .store, [t, v] => do
        unify t (.ref v)
        pure .unit
      | .free, [t] => do
        unify t (.ref (← freshTy))
        pure .unit
      | .swap, [t, v] => do
        unify t (.ref v)
        pure v
      | _, _ => throw "a memory operation has the wrong number of arguments"
    inferTm amb τ (Γ.push σ) body
  | .host id args body => do
    let _ ← args.mapM (atomTy Γ)
    let σ ← match id, args.length with
      | 0, 1 => pure ITy.unit
      | 1, 0 => pure (ITy.tuple [.int, .int])
      | _, _ => throw s!"host operation {id} does not exist with {args.length} arguments"
    inferTm amb τ (Γ.push σ) body
where
  /-- A call: the callee's operations must be served where it is called. -/
  applied (Γ : Array ITy) (amb : IRow) (f : Atom) (args : List Atom) : M ITy := do
    let σ ← freshTy
    let ε' ← freshRow
    unify (← atomTy Γ f) (.func (← args.mapM (atomTy Γ)) σ ε' (← freshCls) (← freshTy))
    needs ε' [] amb
    pure σ
  scope (Γ : Array ITy) (amb : IRow) (thunk : Atom) : M ITy := do
    let σ ← freshTy
    let εt ← freshRow
    -- Applying the label does not return, unless something uses the label as
    -- a callable with a result.
    let ρ ← freshTy
    modify fun s => { s with nevers := s.nevers.push ρ }
    unify (← atomTy Γ thunk)
      (.func [.func [σ] ρ (← freshRow) (.lit false) .never] σ εt (← freshCls) (← freshTy))
    needs εt [] amb
    pure σ
  guarded (Γ : Array ITy) (amb : IRow) (cleanup thunk : Atom) : M ITy := do
    let σ ← freshTy
    let εt ← freshRow
    -- A cleanup performs no operations.
    unify (← atomTy Γ cleanup) (.func [] (← freshTy) ⟨[], none⟩ (← freshCls) (← freshTy))
    unify (← atomTy Γ thunk) (.func [] σ εt (← freshCls) (← freshTy))
    needs εt [] amb
    pure σ

end

/-- Settle, then decide what nothing decided, and settle again: a label's result
is `never`; a call whose callee is still unknown gives back what the code after
it expects; and a value whose fields are read, but whose type nothing else
determines, has the smallest tuple type with those fields. The last happens for
a callable that is never called. -/
partial def settleAll : M Unit := do
  settle
  let mut decided := false
  for ρ in (← get).nevers do
    if let .var v ← find ρ then
      bindTy v .never
      decided := true
  modify fun s => { s with nevers := #[] }
  if decided then return ← settleAll
  match (← get).coerces[0]? with
  | some (r, b) =>
    unify r b
    return ← settleAll
  | none => pure ()
  match (← get).places[0]? with
  | none => pure ()
  | some (t, _, _) =>
    match ← find t with
    | .var v =>
      let mut width := 0
      for (t', i, _) in (← get).places do
        if let .var v' ← find t' then
          if v' == v then width := max width (i + 1)
      bindTy v (.tuple (← freshTys width))
      settleAll
    | _ => settleAll

/-! ## Reading off the result -/

mutual

/-- A finished type. A type nothing determined is unit; an open row is closed. -/
partial def zonk (t : ITy) : M Ty := do
  match ← find t with
  | .var _ => pure (.tuple [])
  | .param _ => pure (.tuple [])
  | .int => pure .int
  | .tuple fs => do pure (.tuple (← fs.mapM zonk))
  | .data n args => do pure (.data n (← args.mapM zonk))
  | .fn ps r ops tail cls env => do
    let once := match ← findCls cls with
      | .lit b => b
      | .var _ => false
    let env ← match ← find env with
      | .tuple stated => do pure (some (← stated.mapM zonk))
      | _ => pure none
    pure (.fn (← ps.mapM zonk) (← zonk r) (← zonkRow ⟨ops, tail⟩) once env)
  | .ref t => do pure (.ref (← zonk t))
  | .never => pure .never

partial def zonkOps (ops : IOps) : M Typing.Row :=
  ops.mapM fun (op, targs) => do pure (op, ← targs.mapM zonk)

/-- A finished row, in a fixed order so that equal rows are equal lists. -/
partial def zonkRow (r : IRow) : M Typing.Row := do
  let r ← flattenRow r
  let ops ← zonkOps r.ops
  let once := ops.foldl (fun acc e => if acc.any (·.1 == e.1) then acc else acc ++ [e]) []
  pure (once.mergeSort fun a b => a.1 ≤ b.1)

end

def zonkHint : IHint → M (List Hint)
  | .ty t => do pure [.ty (← zonk t)]
  | .handler ρ H => do pure [.handler (← zonk ρ) (← zonkOps H)]
  | .result r b => do
    if (← zonk r) == .never then pure [.ty (← zonk b)] else pure []

def zonkHints (hs : Array IHint) : M (List Hint) := do
  pure (← hs.toList.mapM zonkHint).flatten

partial def ofTy : Ty → ITy
  | .int => .int
  | .tuple fs => .tuple (fs.map ofTy)
  | .data n args => .data n (args.map ofTy)
  | .fn ps r eff once env =>
    .fn (ps.map ofTy) (ofTy r) (eff.map fun (op, targs) => (op, targs.map ofTy)) none (.lit once)
      (match env with
        | some stated => .tuple (stated.map ofTy)
        | none => .never)
  | .ref t => .ref (ofTy t)
  | .never => .never

def zonkSig (s : ISig) : M FnSig := do
  pure ⟨← s.caps.mapM zonk, ← s.params.mapM zonk, ← zonk s.ret, ← zonkRow s.row⟩

/-! ## Signatures at the types a program uses -/

/-- Give `fn` the signature `sig`, and with it every function of its group and
everything they refer to, at the types that follow. -/
partial def instantiate (fn : Nat) (sig : FnSig) : M Unit := do
  if ((← get).emitted[fn]?.getD []).contains sig then return
  let sch ← schemeOf ((← get).scc[fn]?.getD fn)
  let outer ← get
  modify fun s =>
    { s with incls := #[], places := #[], coerces := #[], nevers := #[], onces := #[], shows := #[] }
  startCopy
  let members ← sch.members.mapM fun m => do
    pure { m with
      sig := ← copySig sch m.sig
      hints := ← m.hints.mapM fun hs => hs.mapM (copyHint sch)
      refs := ← m.refs.mapM fun (g, s) => do pure (g, ← copySig sch s) }
  let incls ← sch.incls.mapM (copyIncl sch)
  let places ← sch.places.mapM (copyPlace sch)
  let coerces ← sch.coerces.mapM fun (r, b) => do pure (← copyTy sch r, ← copyTy sch b)
  let nevers ← sch.nevers.mapM (copyTy sch)
  let onces ← sch.onces.mapM (copyOnce sch)
  let shows ← sch.shows.mapM (copyShow sch)
  modify fun s =>
    { s with
      incls := incls, places := places, coerces := coerces, nevers := nevers, onces := onces
      shows := shows }
  match members.find? (·.fn == fn) with
  | none => throw s!"certificate: function {fn} is missing from its group"
  | some m =>
    unifyList m.sig.caps (sig.caps.map ofTy)
    unifyList m.sig.params (sig.params.map ofTy)
    unify m.sig.ret (ofTy sig.ret)
    unifyRow m.sig.row ⟨sig.eff.map fun (op, targs) => (op, targs.map ofTy), none⟩
  settleAll
  let mut wanted : List (Nat × FnSig) := []
  for m in members do
    let ground ← zonkSig m.sig
    unless ((← get).emitted[m.fn]?.getD []).contains ground do
      let hints ← m.hints.toList.mapM zonkHints
      modify fun s =>
        { s with
          emitted := s.emitted.insert m.fn (ground :: s.emitted[m.fn]?.getD [])
          entries := s.entries.push ⟨m.fn, ground, hints⟩ }
      for (g, gs) in m.refs do
        wanted := wanted ++ [(g, ← zonkSig gs)]
  modify fun s =>
    { s with
      incls := outer.incls, places := outer.places, coerces := outer.coerces, nevers := outer.nevers
      onces := outer.onces, shows := outer.shows }
  for (g, gs) in wanted do
    instantiate g gs

/-- Every use of a declared type inside a type. -/
partial def dataUses : Ty → List (Nat × List Ty)
  | .int => []
  | .tuple fs => fs.flatMap dataUses
  | .data n args => (n, args) :: args.flatMap dataUses
  | .fn ps r eff _ env =>
    ps.flatMap dataUses ++ dataUses r ++ (eff.flatMap fun (_, targs) => targs.flatMap dataUses)
      ++ (env.getD []).flatMap dataUses
  | .ref t => dataUses t
  | .never => []

/-- Every use of an operation inside a type. -/
partial def opUses : Ty → List (Nat × List Ty)
  | .int => []
  | .tuple fs => fs.flatMap opUses
  | .data _ args => args.flatMap opUses
  | .fn ps r eff _ env =>
    ps.flatMap opUses ++ opUses r ++ eff ++ (eff.flatMap fun (_, targs) => targs.flatMap opUses)
      ++ (env.getD []).flatMap opUses
  | .ref t => opUses t
  | .never => []

def hintTypes : Hint → List Ty
  | .ty t => [t]
  | .handler ρ H => ρ :: H.flatMap (·.2)

def hintOps : Hint → List (Nat × List Ty)
  | .ty _ => []
  | .handler _ H => H

/-- The declarations behind every declared type and operation these types use,
and behind those the declarations use in turn. -/
partial def declsFor (types : List Ty) (opsTodo : List (Nat × List Ty)) (datas : List DataInst)
    (ops : List OpInst) : M (List DataInst × List OpInst) := do
  if datas.length + ops.length ≥ 4000 then
    throw "certificate: too many uses of declared types and operations"
  match opsTodo with
  | (op, args) :: rest =>
    if ops.any (fun o => o.op == op && o.args == args) then declsFor types rest datas ops
    else
      let d ← opDecl op
      let iargs := args.map ofTy
      let payload ← d.payload.mapM fun t => zonk (subst iargs t)
      let result ← match d.result with
        | some t => some <$> zonk (subst iargs t)
        | none => pure none
      declsFor (payload ++ result.toList ++ types) rest datas (ops ++ [⟨op, args, payload, result⟩])
  | [] =>
    match types with
    | [] => pure (datas, ops)
    | t :: rest =>
      let newData := (dataUses t).filter fun (name, args) =>
        !datas.any (fun d => d.name == name && d.args == args)
      match newData with
      | [] => declsFor rest (opUses t) datas ops
      | (name, args) :: _ =>
        let tags := (← get).types[name]?.getD []
        let mut ctors : List (Nat × List Ty) := []
        for tag in tags do
          let d ← ctorDecl tag
          let fields ← d.fields.mapM fun f => zonk (subst (args.map ofTy) f)
          ctors := ctors ++ [(tag, fields)]
        declsFor (ctors.flatMap (·.2) ++ types) opsTodo (datas ++ [⟨name, args, ctors, true⟩]) ops

/-! ## Declarations -/

/-- Read a declared type. A bare unknown name, or `_`, is a field whose type is
inferred: one type for the whole program. -/
partial def resolveType (typeNames params : List String) : TypeExpr → M ITy
  | .name x args => do
    match params.idxOf? x with
    | some i => pure (.param i)
    | none =>
      if x == "Int" then pure .int
      else
        match typeNames.idxOf? x with
        | some id => do pure (.data id (← args.mapM (resolveType typeNames params)))
        | none => freshTy
  | .tuple args => do pure (.tuple (← args.mapM (resolveType typeNames params)))
  | .fn ps r => do
    let row ← freshRow
    pure (.func (← ps.mapM (resolveType typeNames params)) (← resolveType typeNames params r) row
      (← freshCls) (← freshTy))
  | .ref t => do pure (.ref (← resolveType typeNames params t))
  | .never => freshTy
  | .hole => freshTy

def declare (items : List Item) (g : Elab.Globals) : M Unit := do
  let typeNames := items.filterMap fun
    | .enum name _ _ => some name
    | .struct name _ _ => some name
    | _ => none
  let effectNames := items.filterMap fun
    | .effect name _ _ => some name
    | _ => none
  let setAt {α : Type} (arr : Array (Option α)) (i : Nat) (x : α) : Array (Option α) :=
    (if arr.size ≤ i then arr ++ Array.replicate (i + 1 - arr.size) none else arr).set! i (some x)
  modify fun s => { s with types := Array.replicate typeNames.length [] }
  for item in items do
    match item with
    | .enum name params ctors =>
      let owner := (typeNames.idxOf? name).getD 0
      for (c, fields) in ctors do
        match g.ctors.lookup c with
        | some info =>
          let fields ← fields.mapM (resolveType typeNames params)
          modify fun s =>
            { s with
              ctors := setAt s.ctors info.tag ⟨owner, params.length, fields⟩
              types := s.types.modify owner (· ++ [info.tag]) }
        | none => throw s!"constructor `{c}` was not collected"
    | .struct name params fields =>
      let owner := (typeNames.idxOf? name).getD 0
      match g.ctors.lookup name with
      | some info =>
        let fields ← fields.mapM (resolveType typeNames params)
        modify fun s =>
          { s with
            ctors := setAt s.ctors info.tag ⟨owner, params.length, fields⟩
            types := s.types.modify owner (· ++ [info.tag]) }
      | none => throw s!"constructor `{name}` was not collected"
    | .effect name params ops =>
      let effect := (effectNames.idxOf? name).getD 0
      for op in ops do
        match g.ops.lookup op.name with
        | some info =>
          let payload ← op.payload.mapM (resolveType typeNames params)
          let result ← if op.terminal then pure none
            else some <$> resolveType typeNames params (op.result.getD .hole)
          modify fun s => { s with ops := setAt s.ops info.id ⟨effect, params.length, payload, result⟩ }
        | none => throw s!"operation `{op.name}` was not collected"
    | _ => pure ()

/-! ## Recursive groups -/

partial def tmRefs : Core.Tm → List Nat
  | .ret _ => []
  | .let_ rhs body =>
    (match rhs with
      | .closure fn _ => [fn]
      | .rebind _ fn => [fn]
      | _ => []) ++ tmRefs body
  | .call _ _ body => tmRefs body
  | .tail _ _ => []
  | .handle ret ops _ _ body => ret :: ops.map (·.2) ++ tmRefs body
  | .handleTail ret ops _ _ => ret :: ops.map (·.2)
  | .raise _ _ => []
  | .perform _ _ body => tmRefs body
  | .label _ body => tmRefs body
  | .labelTail _ => []
  | .guard _ _ body => tmRefs body
  | .guardTail _ _ => []
  | .cancel _ body => tmRefs body
  | .mem _ _ body => tmRefs body
  | .host _ _ body => tmRefs body

/-- For each function, the least function it is mutually recursive with. -/
def sccs (fns : Array Core.Fn) : Array Nat := Id.run do
  let n := fns.size
  let refs := fns.map fun F => F.clauses.flatMap fun c => tmRefs c.body
  -- reach[i][j]: function i refers, directly or not, to function j.
  let mut reach : Array (Array Bool) := #[]
  for i in [0:n] do
    let mut seen := Array.replicate n false
    let mut stack := refs[i]?.getD []
    let mut fuel := n * n + refs.foldl (fun acc r => acc + r.length) 0 + 1
    while fuel > 0 && !stack.isEmpty do
      fuel := fuel - 1
      match stack with
      | [] => pure ()
      | j :: rest =>
        stack := rest
        if j < n && !(seen[j]?.getD true) then
          seen := seen.set! j true
          stack := (refs[j]?.getD []) ++ stack
    reach := reach.push seen
  let mut out : Array Nat := #[]
  for i in [0:n] do
    let mut least := i
    for j in [0:i] do
      if least == i && (reach[i]?.bind (·[j]?)).getD false && (reach[j]?.bind (·[i]?)).getD false then
        least := j
    out := out.push least
  pure out

/-- Say which uses of declared types are duplicable: all of them, except those
with a field that is not, found by taking flags away until nothing changes. -/
partial def dupFlags (datas : List DataInst) : List DataInst :=
  let C : Cert := ⟨[], datas, [], .int, [], true⟩
  let next := datas.map fun d =>
    { d with dup := d.dup && d.ctors.all fun c => Typing.dupTys C c.2 }
  if next.zip datas |>.all (fun (a, b) => a.dup == b.dup) then next else dupFlags next

/-! ## The certificate -/

/-- How many values each function captures, read off the places that build it. -/
def captureCounts (p : Core.Program) : Array Nat := Id.run do
  let mut out := Array.replicate p.fns.length 0
  let rec visit (out : Array Nat) : Core.Tm → Array Nat
    | .ret _ => out
    | .let_ rhs body =>
      match rhs with
      | .closure fn captures => visit (out.setIfInBounds fn captures.length) body
      | _ => visit out body
    | .call _ _ body => visit out body
    | .tail _ _ => out
    | .handle ret ops captures _ body =>
      visit ((ret :: ops.map (·.2)).foldl (fun o f => o.setIfInBounds f captures.length) out) body
    | .handleTail ret ops captures _ =>
      (ret :: ops.map (·.2)).foldl (fun o f => o.setIfInBounds f captures.length) out
    | .raise _ _ => out
    | .perform _ _ body => visit out body
    | .label _ body => visit out body
    | .labelTail _ => out
    | .guard _ _ body => visit out body
    | .guardTail _ _ => out
    | .cancel _ body => visit out body
    | .mem _ _ body => visit out body
    | .host _ _ body => visit out body
  for F in p.fns do
    for c in F.clauses do
      out := visit out c.body
  visit out p.main

def certifyM (items : List Item) (g : Elab.Globals) (p : Core.Program)
    (envSizes : List (Nat × Nat)) : M Cert := do
  declare items g
  modify fun s =>
    { s with
      scc := sccs s.fns
      ncaps := envSizes.foldl (fun acc (fn, n) => acc.setIfInBounds fn n) (captureCounts p)
      globalTys := s.tys.size, globalRows := s.rows.size, globalClss := s.clss.size }
  let τ ← freshTy
  inferTm ⟨[], none⟩ τ #[] p.main
  let mainHints := (← get).hints
  let refs := (← get).refs
  settleAll
  let mainTy ← zonk τ
  let mainHints ← zonkHints mainHints
  let wanted ← refs.toList.mapM fun (g, gs) => do pure (g, ← zonkSig gs)
  modify fun s =>
    { s with incls := #[], places := #[], coerces := #[], nevers := #[], onces := #[], shows := #[] }
  for (g, gs) in wanted do
    instantiate g gs
  let entries := (← get).entries.toList
  let types : List Ty :=
    mainTy :: mainHints.flatMap hintTypes
      ++ entries.flatMap fun e =>
        e.sig.caps ++ e.sig.params ++ [e.sig.ret] ++ e.sig.eff.flatMap (·.2)
          ++ e.hints.flatMap (·.flatMap hintTypes)
  let opsUsed : List (Nat × List Ty) :=
    mainHints.flatMap hintOps
      ++ entries.flatMap fun e => e.sig.eff ++ e.hints.flatMap (·.flatMap hintOps)
  let (datas, ops) ← declsFor types opsUsed [] []
  let strict := (← get).strict
  pure ⟨entries, dupFlags datas, ops, mainTy, mainHints, strict⟩

/-- Find a certificate for an elaborated program, with the ownership rules or without. -/
def certify (items : List Item) (p : Core.Program) (strict : Bool)
    (envSizes : List (Nat × Nat) := []) : Except String Cert := do
  let (g, _, _) ← Elab.collect items
  let (cert, _) ← (certifyM items g p envSizes).run { fns := p.fns.toArray, strict := strict }
  pure cert

/-- Which part of a program a certificate fails on, for reporting a defect in
this pass or in the elaborator. -/
def rejected (C : Cert) (p : Core.Program) : String :=
  let bad := C.sigs.filterMap fun e =>
    match p.fns[e.fn]? with
    | some F =>
      if Typing.checkFn C e F then none
      else if !Typing.checkClauses C e.sig F.clauses e.hints then
        some s!"function {e.fn} is not typed at one of its signatures"
      else some s!"the clauses of function {e.fn} are not shown to cover its parameters"
    | none => some s!"function {e.fn} does not exist"
  match bad with
  | msg :: _ => msg
  | [] =>
    if Typing.checkTm C [] p.main C.mainHints C.mainTy [] then "nothing" else "`main` is not typed"

end Glorious.Infer
