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

A Core function used at several types gets several signatures. Each place a
function is referred to from outside its own group of mutually recursive
functions gets a fresh copy of that group to infer; equal results are merged at
the end.
-/

namespace Glorious.Infer

open Syntax
open Glorious.Typing (Ty FnSig Hint Cert SigEntry DataInst OpInst)

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
  and a variable for any others if the row is open. -/
  | fn (ps : List ITy) (ret : ITy) (ops : List (Nat × List ITy)) (tail : Option Nat)
  | ref (t : ITy)
  deriving Inhabited

abbrev IOps := List (Nat × List ITy)

structure IRow where
  ops : IOps
  tail : Option Nat
  deriving Inhabited

def ITy.unit : ITy := .tuple []

def ITy.func (ps : List ITy) (ret : ITy) (row : IRow) : ITy := .fn ps ret row.ops row.tail

inductive IHint where
  | ty (t : ITy)
  | handler (ρ : ITy) (H : IOps)

structure CtorDecl where
  owner : Nat
  arity : Nat
  fields : List ITy

structure OpDecl where
  effect : Nat
  arity : Nat
  payload : List ITy
  result : Option ITy

/-- One use of a function: its signature so far, and the hints found for each clause. -/
structure Inst where
  fn : Nat
  group : Nat
  caps : List ITy
  params : List ITy
  ret : ITy
  row : IRow
  hints : Array (Array IHint) := #[]

/-- Every operation of `sub` must be served at the same type: by `under` if it
lists the operation, and by `sup` otherwise. -/
structure Incl where
  sub : IRow
  under : IOps
  sup : IRow

structure St where
  fns : Array Core.Fn
  /-- For each function, an identity shared by the functions it is mutually recursive with. -/
  scc : Array Nat := #[]
  ctors : Array (Option CtorDecl) := #[]
  ops : Array (Option OpDecl) := #[]
  /-- The constructor tags of each declared type. -/
  types : Array (List Nat) := #[]
  tys : Array (Option ITy) := #[]
  rows : Array (Option IRow) := #[]
  /-- Counts bindings, so that a pass over the constraints can tell whether it learnt anything. -/
  gen : Nat := 0
  insts : Array Inst := #[]
  /-- Copies of recursive groups: the group's identity and its instances so far. -/
  groups : Array (Nat × List (Nat × Nat)) := #[]
  incls : Array Incl := #[]
  /-- Field reads whose subject was not yet known: subject, index, field. -/
  places : Array (ITy × Nat × ITy) := #[]
  /-- The hints of the clause being inferred. -/
  hints : Array IHint := #[]

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
  | .fn ps r ops tail => do
    if ← ps.anyM (occurs id) then return true
    if ← occurs id r then return true
    let row ← flattenRow ⟨ops, tail⟩
    row.ops.anyM fun (_, targs) => targs.anyM (occurs id)
  | .ref t => occurs id t

partial def showTy (t : ITy) : M String := do
  match ← find t with
  | .var id => pure s!"?{id}"
  | .param i => pure s!"'{i}"
  | .int => pure "Int"
  | .tuple fs => do pure s!"({", ".intercalate (← fs.mapM showTy)})"
  | .data n args => do pure s!"#{n}<{", ".intercalate (← args.mapM showTy)}>"
  | .fn ps r ops tail => do
    let row ← flattenRow ⟨ops, tail⟩
    let shown := row.ops.map fun (op, _) => toString op
    let open_ := if row.tail.isSome then ["…"] else []
    pure s!"fn({", ".intercalate (← ps.mapM showTy)}) -> {← showTy r} / \{{", ".intercalate (shown ++ open_)}}"
  | .ref t => do pure s!"&{← showTy t}"

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
  | .fn ps r ops tail, .fn ps' r' ops' tail' => do
    unifyList ps ps'
    unify r r'
    unifyRow ⟨ops, tail⟩ ⟨ops', tail'⟩
  | .ref x, .ref y => unify x y
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
  | .fn ps r ops tail =>
    .fn (ps.map (subst args)) (subst args r)
      (ops.map fun (op, targs) => (op, targs.map (subst args))) tail
  | .ref t => .ref (subst args t)

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

mutual

/-- The instance of `fn` to use from an instance in `group`: the group's own if
`fn` belongs to the same recursive group, and otherwise a fresh copy. -/
partial def instOf (group : Option Nat) (fn : Nat) (ncaps : Nat) : M Nat := do
  let s ← get
  let scc := s.scc[fn]?.getD fn
  let target ← match group with
    | some g =>
      match s.groups[g]? with
      | some (scc', members) =>
        if scc' == scc then
          match members.lookup fn with
          | some id => return id
          | none => pure g
        else newGroup scc
      | none => newGroup scc
    | none => newGroup scc
  let F ← match s.fns[fn]? with
    | some F => pure F
    | none => throw s!"function {fn} does not exist"
  let arity := match F.clauses with
    | c :: _ => c.pats.length
    | [] => 0
  let caps ← freshTys ncaps
  let params ← freshTys arity
  let ret ← freshTy
  let row ← freshRow
  let id := (← get).insts.size
  modify fun s =>
    { s with
      insts := s.insts.push ⟨fn, target, caps, params, ret, row, #[]⟩
      groups := s.groups.modify target fun (scc, members) => (scc, (fn, id) :: members) }
  -- Infer the body at once: it may refer back to this instance.
  let outer := (← get).hints
  let mut all : Array (Array IHint) := #[]
  for c in F.clauses do
    modify fun s => { s with hints := #[] }
    unless c.pats.length == arity do
      throw s!"the clauses of function {fn} take different numbers of arguments"
    let binds ← inferPats c.pats params
    inferTm (some target) row ret (params ++ caps ++ binds).toArray c.body
    all := all.push (← get).hints
  modify fun s =>
    { s with hints := outer, insts := s.insts.modify id fun i => { i with hints := all } }
  pure id
where
  newGroup (scc : Nat) : M Nat := do
    let s ← get
    set { s with groups := s.groups.push (scc, []) }
    pure s.groups.size

partial def inferRhs (group : Option Nat) (Γ : Array ITy) : Rhs → M ITy
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
    let id ← instOf group fn captures.length
    match (← get).insts[id]? with
    | some inst =>
      unifyList ts inst.caps
      pure (.func inst.params inst.ret inst.row)
    | none => throw "certificate: an instance is missing"

/-- Infer a handler's functions. Gives the types of its operations, in the order of `ops`. -/
partial def inferHandler (group : Option Nat) (amb : IRow) (Γ : Array ITy) (ret : Nat)
    (ops : List (Nat × Nat)) (captures : List Atom) (σ ρ : ITy) : M IOps := do
  let Cs ← captures.mapM (atomTy Γ)
  let retId ← instOf group ret captures.length
  match (← get).insts[retId]? with
  | some inst =>
    unifyList Cs inst.caps
    unifyList [σ] inst.params
    unify ρ inst.ret
    needs inst.row [] amb
  | none => throw "certificate: an instance is missing"
  let mut H : IOps := []
  let mut shared : List (Nat × List ITy) := []
  for (op, arm) in ops do
    let ((targs, payload, result), shared') ← instOp shared op
    shared := shared'
    H := H ++ [(op, targs)]
    let armId ← instOf group arm captures.length
    match (← get).insts[armId]? with
    | some inst =>
      unifyList Cs inst.caps
      let params := match result with
        | some o => payload ++ [.func [o] ρ amb]
        | none => payload
      unifyList params inst.params
      unify ρ inst.ret
      needs inst.row [] amb
    | none => throw "certificate: an instance is missing"
  pure H

/-- Infer a computation that must give a `τ` and may perform what `amb` serves. -/
partial def inferTm (group : Option Nat) (amb : IRow) (τ : ITy) (Γ : Array ITy) :
    Core.Tm → M Unit
  | .ret a => do unify (← atomTy Γ a) τ
  | .let_ rhs body => do
    let σ ← inferRhs group Γ rhs
    hint (.ty σ)
    inferTm group amb τ (Γ.push σ) body
  | .call f args body => do
    let σ ← applied Γ amb f args
    inferTm group amb τ (Γ.push σ) body
  | .tail f args => do
    let σ ← applied Γ amb f args
    unify σ τ
  | .handle ret ops captures thunk body => do
    let σ ← freshTy
    let ρ ← freshTy
    let εt ← freshRow
    unify (← atomTy Γ thunk) (.func [] σ εt)
    let H ← inferHandler group amb Γ ret ops captures σ ρ
    needs εt H amb
    hint (.handler ρ H)
    inferTm group amb τ (Γ.push ρ) body
  | .handleTail ret ops captures thunk => do
    let σ ← freshTy
    let εt ← freshRow
    unify (← atomTy Γ thunk) (.func [] σ εt)
    let H ← inferHandler group amb Γ ret ops captures σ τ
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
      inferTm group amb τ (Γ.push σ) body
    | none => throw s!"operation {op} is performed for a result, but it never returns"
  | .label thunk body => do
    let σ ← scope Γ amb thunk
    inferTm group amb τ (Γ.push σ) body
  | .labelTail thunk => do
    let σ ← scope Γ amb thunk
    unify σ τ
  | .guard cleanup thunk body => do
    let σ ← guarded Γ amb cleanup thunk
    inferTm group amb τ (Γ.push σ) body
  | .guardTail cleanup thunk => do
    let σ ← guarded Γ amb cleanup thunk
    unify σ τ
  | .cancel k body => do
    let ε' ← freshRow
    unify (← atomTy Γ k) (.func [← freshTy] (← freshTy) ε')
    needs ε' [] amb
    inferTm group amb τ (Γ.push .unit) body
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
      | _, _ => throw "a memory operation has the wrong number of arguments"
    inferTm group amb τ (Γ.push σ) body
  | .host id args body => do
    let _ ← args.mapM (atomTy Γ)
    let σ ← match id, args.length with
      | 0, 1 => pure ITy.unit
      | 1, 0 => pure (ITy.tuple [.int, .int])
      | _, _ => throw s!"host operation {id} does not exist with {args.length} arguments"
    inferTm group amb τ (Γ.push σ) body
where
  /-- A call: the callee's operations must be served where it is called. -/
  applied (Γ : Array ITy) (amb : IRow) (f : Atom) (args : List Atom) : M ITy := do
    let σ ← freshTy
    let ε' ← freshRow
    unify (← atomTy Γ f) (.func (← args.mapM (atomTy Γ)) σ ε')
    needs ε' [] amb
    pure σ
  scope (Γ : Array ITy) (amb : IRow) (thunk : Atom) : M ITy := do
    let σ ← freshTy
    let εt ← freshRow
    unify (← atomTy Γ thunk) (.func [.func [σ] (← freshTy) (← freshRow)] σ εt)
    needs εt [] amb
    pure σ
  guarded (Γ : Array ITy) (amb : IRow) (cleanup thunk : Atom) : M ITy := do
    let σ ← freshTy
    let εt ← freshRow
    -- A cleanup performs no operations.
    unify (← atomTy Γ cleanup) (.func [] (← freshTy) ⟨[], none⟩)
    unify (← atomTy Γ thunk) (.func [] σ εt)
    needs εt [] amb
    pure σ

end

/-! ## Solving what was put off -/

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
  if (← get).gen != before then settle

/-- Settle, and give a value whose fields are read but whose type nothing else
determines the smallest tuple type that has those fields. This happens for a
callable that is never called. -/
partial def settleAll : M Unit := do
  settle
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
  | .fn ps r ops tail => do pure (.fn (← ps.mapM zonk) (← zonk r) (← zonkRow ⟨ops, tail⟩))
  | .ref t => do pure (.ref (← zonk t))

partial def zonkOps (ops : IOps) : M Typing.Row :=
  ops.mapM fun (op, targs) => do pure (op, ← targs.mapM zonk)

/-- A finished row, in a fixed order so that equal rows are equal lists. -/
partial def zonkRow (r : IRow) : M Typing.Row := do
  let r ← flattenRow r
  let ops ← zonkOps r.ops
  let once := ops.foldl (fun acc e => if acc.any (·.1 == e.1) then acc else acc ++ [e]) []
  pure (once.mergeSort fun a b => a.1 ≤ b.1)

end

def zonkHint : IHint → M Hint
  | .ty t => do pure (.ty (← zonk t))
  | .handler ρ H => do pure (.handler (← zonk ρ) (← zonkOps H))

partial def ofTy : Ty → ITy
  | .int => .int
  | .tuple fs => .tuple (fs.map ofTy)
  | .data n args => .data n (args.map ofTy)
  | .fn ps r eff =>
    .fn (ps.map ofTy) (ofTy r) (eff.map fun (op, targs) => (op, targs.map ofTy)) none
  | .ref t => .ref (ofTy t)

/-- Every use of a declared type inside a type. -/
partial def dataUses : Ty → List (Nat × List Ty)
  | .int => []
  | .tuple fs => fs.flatMap dataUses
  | .data n args => (n, args) :: args.flatMap dataUses
  | .fn ps r eff =>
    ps.flatMap dataUses ++ dataUses r ++ eff.flatMap fun (_, targs) => targs.flatMap dataUses
  | .ref t => dataUses t

/-- Every use of an operation inside a type. -/
partial def opUses : Ty → List (Nat × List Ty)
  | .int => []
  | .tuple fs => fs.flatMap opUses
  | .data _ args => args.flatMap opUses
  | .fn ps r eff =>
    ps.flatMap opUses ++ opUses r ++ eff ++ eff.flatMap fun (_, targs) => targs.flatMap opUses
  | .ref t => opUses t

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
        declsFor (ctors.flatMap (·.2) ++ types) opsTodo (datas ++ [⟨name, args, ctors⟩]) ops

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
    pure (.func (← ps.mapM (resolveType typeNames params)) (← resolveType typeNames params r) row)
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

/-! ## The certificate -/

def certifyM (items : List Item) (g : Elab.Globals) (p : Core.Program) : M Cert := do
  declare items g
  modify fun s => { s with scc := sccs s.fns }
  let τ ← freshTy
  inferTm none ⟨[], none⟩ τ #[] p.main
  let mainHints := (← get).hints
  settleAll
  let mut entries : List SigEntry := []
  for inst in (← get).insts do
    let sig : FnSig :=
      ⟨← inst.caps.mapM zonk, ← inst.params.mapM zonk, ← zonk inst.ret, ← zonkRow inst.row⟩
    unless entries.any (fun e => e.fn == inst.fn && e.sig == sig) do
      let hints ← inst.hints.toList.mapM fun hs => hs.toList.mapM zonkHint
      entries := entries ++ [⟨inst.fn, sig, hints⟩]
  let mainTy ← zonk τ
  let mainHints ← mainHints.toList.mapM zonkHint
  let types : List Ty :=
    mainTy :: mainHints.flatMap hintTypes
      ++ entries.flatMap fun e =>
        e.sig.caps ++ e.sig.params ++ [e.sig.ret] ++ e.sig.eff.flatMap (·.2)
          ++ e.hints.flatMap (·.flatMap hintTypes)
  let opsUsed : List (Nat × List Ty) :=
    mainHints.flatMap hintOps
      ++ entries.flatMap fun e => e.sig.eff ++ e.hints.flatMap (·.flatMap hintOps)
  let (datas, ops) ← declsFor types opsUsed [] []
  pure ⟨entries, datas, ops, mainTy, mainHints⟩

/-- Find a certificate for an elaborated program. -/
def certify (items : List Item) (p : Core.Program) : Except String Cert := do
  let (g, _, _) ← Elab.collect items
  let (cert, _) ← (certifyM items g p).run { fns := p.fns.toArray }
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
