import Glorious.Syntax.Ast
import Glorious.Elab

/-!
# Type and effect inference

Checks a program before it is elaborated. Types and effects are inferred:
annotations on functions are optional, and a field of a data or operation
declaration written as a bare name has its type inferred from how the program
uses it. A declaration with type parameters is polymorphic; one with inferred
fields has a single type throughout the program.

The checker establishes that values are used at consistent types, that calls
supply the right number of arguments, that pattern clauses cover every case,
that every effect a program performs is handled before it reaches `main`, and
that no callable able to jump to a label can be called after the label's scope
has ended. It does not yet track how many times a value is used, or how long a
reference lives. This pass is not proved.
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
  | ref (t : Ty)
  deriving Inhabited

/-- A set of effects, possibly open. -/
structure Row where
  effs : List (String × List Ty)
  tail : Option Nat
  deriving Inhabited

def Ty.int : Ty := .con "Int" []

def Ty.unit : Ty := .tuple []

def Ty.func (params : List Ty) (ret : Ty) (row : Row) (cap : Nat) : Ty :=
  .fn params ret row.effs row.tail cap

/-- Something a callable has captured: a label, by the brand of its scope, or a
value of some type. -/
inductive Captured where
  | brand (id : Nat)
  | ty (t : Ty)

/-- A type with some of its variables generalised. `edges` records what the
generalised capture variables capture, to be repeated at each use. -/
structure Scheme where
  tvars : List Nat
  rvars : List Nat
  cvars : List Nat
  edges : List (Nat × Captured)
  ty : Ty

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

structure EffectDecl where
  tvars : List Nat
  ops : List String

/-- What a local name stands for. -/
inductive Binding where
  | val (t : Ty)
  /-- A mutable variable holding a `t`. -/
  | cell (t : Ty)
  /-- A label whose scope yields a `t`; `brand` identifies the scope. -/
  | label (t : Ty) (brand : Nat)
  /-- A local callable, usable at several types. -/
  | poly (s : Scheme)

abbrev Scope := List (String × Binding)

/-- A coverage check to run once the types involved are known. `what` names the
clauses and ends with the verb of the message. -/
structure Pending where
  what : String
  tys : List Ty
  rows : List (List Pattern)

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
  brands : Nat := 0
  /-- Capture variables already visited by the search in progress. -/
  seen : List Nat := []
  types : List (String × TypeDecl) := []
  ctors : List (String × CtorSig) := []
  ops : List (String × OpSig) := []
  effects : List (String × EffectDecl) := []
  aliases : List (String × Expr) := []
  fns : List (String × Scheme) := []
  /-- The functions being inferred together, with their types so far. -/
  group : List (String × Ty) := []
  pending : Array Pending := #[]
  /-- Field reads whose subject was not yet known: subject, index, field type. -/
  projections : Array (Ty × Nat × Ty) := #[]

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

def captures (cap : Nat) (what : Captured) : M Unit :=
  modify fun s => { s with capEdges := s.capEdges.push (cap, what) }

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
  | .ref t => do
    pure (.ref (← zonk t))

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
  | .ref t => s!"&mut {showTy t}"

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
  | .ref t => freeTys t

partial def freeRows : Ty → List Nat
  | .var _ => []
  | .con _ args => args.flatMap freeRows
  | .tuple args => args.flatMap freeRows
  | .fn ps r effs tail _ =>
    ps.flatMap freeRows ++ freeRows r ++ effs.flatMap (fun e => e.2.flatMap freeRows)
      ++ tail.toList
  | .ref t => freeRows t

end

partial def freeCaps : Ty → List Nat
  | .var _ => []
  | .con _ args => args.flatMap freeCaps
  | .tuple args => args.flatMap freeCaps
  | .fn ps r effs _ cap =>
    cap :: (ps.flatMap freeCaps ++ freeCaps r ++ effs.flatMap (fun e => e.2.flatMap freeCaps))
  | .ref t => freeCaps t

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
  | .ref t => .ref (subst tm rm cm t)

def instantiate (s : Scheme) : M Ty := do
  let tm ← s.tvars.mapM fun id => do
    pure (id, ← freshTy)
  let rm ← s.rvars.mapM fun id => do
    pure (id, ← freshRowVar)
  let cm ← s.cvars.mapM fun id => do
    pure (id, ← freshCap)
  for (cap, what) in s.edges do
    captures ((cm.lookup cap).getD cap) (match what with
      | .ty t => .ty (subst tm rm cm t)
      | .brand b => .brand b)
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
  | .ref t => do
    let (t, seen) ← openParams seen t
    pure (.ref t, seen)
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
  for m in keep ++ s.mono.map Ty.var do
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
  for (cap, what) in s.capEdges do
    let root ← findCap cap
    match what with
    | .ty target =>
      let target ← zonk target
      edges := edges.push (root, target)
      all := all.push (root, .ty target)
    | .brand b => all := all.push (root, .brand b)
  let mut reach : List Nat := (freeCaps t).eraseDups
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
  pure ⟨(freeTys t).eraseDups.filter (!fixedTys.contains ·),
    (freeRows t).eraseDups.filter (!fixedRows.contains ·), cvars,
    all.toList.filter (cvars.contains ·.1), t⟩

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
  | .ref x, .ref y => unify x y
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

/-! ## Declarations -/

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
          if decl && args.isEmpty then inferred
          else throw s!"unknown type `{x}`"
  | .tuple args => do
    pure (.tuple (← args.mapM (resolveType params decl)))
  | .fn ps r => do
    let ps ← ps.mapM (resolveType params decl)
    let r ← resolveType params decl r
    let tail ← freshRowVar
    let cap ← freshCap
    if decl then
      modify fun s => { s with monoRows := tail :: s.monoRows, monoCaps := cap :: s.monoCaps }
    pure (.fn ps r [] (some tail) cap)
  | .ref t => do
    pure (.ref (← resolveType params decl t))
  | .never => throw "`!` can only be the result of an operation"
  | .hole => if decl then inferred else freshTy
where
  inferred : M Ty := do
    let t ← freshTy
    match t with
    | .var id => modify fun s => { s with mono := id :: s.mono }
    | _ => pure ()
    pure t

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
        modify fun s => { s with ops := (op.name, ⟨name, ids, payload, result⟩) :: s.ops }
      modify fun s => { s with effects := (name, ⟨ids, ops.map (·.name)⟩) :: s.effects }
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
  | .call (.name q x) args => do
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
  let mut left : Array (Ty × Nat × Ty) := #[]
  for (subject, idx, result) in waiting do
    match ← fieldType subject idx with
    | some t => unifyAt s!"the field `.{idx}`" result t
    | none => left := left.push (subject, idx, result)
  if left.isEmpty then pure ()
  else if left.size < waiting.size then
    modify fun s => { s with projections := left ++ s.projections }
    runProjections final
  else if !final then
    modify fun s => { s with projections := left ++ s.projections }
  else
    match left[0]? with
    | some (_, idx, _) =>
      throw s!"`.{idx}` reads a field of a value whose type is not known here; \
        annotate the value it is read from"
    | none => pure ()

def runPending : M Unit := do
  runProjections true
  let pending := (← get).pending
  modify fun s => { s with pending := #[] }
  for p in pending do
    let rows ← p.rows.mapM (·.mapM normPat)
    unless ← exhaustive p.tys rows do
      throw s!"{p.what} not cover every case"

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
  | .ref t => tyHolds brand t

end

/-- Reject a scope whose label could still be reached after the scope has ended.
`roots` are the types that outlive the scope, each with a description. -/
def checkEscape (brand : Nat) (label : String) (roots : List (String × Ty)) (amb : Row) :
    M Unit := do
  runProjections false
  let holds := fun (t : Ty) => do
    modify fun s => { s with seen := [] }
    tyHolds brand t
  let escape := fun (how : String) =>
    (throw s!"a callable that jumps to `@{label}` could be called after `@{label}` has \
      ended: {how}" : M Unit)
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

/-- The types of the bindings in scope, described for an escape message. -/
def scopeRoots (scope : Scope) : List (String × Ty) :=
  scope.map fun (name, b) =>
    match b with
    | .val t => (s!"`{name}`, which outlives the scope, could hold it", t)
    | .cell t => (s!"`{name}`, which outlives the scope, could hold it", t)
    | .label t _ => (s!"it can be passed out through `{name}`", t)
    | .poly s => (s!"`{name}`, which outlives the scope, could hold it", s.ty)

/-- Can this pattern fail to match? Decided from its shape alone. -/
partial def irrefutable : Pattern → M Bool
  | .wild => pure true
  | .int _ => pure false
  | .tuple ps => ps.allM irrefutable
  | .var x => do
    if (← resolveCtor x none).isSome then return false
    return ((← get).aliases.lookup x).isNone
  | .ctor _ _ _ => pure false

/-! ## Expressions -/

/-- What a name in an expression refers to. -/
inductive Head where
  | local (b : Binding)
  | fn (t : Ty)
  | ctor (sig : CtorSig)
  | op (sig : OpSig)
  | prim
  | host (id : Nat)
  | cancel
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
  if let some t := s.group.lookup x then return .fn t
  if let some scheme := s.fns.lookup x then return .fn (← instantiate scheme)
  if (Elab.prims.lookup x).isSome then return .prim
  if let some (id, _) := Elab.hosts.lookup x then return .host id
  if x == "cancel" then return .cancel
  if let some e := s.aliases.lookup x then return .const e
  throw s!"unknown name `{x}`"

/-- A label is a callable that never returns: it accepts the value its scope
yields, and holds the scope's brand. -/
private def labelType (t : Ty) (brand : Nat) : M Ty := do
  let cap ← freshCap
  captures cap (.brand brand)
  pure (.func [t] (← freshTy) (← freshRow) cap)

private def arguments (n : Nat) : String :=
  if n == 1 then "1 argument" else s!"{n} arguments"

private def arityError (what : String) (expected found : Nat) : M Unit :=
  throw s!"{what} takes {arguments expected}, but is given {found}"

mutual

partial def inferExpr (scope : Scope) (amb : Row) : Expr → M Ty
  | .int _ => pure .int
  | .name q x => do
    match ← resolveName scope q x with
    | .local (.val t) => pure t
    | .local (.cell t) => pure t
    | .local (.label t brand) => labelType t brand
    | .local (.poly s) => instantiate s
    | .fn t => pure t
    | .ctor sig => do
      let (fields, result) ← instCtor sig
      unless fields.isEmpty do arityError s!"constructor `{x}`" fields.length 0
      pure result
    | .op _ => throw s!"operation `{x}` must be called"
    | .prim => throw s!"intrinsic `{x}` must be called"
    | .host _ => throw s!"host operation `{x}` must be called"
    | .cancel => throw "`cancel` must be applied to a resumption"
    | .const e => inferExpr [] amb e
  | .label l =>
    match scope.lookup ("@" ++ l) with
    | some (.label t brand) => labelType t brand
    | _ => throw s!"unknown label `@{l}`"
  | .tuple es => do
    pure (.tuple (← es.mapM (inferExpr scope amb)))
  | .proj e idx => do
    let subject ← inferExpr scope amb e
    match ← fieldType subject idx with
    | some t => pure t
    | none => do
      -- Not known yet: settle it once the rest of the function is inferred.
      let t ← freshTy
      modify fun s => { s with projections := s.projections.push (subject, idx, t) }
      pure t
  | .call f args => inferCall scope amb f args
  | .tailCall f args => inferCall scope amb f args
  | .closure clauses => inferCallable scope [] none none clauses "the clauses of this callable do"
  | .handle subject arms => inferHandle scope amb subject arms
  | .labelScope l body => do
    let t ← freshTy
    let brand ← freshBrand
    let found ← inferStmts (("@" ++ l, .label t brand) :: scope) amb body
    unifyAt s!"the result of the scope `@{l}`" t found
    checkEscape brand l (("it is the result of the scope", t) :: scopeRoots scope) amb
    pure t
  | .ref x =>
    match scope.lookup x with
    | some (.cell t) => pure (.ref t)
    | some _ => throw s!"`{x}` is not a mutable variable, so it cannot be borrowed"
    | none => throw s!"unknown name `{x}`"
  | .deref e => do
    let t ← inferExpr scope amb e
    let inner ← freshTy
    unifyAt "`*` reads through a reference" (.ref inner) t
    pure inner

/-- Check the arguments of a call against the parameter types. -/
partial def checkArgs (scope : Scope) (amb : Row) (what : String) (params : List Ty)
    (args : List Expr) : M Unit := do
  unless params.length == args.length do arityError what params.length args.length
  let mut i := 1
  for (p, a) in params.zip args do
    unifyAt s!"argument {i} of {what}" p (← inferExpr scope amb a)
    i := i + 1

/-- Apply a callee of a given type in the ambient effects. -/
partial def applyTy (scope : Scope) (amb : Row) (what : String) (callee : Ty) (args : List Expr) :
    M Ty := do
  match ← find callee with
  | .fn ps r effs tail _ => do
    checkArgs scope amb what ps args
    try unifyRow ⟨effs, tail⟩ amb
    catch e => throw s!"{what} cannot be called here: {e}"
    pure r
  | t => do
    let argTys ← args.mapM (inferExpr scope amb)
    let r ← freshTy
    unifyAt s!"{what} is called with {arguments args.length}"
      (.func argTys r amb (← freshCap)) t
    pure r

partial def inferCall (scope : Scope) (amb : Row) (f : Expr) (args : List Expr) : M Ty := do
  match f with
  | .name q x =>
    match ← resolveName scope q x with
    | .ctor sig => do
      let (fields, result) ← instCtor sig
      checkArgs scope amb s!"constructor `{x}`" fields args
      pure result
    | .op sig => do
      let decl := ((← get).effects.lookup sig.effect).getD ⟨[], []⟩
      let inst ← decl.tvars.mapM fun _ => freshTy
      let (payload, result) := instOp sig inst
      try unifyRow amb ⟨[(sig.effect, inst)], some (← freshRowVar)⟩
      catch e => throw s!"operation `{x}` cannot be performed here: {e}"
      checkArgs scope amb s!"operation `{x}`" payload args
      match result with
      | some r => pure r
      | none => freshTy
    | .prim => do
      checkArgs scope amb s!"intrinsic `{x}`" [.int, .int] args
      pure .int
    | .host id => do
      if id == 0 then
        checkArgs scope amb s!"`{x}`" [← freshTy] args
        pure .unit
      else
        checkArgs scope amb s!"`{x}`" [] args
        pure (.tuple [.int, .int])
    | .cancel => do
      checkArgs scope amb "`cancel`" [← freshTy] args
      pure .unit
    | .local (.val t) => applyTy scope amb s!"`{x}`" t args
    | .local (.cell t) => applyTy scope amb s!"`{x}`" t args
    | .local (.label t brand) => do
      applyTy scope amb s!"the label `{x}`" (← labelType t brand) args
    | .local (.poly s) => do
      applyTy scope amb s!"`{x}`" (← instantiate s) args
    | .fn t => applyTy scope amb s!"`{x}`" t args
    | .const e => do
      applyTy scope amb s!"`{x}`" (← inferExpr [] amb e) args
  | .label l => do
    applyTy scope amb s!"the label `@{l}`" (← inferExpr scope amb f) args
  | _ => do
    applyTy scope amb "this callee" (← inferExpr scope amb f) args

/-- The type of a block: that of its last expression, or unit. -/
partial def inferStmts (scope : Scope) (amb : Row) : List Stmt → M Ty
  | [] => pure .unit
  | [.expr e] => inferExpr scope amb e
  | .expr e :: rest => do
    let _ ← inferExpr scope amb e
    inferStmts scope amb rest
  | .let_ (.var x) (.closure clauses) :: rest => do
    let t ← inferExpr scope amb (.closure clauses)
    if (← resolveCtor x none).isSome || ((← get).aliases.lookup x).isSome then
      let binds ← inferPat (.var x) t
      inferStmts (binds ++ scope) amb rest
    else
      -- A callable bound by `let` is a value, so it can be used at several types.
      -- Everything its surroundings already depend on stays fixed.
      let s ← get
      let mut keep : List Ty := [.func [] .unit amb (← freshCap)]
      for (_, b) in scope do
        keep := (match b with
          | .val t => t
          | .cell t => t
          | .label t _ => t
          | .poly p => p.ty) :: keep
      for (_, t) in s.group do
        keep := t :: keep
      for (subject, _, result) in s.projections do
        keep := subject :: result :: keep
      let scheme ← generalize t keep (top := false)
      inferStmts ((x, .poly scheme) :: scope) amb rest
  | .let_ pat value :: rest => do
    let t ← inferExpr scope amb value
    let binds ← inferPat pat t
    let check : Pending := ⟨"the pattern of this `let` does", [t], [[pat]]⟩
    modify fun s => { s with pending := s.pending.push check }
    inferStmts (binds ++ scope) amb rest
  | .letMut x value :: rest => do
    let t ← inferExpr scope amb value
    inferStmts ((x, .cell t) :: scope) amb rest
  | .assign target value :: rest => do
    let expected ← match target with
      | .name none x =>
        match scope.lookup x with
        | some (.cell t) => pure t
        | some _ => throw s!"`{x}` is not a mutable variable"
        | none => throw s!"unknown name `{x}`"
      | .deref e => do
        let inner ← freshTy
        unifyAt "`*` assigns through a reference" (.ref inner) (← inferExpr scope amb e)
        pure inner
      | _ => throw "only a mutable variable or `*reference` can be assigned"
    unifyAt "the assigned value" expected (← inferExpr scope amb value)
    inferStmts scope amb rest
  | .defer e :: rest => do
    let _ ← inferExpr scope amb e
    inferStmts scope amb rest

/-- Check a pattern against a type; the names it binds. -/
partial def inferPat (p : Pattern) (t : Ty) : M Scope := do
  match p with
  | .wild => pure []
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
    (self : Option String) (clauses : List Clause) (what : String) : M Ty := do
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
  -- What the callable captures from the scope it is written in.
  let cap ← freshCap
  for name in (clauses.flatMap (Elab.fvClause [])).eraseDups do
    match scope.lookup name with
    | some (.val t) => captures cap (.ty t)
    | some (.cell t) => captures cap (.ty t)
    | some (.label _ brand) => captures cap (.brand brand)
    | some (.poly s) => captures cap (.ty s.ty)
    | none => pure ()
  let brand ← freshBrand
  let scope := match self with
    | some name => ("@" ++ name, Binding.label result brand) :: scope
    | none => scope
  for clause in clauses do
    match clause with
    | .mk pats body =>
      unless pats.length == arity do
        throw "the clauses of a callable take different numbers of arguments"
      let binds ← inferPats pats params
      unifyAt "the result of a clause" result (← inferStmts (binds ++ scope) row body)
  let check : Pending := ⟨what, params, clauses.map fun
    | .mk pats _ => pats⟩
  modify fun s => { s with pending := s.pending.push check }
  -- A function's own label returns from it, so nothing holding that label may
  -- be handed back to the caller.
  if let some name := self then
    let roots := ("it is returned from the function", result) ::
      params.map fun p => ("the caller could hold it through a parameter", p)
    checkEscape brand name roots row
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
  let subjectTy ← inferExpr scope ⟨insts ++ ambFlat.effs, ambFlat.tail⟩ subject
  let result ← freshTy
  if completions.isEmpty then unify result subjectTy
  else
    for (p, body) in completions do
      let binds ← inferPat p subjectTy
      unifyAt "the result of a completion clause" result
        (← inferStmts (binds ++ scope) amb body)
    let check : Pending := ⟨"the completion clauses of this handler do", [subjectTy],
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
      unifyAt s!"the result of the arm for `{x}`" result (← inferStmts (binds ++ scope) amb body)
      if ← ps.allM irrefutable then covered := x :: covered
    | some o =>
      if ps.length == payload.length + 1 then
        let binds ← inferPats ps (payload ++ [.func [o] result amb (← freshCap)])
        unifyAt s!"the result of the arm for `{x}`" result
          (← inferStmts (binds ++ scope) amb body)
        if ← (ps.take payload.length).allM irrefutable then covered := x :: covered
      else if ps.length == payload.length then
        let binds ← inferPats ps payload
        unifyAt s!"the value the arm for `{x}` resumes with" o
          (← inferStmts (binds ++ scope) amb body)
        if ← ps.allM irrefutable then covered := x :: covered
      else arityError s!"an arm for the operation `{x}`" payload.length ps.length
  for (e, inst) in insts do
    let decl := (s.effects.lookup e).getD ⟨[], []⟩
    unless decl.ops.all covered.contains do
      try unifyRow amb ⟨[(e, inst)], some (← freshRowVar)⟩
      catch err =>
        throw s!"this handler does not handle every `{e}` operation, and the rest cannot \
          be passed on: {err}"
  pure result

end

/-! ## Programs -/

structure FnDecl where
  name : String
  params : List String
  annots : List (Option TypeExpr)
  ret : Option TypeExpr
  clauses : List Clause

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
  for d in decls do
    try
      let rigid := d.params.map fun p => (p, Ty.con s!"'{p}@{d.name}" [])
      let annots ← d.annots.mapM fun
        | some t => some <$> resolveType rigid false t
        | none => pure none
      let ret ← match d.ret with
        | some t => some <$> resolveType rigid false t
        | none => pure none
      let t ← inferCallable [] annots ret (some d.name) d.clauses s!"the clauses of `{d.name}` do"
      unifyAt s!"`{d.name}` is used recursively at a different type" ((group.lookup d.name).getD t) t
      runPending
    catch e =>
      -- The usual cause: the body ends in an expression such as an `if` with no
      -- `else`, whose value becomes the function's result.
      let recursive := (e.splitOn "is used recursively").length > 1
        && (e.splitOn "contains itself").length > 1
      let hint := if recursive then
        "; if the last expression of the body is not meant as the result, end it with `;`"
        else ""
      throw s!"in `{d.name}`: {e}{hint}"
  for d in decls do
    let scheme ← generalize ((group.lookup d.name).getD .unit)
    modify fun s => { s with fns := (d.name, scheme) :: s.fns }
  modify fun s => { s with group := [] }

/-- Check a whole program. -/
def checkProgram (items : List Item) : Except String Unit := do
  let decls : List FnDecl := items.filterMap fun
    | .fn name params annots ret clauses => some ⟨name, params, annots, ret, clauses⟩
    | _ => none
  let names := decls.map (·.name)
  let deps := fun (name : String) =>
    match decls.find? (·.name == name) with
    | some d => ((d.clauses.flatMap (Elab.fvClause [])).filter names.contains).eraseDups
    | none => []
  let action : M Unit := do
    declare items
    for comp in components names deps do
      checkGroup (comp.filterMap fun n => decls.find? (·.name == n))
    match (← get).fns.lookup "main" with
    | none => pure ()
    | some scheme =>
      match ← zonk (← instantiate scheme) with
      | .fn ps _ effs _ _ =>
        unless ps.isEmpty do throw "`main` takes no arguments"
        unless effs.isEmpty do
          throw s!"`main` performs effects that nothing handles: {showEffs effs}"
      | _ => pure ()
  let _ ← action.run {}
  pure ()

end Glorious.Check
