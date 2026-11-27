module

public import Glorious.Lower.Types
public import Glorious.Trace
public import Glorious.Elab

/-!
# Core's types

What the typed lowering needs (`Lower.Typed`): each function at each
signature a closure of it is used at, with the type of each of its `let`s;
and the declared types and operations those use (a `Cert`).

Found from Core as written, by unification: first each group of functions
that refer to each other, in the order they depend on each other, at types
of its own (`Scheme`), every type it did not decide open to each use; then,
from `main`, each function at each signature a use of it gives it, its body
gone through again at those types (`Inst`), which decides the types of its
locals and of the closures it makes.

There are no regions: every reference is to `.cell 0`, and no callable binds
one. Nothing here is checked: the checker of the source text is what the
program is held to; types this gets wrong only make the lowering refuse.
-/

@[expose] public section

namespace Glorious.Typer

open Lower Core Syntax

/-- What is declared, as Core's types are made of it. -/
structure Decls where
  /-- Each declared type's name, by its number in Core (`Ty.data`). -/
  typeNames : Array String := #[]
  typeIds : Std.HashMap String Nat := {}
  /-- Each declared type's parameters, and which are lifetimes. -/
  typeParams : Array (List String) := #[]
  /-- Each constructor, by its tag: its type's number, and its fields as
  written. -/
  ctors : Std.HashMap Nat (Nat × List TypeExpr) := {}
  /-- Each type's constructors' tags, in order. -/
  tagsOf : Std.HashMap Nat (List Nat) := {}
  /-- Each operation, by its identity: its effect's parameters, what it
  takes and what it is resumed with (none: it is not). -/
  ops : Std.HashMap Nat (List String × List TypeExpr × Option TypeExpr) := {}
  /-- Each effect's operations, by the effect's name. -/
  effectOps : Std.HashMap String (List Nat) := {}
  /-- Each top-level function's type parameters and the types written of
  its parameters and result, by its number. -/
  fns : Std.HashMap Nat (List String × List (Option TypeExpr) × Option TypeExpr) := {}

/-- The declarations of `items` (each a declared one, `Elab.declaredOf`), with
the elaborator's numbers for constructors, operations and functions. -/
partial def declsOf (items : List Item) (g : Elab.Globals) : Decls := Id.run do
  let rec flat : List Item → List Item
    | [] => []
    | .pub _ i :: rest => flat (i :: rest)
    | .module _ (some body) :: rest => flat body ++ flat rest
    | i :: rest => i :: flat rest
  let items := flat items
  let mut d : Decls := {}
  for item in items do
    match item with
    | .enum name ps _ | .struct name ps _ =>
      d := { d with typeIds := d.typeIds.insert name d.typeNames.size, typeNames := d.typeNames.push name
                    typeParams := d.typeParams.push (genericParams ps) }
    | _ => pure ()
  for item in items do
    let add := fun (d : Decls) (name c : String) (fields : List TypeExpr) =>
      match g.ctors[c]?, d.typeIds[name]? with
      | some info, some owner =>
        { d with ctors := d.ctors.insert info.tag (owner, fields)
                 tagsOf := d.tagsOf.insert owner (d.tagsOf.getD owner [] ++ [info.tag]) }
      | _, _ => d
    match item with
    | .enum name _ cs => for (c, fields) in cs do d := add d name c fields
    | .struct name _ fields => d := add d name name fields
    | .effect name ps ops =>
      for op in ops do
        if let some info := g.ops.lookup op.name then
          d := { d with ops := d.ops.insert info.id (genericParams ps, op.payload,
                          if op.terminal then none else some (op.result.getD (.tuple [])))
                        effectOps := d.effectOps.insert name (d.effectOps.getD name [] ++ [info.id]) }
    | .fn name ps annots ret _ =>
      if let some f := g.fns[name]? then d := { d with fns := d.fns.insert f (genericParams ps, annots, ret) }
    | _ => pure ()
  pure d


/-- A type being found: `var` one not known yet. A callable's `row` is what it
performs; `env` what it was made with (a tuple of the captures' types, once
known; `never` for a label or a resumption). -/
inductive U where
  | var (id : Nat)
  | int
  | scalar (bits : Int)
  | tuple (fs : List U)
  | data (name : Nat) (args : List U)
  | fn (ps : List U) (r : U) (row : Nat) (env : U) (once : Bool)
  | ref (t : U)
  | never
  deriving Inhabited, BEq

def U.unit : U := .tuple []

/-- Operations performed, each with its effect's type arguments. -/
abbrev Ops := List (Nat × List U)


/-- A row being found: the operations known to be in it, or the row it was
joined to. Rows are open: one can always be found to perform more. -/
inductive RowC where
  | link (to : Nat)
  | ops (ops : Ops)
  deriving Inhabited

/-- A function's signature being found: what it is made with, given and
gives, and what it performs. -/
structure Sig where
  caps : List U
  params : List U
  ret : U
  row : Nat
  deriving Inhabited

/-- What a computation says to the lowering, being found. -/
inductive UHint where
  | ty (t : U)
  /-- After a call that gives an `r`: the type of what is bound, if the
  callee never returns. -/
  | result (r b : U)
  | handler (ρ : U) (H : Ops) (fns : Nat)
  deriving Inhabited

/-- A use of a function inside a computation being found: a closure of it
made, or a handler's function. -/
structure Use where
  fn : Nat
  sig : Sig

/-- What was left undecided of a group of functions: copied with each copy
of a function of it (`copyMember`). -/
structure Asks where
  places : Array (U × Nat × U) := #[]
  coerces : Array (U × U) := #[]
  shows : Array (U × List U) := #[]
  deriving Inhabited

/-- A function as its group found it: its signature, its clauses' hints, and
the uses its body makes, all of the group's types. Each signature it is used
at is a copy of it (`copyMember`). -/
structure Member where
  sig : Sig
  hints : List (Array UHint)
  uses : Array Use
  deriving Inhabited

structure St where
  tys : Array (Option U) := #[]
  rows : Array RowC := #[]
  /-- Fields of types not known yet: `(t, i, r)` says field `i` of a `t` is
  an `r`. -/
  places : Array (U × Nat × U) := #[]
  /-- What a call gives and what is bound to it: the same, unless the call
  never returns. -/
  coerces : Array (U × U) := #[]
  /-- Types that are `never` if nothing says otherwise: what applying a
  label gives. -/
  nevers : Array U := #[]
  /-- What was left undecided of each function's group that its signature
  mentions, by function: what a reference to it copies. -/
  asks : Std.HashMap Nat Asks := {}
  /-- Each function as its group found it, and what was left undecided of
  its group that its hints and uses mention too. -/
  members : Std.HashMap Nat Member := {}
  wholeAsks : Std.HashMap Nat Asks := {}
  /-- The functions of the group being found, at their signatures. -/
  cur : Std.HashMap Nat Sig := {}
  hints : Array UHint := #[]
  uses : Array Use := #[]
  /-- Each variable and row as written out (`zonk`), while nothing is
  decided; let go once something is. -/
  zonked : Std.HashMap Nat Ty := {}
  zonkedRows : Std.HashMap Nat Row := {}
  /-- Closures' environments and what they were made with (`showEnvs`). -/
  shows : Array (U × List U) := #[]
  /-- How many copies of signatures were made, and of asks with them (`GLORIOUS_TRACE`). -/
  copies : Nat := 0
  askCopies : Nat := 0
  placeCopies : Nat := 0
  showCopies : Nat := 0
  /-- Variables that are numbers' if nothing says otherwise: matched by a
  number. -/
  numeric : Std.HashSet Nat := {}
  /-- Variables of what a program sees as of another type (`transmute`, a
  foreign call's result): `anyName`'s if nothing says otherwise, held by the
  machine whatever it is. -/
  seenAs : Std.HashSet Nat := {}

/-- Each function's captures' count, its group, and the declarations. -/
structure Env where
  decls : Decls
  p : Program
  ncaps : Array Nat


/-- (`EStateM`, not `StateT` over `Except`: where a failure is caught, the
state before is not held for it, and every array in the state is changed in
place.) -/
abbrev M := ReaderT Env (EStateM String St)

def freshTy : M U := modifyGet fun s => (.var s.tys.size, { s with tys := s.tys.push none })

def freshTys (n : Nat) : M (List U) := (List.range n).mapM fun _ => freshTy

def freshRowOf (ops : Ops) : M Nat := modifyGet fun s => (s.rows.size, { s with rows := s.rows.push (.ops ops) })

def freshRow : M Nat := freshRowOf []

partial def find (t : U) : M U := do
  match t with
  | .var i => match (← get).tys[i]? with
    | some (some u@(.var _)) =>
      -- (The chain cut short, for the next.)
      let r ← find u
      modify fun s => { s with tys := s.tys.set! i (some r) }
      pure r
    | some (some u) => pure u
    | _ => pure t
  | _ => pure t

partial def findRow (r : Nat) : M Nat := do
  match (← get).rows[r]? with
  | some (.link to) =>
    let root ← findRow to
    if root != to then modify fun s => { s with rows := s.rows.set! r (.link root) }
    pure root
  | _ => pure r

def rowOps (r : Nat) : M Ops := do
  match (← get).rows[← findRow r]? with
  | some (.ops ops) => pure ops
  | _ => pure []

/-- A type, as messages show it. -/
partial def showU (t : U) : M String := do
  match ← find t with
  | .var i => pure s!"?{i}"
  | .int => pure "Int"
  | .scalar b => pure s!"s{b}"
  | .tuple fs => pure ("(" ++ ", ".intercalate (← fs.mapM showU) ++ ")")
  | .data n args => pure (s!"#{n}<" ++ ", ".intercalate (← args.mapM showU) ++ ">")
  | .fn ps r _ _ _ => pure ("fn(" ++ ", ".intercalate (← ps.mapM showU) ++ s!") -> {← showU r}")
  | .ref t => pure ("&" ++ (← showU t))
  | .never => pure "!"

mutual

partial def unify (a b : U) : M Unit := do
  let a ← find a
  let b ← find b
  match a, b with
  | .var i, .var j => if i == j then pure () else bindTy i b
  | .var i, t | t, .var i => bindTy i t
  | .int, .int | .never, .never => pure ()
  | .scalar x, .scalar y => unless x == y do throw s!"s{x} is not s{y}"
  | .tuple xs, .tuple ys => unifyList xs ys
  | .data n xs, .data m ys =>
    if n == m then unifyList xs ys else throw s!"{← showU a} is not {← showU b}"
  | .fn ps r ρ e o, .fn qs s σ f _ =>
    let _ := o
    unifyList ps qs
    unify r s
    unifyRow ρ σ
    unify e f
  | .ref x, .ref y => unify x y
  | _, _ => throw s!"{← showU a} is not {← showU b}"

partial def bindTy (i : Nat) (t : U) : M Unit := do
  if ← occurs i t then throw "a type that holds itself"
  -- (A number's, if nothing says otherwise, still: `numeric`.)
  if let .var j := t then
    if (← get).numeric.contains i then modify fun s => { s with numeric := s.numeric.insert j }
    if (← get).seenAs.contains i then modify fun s => { s with seenAs := s.seenAs.insert j }
  modify fun s => { s with tys := s.tys.set! i (some t) }

partial def occurs (i : Nat) (t : U) : M Bool := do
  match ← find t with
  | .var j => pure (i == j)
  | .tuple fs | .data _ fs => fs.anyM (occurs i)
  | .fn ps r _ e _ => do pure ((← ps.anyM (occurs i)) || (← occurs i r) || (← occurs i e))
  | .ref t => occurs i t
  | _ => pure false

partial def unifyList (xs ys : List U) : M Unit := do
  unless xs.length == ys.length do
    throw s!"{xs.length} types are not {ys.length}"
  for (x, y) in xs.zip ys do unify x y

/-- Two rows made one, with the operations of both. -/
partial def unifyRow (a b : Nat) : M Unit := do
  let a ← findRow a
  let b ← findRow b
  if a == b then return
  let xs ← rowOps a
  let ys ← rowOps b
  modify fun s => { s with rows := s.rows.set! a (.link b) }
  addOps b xs
  let _ := ys

/-- That a row has these operations. -/
partial def addOps (r : Nat) (ops : Ops) : M Unit := do
  for (op, targs) in ops do
    let r ← findRow r
    let held ← rowOps r
    match held.lookup op with
    | some targs' => unifyList targs targs'
    | none => modify fun s => { s with rows := s.rows.set! r (.ops (held ++ [(op, targs)])) }

end

/-- Whether two types can be made one, without making them so: of the same
shape wherever both are known, no variable made to hold itself. -/
partial def unifiable (a b : U) : M Bool := do
  let a ← find a
  let b ← find b
  match a, b with
  | .var i, .var j => pure true <* pure (i == j)
  | .var i, t | t, .var i => do pure !(← occurs i t)
  | .int, .int | .never, .never => pure true
  | .scalar x, .scalar y => pure (x == y)
  | .tuple xs, .tuple ys => all xs ys
  | .data n xs, .data m ys => if n == m then all xs ys else pure false
  | .fn ps r _ e _, .fn qs s _ f _ => do
    pure ((← all ps qs) && (← unifiable r s) && (← unifiable e f))
  | .ref x, .ref y => unifiable x y
  | _, _ => pure false
where
  all (xs ys : List U) : M Bool := do
    if xs.length != ys.length then return false
    (xs.zip ys).allM fun (x, y) => unifiable x y

/-- A type as written, each name as `vars` has it; a name not known, and
what is not written, a type not known yet. -/
partial def writtenU (vars : List (String × U)) : TypeExpr → M U
  | .name x args => do
    if args.isEmpty then
      if let some t := vars.lookup x then return t
    if x == rankedMark then
      return ← match args.getLast? with
        | some inner => writtenU vars inner
        | none => freshTy
    let d := (← read).decls
    if x.startsWith "'" then return .ref .unit
    if x == "Int" then return .int
    if isScalar x then return .scalar (scalarBits x)
    if x == "Fixed" then
      match args with
      | [t, n] => return .data fixedName [← writtenU vars t, ← lengthU n]
      | _ => return ← freshTy
    match d.typeIds[x]? with
    | some id =>
      let given ← args.mapM (writtenU vars)
      -- (A lifetime the type takes that is not written is one of its own.)
      let lifetimes := ((d.typeParams[id]?).getD []).map (·.startsWith "'")
      let mut missing := lifetimes.length - given.length
      let mut rest := given
      let mut out : Array U := #[]
      for isLifetime in lifetimes do
        if isLifetime && missing > 0 then
          out := out.push (.ref .unit)
          missing := missing - 1
        else
          match rest with
          | a :: more =>
            out := out.push a
            rest := more
          | [] => out := out.push (← freshTy)
      pure (.data id (out.toList ++ rest))
    | none => freshTy
  | .tuple ts => do pure (.tuple (← ts.mapM (writtenU vars)))
  | .fn ps r => do
    -- (`fn(..P) -> R`: of as many as `P` has, not known here.)
    if ps.any (fun | .name n _ => n == spreadParams | _ => false) then return ← freshTy
    pure (.fn (← ps.mapM (writtenU vars)) (← writtenU vars r) (← freshRow) (← freshTy) false)
  | .performs r _ => writtenU vars r
  | .ref _ t _ => do pure (.ref (← writtenU vars t))
  | .never | .hole => freshTy
where
  /-- A `[T; N]`'s length, a type of its own. -/
  lengthU (n : TypeExpr) : M U := do
    let rec count : TypeExpr → Option Nat
      | .name "Z" [] | .name "%prelude::Z" [] => some 0
      | .name b [inner] =>
        if b.endsWith "B0" then (count inner).map (2 * ·)
        else if b.endsWith "B1" then (count inner).map (2 * · + 1)
        else none
      | _ => none
    match count n with
    | some k => pure (.data (lenBase + k) [])
    | none => freshTy

/-- A declared type's arguments, not known yet: a lifetime's, a reference to
nothing. -/
def argsFor (params : List String) : M (List (String × U)) :=
  params.mapM fun p => do pure (p, ← if p.startsWith "'" then pure (U.ref .unit) else freshTy)

/-- What a constructor builds and its fields, at arguments not known yet. -/
def instCtor (tag : Nat) : M (U × List U) := do
  if fixedBase ≤ tag then
    let t ← freshTy
    return (.data fixedName [t, .data (lenBase + (tag - fixedBase)) []], List.replicate (tag - fixedBase) t)
  let d := (← read).decls
  let some (owner, fields) := d.ctors[tag]? | throw s!"constructor {tag} is not declared"
  let vars ← argsFor ((d.typeParams[owner]?).getD [])
  pure (.data owner (vars.map (·.2)), ← fields.mapM (writtenU vars))

/-- An operation at type arguments not known yet: those, what it takes, and
what it is resumed with. -/
def instOp (op : Nat) : M (List U × List U × Option U) := do
  let d := (← read).decls
  let some (ps, payload, result) := d.ops[op]? | throw s!"operation {op} is not declared"
  let vars ← argsFor ps
  pure (vars.map (·.2), ← payload.mapM (writtenU vars), ← result.mapM (writtenU vars))

/-- The fields of a value of type `t`, if its type is known well enough to
say: a tuple, or a type of one constructor, or a `[T; N]`'s elements. -/
def fieldsNow (t : U) (i : Nat) : M (Option U) := do
  match ← find t with
  | .tuple fs => match fs[i]? with
    | some f => pure (some f)
    | none => throw s!"a tuple of {fs.length} has no field {i}"
  | .data n args =>
    if n == fixedName then
      match args with
      | e :: _ => pure (some e)
      | [] => throw "a `[T; N]` of no element type"
    else
      let d := (← read).decls
      match d.tagsOf[n]? with
      | some [tag] =>
        let some (_, fields) := d.ctors[tag]? | throw s!"constructor {tag} is not declared"
        let vars := ((d.typeParams[n]?).getD []).zip args
        match fields[i]? with
        | some f => pure (some (← writtenU vars f))
        | none => throw s!"constructor {tag} has no field {i}"
      | _ => throw "a field of a type of several constructors"
  | .var _ => pure none
  | _ => throw "a field of what has none"

def field (t : U) (i : Nat) : M U := do
  match ← fieldsNow t i with
  | some f => pure f
  | none =>
    let r ← freshTy
    modify fun s => { s with places := s.places.push (t, i, r) }
    pure r

def atomTy (Γ : Array U) : Atom → M U
  | .var i => match Γ[i]? with
    | some t => pure t
    | none => throw s!"local {i} does not exist"
  | .int _ => pure .int

def hint (h : UHint) : M Unit := modify fun s => { s with hints := s.hints.push h }

/-- A call gives an `r` where a `b` is wanted: the same, unless the call does
not return. -/
def coerce (r b : U) : M Unit := do
  match ← find r with
  | .never => pure ()
  | .var _ => modify fun s => { s with coerces := s.coerces.push (r, b) }
  | _ => unify r b

/-- That `amb` performs `op` at `targs`. -/
def requireOp (amb : Nat) (op : Nat) (targs : List U) : M Unit := addOps amb [(op, targs)]

def setRow (r : Nat) (ops : Ops) : M Unit := modify fun s => { s with rows := s.rows.set! r (.ops ops) }

/-- A copy of a function as its group found it, and of what was left
undecided of the group, every variable in them new; the copy of what was
left undecided is put with what is to be decided now. -/
partial def copyMember (m : Member) (asks : Asks) : M Member := do
  modify fun s => { s with copies := s.copies + 1, askCopies := s.askCopies + asks.places.size + asks.coerces.size
                           placeCopies := s.placeCopies + asks.places.size, showCopies := s.showCopies + asks.shows.size }
  let ((m, asks), _) ← (go m asks).run ({}, {})
  modify fun s => { s with places := s.places ++ asks.places, coerces := s.coerces ++ asks.coerces
                           shows := s.shows ++ asks.shows }
  pure m
where
  go (m : Member) (asks : Asks) : StateT (Std.HashMap Nat U × Std.HashMap Nat Nat) M (Member × Asks) := do
    let m : Member := { sig := ← sig m.sig, hints := ← m.hints.mapM (·.mapM hint), uses := ← m.uses.mapM fun u => do pure ⟨u.fn, ← sig u.sig⟩ }
    let places ← asks.places.mapM fun (t, i, r) => do pure (← ty t, i, ← ty r)
    let coerces ← asks.coerces.mapM fun (r, b) => do pure (← ty r, ← ty b)
    let shows ← asks.shows.mapM fun (e, cs) => do pure (← ty e, ← cs.mapM ty)
    pure (m, { places, coerces, shows })
  sig (s : Sig) : StateT (Std.HashMap Nat U × Std.HashMap Nat Nat) M Sig := do
    pure ⟨← s.caps.mapM ty, ← s.params.mapM ty, ← ty s.ret, ← row s.row⟩
  hint : UHint → StateT (Std.HashMap Nat U × Std.HashMap Nat Nat) M UHint
    | .ty t => do pure (.ty (← ty t))
    | .result r b => do pure (.result (← ty r) (← ty b))
    | .handler ρ H n => do pure (.handler (← ty ρ) (← H.mapM fun (op, ts) => do pure (op, ← ts.mapM ty)) n)
  ty (t : U) : StateT (Std.HashMap Nat U × Std.HashMap Nat Nat) M U := do
    -- (Each variable's once, bound or not: what is reached through many
    -- is copied once, and shared.)
    if let .var v := t then
      if let some u := (← get).1[v]? then return u
    let found ← find t
    let u ← match found with
      | .var i =>
        match (← get).1[i]? with
        | some u => pure u
        | none =>
          let u ← freshTy
          if (← getThe St).numeric.contains i then
            if let .var j := u then modifyThe St fun s => { s with numeric := s.numeric.insert j }
          if (← getThe St).seenAs.contains i then
            if let .var j := u then modifyThe St fun s => { s with seenAs := s.seenAs.insert j }
          modify fun (m, r) => (m.insert i u, r)
          pure u
      | other => tyFound other
    if let .var v := t then modify fun (m, r) => (m.insert v u, r)
    pure u
  tyFound (t : U) : StateT (Std.HashMap Nat U × Std.HashMap Nat Nat) M U := do
    match t with
    | .var _ => pure t
    | .int => pure .int
    | .scalar b => pure (.scalar b)
    | .tuple fs => pure (.tuple (← fs.mapM ty))
    | .data n args => pure (.data n (← args.mapM ty))
    | .fn ps r ρ e o => pure (.fn (← ps.mapM ty) (← ty r) (← row ρ) (← ty e) o)
    | .ref t => pure (.ref (← ty t))
    | .never => pure .never
  row (r : Nat) : StateT (Std.HashMap Nat U × Std.HashMap Nat Nat) M Nat := do
    let r ← findRow r
    match (← get).2[r]? with
    | some r' => pure r'
    | none =>
      let r' ← freshRow
      modify fun (m, rs) => (m, rs.insert r r')
      let ops ← rowOps r
      let ops ← ops.mapM fun (op, targs) => do pure (op, ← targs.mapM ty)
      setRow r' ops
      pure r'

/-- The signature to use for a reference to `fn`: its group's own inside
its group, else a copy of its general one. -/
def refSig (fn : Nat) : M Sig := do
  -- (Only what is read is taken from the state: held whole while a copy is
  -- made, its arrays would be copied by the first change.)
  if let some sig := (← get).cur[fn]? then return sig
  let some m := (← get).members[fn]? | throw s!"function {fn} is used before it is found"
  let asks := ((← get).asks[fn]?).getD {}
  pure (← copyMember { m with hints := [], uses := #[] } asks).sig

/-- The type of a closure of a function at a signature. -/
def closureTy (sig : Sig) : M U := do
  let env ← freshTy
  modify fun s => { s with shows := s.shows.push (env, sig.caps) }
  pure (.fn sig.params sig.ret sig.row env false)

/-- Each closure's environment made its captures' types, where that can be:
not where it would make a type hold itself (a closure that captured a
resumption whose result is a closure of it). -/
def showEnvs : M Unit := do
  let shows := (← get).shows
  modify fun s => { s with shows := #[] }
  for (env, caps) in shows do
    if ← unifiable env (.tuple caps) then
      try unify env (.tuple caps) catch _ => pure ()
    else
      -- (Not where it would hold itself.)
      if let .var v ← find env then
        if ← occurs v (.tuple caps) then continue
      throw s!"a closure made with ({", ".intercalate (← caps.mapM showU)}) where one with {← showU env} is taken"

def use (fn : Nat) (sig : Sig) : M Unit := modify fun s => { s with uses := s.uses.push ⟨fn, sig⟩ }

mutual

partial def inferPat (p : Pat) (t : U) : M (List U) := do
  match p with
  | .wild => pure []
  | .bind => pure [t]
  | .int _ =>
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
        throw s!"a pattern of constructor {tag} has {ps.length} fields"
      inferPats ps fields

partial def inferPats (ps : List Pat) (ts : List U) : M (List U) := do
  let mut out : List U := []
  for (p, t) in ps.zip ts do
    out := out ++ (← inferPat p t)
  pure out

end

def inferRhs (Γ : Array U) : Rhs → M U
  | .atom a => atomTy Γ a
  | .prim p args => do
    match p, args with
    | .cast b into, [a] =>
      if into then do unify (← atomTy Γ a) .int; pure (.scalar b)
      else do unify (← atomTy Γ a) (.scalar b); pure .int
    | .fixed 0, [a, .int n] => do
      pure (.data fixedName [← atomTy Γ a, .data (lenBase + n.toNat) []])
    | .fixed op, a :: rest => do
      let t ← freshTy
      let fixed := U.data fixedName [t, ← freshTy]
      unify (← atomTy Γ a) fixed
      match op, rest with
      | 2, [i] => do unify (← atomTy Γ i) .int; pure t
      | 3, [i, v] => do unify (← atomTy Γ i) .int; unify (← atomTy Γ v) t; pure fixed
      | 4, [] => pure .int
      | _, _ => throw "an intrinsic of `[T; N]` is given what it does not take"
    | _, _ =>
      for a in args do unify (← atomTy Γ a) .int
      pure .int
  | .construct tag args => do
    let ts ← args.mapM (atomTy Γ)
    if tag == 0 then return .tuple ts
    let (result, fields) ← instCtor tag
    unless fields.length == ts.length do
      throw s!"constructor {tag} is given {ts.length} fields"
    -- (A number written out is a scalar's where the field is one.)
    for ((a, t), f) in (args.zip ts).zip fields do
      match a, ← find f with
      | .int _, .scalar _ => pure ()
      | _, _ => unify t f
    pure result
  | .place pl => do
    let mut t ← atomTy Γ (.var pl.var)
    for i in pl.path do t ← field t i
    pure t
  | .closure fn captures => do
    let sig ← refSig fn
    unifyList (← captures.mapM (atomTy Γ)) sig.caps
    use fn sig
    closureTy sig

/-- A handler's functions: what it serves, in the order of `ops`. -/
def inferHandler (amb : Nat) (Γ : Array U) (ret : Nat) (ops : List (Nat × Nat))
    (captures : List Atom) (σ ρ : U) : M Ops := do
  let Cs ← captures.mapM (atomTy Γ)
  let retSig ← refSig ret
  unifyList Cs retSig.caps
  unifyList [σ] retSig.params
  unify ρ retSig.ret
  unifyRow retSig.row amb
  use ret retSig
  let mut H : Ops := []
  let mut shared : List (Nat × List U) := []
  for (op, arm) in ops do
    let (targs, payload, result) ← instOp op
    -- (Operations of one effect share its arguments.)
    let effect := effectOf (← read).decls op
    let targs ← match shared.lookup effect with
      | some ts => do unifyList targs ts; pure ts
      | none => do shared := (effect, targs) :: shared; pure targs
    H := H ++ [(op, targs)]
    let armSig ← refSig arm
    unifyList Cs armSig.caps
    let params := match result with
      | some o => payload ++ [.fn [o] ρ amb .never true]
      | none => payload
    unifyList params armSig.params
    unify ρ armSig.ret
    unifyRow armSig.row amb
    use arm armSig
  pure H
where
  effectOf (d : Decls) (op : Nat) : Nat :=
    (d.effectOps.toList.findIdx? fun (_, ops) => ops.contains op).getD op

mutual

/-- A computation that gives a `τ` and may perform what `amb` has. -/
partial def inferTm (amb : Nat) (τ : U) (Γ : Array U) (tm : Tm) : M Unit :=
  tryCatch (inferTm' amb τ Γ tm) fun e =>
    throw (if (e.splitOn " (at local ").length > 1 then e else s!"{e} (at local {Γ.size})")

partial def inferTm' (amb : Nat) (τ : U) (Γ : Array U) : Tm → M Unit
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
  | .tail f args => do coerce (← applied Γ amb f args) τ
  | .handle ret ops captures thunk body => do
    let σ ← freshTy
    let ρ ← freshTy
    let εt ← freshRow
    unify (← atomTy Γ thunk) (.fn [] σ εt (← freshTy) false)
    let H ← inferHandler amb Γ ret ops captures σ ρ
    unifyRow εt amb
    hint (.handler ρ H ops.length)
    inferTm amb τ (Γ.push ρ) body
  | .handleTail ret ops captures thunk => do
    let σ ← freshTy
    let εt ← freshRow
    unify (← atomTy Γ thunk) (.fn [] σ εt (← freshTy) false)
    let H ← inferHandler amb Γ ret ops captures σ τ
    unifyRow εt amb
    hint (.handler τ H ops.length)
  | .raise op args => do
    let (targs, payload, _) ← instOp op
    unifyList (← args.mapM (atomTy Γ)) payload
    requireOp amb op targs
  | .perform op args body => do
    let (targs, payload, result) ← instOp op
    unifyList (← args.mapM (atomTy Γ)) payload
    requireOp amb op targs
    inferTm amb τ (Γ.push (result.getD .unit)) body
  | .label thunk body => do
    let σ ← scope Γ amb thunk
    inferTm amb τ (Γ.push σ) body
  | .labelTail thunk => do unify (← scope Γ amb thunk) τ
  | .guard cleanup thunk body => do
    let σ ← guarded Γ amb cleanup thunk
    inferTm amb τ (Γ.push σ) body
  | .guardTail cleanup thunk => do unify (← guarded Γ amb cleanup thunk) τ
  | .cancel _ body => inferTm amb τ (Γ.push .unit) body
  | .cell init thunk body | .cellL _ init thunk body => do
    let ρ ← freshTy
    unify (← atomTy Γ thunk) (.fn [.ref (← atomTy Γ init)] ρ (← inferTm'.within amb) (← freshTy) false)
    inferTm amb τ (Γ.push ρ) body
  | .cellTail init thunk | .cellTailL _ init thunk => do
    unify (← atomTy Γ thunk) (.fn [.ref (← atomTy Γ init)] τ (← inferTm'.within amb) (← freshTy) false)
  | .lend _ r thunk pre post body => do
    let ρ ← freshTy
    let σ ← freshTy
    unify (← atomTy Γ r) (.ref σ)
    let before ← pre.mapM (atomTy Γ)
    let after ← post.mapM (atomTy Γ)
    unify (← atomTy Γ thunk) (.fn (before ++ .ref σ :: after) ρ (← inferTm'.within amb) (← freshTy) false)
    inferTm amb τ (Γ.push ρ) body
  | .mem op args body => do
    let ts ← args.mapM (atomTy Γ)
    let int := fun (t : U) => unify t .int
    let addr := fun (t : U) => unify t (.scalar (-64))
    let σ ← match op, ts with
      | .alloc, [s, a] => do addr s; addr a; pure (.scalar (-64))
      | .free, [a] => do addr a; pure .unit
      | .readBits, [a, w] => do addr a; int w; pure .int
      | .writeBits, [a, w, v] => do addr a; int w; int v; pure .unit
      | .copy, [a, b, n] => do addr a; addr b; addr n; pure .unit
      | .sizeOf, [_] | .alignOf, [_] | .staticAt, _ => pure (.scalar (-64))
      | .addressOf, [r, _] =>
        match args with
        | [_, .int tag] => do
          let elem ← freshTy
          unify r (.ref (.data fixedName [elem, ← freshTy]))
          let (whole, _) ← instCtor tag.toNat
          match ← find whole with
          | .data _ (t :: _) => do unify t elem; pure whole
          | _ => throw "a pointer of a type with no argument"
        | _ => throw "a `[T; N]`'s address without its pointer's constructor"
      | .deref, [p, a, _] =>
        match args with
        | [_, _, .int tag] => do
          addr a
          let (whole, _) ← instCtor tag.toNat
          unify p whole
          match ← find whole with
          | .data _ (t :: _) => pure (.ref t)
          | _ => throw "a pointer of a type with no argument"
        | _ => throw "a pointer without its type's constructor"
      | .load, [t] => do
        let σ ← freshTy
        unify t (.ref σ)
        pure σ
      | .store, [t, v] => do unify t (.ref v); pure .unit
      | .swap, [t, v] => do unify t (.ref v); pure v
      | .tag, t :: _ => do unify t (.ref (← freshTy)); pure .int
      | .focus, [t, _] => do
        let σ ← freshTy
        unify t (.ref σ)
        match args with
        | [_, .int i] => pure (.ref (← field σ i.toNat))
        | _ => throw "a memory operation has the wrong number of arguments"
      | .focus, [t, _, _] =>
        match args with
        | [_, ix, .int (-1)] => do
          unify (← atomTy Γ ix) .int
          let elem ← freshTy
          unify t (.ref (.data fixedName [elem, ← freshTy]))
          pure (.ref elem)
        | [_, .int i, .int built] => do
          if built ≤ 0 || fixedBase ≤ built.toNat then
            throw "a reference into a constructor's field names no constructor"
          let (whole, fields) ← instCtor built.toNat
          unify t (.ref whole)
          match fields[i.toNat]? with
          | some σ => pure (.ref σ)
          | none => throw s!"constructor {built} has no field {i}"
        | _ => throw "a memory operation has the wrong number of arguments"
      | _, _ => throw "a memory operation has the wrong number of arguments"
    inferTm amb τ (Γ.push σ) body
  | .host id args body => do
    let ts ← args.mapM (atomTy Γ)
    let int := fun (t : U) => unify t .int
    let σ ← match id, ts with
      | 0, [_] => pure U.unit
      | 1, [] => pure (U.tuple [.int, .int])
      | 2, _ => do ts.forM int; pure .int
      | 5, [_, n] => do int n; pure (.scalar (-64))
      | 6, [v, of] => do unify of (.data fixedName [v, .data lenBase []]); pure .int
      | 7, [c, of] => do
        int c
        let v ← freshTy
        unify of (.data fixedName [v, .data lenBase []])
        pure v
      | 8, [c, v, of] => do int c; unify of (.data fixedName [v, .data lenBase []]); pure .unit
      | 9, [v, i] => do int i; pure (U.tuple [.int, v])
      | 10, [] => pure (U.tuple [.int, .int])
      | 14, [_] => do
        let t ← freshTy
        if let .var v := t then modify fun s => { s with seenAs := s.seenAs.insert v }
        pure t
      | 21, [c] => do int c; pure .unit
      | 22, [] => pure .unit
      | _, _ => throw s!"host operation {id} does not exist with {args.length} arguments"
    if 2 ≤ id then hint (.ty σ)
    inferTm amb τ (Γ.push σ) body
where
  /-- A call: what the callee performs, the caller does. -/
  applied (Γ : Array U) (amb : Nat) (f : Atom) (args : List Atom) : M U := do
    let σ ← freshTy
    let given ← args.mapM (atomTy Γ)
    unify (← atomTy Γ f) (.fn given σ (← within amb) (← freshTy) false)
    pure σ
  /-- The row of what is called or run here: the code around's own. (One
  row for both, not one within the other: a function's signature is then
  the same wherever it is used, and few are made.) -/
  within (amb : Nat) : M Nat := pure amb
  /-- A label's scope: the callable it runs is given the label, which does
  not return unless something uses it as a callable with a result. -/
  scope (Γ : Array U) (amb : Nat) (thunk : Atom) : M U := do
    let σ ← freshTy
    let ρ ← freshTy
    modify fun s => { s with nevers := s.nevers.push ρ }
    unify (← atomTy Γ thunk) (.fn [.fn [σ] ρ (← freshRow) .never false] σ (← within amb) (← freshTy) false)
    pure σ
  guarded (Γ : Array U) (amb : Nat) (cleanup thunk : Atom) : M U := do
    let σ ← freshTy
    unify (← atomTy Γ cleanup) (.fn [] (← freshTy) (← freshRow) (← freshTy) false)
    unify (← atomTy Γ thunk) (.fn [] σ (← within amb) (← freshTy) false)
    pure σ

end

/-- Decide what can be: fields of types now known, calls' results, and what
handled computations perform beyond their handlers. -/
partial def settle : M Unit := do
  let mut changed := true
  while changed do
    changed := false
    let places := (← get).places
    let coerces := (← get).coerces
    modify fun s => { s with places := #[], coerces := #[] }
    for (t, i, r) in places do
      match ← fieldsNow t i with
      | some f => do
        tryCatch (unify f r) fun e => do throw s!"{e} (field {i} of {← showU t})"
        changed := true
      | none => modify fun s => { s with places := s.places.push (t, i, r) }
    for (r, b) in coerces do
      match ← find r with
      | .never => changed := true
      | .var _ => modify fun s => { s with coerces := s.coerces.push (r, b) }
      | _ => do
        tryCatch (unify r b) fun e => do throw s!"{e} (what a call gives)"
        changed := true

/-- What nothing decided, decided: a call's result is what is bound to it,
a label's result `never`. -/
def finish : M Unit := do
  settle
  -- (What is read a part at a time and nothing else says the type of is a
  -- tuple of as many parts as are read.)
  let mut widths : Std.HashMap Nat Nat := {}
  for (t, i, _) in (← get).places do
    if let .var v ← find t then widths := widths.insert v (max (widths.getD v 0) (i + 1))
  for (v, n) in widths.toList do
    if let .var _ ← find (.var v) then unify (.var v) (.tuple (← freshTys n))
  settle
  for ρ in (← get).nevers do
    if let .var _ ← find ρ then unify ρ .never
  settle
  for (r, b) in (← get).coerces do
    if let .var _ ← find r then unify r b
  modify fun s => { s with coerces := #[] }
  showEnvs
  settle

mutual

/-- A type found, as the lowering reads it: what nothing decided is `()`, as
no value of it is looked at (a number's, if a number was matched against it;
`anyName`'s, if a value is seen as of it, `transmute`). Each
variable's once: a type found is shared where it is reached through many
variables, and written out again for each would be as large as every way of
reaching it. -/
partial def zonk (t : U) : M Ty := do
  if let .var v := t then
    if let some z := (← get).zonked[v]? then return z
    let z ← zonkFound (← find t)
    modify fun s => { s with zonked := s.zonked.insert v z }
    return z
  zonkFound t

partial def zonkFound (t : U) : M Ty := do
  match t with
  | .var i => do
    if (← get).numeric.contains i then pure .int
    else if (← get).seenAs.contains i then pure (.data anyName [])
    else pure .unit
  | .int => pure .int
  | .scalar b => pure (.scalar b)
  | .tuple fs => pure (.tuple (← fs.mapM zonk))
  | .data n args => pure (.data n (← args.mapM zonk))
  | .fn ps r row env once =>
    let env ← match ← find env with
      | .tuple cs => do pure (some (← cs.mapM zonk))
      | _ => pure none
    pure (.fn (← ps.mapM zonk) (← zonk r) (← zonkRow row) once env)
  | .ref t => pure (.ref (← zonk t))
  | .never => pure .never

/-- A row found, its operations in order, each once. -/
partial def zonkRow (r : Nat) : M Row := do
  let r ← findRow r
  if let some z := (← get).zonkedRows[r]? then return z
  let ops ← (← rowOps r).mapM fun (op, targs) => do pure (op, ← targs.mapM zonk)
  let once := ops.foldl (fun acc e => if acc.any (·.1 == e.1) then acc else acc ++ [e]) []
  let z := once.mergeSort fun a b => a.1 ≤ b.1
  modify fun s => { s with zonkedRows := s.zonkedRows.insert r z }
  pure z

end

def zonkOps (H : Ops) : M Row := H.mapM fun (op, targs) => do pure (op, ← targs.mapM zonk)

def zonkSig (sig : Sig) : M FnSig := do
  pure { caps := ← sig.caps.mapM zonk, params := ← sig.params.mapM zonk, ret := ← zonk sig.ret
         eff := ← zonkRow sig.row }

def zonkHint : UHint → M (List Hint)
  | .ty t => do pure [.ty (← zonk t)]
  | .result r b => do if (← zonk r) == .never then pure [.ty (← zonk b)] else pure []
  | .handler ρ H _ => do pure [.handler (← zonk ρ) (← zonkOps H)]

/-- A type of the certificate, as one being found. -/
partial def ofTy : Ty → M U
  | .int => pure .int
  | .scalar b => pure (.scalar b)
  | .tuple fs => do pure (.tuple (← fs.mapM ofTy))
  | .data n args => do
    if n == anyName then freshTy else pure (.data n (← args.mapM ofTy))
  | .fn ps r eff once env => do
    let ops ← eff.mapM fun (op, targs) => do pure (op, ← targs.mapM ofTy)
    let env ← match env with
      | some cs => do pure (U.tuple (← cs.mapM ofTy))
      | none => freshTy
    pure (.fn (← ps.mapM ofTy) (← ofTy r) (← freshRowOf ops) env once)
  | .ref t => do pure (.ref (← ofTy t))
  | .never => pure .never

/-- The functions each function refers to. -/
partial def refsOf : Tm → List Nat
  | .let_ (.closure f _) b => f :: refsOf b
  | .let_ _ b | .call _ _ b | .perform _ _ b | .label _ b | .guard _ _ b | .cancel _ b
  | .cell _ _ b | .cellL _ _ _ b | .lend _ _ _ _ _ b | .mem _ _ b | .host _ _ b => refsOf b
  | .handle ret ops _ _ b => ret :: ops.map (·.2) ++ refsOf b
  | .handleTail ret ops _ _ => ret :: ops.map (·.2)
  | _ => []

/-- How many values each function is made with, where it is made. -/
partial def capsOf : Tm → List (Nat × Nat)
  | .let_ (.closure f cs) b => (f, cs.length) :: capsOf b
  | .let_ _ b | .call _ _ b | .perform _ _ b | .label _ b | .guard _ _ b | .cancel _ b
  | .cell _ _ b | .cellL _ _ _ b | .lend _ _ _ _ _ b | .mem _ _ b | .host _ _ b => capsOf b
  | .handle ret ops cs _ b => (ret :: ops.map (·.2)).map (·, cs.length) ++ capsOf b
  | .handleTail ret ops cs _ => (ret :: ops.map (·.2)).map (·, cs.length)
  | _ => []

/-- The groups of functions that refer to each other, each after those it
refers to (Tarjan's). -/
partial def groups (refs : Array (List Nat)) : List (List Nat) := Id.run do
  let n := refs.size
  let mut index : Array (Option Nat) := Array.replicate n none
  let mut low : Array Nat := Array.replicate n 0
  let mut onStack : Array Bool := Array.replicate n false
  let mut stack : List Nat := []
  let mut out : Array (List Nat) := #[]
  let mut counter := 0
  for root in [0:n] do
    if index[root]!.isSome then continue
    -- (Each frame: a function and the references of it still to look at.)
    let mut work : List (Nat × List Nat) := [(root, refs[root]!)]
    index := index.set! root (some counter)
    low := low.set! root counter
    counter := counter + 1
    stack := root :: stack
    onStack := onStack.set! root true
    while !work.isEmpty do
      match work with
      | (v, w :: rest) :: more =>
        work := (v, rest) :: more
        if w < n then
          match index[w]! with
          | none =>
            index := index.set! w (some counter)
            low := low.set! w counter
            counter := counter + 1
            stack := w :: stack
            onStack := onStack.set! w true
            work := (w, refs[w]!) :: work
          | some iw =>
            if onStack[w]! then low := low.set! v (min low[v]! iw)
      | (v, []) :: more =>
        work := more
        if let (u, _) :: _ := more then low := low.set! u (min low[u]! low[v]!)
        if some low[v]! == index[v]! then
          let mut comp : List Nat := []
          let mut going := true
          while going do
            match stack with
            | x :: xs =>
              stack := xs
              onStack := onStack.set! x false
              comp := x :: comp
              if x == v then going := false
            | [] => going := false
          out := out.push comp
      | [] => pure ()
  pure out.toList

/-- What a function says of its parameters and result, where it says it. -/
def declaredParams (f : Nat) (sig : Sig) : M Unit := do
  let some (tparams, annots, written) := (← read).decls.fns[f]? | return
  unless annots.length == sig.params.length do return
  let vars ← tparams.mapM fun p => do pure (p, ← freshTy)
  for (p, annot) in (sig.params ++ [sig.ret]).zip (annots ++ [written]) do
    if let some te := annot then
      match te with
      | .name .. | .tuple _ | .ref .. =>
        -- (Where what is written cannot be said of Core's type, as of a
        -- parameter that is a dictionary of implementations, it is not.)
        let w ← writtenU vars te
        if ← unifiable p w then
          try unify p w catch _ => pure ()
      | _ => pure ()

/-- The variables and rows a type mentions, added to `seen`. -/
partial def mentions (t : U) (seen : Std.HashSet Nat × Std.HashSet Nat) :
    M (Std.HashSet Nat × Std.HashSet Nat) := do
  match ← find t with
  | .var i => pure (seen.1.insert i, seen.2)
  | .tuple fs | .data _ fs => fs.foldlM (fun s f => mentions f s) seen
  | .fn ps r row e _ => do
    let seen ← (ps ++ [r, e]).foldlM (fun s f => mentions f s) seen
    mentionsRow row seen
  | .ref t => mentions t seen
  | _ => pure seen
where
  mentionsRow (row : Nat) (seen : Std.HashSet Nat × Std.HashSet Nat) : M (Std.HashSet Nat × Std.HashSet Nat) := do
    let r ← findRow row
    if seen.2.contains r then return seen
    let seen := (seen.1, seen.2.insert r)
    (← rowOps r).foldlM (fun s (_, targs) => targs.foldlM (fun s t => mentions t s) s) seen

/-- What a group left undecided that `roots` can still be decided by: what
mentions them, and what that mentions, and so on. (The rest can change
nothing a copy sees: taken with every copy, it would grow with every group
that uses another.) -/
def liveAsks (roots : List U) (rows : List Nat) : M Asks := do
  let mut live : Std.HashSet Nat × Std.HashSet Nat := ({}, {})
  for t in roots do live ← mentions t live
  for r in rows do live ← mentions.mentionsRow r live
  let places := (← get).places.toList.zipIdx
  let coerces := (← get).coerces.toList.zipIdx
  let shows := (← get).shows.toList.zipIdx
  let mut keepP : Std.HashSet Nat := {}
  let mut keepC : Std.HashSet Nat := {}
  let mut keepS : Std.HashSet Nat := {}
  let touches := fun (live : Std.HashSet Nat × Std.HashSet Nat) (m : Std.HashSet Nat × Std.HashSet Nat) =>
    m.1.toList.any live.1.contains || m.2.toList.any live.2.contains
  let mut changed := true
  while changed do
    changed := false
    for ((t, _, r), k) in places do
      unless keepP.contains k do
        if touches live (← mentions r (← mentions t ({}, {}))) then
          keepP := keepP.insert k
          live ← mentions r (← mentions t live)
          changed := true
    for ((r, b), k) in coerces do
      unless keepC.contains k do
        if touches live (← mentions b (← mentions r ({}, {}))) then
          keepC := keepC.insert k
          live ← mentions b (← mentions r live)
          changed := true
    for ((e, cs), k) in shows do
      unless keepS.contains k do
        if touches live (← mentions e ({}, {})) then
          keepS := keepS.insert k
          live ← cs.foldlM (fun l c => mentions c l) live
          changed := true
  pure { places := (places.filter fun (_, k) => keepP.contains k).map (·.1) |>.toArray
         coerces := (coerces.filter fun (_, k) => keepC.contains k).map (·.1) |>.toArray
         shows := (shows.filter fun (_, k) => keepS.contains k).map (·.1) |>.toArray }

/-- The types and rows a function as found mentions. -/
def Member.roots (m : Member) : List U × List Nat :=
  let sigTys := fun (s : Sig) => s.caps ++ s.params ++ [s.ret]
  let hintTys : UHint → List U
    | .ty t => [t]
    | .result r b => [r, b]
    | .handler ρ H _ => ρ :: H.flatMap (·.2)
  (sigTys m.sig ++ m.hints.flatMap (·.toList.flatMap hintTys) ++ m.uses.toList.flatMap (sigTys ·.sig),
   m.sig.row :: m.uses.toList.map (·.sig.row))

/-- Each function as its group finds it, group by group. -/
def inferGroups : M Unit := do
  let env ← read
  let fns := env.p.fns
  let refs := fns.map fun F => (F.clauses.flatMap (refsOf ·.body)).eraseDups
  for grp in groups refs do
    let mut cur : Std.HashMap Nat Sig := {}
    for f in grp do
      let arity := match fns[f]? with
        | some ⟨c :: _⟩ => c.pats.length
        | _ => 0
      let sig : Sig := ⟨← freshTys ((env.ncaps[f]?).getD 0), ← freshTys arity, ← freshTy, ← freshRow⟩
      declaredParams f sig
      cur := cur.insert f sig
    modify fun s => { s with cur, places := #[], coerces := #[], nevers := #[], shows := #[] }
    let mut members : List (Nat × Member) := []
    for f in grp do
      let sig := cur[f]!
      modify fun s => { s with uses := #[] }
      let mut hints : List (Array UHint) := []
      for c in ((fns[f]?).map (·.clauses)).getD [] do
        modify fun s => { s with hints := #[] }
        try
          let binds ← inferPats c.pats sig.params
          inferTm sig.row sig.ret (sig.params ++ sig.caps ++ binds).toArray c.body
        catch e => throw (if (e.splitOn "(in function ").length > 1 then e else s!"{e} (in function {f})")
        hints := hints ++ [(← get).hints]
      members := members ++ [(f, { sig, hints, uses := (← get).uses })]
    tryCatch settle fun e => throw s!"{e} (in the group of function {grp.headD 0})"
    -- (Labels' results are decided here: nothing outside the group can say
    -- more of them.)
    for ρ in (← get).nevers do
      if let .var _ ← find ρ then unify ρ .never
    settle
    -- (A call whose result is not known yet, and that nothing outside the
    -- group can say more of, gives what is bound to it. One the group's
    -- signatures mention stays to be decided where it is used: what a
    -- label a block was given gives, which is `!` where the label is made.)
    let mut sigLive : Std.HashSet Nat × Std.HashSet Nat := ({}, {})
    for (_, m) in members do
      for t in m.sig.caps ++ m.sig.params ++ [m.sig.ret] do sigLive ← mentions t sigLive
    let coerces := (← get).coerces
    modify fun s => { s with coerces := #[] }
    for (r, b) in coerces do
      match ← find r with
      | .var v =>
        if sigLive.1.contains v then modify fun s => { s with coerces := s.coerces.push (r, b) }
        else tryCatch (unify r b) fun e => throw s!"{e} (what a call gives, in the group of function {grp.headD 0})"
      | _ => modify fun s => { s with coerces := s.coerces.push (r, b) }
    settle
    -- (What a reference to one of them copies, and what a function made at
    -- a signature copies.)
    let sigRoots := members.flatMap fun (_, m) => m.sig.caps ++ m.sig.params ++ [m.sig.ret]
    let asks ← liveAsks sigRoots (members.map (·.2.sig.row))
    let whole := members.foldl (fun (acc : List U × List Nat) (_, m) =>
      let (ts, rs) := m.roots
      (acc.1 ++ ts, acc.2 ++ rs)) ([], [])
    let all ← liveAsks whole.1 whole.2
    modify fun s => { s with members := members.foldl (fun m (f, mem) => m.insert f mem) s.members
                             cur := {}, hints := #[], uses := #[]
                             asks := grp.foldl (·.insert · asks) s.asks
                             wholeAsks := grp.foldl (·.insert · all) s.wholeAsks }

/-- A function at a signature: a copy of it as its group found it, its
types decided by the signature. Its hints, the uses its body makes, and what
it performs. -/
def instAt (fn : Nat) (want : FnSig) : M (List (List Hint) × List (Nat × FnSig) × Row) := do
  modify fun s => { s with places := #[], coerces := #[], nevers := #[], shows := #[], uses := #[] }
  let some m := (← get).members[fn]? | throw s!"function {fn} has no signature"
  let m ← copyMember m (((← get).wholeAsks[fn]?).getD {})
  let sig := m.sig
  unifyList sig.caps (← want.caps.mapM ofTy)
  -- (What it performs is what its body does, whatever the use says: one
  -- function at one signature, wherever it is used.)
  unifyList sig.params (← want.params.mapM ofTy)
  unify sig.ret (← ofTy want.ret)
  finish
  modify fun s => { s with zonked := {}, zonkedRows := {} }
  let hs ← m.hints.mapM fun h => do pure (← h.toList.mapM zonkHint).flatten
  let uses ← m.uses.toList.mapM fun u => do pure (u.fn, ← zonkSig u.sig)
  pure (hs, uses, ← zonkRow sig.row)

/-- Each declared type and operation the types use, as the certificate has
them. -/
partial def declsFor (types : List Ty) (rows : List (Nat × List Ty)) : M (List DataInst × List OpInst) := do
  let mut datas : Array DataInst := #[]
  let mut seen : Std.HashSet (Nat × List Ty) := {}
  let mut ops : Array OpInst := #[]
  let mut seenOps : Std.HashSet (Nat × List Ty) := {}
  let mut todo := types
  let mut opsTodo := rows
  let d := (← read).decls
  while !todo.isEmpty || !opsTodo.isEmpty do
    match opsTodo with
    | (op, targs) :: rest =>
      opsTodo := rest
      unless seenOps.contains (op, targs) do
        seenOps := seenOps.insert (op, targs)
        let some (ps, payload, result) := d.ops[op]? | throw s!"operation {op} is not declared"
        let vars ← (ps.zip targs).mapM fun (p, t) => do pure (p, ← ofTy t)
        let payload ← payload.mapM fun w => do zonk (← writtenU vars w)
        let result ← result.mapM fun w => do zonk (← writtenU vars w)
        ops := ops.push ⟨op, targs, payload, result⟩
        todo := payload ++ result.toList ++ targs ++ todo
    | [] =>
      match todo with
      | t :: rest =>
        todo := rest
        match t with
        | .data name args =>
          todo := args ++ todo
          if name < builtinNames && !seen.contains (name, args) then
            seen := seen.insert (name, args)
            let vars ← (((d.typeParams[name]?).getD []).zip args).mapM fun (p, t) => do pure (p, ← ofTy t)
            let mut ctors : List (Nat × List Ty) := []
            for tag in d.tagsOf.getD name [] do
              let some (_, fields) := d.ctors[tag]? | throw s!"constructor {tag} is not declared"
              let fs ← fields.mapM fun w => do zonk (← writtenU vars w)
              ctors := ctors ++ [(tag, fs)]
              todo := fs ++ todo
            datas := datas.push ⟨name, args, ctors⟩
        | .tuple fs => todo := fs ++ todo
        | .fn ps r eff _ env =>
          todo := ps ++ [r] ++ (env.getD []) ++ todo
          opsTodo := eff ++ opsTodo
        | .ref t => todo := t :: todo
        | _ => pure ()
      | [] => pure ()
  pure (datas.toList, ops.toList)

/-- A type of the certificate, as messages show it. -/
partial def showTy : Ty → String
  | .int => "Int"
  | .scalar b => s!"s{b}"
  | .tuple fs => "(" ++ ", ".intercalate (fs.map showTy) ++ ")"
  | .data n args => (if n == anyName then "?" else s!"#{n}") ++ "<" ++ ", ".intercalate (args.map showTy) ++ ">"
  | .fn ps r eff once env => "fn(" ++ ", ".intercalate (ps.map showTy) ++ s!") -> {showTy r}" ++
      (if eff.isEmpty then "" else s!" / {eff.map (·.1)}") ++ (if once then " once" else "") ++
      (match env with | some cs => " [" ++ ", ".intercalate (cs.map showTy) ++ "]" | none => "")
  | .ref t => "&" ++ showTy t
  | .never => "!"

/-- A signature, as messages show it. -/
def showSig (sig : FnSig) : String :=
  s!"caps [{", ".intercalate (sig.caps.map showTy)}] ({", ".intercalate (sig.params.map showTy)}) -> {showTy sig.ret}" ++
    (if sig.eff.isEmpty then "" else s!" / {sig.eff.map (·.1)}")

/-- Each signature, as messages show them. -/
def showSigs (C : Types) : String :=
  "\n".intercalate (C.sigs.toList.map fun e => s!"fn{e.fn}: {showSig e.sig}")

/-- The types of a program's Core, for the typed lowering. -/
def typesOf (items : List Item) (out : Elab.Output) : Except String Types := do
  let g ← Elab.collectDeclared items
  let decls := declsOf items g
  let p := out.program
  let counts := (p.main :: p.fns.toList.flatMap (·.clauses.map (·.body))).flatMap capsOf
  let ncaps := counts.foldl (fun (acc : Array Nat) (f, n) => acc.setIfInBounds f n) (Array.replicate p.fns.size 0)
  let env : Env := { decls, p, ncaps }
  let action : M Types := do
    -- (`main`: run with nothing, performing nothing.)
    modify fun s => { s with places := #[], coerces := #[], nevers := #[], shows := #[], uses := #[], hints := #[] }
    let τ ← freshTy
    inferTm (← freshRow) τ #[] p.main
    finish
    modify fun s => { s with zonked := {}, zonkedRows := {} }
    let mainTy ← zonk τ
    let mainHints := (← (← get).hints.toList.mapM zonkHint).flatten
    let mut todo := (← (← get).uses.toList.mapM fun u => do pure (u.fn, ← zonkSig u.sig, none))
    let mut emitted : Std.HashMap Nat (List FnSig) := {}
    let mut sigs : Array SigEntry := #[]
    while !todo.isEmpty do
      match todo with
      | (fn, sig, parent) :: rest =>
        todo := rest
        -- (One signature whatever its uses say it performs.)
        let sig := { sig with eff := [] }
        unless (emitted.getD fn []).contains sig do
          emitted := emitted.insert fn (sig :: emitted.getD fn [])
          if Trace.typesTraced then
            dbgTrace s!"wanted: fn{fn} by {parent.map (s!"fn{·}")}: {showSig sig}" fun _ => pure ()
          -- (What a function's types at a signature made is let go once they
          -- are read out: nothing found before refers to it.)
          let (nTys, nRows) := ((← get).tys.size, (← get).rows.size)
          let (hints, uses, eff) ← try instAt fn sig
            catch e => throw (if (e.splitOn "(in function ").length > 1 then e else s!"{e} (in function {fn})")
          modify fun s => { s with tys := s.tys.shrink nTys, rows := s.rows.shrink nRows
                                   numeric := s.numeric.filter (· < nTys), seenAs := s.seenAs.filter (· < nTys) }
          sigs := sigs.push ⟨fn, { sig with eff }, hints⟩
          todo := uses.map (fun (g, s) => (g, s, some fn)) ++ rest
          -- (What destroys a closure of it, at what destroys one of these.)
          if let some d := p.drops.lookup fn then
            todo := todo ++ [(d, dropSig sig, some fn)]
      | [] => pure ()
    let types := mainTy :: mainHints.flatMap hintTypes ++ sigs.toList.flatMap fun e =>
      e.sig.caps ++ e.sig.params ++ [e.sig.ret] ++ e.sig.eff.flatMap (·.2) ++ e.hints.flatMap (·.flatMap hintTypes)
    let rows := sigs.toList.flatMap fun e => e.sig.eff ++ e.hints.flatMap (·.flatMap hintOps)
    modify fun s => { s with zonked := {}, zonkedRows := {} }
    let (datas, ops) ← declsFor types (rows ++ mainHints.flatMap hintOps)
    if Trace.enabled then
      let s ← get
      let byFn := sigs.foldl (fun (m : Std.HashMap Nat (List FnSig)) e => m.insert e.fn (e.sig :: m.getD e.fn [])) {}
      let top := (byFn.toList.toArray.qsort fun a b => a.2.length > b.2.length).toList.take 6
      let said := top.map fun (fn, ss) =>
        s!"fn{fn}: {ss.length}" ++ (match ss with
          | a :: b :: _ => s!"\n    {showSig a}\n    {showSig b}"
          | _ => "")
      dbgTrace (s!"types: {sigs.size} signatures, {s.copies} copies with {s.askCopies} asks ({s.placeCopies} places, {s.showCopies} environments), {s.tys.size} variables\n" ++ "\n".intercalate said) fun _ => pure ()
    pure (Types.withIndex ⟨sigs, datas, ops, mainTy, mainHints, #[]⟩)
  let st ← match Trace.timed "types: groups" fun _ => (inferGroups.run env).run {} with
    | .ok () st => pure st
    | .error e _ => throw e
  match Trace.timed "types: each function at its signatures" fun _ => (action.run env).run st with
  | .ok c _ => pure c
  | .error e _ => throw e
where
  hintTypes : Hint → List Ty
    | .ty t => [t]
    | .handler ρ H => ρ :: H.flatMap (·.2)
  hintOps : Hint → List (Nat × List Ty)
    | .handler _ H => H
    | _ => []

end Glorious.Typer
