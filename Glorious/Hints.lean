module

public import Glorious.Typer

/-!
# Core's types from the checker's, forward

Each function at a signature gone through once, each local's type found
from its parts' and, for what its parts do not say, from the type the
checker found of the expression it is made for (`Blocks.nodeTys`, by the
node's identity; the elaborator notes which local is made for which,
`Output.fnNodes`). Nothing is unified.

For now beside `Typer`: each hint `Typer` found is compared with the one
found here (`GLORIOUS_TRACE=hints`), and `Typer`'s is what the walk goes on
with.
-/

@[expose] public section

namespace Glorious.Hints

open Lower Core Syntax

structure Env where
  decls : Typer.Decls
  p : Program
  /-- The checker's type of the expression each local is made for, by
  function, clause and local, where it knows the type whole. -/
  said : Std.HashMap (Nat × Nat × Nat) TypeExpr := {}
  names : Array String := #[]
  /-- Each top-level function's type as the checker found it. -/
  selfTy : Std.HashMap Nat TypeExpr := {}

/-- How the hints found compare, by what they are of. -/
structure Tally where
  counts : Std.HashMap String (Nat × Nat × Nat) := {}
  /-- What a function's type parameters are where a closure of each callable
  was made, learned there: where its body is gone through, they are. -/
  closureBinds : Std.HashMap (Nat × List Ty) (List (String × Ty)) := {}
  lost : Nat := 0
  examples : Array String := #[]

def Tally.add (t : Tally) (kind : String) (r : Option Bool) (ex : Option String := none) : Tally :=
  let (a, d, u) := t.counts.getD kind (0, 0, 0)
  let c := match r with
    | some true => (a + 1, d, u)
    | some false => (a, d + 1, u)
    | none => (a, d, u + 1)
  { t with counts := t.counts.insert kind c
           examples := match ex with
             | some e => if t.examples.size < 40 then t.examples.push e else t.examples
             | none => t.examples }

/-- A type written whole, as Core's types are: a callable's not (its
effects and what it was made with are not written). -/
partial def tyOf (d : Typer.Decls) (vars : List (String × Ty) := []) : TypeExpr → Option Ty
  | .name x args =>
    if let (some t, []) := (vars.lookup x, args) then some t
    else if x.startsWith "'" then some (.ref .unit)
    else if x == "Int" then some .int
    else if isScalar x then some (.scalar (scalarBits x))
    else if x == "Fixed" then
      match args with
      | [t, n] => do pure (.data fixedName [← tyOf d vars t, ← lengthOf n])
      | _ => none
    else match d.typeIds[x]? with
      | some id => do
        let given ← args.mapM (tyOf d vars)
        let lifetimes := ((d.typeParams[id]?).getD []).map (·.startsWith "'")
        let mut missing := lifetimes.length - given.length
        let mut rest := given
        let mut out : Array Ty := #[]
        for isLife in lifetimes do
          if isLife && missing > 0 then
            out := out.push (.ref .unit)
            missing := missing - 1
          else
            match rest with
            | a :: more =>
              out := out.push a
              rest := more
            | [] => none
        pure (.data id (out.toList ++ rest))
      | none => none
  | .tuple ts => do pure (.tuple (← ts.mapM (tyOf d vars)))
  | .ref _ t _ => do pure (.ref (← tyOf d vars t))
  | .performs r _ => tyOf d vars r
  | .never => some .never
  -- (What it performs and was made with are not written: found apart.)
  | .fn ps r => do pure (.fn (← ps.mapM (tyOf d vars)) (← tyOf d vars r) [] false none)
  | _ => none
where
  lengthOf (n : TypeExpr) : Option Ty :=
    let rec count : TypeExpr → Option Nat
      | .name "Z" [] | .name "%prelude::Z" [] => some 0
      | .name b [inner] =>
        if b.endsWith "B0" then (count inner).map (2 * ·)
        else if b.endsWith "B1" then (count inner).map (2 * · + 1)
        else none
      | _ => none
    (count n).map fun k => .data (lenBase + k) []

/-- What each type parameter (`%rigid:T`) a written type names is, where
the type is `t`: added to `binds`. -/
partial def matchTy (d : Typer.Decls) (binds : List (String × Ty)) : TypeExpr → Ty → List (String × Ty)
  | .name x [], t =>
    if x.startsWith "%rigid:" && (binds.lookup x).isNone then (x, t) :: binds else binds
  | .name x args, .data n targs =>
    if d.typeIds[x]? == some n then
      let lifetimes := ((d.typeParams[n]?).getD []).map (·.startsWith "'")
      let typed := (lifetimes.zip targs).filterMap fun (l, t) => if l then none else some t
      if typed.length == args.length then
        (args.zip typed).foldl (fun b (a, t) => matchTy d b a t) binds
      else binds
    else binds
  | .tuple ps, .tuple ts => (ps.zip ts).foldl (fun b (a, t) => matchTy d b a t) binds
  | .ref _ a _, .ref t => matchTy d binds a t
  | .fn ps r, .fn ts s _ _ _ => matchTy d ((ps.zip ts).foldl (fun b (a, t) => matchTy d b a t) binds) r s
  | .performs r _, t => matchTy d binds r t
  | _, _ => binds

/-- A field of a value of a type, where the type says it. -/
def fieldOf (d : Typer.Decls) (t : Ty) (i : Nat) : Option Ty :=
  match t with
  | .tuple fs => fs[i]?
  | .data n args =>
    if n == fixedName then args.head?
    else match d.tagsOf[n]? with
      | some [tag] => do
        let (_, fields) ← d.ctors[tag]?
        let f ← fields[i]?
        tyOf d (((d.typeParams[n]?).getD []).zip args) f
      | _ => none
  | _ => none

/-- The same, but for what callables perform and were made with, which are
found apart. -/
partial def shape : Ty → Ty
  | .fn ps r _ _ _ => .fn (ps.map shape) (shape r) [] false none
  | .tuple fs => .tuple (fs.map shape)
  | .data n args => .data n (args.map shape)
  | .ref t => .ref (shape t)
  | t => t

/-- The value a callable gives, of its type. -/
def retOf : Ty → Option Ty
  | .fn _ r _ _ _ => some r
  | _ => none

/-- The type of what a memory operation gives. -/
def memTy (env : Env) (Γ : Array (Option Ty)) (op : MemOp) (args : List Atom) : Option Ty :=
  let atomTy := fun (a : Atom) => match a with
    | .var i => Γ[i]?.join
    | .int _ => some .int
  match op, args with
  | .load, [r] => match atomTy r with | some (.ref t) => some t | _ => none
  | .store, _ | .free, _ | .writeBits, _ | .copy, _ => some .unit
  | .swap, [_, v] => atomTy v
  | .tag, _ | .readBits, _ => some .int
  | .alloc, _ | .sizeOf, _ | .alignOf, _ | .staticAt, _ => some (.scalar (-64))
  | .focus, [r, .int i] => match atomTy r with
    | some (.ref t) => (fieldOf env.decls t i.toNat).map .ref
    | _ => none
  | _, _ => none

/-- The type of what a host operation gives. -/
def hostTy (id : Nat) (_args : List Atom) : Option Ty :=
  match id with
  | 0 | 8 | 21 | 22 => some .unit
  | 1 | 10 => some (.tuple [.int, .int])
  | 2 | 6 => some .int
  | 5 => some (.scalar (-64))
  | _ => none

mutual
/-- The types a pattern binds of a value of a type, the declarations read. -/
partial def patTysD (d : Typer.Decls) : Pat → Ty → Option (List Ty)
  | .wild, _ => some []
  | .bind, τ => some [τ]
  | .int _, _ => some []
  | .ctor 0 ps, .tuple fs => patsTysD d ps fs
  | .ctor tag ps, .data n args => do
    let (_, fields) ← d.ctors[tag]?
    let vars := ((d.typeParams[n]?).getD []).zip args
    patsTysD d ps (← fields.mapM (tyOf d vars))
  | _, _ => none
partial def patsTysD (d : Typer.Decls) : List Pat → List Ty → Option (List Ty)
  | [], [] => some []
  | p :: ps, τ :: τs => do pure ((← patTysD d p τ) ++ (← patsTysD d ps τs))
  | _, _ => none
end

/-- The type of a right-hand side, where its parts or the checker say it. -/
def rhsTy (env : Env) (binds : List (String × Ty)) (Γ : Array (Option Ty)) (said : Option TypeExpr) : Rhs → Option Ty
  | .atom a => atomTy Γ a
  | .prim p args =>
    match p, args with
    | .cast b into, _ => some (if into then .scalar b else .int)
    | .fixed 0, [a, .int n] => do pure (.data fixedName [← atomTy Γ a, .data (lenBase + n.toNat) []])
    | .fixed 2, a :: _ => do fixedElem (← atomTy Γ a)
    | .fixed 3, a :: _ => atomTy Γ a
    | .fixed 4, _ => some .int
    | .fixed _, _ => none
    | _, _ => some .int
  | .construct 0 args => do pure (.tuple (← args.mapM (atomTy Γ)))
  | .construct _ _ => said.bind (tyOf env.decls binds)
  | .place pl => do
    let mut t ← Γ[pl.var]?.join
    for i in pl.path do t ← fieldOf env.decls t i
    pure t
  | .closure _ caps => do
    match ← said.bind (tyOf env.decls binds) with
    | .fn ps r _ _ _ => pure (.fn ps r [] false (some (← caps.mapM (atomTy Γ))))
    | _ => none
where
  atomTy (Γ : Array (Option Ty)) : Atom → Option Ty
    | .var i => Γ[i]?.join
    | .int _ => some .int

mutual

/-- The result of a clause of `f`, going through it forward from its
locals' first types (`Γ`): of what it returns. -/
partial def fwd (env : Env) (depth : Nat) (f c : Nat) (binds : List (String × Ty)) (Γ : Array (Option Ty)) (tm : Tm) : Option Ty :=
  let said := fun (i : Nat) => env.said[(f, c, i)]?
  let atomTy := fun (a : Atom) => match a with
    | .var i => Γ[i]?.join
    | .int _ => some .int
  match tm with
  | .ret a => atomTy a
  | .tail g _ => (atomTy g).bind retOf
  | .raise .. => some .never
  | .labelTail thunk | .guardTail _ thunk | .cellTail _ thunk | .cellTailL _ _ thunk => (atomTy thunk).bind retOf
  | .handleTail .. => none
  | .let_ rhs body =>
    let mine := match rhs with
      | .closure g caps => (rhsTy env binds Γ (said Γ.size) rhs).orElse fun _ =>
          closureTy env depth f c binds Γ g caps body
      | _ => rhsTy env binds Γ (said Γ.size) rhs
    let binds := match said Γ.size, mine with
      | some te, some m => matchTy env.decls binds te m
      | _, _ => binds
    fwd env depth f c binds (Γ.push mine) body
  | .call g _ body => fwd env depth f c binds (Γ.push ((atomTy g).bind retOf)) body
  | .handle _ _ _ _ body => fwd env depth f c binds (Γ.push ((said Γ.size).bind (tyOf env.decls binds))) body
  | .perform _ _ body => fwd env depth f c binds (Γ.push none) body
  | .label thunk body | .guard _ thunk body | .cell _ thunk body | .cellL _ _ thunk body | .lend _ _ thunk _ _ body =>
    fwd env depth f c binds (Γ.push ((atomTy thunk).bind retOf)) body
  | .cancel _ body => fwd env depth f c binds (Γ.push (some .unit)) body
  | .mem op args body => fwd env depth f c binds (Γ.push (memTy env Γ op args)) body
  | .host id args body => fwd env depth f c binds (Γ.push (hostTy id args)) body

/-- The type of a closure of `g` made with `caps`, where the checker did not
say it: what it is given read off where it is used straight after (a cell's,
a guard's, a borrow's or a label's scope, or a call), and what it gives off
its body gone through at that. -/
partial def closureTy (env : Env) (depth : Nat) (f c : Nat) (binds : List (String × Ty)) (Γ : Array (Option Ty))
    (g : Nat) (caps : List Atom) (body : Tm) : Option Ty := do
  if depth > 12 then none
  let here := Γ.size
  let atomTy := fun (a : Atom) => match a with
    | .var i => Γ[i]?.join
    | .int _ => some .int
  let capTys ← caps.mapM atomTy
  let isHere := fun (a : Atom) => a == .var here
  let params : Option (List Ty) := match body with
    | .cell a t _ | .cellTail a t => if isHere t then (atomTy a).map fun σ => [.ref σ] else none
    | .guard _ t _ | .guardTail _ t => if isHere t then some [] else none
    | .lend _ r t pre post _ =>
      if isHere t then do pure ((← pre.mapM atomTy) ++ [← atomTy r] ++ (← post.mapM atomTy)) else none
    | .call h args _ | .tail h args => if isHere h then args.mapM atomTy else none
    | _ => none
  -- (A label's: given the label, whose result is the scope's, as the
  -- checker says it.)
  let params ← params.orElse fun _ => match body with
    | .label t _ | .labelTail t =>
      if isHere t then do
        let σ ← (env.said[(f, c, here + 1)]?).bind (tyOf env.decls binds)
        pure [.fn [σ] .never [] false none]
      else none
    | _ => none
  -- (What it gives is what the place it is used at gives, where the
  -- checker says that; else its body's, and where that does not return,
  -- what the place wants.)
  let atUse := (env.said[(f, c, here + 1)]?).bind (tyOf env.decls binds)
  let ret ← match atUse, body with
    | some r, .call .. => some r
    | _, _ => match fnRet env (depth + 1) g binds params capTys with
      | some .never | none => atUse
      | r => r
  pure (.fn params ret [] false (some capTys))

/-- What `g` gives at what it is given and made with: its first clause's
that says. -/
partial def fnRet (env : Env) (depth : Nat) (g : Nat) (binds : List (String × Ty)) (params caps : List Ty) : Option Ty := do
  let fn ← env.p.fns[g]?
  -- (A function of its own: its type parameters of what it is given.)
  let binds := match env.selfTy[g]? with
    | some (.fn ps _) => (ps.zip params).foldl (fun b (a, p) => matchTy env.decls b a p) []
    | _ => binds
  fn.clauses.zipIdx.findSome? fun (cl, ci) => do
    let bound ← patsTysD env.decls cl.pats params
    fwd env depth g ci binds ((params ++ caps ++ bound).toArray.map some) cl.body

end

/-- Go through a clause at its locals' first types, beside `Typer`'s hints:
each compared, `Typer`'s gone on with. -/
partial def walk (env : Env) (f c : Nat) (binds : List (String × Ty)) (Γ : Array (Option Ty)) (hints : List Hint) (tm : Tm) (t : Tally) : Tally :=
  let said := fun (i : Nat) => env.said[(f, c, i)]?
  let atomTy := fun (a : Atom) => match a with
    | .var i => Γ[i]?.join
    | .int _ => some .int
  -- (Typer's next hint, of a type, compared with this one.)
  let take := fun (t : Tally) (kind : String) (mine : Option Ty) (k : Option Ty → List Hint → Tally → Tally) =>
    match hints with
    | .ty σ :: rest =>
      let r := mine.map fun m => shape m == shape σ
      let ex := if r == some false then some s!"{env.names[f]?.getD "?"} {kind} local {Γ.size}: here {(mine.map Typer.showTy).getD "?"}, Typer {Typer.showTy σ}" else none
      k (some σ) rest (t.add kind r ex)
    | _ => { t with lost := t.lost + 1 }
  match tm with
  | .ret _ | .tail .. | .raise .. | .labelTail _ | .guardTail .. | .cellTail .. | .cellTailL .. => t
  | .handleTail .. => t
  | .let_ rhs body =>
    let kind := match rhs with
      | .atom _ => "atom" | .prim _ _ => "prim" | .construct 0 _ => "tuple" | .construct _ _ => "construct"
      | .place _ => "place" | .closure _ _ => "closure"
    let mine := match rhs with
      | .closure g caps => (rhsTy env binds Γ (said Γ.size) rhs).orElse fun _ =>
          closureTy env 0 f c binds Γ g caps body
      | _ => rhsTy env binds Γ (said Γ.size) rhs
    -- (What it says of the type parameters, learned of what was found here.)
    let binds := match said Γ.size, mine with
      | some te, some m => matchTy env.decls binds te m
      | _, _ => binds
    let t1 := match rhs, mine with
      | .closure g _, none =>
        if t.examples.size < 60 && (t.counts.getD "closure" (0,0,0)).2.2 % 401 == 0 then
          { t with examples := t.examples.push s!"not found: in {env.names[f]?.getD "?"}: closure of {env.names[g]?.getD "?"}, said {(said Γ.size).isSome}" }
        else t
      | _, _ => t
    let t1 := match rhs with
      | .closure g caps =>
        match caps.mapM atomTy with
        | some capTys =>
          -- (Of a callable of this function's own, not of another function.)
          if binds.isEmpty || (env.selfTy[g]?).isSome || (env.decls.fns[g]?).isSome then t1
          else { t1 with closureBinds := t1.closureBinds.insert (g, capTys) binds }
        | none => t1
      | _ => t1
    take t1 kind mine fun σ rest t => walk env f c binds (Γ.push σ) rest body t
  | .call g _ body =>
    match (atomTy g).bind retOf with
    | some .never => take t "never" (some .never) fun σ rest t => walk env f c binds (Γ.push σ) rest body t
    | some r => walk env f c binds (Γ.push (some r)) hints body t
    | none => { t with lost := t.lost + 1 }
  | .handle _ _ _ _ body =>
    match hints with
    | .handler ρ _ :: rest => walk env f c binds (Γ.push (some ρ)) rest body t
    | _ => { t with lost := t.lost + 1 }
  | .perform _ _ body => walk env f c binds (Γ.push none) hints body t
  | .label thunk body => walk env f c binds (Γ.push ((atomTy thunk).bind retOf)) hints body t
  | .guard _ thunk body => walk env f c binds (Γ.push ((atomTy thunk).bind retOf)) hints body t
  | .cancel _ body => walk env f c binds (Γ.push (some .unit)) hints body t
  | .cell _ thunk body | .cellL _ _ thunk body => walk env f c binds (Γ.push ((atomTy thunk).bind retOf)) hints body t
  | .lend _ _ thunk _ _ body => walk env f c binds (Γ.push ((atomTy thunk).bind retOf)) hints body t
  | .mem op args body =>
    let σ : Option Ty := match op, args with
      | .load, [r] => match atomTy r with | some (.ref t) => some t | _ => none
      | .store, _ | .free, _ | .writeBits, _ | .copy, _ => some .unit
      | .swap, [_, v] => atomTy v
      | .tag, _ | .readBits, _ => some .int
      | .alloc, _ | .sizeOf, _ | .alignOf, _ | .staticAt, _ => some (.scalar (-64))
      | .focus, [r, .int i] => match atomTy r with
        | some (.ref t) => (fieldOf env.decls t i.toNat).map .ref
        | _ => none
      | _, _ => none
    walk env f c binds (Γ.push σ) hints body t
  | .host id args body =>
    let σ : Option Ty := match id, args with
      | 0, _ | 8, _ | 21, _ | 22, _ => some .unit
      | 1, _ | 10, _ => some (.tuple [.int, .int])
      | 2, _ | 6, _ => some .int
      | 5, _ => some (.scalar (-64))
      | _, _ => none
    if 2 ≤ id then take t "host" σ fun σ rest t => walk env f c binds (Γ.push σ) rest body t
    else walk env f c binds (Γ.push σ) hints body t

/-- A written type with the type parameters `ps` named as the checker's
(`%rigid:T`). -/
partial def rigidOf (ps : List String) : TypeExpr → TypeExpr
  | .name x [] => if ps.contains x then .name s!"%rigid:{x}" [] else .name x []
  | .name x args => .name x (args.map (rigidOf ps))
  | .tuple ts => .tuple (ts.map (rigidOf ps))
  | .fn as r => .fn (as.map (rigidOf ps)) (rigidOf ps r)
  | .performs r effs => .performs (rigidOf ps r) effs
  | .ref u t l => .ref u (rigidOf ps t) l
  | t => t

/-- The hints of every function at every signature `Typer` found, compared. -/
def compare (env : Env) (C : Types) : Tally := Id.run do
  let mut t : Tally := {}
  for e in C.sigs do
    let some fn := env.p.fns[e.fn]? | continue
    for ((cl, hs), ci) in (fn.clauses.zip e.hints).zipIdx do
      let bound := (patsTys C cl.pats e.sig.params).getD []
      let Γ : Array (Option Ty) := (e.sig.params ++ e.sig.caps ++ bound).toArray.map some
      -- (A function's type parameters, of what its parameters are said to be.)
      let binds := match env.decls.fns[e.fn]? with
        | some (tparams, annots, _) =>
          (annots.zip e.sig.params).foldl (fun b (a, p) => match a with
            | some te => matchTy env.decls b (rigidOf tparams te) p
            | none => b) []
        | none => []
      -- (And of what the checker found the function to be; a closure's, as
      -- where it was made.)
      let binds := binds ++ (t.closureBinds.getD (e.fn, e.sig.caps) [])
      let binds := match env.selfTy[e.fn]? with
        | some (.fn ps r) => matchTy env.decls ((ps.zip e.sig.params).foldl (fun b (a, p) => matchTy env.decls b a p) binds) r e.sig.ret
        | _ => binds
      t := walk env e.fn ci binds Γ hs cl.body t
  pure t

/-- `compare`, said. -/
def report (items : List Item) (out : Elab.Output) (nodeTys : Std.HashMap String (Std.HashMap Nat TypeExpr))
    (C : Types) : String := Id.run do
  let some g := (Elab.collectDeclared items).toOption | return "hints: no declarations"
  let decls := Typer.declsOf items g
  let said := out.fnNodes.fold (fun m f (owner, clauses) =>
    let base := (owner.splitOn "⟨").headD owner
    match nodeTys[owner]? <|> nodeTys[base]? with
    | none => m
    | some tys => clauses.zipIdx.foldl (fun m (locals, c) =>
        locals.foldl (fun m (i, n) => match tys[n]? with
          | some te => m.insert (f, c, i) te
          | none => m) m) m) {}
  let selfTy := out.fnNodes.fold (fun m f (owner, _) =>
    if out.fnNames[f]? != some s!"`{owner}`" then m else
    let base := (owner.splitOn "⟨").headD owner
    match (nodeTys[owner]? <|> nodeTys[base]?).bind (·[Flat.selfNode]?) with
    | some te => m.insert f te
    | none => m) {}
  let t := compare { decls, p := out.program, said, names := out.fnNames, selfTy } C
  let lines := t.counts.toList.map fun (k, (a, d, u)) => s!"  {k}: {a} agree, {d} not, {u} not found"
  "\n".intercalate ([s!"hints: {t.lost} clauses lost"] ++ lines ++ t.examples.toList.map ("  " ++ ·))

end Glorious.Hints
