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
             | some e => if t.examples.size < 60 then t.examples.push e else t.examples
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
  -- (What it performs, each operation of each effect at the effect's
  -- arguments; what it was made with is not written, found apart.)
  | .fn ps (.performs r effs) => do
    let eff ← effs.flatMapM fun (e, args) => do
      let targs ← args.mapM (tyOf d vars)
      pure (((d.effectOps[e]?).getD []).map (·, targs))
    pure (.fn (← ps.mapM (tyOf d vars)) (← tyOf d vars r) eff false none)
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
    | .fn ps r eff _ _ => pure (.fn ps r eff false (some (← caps.mapM (atomTy Γ))))
    | _ => none
where
  atomTy (Γ : Array (Option Ty)) : Atom → Option Ty
    | .var i => Γ[i]?.join
    | .int _ => some .int

/-- A clause being gone through: each local's type found so far, the
closures whose type waits on where they are used (by local: the function
and what it was made with), the hints found in order (none where not, or
not yet: by local, which), and the type parameters learned. -/
structure W where
  Γ : Array (Option Ty) := #[]
  pend : Std.HashMap Nat (Nat × List Ty) := {}
  hints : Array (Option Hint) := #[]
  hintAt : Std.HashMap Nat Nat := {}
  binds : List (String × Ty) := []
  /-- The type parameters where a closure of each callable of the function's
  own was made (by the callable and what it was made with). -/
  made : Array ((Nat × List Ty) × List (String × Ty)) := #[]

def W.atomTy (w : W) : Atom → Option Ty
  | .var i => w.Γ[i]?.join
  | .int _ => some .int

/-- The local `i`'s type found: where it waited, its hint too. -/
def W.found (w : W) (i : Nat) (σ : Ty) : W :=
  let w := { w with Γ := w.Γ.set! i (some σ), pend := w.pend.erase i }
  match w.hintAt[i]? with
  | some h => { w with hints := w.hints.set! h (some (.ty σ)) }
  | none => w

/-- A local and its hint. -/
def W.bind (w : W) (σ : Option Ty) (hinted : Bool) : W :=
  let i := w.Γ.size
  let w := { w with Γ := w.Γ.push σ }
  if hinted then { w with hints := w.hints.push (σ.map .ty), hintAt := w.hintAt.insert i w.hints.size }
  else w

mutual

/-- The type of a closure that waited, at its first use as a callable, `at_`
(`pend`): what it is given read off that; what it gives what the place says
it gives where the checker says that, else what the function says it
gives, else its body's. -/
partial def useOf (env : Env) (depth : Nat) (f c : Nat) (w : W) (at_ : Tm) : W := Id.run do
  let callee := fun (a : Atom) => match a with
    | .var i => (w.pend[i]?).map (i, ·)
    | .int _ => none
  let mut w := w
  -- (The callable, what it is given, and the local the use binds, if any.)
  let uses : List (Atom × Option (List Ty)) := match at_ with
    | .guard cl t _ | .guardTail cl t => [(cl, some []), (t, some [])]
    | .cell a t _ | .cellTail a t => [(t, (w.atomTy a).map fun σ => [.ref σ])]
    | .lend _ r t pre post _ => [(t, do pure ((← pre.mapM w.atomTy) ++ [← w.atomTy r] ++ (← post.mapM w.atomTy)))]
    | .call h args _ | .tail h args => [(h, args.mapM w.atomTy)]
    | .handle _ _ _ t _ | .handleTail _ _ _ t => [(t, some [])]
    | .label t _ | .labelTail t =>
      -- (Given the label, whose result is the scope's: as the checker says
      -- it, else as the scope's body gives it, `labelRet`.)
      [(t, do
        let σ ← ((env.said[(f, c, w.Γ.size)]?).bind (tyOf env.decls w.binds)).orElse fun _ =>
          match t with
          | .var i => do
            let (g, caps) ← w.pend[i]?
            labelRet env depth g w.binds caps
          | _ => none
        pure [.fn [σ] .never [] false none])]
    | _ => []
  for (a, params) in uses do
    let some (i, (g, caps)) := callee a | continue
    let some params := params | continue
    -- (What the use gives, as the checker says it: a call's.)
    let atUse := match at_ with
      | .call .. => (env.said[(f, c, w.Γ.size)]?).bind (tyOf env.decls w.binds)
      | _ => none
    let written : Option Ty := do
      let (tparams, annots, ret) ← env.decls.fns[g]?
      -- (One that says nothing of it gives `()`.)
      let ret := ret.getD (.tuple [])
      let b := (annots.zip params).foldl (fun b (a, p) => match a with
        | some te => matchTy env.decls b (rigidOf tparams te) p
        | none => b) []
      tyOf env.decls b (rigidOf tparams ret)
    let ret := atUse <|> written <|> (match fnRet env (depth + 1) g w.binds params caps with
      | some .never | none => none
      | r => r)
    if let some r := ret then
      w := w.found i (.fn params r [] false (some caps))
  pure w

/-- Go through a clause: its hints and what it gives. -/
partial def go (env : Env) (depth : Nat) (f c : Nat) (w : W) (tm : Tm) : W × Option Ty :=
  let said := fun (i : Nat) => env.said[(f, c, i)]?
  let w := if w.pend.isEmpty then w else useOf env depth f c w tm
  match tm with
  | .ret a => (w, w.atomTy a)
  | .tail g _ => (w, (w.atomTy g).bind retOf)
  | .raise .. => (w, some .never)
  | .labelTail thunk | .guardTail _ thunk | .cellTail _ thunk | .cellTailL _ _ thunk => (w, (w.atomTy thunk).bind retOf)
  | .handleTail ret ops caps thunk =>
    let w := match caps.mapM w.atomTy with
      | some capTys => if w.binds.isEmpty then w else
          { w with made := (ret :: ops.map (fun (p : Nat × Nat) => p.2)).foldl (fun (m : Array ((Nat × List Ty) × List (String × Ty))) g => m.push ((g, capTys), w.binds)) w.made }
      | none => w
    let H : Option Row := ops.mapM fun (op, _) => do
      let (ps, _, _) ← env.decls.ops[op]?
      if ps.isEmpty then pure (op, []) else
        match w.atomTy thunk with
        | some (.fn _ _ eff _ _) => (eff.lookup op).map (op, ·)
        | _ => none
    -- (What it gives is what the clause gives: found by its callers.)
    ({ w with hints := w.hints.push (H.map (.handler .never ·)) }, none)
  | .let_ rhs body =>
    let i := w.Γ.size
    let mine := rhsTy env w.binds w.Γ (said i) rhs
    let w := match said i, mine with
      | some te, some m => { w with binds := matchTy env.decls w.binds te m }
      | _, _ => w
    match rhs, mine with
    | .closure g caps, none =>
      let w := w.bind none true
      match caps.mapM w.atomTy with
      | some capTys =>
        let w := { w with pend := w.pend.insert i (g, capTys) }
        let w := if w.binds.isEmpty || (env.selfTy[g]?).isSome || (env.decls.fns[g]?).isSome then w
          else { w with made := w.made.push ((g, capTys), w.binds) }
        go env depth f c w body
      | none => go env depth f c w body
    | .closure g caps, some σ =>
      let w := w.bind (some σ) true
      let w := match caps.mapM w.atomTy with
        | some capTys =>
          if w.binds.isEmpty || (env.selfTy[g]?).isSome || (env.decls.fns[g]?).isSome then w
          else { w with made := w.made.push ((g, capTys), w.binds) }
        | none => w
      go env depth f c w body
    | _, _ => go env depth f c (w.bind mine true) body
  | .call g _ body =>
    match (w.atomTy g).bind retOf with
    | some .never => go env depth f c (w.bind ((said w.Γ.size).bind (tyOf env.decls w.binds)) true) body
    | r => go env depth f c (w.bind r false) body
  | .handle ret ops caps thunk body =>
    -- (Its functions are of this one's type parameters.)
    let w := match caps.mapM w.atomTy with
      | some capTys => if w.binds.isEmpty then w else
          { w with made := (ret :: ops.map (fun (p : Nat × Nat) => p.2)).foldl (fun (m : Array ((Nat × List Ty) × List (String × Ty))) g => m.push ((g, capTys), w.binds)) w.made }
      | none => w
    -- (What it gives, as the checker says it; the operations it serves,
    -- each at its effect's arguments: none, of an effect that takes none.)
    let ρ := (said w.Γ.size).bind (tyOf env.decls w.binds)
    let H : Option Row := ops.mapM fun (op, _) => do
      let (ps, _, _) ← env.decls.ops[op]?
      if ps.isEmpty then pure (op, []) else
        -- (Else at what the handled computation performs it at.)
        match w.atomTy thunk with
        | some (.fn _ _ eff _ _) => (eff.lookup op).map (op, ·)
        | _ => none
    let w := { w with hints := w.hints.push (do pure (.handler (← ρ) (← H))) }
    go env depth f c (w.bind ρ false) body
  | .perform _ _ body => go env depth f c (w.bind none false) body
  | .label thunk body | .guard _ thunk body | .cell _ thunk body | .cellL _ _ thunk body | .lend _ _ thunk _ _ body =>
    go env depth f c (w.bind ((w.atomTy thunk).bind retOf) false) body
  | .cancel _ body => go env depth f c (w.bind (some .unit) false) body
  | .mem op args body => go env depth f c (w.bind (memTy env w.Γ op args) false) body
  | .host id args body => go env depth f c (w.bind (hostTy id args) (2 ≤ id)) body

/-- What a label's scope `g` gives, its body gone through with a label of a
result not known: what it ends with where that returns. -/
partial def labelRet (env : Env) (depth : Nat) (g : Nat) (binds : List (String × Ty)) (caps : List Ty) : Option Ty :=
  match fnRet env (depth + 1) g binds [.fn [.never] .never [] false none] caps with
  | some .never | none => none
  | r => r

/-- What `g` gives at what it is given and made with: its first clause's
that says. -/
partial def fnRet (env : Env) (depth : Nat) (g : Nat) (binds : List (String × Ty)) (params caps : List Ty) : Option Ty := do
  if depth > 12 then none
  let fn ← env.p.fns[g]?
  -- (A function of its own: its type parameters of what it is given.)
  let binds := match env.selfTy[g]? with
    | some (.fn ps _) => (ps.zip params).foldl (fun b (a, p) => matchTy env.decls b a p) []
    | _ => binds
  fn.clauses.zipIdx.findSome? fun (cl, ci) => do
    let bound ← patsTysD env.decls cl.pats params
    (go env depth g ci { Γ := (params ++ caps ++ bound).toArray.map some, binds } cl.body).2

end

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
      let (w, _) := go env 0 e.fn ci { Γ, binds } cl.body
      t := { t with closureBinds := w.made.foldl (fun m (k, b) => m.insert k b) t.closureBinds }
      if w.hints.size != hs.length then
        t := { t with lost := t.lost + 1 }
        continue
      let localOf : Std.HashMap Nat Nat := w.hintAt.fold (fun m i h => m.insert h i) {}
      for ((mine, theirs), h) in (w.hints.toList.zip hs).zipIdx do
        match theirs with
        | .ty σ =>
          let r := mine.map fun | .ty m => shape m == shape σ | _ => false
          let ex := if r == some false then
              some s!"{env.names[e.fn]?.getD "?"}: here {(mine.map fun | .ty m => Typer.showTy m | _ => "?").getD "?"}, Typer {Typer.showTy σ}"
            else if r.isNone && (t.counts.getD "nf" (0,0,0)).1 % 97 == 0 then
              some s!"not found: {env.names[e.fn]?.getD "?"} local {(localOf[h]?).getD 0} ({env.said[(e.fn, ci, (localOf[h]?).getD 0)]?.isSome}): Typer {Typer.showTy σ}"
            else none
          let t' := if r.isNone then t.add "nf" (some true) else t
          let kind := match σ with
            | .fn .. => "callable"
            | .data .. => "data"
            | .tuple _ => "tuple"
            | _ => "other"
          t := t'.add kind r ex
        | .handler ρ H =>
          let r := mine.map fun
            | .handler ρ' H' => (ρ' == .never || shape ρ' == shape ρ) && H' == H
            | _ => false
          let shown : Option String := mine.map fun
            | .handler ρ' H' => s!"{Typer.showTy ρ'} {H'.map (·.1)}"
            | _ => "?"
          let ex := if r == some false then some s!"{env.names[e.fn]?.getD "?"}: handler here {shown.getD "?"}, Typer {Typer.showTy ρ} {H.map (·.1)}" else none
          t := t.add "handler" r ex
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
