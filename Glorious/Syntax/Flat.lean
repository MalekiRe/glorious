module

public import Glorious.Syntax.Ast

/-!
# A declaration's body, flat

A function's clauses as trees: each pass over a program rebuilds every node it
passes through. Flat, a body's expressions, statements and clauses are each
one array, and a node names its parts by their places in those (`ExprId`,
...). Every expression has a place of its own in its body, by which what is
decided of it can be said beside it rather than written into a copy of the
tree. Each declaration has a body of its own, so that its places do not move
when another declaration changes, and a body is the same value wherever the
same text is (per-declaration caching).

Patterns and types stay trees: they are small, and are read whole.

`ofClauses` and `toClauses` go between the two; `toClauses (ofClauses cs)` is
`cs` again (checked of the prelude, the library and every example,
`Checks`).
-/

public section

namespace Glorious.Syntax.Flat

/-- A node with each node directly in it made by `fe`, a callable's clauses by
`fc` and a block's statements by `fb`; the rest as it is. -/
@[specialize] def FExpr.mapIds {m : Type → Type} [Monad m] (fe : ExprId → m ExprId)
    (fc : ClauseId → m ClauseId) (fb : Array StmtId → m (Array StmtId)) : FExpr → m FExpr
  | .call id f args => do pure (.call id (← fe f) (← args.mapM fe))
  | .tailCall id f args => do pure (.tailCall id (← fe f) (← args.mapM fe))
  | .tuple args => do pure (.tuple (← args.mapM fe))
  | .proj x i => do pure (.proj (← fe x) i)
  | .closure id cs => do pure (.closure id (← cs.mapM fc))
  | .handle s cs => do pure (.handle (← fe s) (← cs.mapM fc))
  | .labelScope l body => do pure (.labelScope l (← fb body))
  | .deref x => do pure (.deref (← fe x))
  | .reborrow u x => do pure (.reborrow u (← fe x))
  | .fieldOf id x n => do pure (.fieldOf id (← fe x) n)
  | n => pure n

/-- A statement with its expressions made by `fe`, the statement it places by
`fs` and a `let`'s pattern by `fp`. -/
@[specialize] def FStmt.mapIds {m : Type → Type} [Monad m] (fe : ExprId → m ExprId)
    (fs : StmtId → m StmtId) (fp : Pattern → Pattern := id) : FStmt → m FStmt
  | .let_ p v => do pure (.let_ (fp p) (← fe v))
  | .expr v => do pure (.expr (← fe v))
  | .defer v => do pure (.defer (← fe v))
  | .letMut x v => do pure (.letMut x (← fe v))
  | .assign t v => do pure (.assign (← fe t) (← fe v))
  | .located l c inner => do pure (.located l c (← fs inner))

namespace Body

@[inline] def expr (b : Body) (e : ExprId) : FExpr := b.exprs[e]!
@[inline] def stmt (b : Body) (s : StmtId) : FStmt := b.stmts[s]!
@[inline] def clause (b : Body) (c : ClauseId) : FClause := b.clauses[c]!

/-- The statement under its places (`located`), with the place of the
innermost. -/
partial def unlocated (b : Body) (s : StmtId) : StmtId :=
  match b.stmt s with
  | .located _ _ inner => b.unlocated inner
  | _ => s

/-- The expressions a statement has (`Stmt.exprs`). -/
partial def stmtExprs (b : Body) (s : StmtId) : Array ExprId :=
  match b.stmt s with
  | .let_ _ v | .expr v | .defer v | .letMut _ v => #[v]
  | .assign t v => #[t, v]
  | .located _ _ s => b.stmtExprs s

/-- The expressions directly inside an expression, outside any block
(`Expr.direct`). -/
def direct (b : Body) (e : ExprId) : Array ExprId :=
  match b.expr e with
  | .call _ f args | .tailCall _ f args => #[f] ++ args
  | .tuple args => args
  | .proj e _ | .deref e | .reborrow _ e | .fieldOf _ e _ => #[e]
  | .handle subject _ => #[subject]
  | _ => #[]

/-- `direct`'s expressions folded from the left, without making the array. -/
@[inline] def foldDirect {α : Type} (b : Body) (f : α → ExprId → α) (init : α) (e : ExprId) : α :=
  match b.expr e with
  | .call _ g args | .tailCall _ g args => args.foldl f (f init g)
  | .tuple args => args.foldl f init
  | .proj x _ | .deref x | .reborrow _ x | .fieldOf _ x _ | .handle x _ => f init x
  | _ => init

/-- `direct`'s expressions folded from the right, without making the array. -/
@[inline] def foldrDirect {α : Type} (b : Body) (f : ExprId → α → α) (init : α) (e : ExprId) : α :=
  match b.expr e with
  | .call _ g args | .tailCall _ g args => f g (args.foldr f init)
  | .tuple args => args.foldr f init
  | .proj x _ | .deref x | .reborrow _ x | .fieldOf _ x _ | .handle x _ => f x init
  | _ => init

/-- The body with each of its own clauses begun by `%unsafe`: what follows
may name what is unsafe (`unsafe fn`). -/
def unsafeBody (b : Body) : Body :=
  let (e, b) := b.add (.mark .unsafe_)
  let s := b.stmts.size
  { b with stmts := b.stmts.push (.expr e),
           clauses := b.roots.foldl (fun cs c => cs.modify c fun ⟨pats, body⟩ => ⟨pats, #[s] ++ body⟩) b.clauses }

/-- The mark an expression is, if it is one (`Syntax.Mark`). -/
@[inline] def mark? (b : Body) (e : ExprId) : Option Mark :=
  match b.expr e with
  | .mark m => some m
  | _ => none

/-- The type written where `e` is, among expressions (`FExpr.type`); `_`
where it is none. -/
@[inline] def typeAt (b : Body) (e : ExprId) : TypeExpr :=
  match b.expr e with
  | .type t => t
  | _ => .hole

/-- Is the expression a call marked `m`, `%as(value, type)`? Its arguments. -/
@[inline] def marked? (b : Body) (m : Mark) (e : ExprId) : Option (Array ExprId) :=
  match b.expr e with
  | .call _ f args => if b.mark? f == some m then some args else none
  | _ => none

/-- The name an expression is, if it is one. -/
@[inline] def name? (b : Body) (e : ExprId) : Option (Option String × String) :=
  match b.expr e with
  | .name q x => some (q, x)
  | _ => none

/-- The name an expression is, if it is one written without a path. -/
@[inline] def bare? (b : Body) (e : ExprId) : Option String :=
  match b.expr e with
  | .name none x => some x
  | _ => none

/-- The expressions one level down, blocks' too. -/
def children (b : Body) (e : ExprId) : List ExprId :=
  (b.direct e).toList ++ match b.expr e with
    | .closure _ cs | .handle _ cs => cs.toList.flatMap fun c => (b.clause c).body.toList.flatMap fun s => (b.stmtExprs s).toList
    | .labelScope _ body => body.toList.flatMap fun s => (b.stmtExprs s).toList
    | _ => []

mutual

/-- Is `p` true of an expression or of one inside it, blocks' too? -/
partial def anyExpr (b : Body) (p : FExpr → Bool) (e : ExprId) : Bool :=
  let n := b.expr e
  p n || match n with
    | .closure _ cs => cs.any (b.anyClause p)
    | .handle s cs => b.anyExpr p s || cs.any (b.anyClause p)
    | .labelScope _ body => body.any (b.anyStmt p)
    | _ => b.foldDirect (fun a x => a || b.anyExpr p x) false e

partial def anyClause (b : Body) (p : FExpr → Bool) (c : ClauseId) : Bool :=
  (b.clause c).body.any (b.anyStmt p)

partial def anyStmt (b : Body) (p : FExpr → Bool) (s : StmtId) : Bool :=
  (b.stmtExprs s).any (b.anyExpr p)

end

end Body

/-! ## From trees -/

/-- The nodes made so far. -/
abbrev Build := StateM Body

def pushExpr (e : FExpr) : Build ExprId := modifyGet fun b => b.add e
def pushStmt (s : FStmt) : Build StmtId := modifyGet fun b => (b.stmts.size, { b with stmts := b.stmts.push s })
def pushClause (c : FClause) : Build ClauseId := modifyGet fun b => (b.clauses.size, { b with clauses := b.clauses.push c })

mutual

partial def flatExpr : Expr → Build ExprId
  | .int n => pushExpr (.int n)
  | .name q x => pushExpr (.name q x)
  | .label x => pushExpr (.label x)
  | .call id f args => do
    let f ← flatExpr f
    let args ← args.toArray.mapM flatExpr
    pushExpr (.call id f args)
  | .tailCall id f args => do
    let f ← flatExpr f
    let args ← args.toArray.mapM flatExpr
    pushExpr (.tailCall id f args)
  | .tuple args => do
    let args ← args.toArray.mapM flatExpr
    pushExpr (.tuple args)
  | .proj e i => do pushExpr (.proj (← flatExpr e) i)
  | .closure id clauses => do
    let cs ← clauses.toArray.mapM flatClause
    pushExpr (.closure id cs)
  | .handle subject arms => do
    let s ← flatExpr subject
    let cs ← arms.toArray.mapM flatClause
    pushExpr (.handle s cs)
  | .labelScope x body => do
    let b ← body.toArray.mapM flatStmt
    pushExpr (.labelScope x b)
  | .ref uniq x => pushExpr (.ref uniq x)
  | .deref e => do pushExpr (.deref (← flatExpr e))
  | .reborrow uniq e => do pushExpr (.reborrow uniq (← flatExpr e))
  | .refField id uniq x path star => pushExpr (.refField id uniq x path star)
  | .fieldOf id e x => do pushExpr (.fieldOf id (← flatExpr e) x)
  | .mark m => pushExpr (.mark m)
  | .type t => pushExpr (.type t)

partial def flatStmt : Stmt → Build StmtId
  | .let_ p v => do pushStmt (.let_ p (← flatExpr v))
  | .expr e => do pushStmt (.expr (← flatExpr e))
  | .defer e => do pushStmt (.defer (← flatExpr e))
  | .letMut x v => do pushStmt (.letMut x (← flatExpr v))
  | .assign t v => do
    let t ← flatExpr t
    let v ← flatExpr v
    pushStmt (.assign t v)
  | .located l c s => do pushStmt (.located l c (← flatStmt s))

partial def flatClause : Clause → Build ClauseId
  | .mk pats body => do
    let b ← body.toArray.mapM flatStmt
    pushClause ⟨pats, b⟩

end

/-- Clauses as a body of their own. -/
def ofClauses (clauses : List Clause) : Body :=
  let (roots, b) := (clauses.toArray.mapM flatClause).run {}
  { b with roots }

/-- An expression as a body of its own, and its place there. -/
def ofExpr (e : Expr) : Body × ExprId :=
  let (id, b) := (flatExpr e).run {}
  (b, id)

/-! ## Back to trees -/

instance : Inhabited Stmt := ⟨.expr (.int 0)⟩
instance : Inhabited Clause := ⟨.mk [] []⟩
instance : Inhabited Item := ⟨.fixity⟩

mutual

partial def treeExpr (b : Body) (e : ExprId) : Expr :=
  match b.expr e with
  | .int n => .int n
  | .name q x => .name q x
  | .label x => .label x
  | .call id f args => .call id (treeExpr b f) (args.toList.map (treeExpr b))
  | .tailCall id f args => .tailCall id (treeExpr b f) (args.toList.map (treeExpr b))
  | .tuple args => .tuple (args.toList.map (treeExpr b))
  | .proj e i => .proj (treeExpr b e) i
  | .closure id cs => .closure id (cs.toList.map (treeClause b))
  | .handle s cs => .handle (treeExpr b s) (cs.toList.map (treeClause b))
  | .labelScope x body => .labelScope x (body.toList.map (treeStmt b))
  | .ref uniq x => .ref uniq x
  | .deref e => .deref (treeExpr b e)
  | .reborrow uniq e => .reborrow uniq (treeExpr b e)
  | .refField id uniq x path star => .refField id uniq x path star
  | .fieldOf id e x => .fieldOf id (treeExpr b e) x
  | .mark m => .mark m
  | .type t => .type t

partial def treeStmt (b : Body) (s : StmtId) : Stmt :=
  match b.stmt s with
  | .let_ p v => .let_ p (treeExpr b v)
  | .expr e => .expr (treeExpr b e)
  | .defer e => .defer (treeExpr b e)
  | .letMut x v => .letMut x (treeExpr b v)
  | .assign t v => .assign (treeExpr b t) (treeExpr b v)
  | .located l c s => .located l c (treeStmt b s)

partial def treeClause (b : Body) (c : ClauseId) : Clause :=
  let ⟨ps, body⟩ := b.clause c
  .mk ps (body.toList.map (treeStmt b))

end

/-- A body's own clauses as trees again. -/
def toClauses (b : Body) : List Clause := b.roots.toList.map (treeClause b)

/-! ## A body without what nothing reaches

A pass writes what it makes after what was there; what it made anew of is
then reached by nothing. `compact` copies what the roots reach, in order,
into a body of its own. -/

mutual

partial def compactExpr (src : Body) (e : ExprId) : Build ExprId := do
  pushExpr (← (src.expr e).mapIds (compactExpr src) (compactClause src) (·.mapM (compactStmt src)))

partial def compactStmt (src : Body) (s : StmtId) : Build StmtId := do
  pushStmt (← (src.stmt s).mapIds (compactExpr src) (compactStmt src))

partial def compactClause (src : Body) (c : ClauseId) : Build ClauseId := do
  let ⟨pats, body⟩ := src.clause c
  pushClause ⟨pats, ← body.mapM (compactStmt src)⟩

end

/-- The body with only what its roots reach. -/
def Body.compact (b : Body) : Body :=
  let (roots, nb) := (b.roots.mapM (compactClause b)).run {}
  { nb with roots }

/-- Do clauses come back as they were from their body? -/
def roundTrips (clauses : List Clause) : Bool :=
  hash (toClauses (ofClauses clauses)) == hash clauses

end Glorious.Syntax.Flat

/-! ## Items -/

namespace Glorious.Syntax

open Flat

/-- A function written as clauses, its body flat. -/
def Item.fnOf (name : String) (params : List String) (annots : List (Option TypeExpr))
    (ret : Option TypeExpr) (clauses : List Clause) : Item :=
  .fn name params annots ret (ofClauses clauses)

/-- A constant or another name of a constructor, its value flat. -/
def Item.aliasOf (name : String) (value : Expr) : Item :=
  let (b, e) := ofExpr value
  .alias name b e

/-- The item as what it declares: every function in it, at any depth,
without its clauses (whose bodies `Item.bodies` gives). -/
partial def Item.declared : Item → Item
  | .fn n ps annots ret _ => .fn n ps annots ret {}
  | .impl whole@{ methods := ms, .. } => .impl { whole with methods := (ms.map Item.declared) }
  | .traitInfo n supers ds ps assocs => .traitInfo n supers (ds.map Item.declared) ps assocs
  | .module n body => .module n (body.map (·.map Item.declared))
  | .pub parent item => .pub parent item.declared
  | item => item

/-- Every body in an item: its functions' at any depth, and a constant's. -/
partial def Item.allBodies : Item → List Body
  | .fn _ _ _ _ b => [b]
  | .alias _ b _ => [b]
  | .impl { methods := ms, .. } => ms.flatMap Item.allBodies
  | .traitInfo _ _ ds _ _ => ds.flatMap Item.allBodies
  | .module _ (some body) => body.flatMap Item.allBodies
  | .pub _ item => item.allBodies
  | _ => []

/-- The bodies of an item's functions, each under the name the function is
checked by: its own, or an implementation's (`implFnName`). -/
partial def Item.bodies : Item → List (String × Body)
  | .fn n _ _ _ b => [(n, b)]
  | .impl { trait := tr, head := head, methods := ms, .. } => ms.filterMap fun
    | .fn m _ _ _ b => some (implFnName tr.spelled head m, b)
    | _ => none
  | .pub _ item => item.bodies
  | _ => []

/-- Every function of these items with its body made by `f`: in
implementations, traits' defaults and modules too. -/
partial def Item.mapBodies (f : Body → Body) : Item → Item
  | .fn n ps annots ret b => .fn n ps annots ret (f b)
  | .impl whole@{ methods := ms, .. } => .impl { whole with methods := (ms.map (·.mapBodies f)) }
  | .traitInfo n supers ds ps assocs => .traitInfo n supers (ds.map (·.mapBodies f)) ps assocs
  | .module n (some body) => .module n (some (body.map (·.mapBodies f)))
  | .pub parent item => .pub parent (item.mapBodies f)
  | item => item

/-- Every body of these items with only what its roots reach; a constant's
too. -/
partial def Item.compact : Item → Item
  | .alias n b e => let (e, nb) := (compactExpr b e).run {}; .alias n nb e
  | .impl whole@{ methods := ms, .. } => .impl { whole with methods := (ms.map Item.compact) }
  | .traitInfo n supers ds ps assocs => .traitInfo n supers (ds.map Item.compact) ps assocs
  | .module n (some body) => .module n (some (body.map Item.compact))
  | .pub parent item => .pub parent item.compact
  | .fn n ps annots ret b => .fn n ps annots ret b.compact
  | item => item

end Glorious.Syntax
