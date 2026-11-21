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

/-- Where a node is in its body's arrays. -/
abbrev ExprId := Nat
abbrev StmtId := Nat
abbrev ClauseId := Nat

deriving instance BEq for Pattern

/-- An expression, its parts by place (`Syntax.Expr`). -/
inductive FExpr where
  | int (n : Int)
  | name (qual : Option String) (name : String)
  | label (name : String)
  | call (id : Nat) (f : ExprId) (args : Array ExprId)
  | tailCall (id : Nat) (f : ExprId) (args : Array ExprId)
  | tuple (args : Array ExprId)
  | proj (e : ExprId) (idx : Nat)
  | closure (id : Nat) (clauses : Array ClauseId)
  | handle (subject : ExprId) (arms : Array ClauseId)
  | labelScope (name : String) (body : Array StmtId)
  | ref (uniq : Bool) (name : String)
  | deref (e : ExprId)
  | reborrow (uniq : Bool) (e : ExprId)
  | refField (id : Nat) (uniq : Bool) (name : String) (path : List String) (star : Bool)
  | fieldOf (id : Nat) (e : ExprId) (name : String)
  deriving Inhabited, Hashable, BEq

/-- A statement, its parts by place (`Syntax.Stmt`). -/
inductive FStmt where
  | let_ (pat : Pattern) (value : ExprId)
  | expr (e : ExprId)
  | defer (e : ExprId)
  | letMut (name : String) (value : ExprId)
  | assign (target : ExprId) (value : ExprId)
  | located (line col : Nat) (s : StmtId)
  deriving Inhabited, Hashable, BEq

/-- A clause: its patterns, and its body's statements by place. -/
structure FClause where
  pats : List Pattern
  body : Array StmtId
  deriving Inhabited, Hashable, BEq

/-- A declaration's body: its nodes, each kind in an array of its own, and
its own clauses (`roots`). -/
structure Body where
  exprs : Array FExpr := #[]
  stmts : Array FStmt := #[]
  clauses : Array FClause := #[]
  roots : Array ClauseId := #[]
  deriving Inhabited, Hashable, BEq

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

mutual

/-- Is `p` true of an expression or of one inside it, blocks' too? -/
partial def anyExpr (b : Body) (p : FExpr → Bool) (e : ExprId) : Bool :=
  let n := b.expr e
  p n || match n with
    | .call _ f args | .tailCall _ f args => b.anyExpr p f || args.any (b.anyExpr p)
    | .tuple args => args.any (b.anyExpr p)
    | .proj e _ | .deref e | .reborrow _ e | .fieldOf _ e _ => b.anyExpr p e
    | .closure _ cs => cs.any (b.anyClause p)
    | .handle s cs => b.anyExpr p s || cs.any (b.anyClause p)
    | .labelScope _ body => body.any (b.anyStmt p)
    | _ => false

partial def anyClause (b : Body) (p : FExpr → Bool) (c : ClauseId) : Bool :=
  (b.clause c).body.any (b.anyStmt p)

partial def anyStmt (b : Body) (p : FExpr → Bool) (s : StmtId) : Bool :=
  (b.stmtExprs s).any (b.anyExpr p)

end

end Body

/-! ## From trees -/

/-- The nodes made so far. -/
abbrev Build := StateM Body

def pushExpr (e : FExpr) : Build ExprId := modifyGet fun b => (b.exprs.size, { b with exprs := b.exprs.push e })
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

/-! ## Items with flat bodies -/

/-- An item whose functions' clauses, and whose constant's value, are flat
bodies of their own; an item with no code is as it was (`other`). -/
inductive FItem where
  | fn (name : String) (params : List String) (annots : List (Option TypeExpr))
      (ret : Option TypeExpr) (body : Body)
  | alias (name : String) (body : Body) (value : ExprId)
  | impl (params : List String) (trait : String) (head : String) (args : List String)
      (context : List (String × String)) (methods : List FItem)
  | traitInfo (name : String) (supers : List String) (defaults : List FItem)
      (params : List String) (assocs : List String)
  | module (name : String) (body : Option (List FItem))
  | pub (parent : Bool) (item : FItem)
  | other (item : Item)
  deriving Inhabited, Hashable

/-- An item with its code flat. -/
partial def ofItem : Item → FItem
  | .fn n ps annots ret clauses => .fn n ps annots ret (ofClauses clauses)
  | .alias n v => let (b, e) := ofExpr v; .alias n b e
  | .impl ps tr head args ctx ms => .impl ps tr head args ctx (ms.map ofItem)
  | .traitInfo n supers ds ps assocs => .traitInfo n supers (ds.map ofItem) ps assocs
  | .module n body => .module n (body.map (·.map ofItem))
  | .pub parent item => .pub parent (ofItem item)
  | item => .other item

/-- The item as a tree again. -/
partial def FItem.toItem : FItem → Item
  | .fn n ps annots ret b => .fn n ps annots ret (toClauses b)
  | .alias n b e => .alias n (treeExpr b e)
  | .impl ps tr head args ctx ms => .impl ps tr head args ctx (ms.map FItem.toItem)
  | .traitInfo n supers ds ps assocs => .traitInfo n supers (ds.map FItem.toItem) ps assocs
  | .module n body => .module n (body.map (·.map FItem.toItem))
  | .pub parent item => .pub parent item.toItem
  | .other item => item

def ofItems (items : List Item) : List FItem := items.map ofItem

/-- The item as what it declares: every function in it, at any depth,
without its clauses (whose bodies `FItem.bodies` gives). -/
partial def FItem.declared : FItem → Item
  | .fn n ps annots ret _ => .fn n ps annots ret []
  | .alias n b e => .alias n (treeExpr b e)
  | .impl ps tr head args ctx ms => .impl ps tr head args ctx (ms.map FItem.declared)
  | .traitInfo n supers ds ps assocs => .traitInfo n supers (ds.map FItem.declared) ps assocs
  | .module n body => .module n (body.map (·.map FItem.declared))
  | .pub parent item => .pub parent item.declared
  | .other item => item

/-- Every body in an item: its functions' at any depth, and a constant's. -/
partial def FItem.allBodies : FItem → List Body
  | .fn _ _ _ _ b => [b]
  | .alias _ b _ => [b]
  | .impl _ _ _ _ _ ms => ms.flatMap FItem.allBodies
  | .traitInfo _ _ ds _ _ => ds.flatMap FItem.allBodies
  | .module _ (some body) => body.flatMap FItem.allBodies
  | .pub _ item => item.allBodies
  | _ => []

/-- The bodies of an item's functions, each under the name the function is
checked by: its own, or an implementation's (`implFnName`). -/
partial def FItem.bodies : FItem → List (String × Body)
  | .fn n _ _ _ b => [(n, b)]
  | .impl _ tr head _ _ ms => ms.filterMap fun
    | .fn m _ _ _ b => some (implFnName tr head m, b)
    | _ => none
  | .pub _ item => item.bodies
  | _ => []
def toItems (items : List FItem) : List Item := items.map FItem.toItem

/-- Every function of these items with its body made by `f`: in
implementations, traits' defaults and modules too (`Item.mapClauses`). -/
partial def FItem.mapBodies (f : Body → Body) : FItem → FItem
  | .fn n ps annots ret b => .fn n ps annots ret (f b)
  | .impl ps tr head args ctx ms => .impl ps tr head args ctx (ms.map (·.mapBodies f))
  | .traitInfo n supers ds ps assocs => .traitInfo n supers (ds.map (·.mapBodies f)) ps assocs
  | .module n (some body) => .module n (some (body.map (·.mapBodies f)))
  | .pub parent item => .pub parent (item.mapBodies f)
  | item => item

/-- Do clauses come back as they were from their body? -/
def roundTrips (clauses : List Clause) : Bool :=
  hash (toClauses (ofClauses clauses)) == hash clauses

/-- Does every function of these items come back as it was from its body? -/
partial def itemsRoundTrip (items : List Item) : Bool :=
  items.all fun
    | .fn _ _ _ _ clauses => roundTrips clauses
    | .impl _ _ _ _ _ methods => itemsRoundTrip methods
    | .traitInfo _ _ defaults _ _ => itemsRoundTrip defaults
    | .module _ (some body) => itemsRoundTrip body
    | .pub _ item => itemsRoundTrip [item]
    | .alias _ value => let (b, e) := ofExpr value; hash (treeExpr b e) == hash value
    | _ => true

end Glorious.Syntax.Flat
