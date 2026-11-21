module

public import Glorious.Syntax.Ast

/-!
# A module's items, flat

The parser's items are trees: each pass over a program rebuilds every node it
passes through, and keeping a parsed module keeps every node apart. Flat, a
module's expressions, statements, clauses and patterns are each one array,
and a node names its parts by their places in those (`ExprId`, ...). Every
expression has a place of its own, by which what is decided of it can be said
beside it rather than written into a copy of the tree.

`flatten` and `unflatten` go between the two; `unflatten (flatten items)` is
the items again (checked of the prelude, the library and every example,
`Checks`). Types stay trees: they are small, and the checker reads them whole.
-/

public section

namespace Glorious.Syntax.Flat

/-- Where a node is in its module's arrays. -/
abbrev ExprId := Nat
abbrev StmtId := Nat
abbrev ClauseId := Nat
abbrev PatId := Nat

/-- A pattern, its parts by place. -/
inductive FPat where
  | wild
  | var (name : String)
  | int (n : Int)
  | ctor (name : String) (qual : Option String) (args : Array PatId)
  | tuple (args : Array PatId)
  deriving Inhabited, Hashable, BEq

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
  | let_ (pat : PatId) (value : ExprId)
  | expr (e : ExprId)
  | defer (e : ExprId)
  | letMut (name : String) (value : ExprId)
  | assign (target : ExprId) (value : ExprId)
  | located (line col : Nat) (s : StmtId)
  deriving Inhabited, Hashable, BEq

/-- A clause: its patterns and its body, by place. -/
structure FClause where
  pats : Array PatId
  body : Array StmtId
  deriving Inhabited, Hashable, BEq

/-- An item, its functions' clauses by place (`Syntax.Item`). -/
inductive FItem where
  | enum (name : String) (params : List String) (ctors : List (String × List TypeExpr))
  | struct (name : String) (params : List String) (fields : List TypeExpr)
  | effect (name : String) (params : List String) (ops : List OpDecl)
  | fn (name : String) (params : List String) (annots : List (Option TypeExpr))
      (ret : Option TypeExpr) (clauses : Array ClauseId)
  | alias (name : String) (value : ExprId)
  | fixity
  | coerce (name : String)
  | trait (name : String) (methods : List (String × List TypeExpr × Option TypeExpr))
  | impl (params : List String) (trait : String) (head : String) (args : List String)
      (context : List (String × String)) (methods : Array FItem)
  | use (head : String) (lower : Nat) (upper : Option Nat)
  | fieldNames (ctor : String) (names : List String) (pubs : List Bool)
  | typeAlias (name : String) (params : List String) (body : TypeExpr)
  | traitInfo (name : String) (supers : List String) (defaults : Array FItem)
      (params : List String) (assocs : List String)
  | bounds (fn : String) (bounds : List Bound)
  | pub (parent : Bool) (item : FItem)
  | unsafeFn (name : String)
  | module (name : String) (body : Option (Array FItem))
  | import (path : List String) (rename : Option String) (glob : Bool)
  deriving Inhabited

/-- A module's items, flat: the nodes, each kind in an array of its own, and
the items, which name the nodes by place. -/
structure Module where
  exprs : Array FExpr := #[]
  stmts : Array FStmt := #[]
  clauses : Array FClause := #[]
  pats : Array FPat := #[]
  items : Array FItem := #[]
  deriving Inhabited

/-! ## From trees -/

/-- The nodes made so far. -/
abbrev Build := StateM Module

def pushPat (p : FPat) : Build PatId := modifyGet fun m => (m.pats.size, { m with pats := m.pats.push p })
def pushExpr (e : FExpr) : Build ExprId := modifyGet fun m => (m.exprs.size, { m with exprs := m.exprs.push e })
def pushStmt (s : FStmt) : Build StmtId := modifyGet fun m => (m.stmts.size, { m with stmts := m.stmts.push s })
def pushClause (c : FClause) : Build ClauseId := modifyGet fun m => (m.clauses.size, { m with clauses := m.clauses.push c })

partial def flatPat : Pattern → Build PatId
  | .wild => pushPat .wild
  | .var x => pushPat (.var x)
  | .int n => pushPat (.int n)
  | .ctor name qual args => do
    let args ← args.toArray.mapM flatPat
    pushPat (.ctor name qual args)
  | .tuple args => do
    let args ← args.toArray.mapM flatPat
    pushPat (.tuple args)

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
  | .let_ p v => do
    let p ← flatPat p
    let v ← flatExpr v
    pushStmt (.let_ p v)
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
    let ps ← pats.toArray.mapM flatPat
    let b ← body.toArray.mapM flatStmt
    pushClause ⟨ps, b⟩

end

partial def flatItem : Item → Build FItem
  | .enum n ps cs => pure (.enum n ps cs)
  | .struct n ps fs => pure (.struct n ps fs)
  | .effect n ps ops => pure (.effect n ps ops)
  | .fn n ps annots ret clauses => do
    let cs ← clauses.toArray.mapM flatClause
    pure (.fn n ps annots ret cs)
  | .alias n v => do pure (.alias n (← flatExpr v))
  | .fixity => pure .fixity
  | .coerce n => pure (.coerce n)
  | .trait n ms => pure (.trait n ms)
  | .impl ps tr head args context methods => do
    let ms ← methods.toArray.mapM flatItem
    pure (.impl ps tr head args context ms)
  | .use head lo hi => pure (.use head lo hi)
  | .fieldNames c ns ps => pure (.fieldNames c ns ps)
  | .typeAlias n ps body => pure (.typeAlias n ps body)
  | .traitInfo n supers defaults ps assocs => do
    let ds ← defaults.toArray.mapM flatItem
    pure (.traitInfo n supers ds ps assocs)
  | .bounds f bs => pure (.bounds f bs)
  | .pub parent item => do pure (.pub parent (← flatItem item))
  | .unsafeFn n => pure (.unsafeFn n)
  | .module n none => pure (.module n none)
  | .module n (some body) => do
    let b ← body.toArray.mapM flatItem
    pure (.module n (some b))
  | .import path rename glob => pure (.import path rename glob)

/-- A module's items, flat. -/
def flatten (items : List Item) : Module :=
  let (fs, m) := (items.toArray.mapM flatItem).run {}
  { m with items := fs }

/-! ## Back to trees -/

instance : Inhabited Stmt := ⟨.expr (.int 0)⟩
instance : Inhabited Clause := ⟨.mk [] []⟩
instance : Inhabited Item := ⟨.fixity⟩

partial def treePat (m : Module) (p : PatId) : Pattern :=
  match m.pats[p]? with
  | some .wild => .wild
  | some (.var x) => .var x
  | some (.int n) => .int n
  | some (.ctor name qual args) => .ctor name qual (args.toList.map (treePat m))
  | some (.tuple args) => .tuple (args.toList.map (treePat m))
  | none => .wild

mutual

partial def treeExpr (m : Module) (e : ExprId) : Expr :=
  match m.exprs[e]? with
  | some (.int n) => .int n
  | some (.name q x) => .name q x
  | some (.label x) => .label x
  | some (.call id f args) => .call id (treeExpr m f) (args.toList.map (treeExpr m))
  | some (.tailCall id f args) => .tailCall id (treeExpr m f) (args.toList.map (treeExpr m))
  | some (.tuple args) => .tuple (args.toList.map (treeExpr m))
  | some (.proj e i) => .proj (treeExpr m e) i
  | some (.closure id cs) => .closure id (cs.toList.map (treeClause m))
  | some (.handle s cs) => .handle (treeExpr m s) (cs.toList.map (treeClause m))
  | some (.labelScope x b) => .labelScope x (b.toList.map (treeStmt m))
  | some (.ref uniq x) => .ref uniq x
  | some (.deref e) => .deref (treeExpr m e)
  | some (.reborrow uniq e) => .reborrow uniq (treeExpr m e)
  | some (.refField id uniq x path star) => .refField id uniq x path star
  | some (.fieldOf id e x) => .fieldOf id (treeExpr m e) x
  | none => .int 0

partial def treeStmt (m : Module) (s : StmtId) : Stmt :=
  match m.stmts[s]? with
  | some (.let_ p v) => .let_ (treePat m p) (treeExpr m v)
  | some (.expr e) => .expr (treeExpr m e)
  | some (.defer e) => .defer (treeExpr m e)
  | some (.letMut x v) => .letMut x (treeExpr m v)
  | some (.assign t v) => .assign (treeExpr m t) (treeExpr m v)
  | some (.located l c s) => .located l c (treeStmt m s)
  | none => .expr (.int 0)

partial def treeClause (m : Module) (c : ClauseId) : Clause :=
  match m.clauses[c]? with
  | some ⟨ps, b⟩ => .mk (ps.toList.map (treePat m)) (b.toList.map (treeStmt m))
  | none => .mk [] []

end

partial def treeItem (m : Module) : FItem → Item
  | .enum n ps cs => .enum n ps cs
  | .struct n ps fs => .struct n ps fs
  | .effect n ps ops => .effect n ps ops
  | .fn n ps annots ret cs => .fn n ps annots ret (cs.toList.map (treeClause m))
  | .alias n v => .alias n (treeExpr m v)
  | .fixity => .fixity
  | .coerce n => .coerce n
  | .trait n ms => .trait n ms
  | .impl ps tr head args context ms => .impl ps tr head args context (ms.toList.map (treeItem m))
  | .use head lo hi => .use head lo hi
  | .fieldNames c ns ps => .fieldNames c ns ps
  | .typeAlias n ps body => .typeAlias n ps body
  | .traitInfo n supers ds ps assocs => .traitInfo n supers (ds.toList.map (treeItem m)) ps assocs
  | .bounds f bs => .bounds f bs
  | .pub parent item => .pub parent (treeItem m item)
  | .unsafeFn n => .unsafeFn n
  | .module n none => .module n none
  | .module n (some b) => .module n (some (b.toList.map (treeItem m)))
  | .import path rename glob => .import path rename glob

/-- A module's items as trees again. -/
def unflatten (m : Module) : List Item := m.items.toList.map (treeItem m)

end Glorious.Syntax.Flat
