module

public import Glorious.Syntax.Flat

/-!
# What is asked of a flat body

The questions the checker asks of a function's code, asked of its flat body
(`Flat.Body`): the names free in it, how a name is used, whether a value is
given away, and the like. Each is the tree's (`Syntax`, `Elab`) asked of the
nodes by place; a statement list is walked as a list of places.
-/

public section

namespace Glorious.Syntax.Flat

namespace Body

/-- The label `@l` as a name in scope (`Elab.labelName`). -/
def labelName (l : String) : String := "@" ++ l

/-- A body's statements as a list of places. -/
@[inline] def list (ss : Array StmtId) : List StmtId := ss.toList

mutual

/-- The names free in an expression (`Elab.fvExpr`). -/
partial def fvExpr (b : Body) (bound : List String) (e : ExprId) : List String :=
  match b.expr e with
  | .name qual x => if qual.isNone && !bound.contains x then [x] else []
  | .label l => if bound.contains (labelName l) then [] else [labelName l]
  | .labelScope l body => b.fvStmts (labelName l :: bound) body.toList
  | .ref _ x | .refField _ _ x _ _ => if bound.contains x then [] else [x]
  | .closure _ cs => cs.toList.flatMap (b.fvClause bound)
  | .handle s cs => b.fvExpr bound s ++ cs.toList.flatMap (b.fvClause bound)
  | _ => (b.direct e).toList.flatMap (b.fvExpr bound)

partial def fvClause (b : Body) (bound : List String) (c : ClauseId) : List String :=
  let ⟨pats, body⟩ := b.clause c
  b.fvStmts (pats.flatMap patternNames ++ bound) body.toList

partial def fvStmts (b : Body) (bound : List String) : List StmtId → List String
  | [] => []
  | s :: rest =>
    match b.stmt s with
    | .let_ pat value => b.fvExpr bound value ++ b.fvStmts (patternNames pat ++ bound) rest
    | .expr e | .defer e => b.fvExpr bound e ++ b.fvStmts bound rest
    | .located _ _ s => b.fvStmts bound (s :: rest)
    | .letMut x value => b.fvExpr bound value ++ b.fvStmts (x :: bound) rest
    | .assign target value => b.fvExpr bound target ++ b.fvExpr bound value ++ b.fvStmts bound rest

end

/-- The names free in clauses. -/
def fvClauses (b : Body) (cs : Array ClauseId) : List String := cs.toList.flatMap (b.fvClause [])

/-- The expressions one level down, blocks' too (`Expr.children`). -/
def children (b : Body) (e : ExprId) : List ExprId :=
  (b.direct e).toList ++ match b.expr e with
    | .closure _ cs | .handle _ cs => cs.toList.flatMap fun c => (b.clause c).body.toList.flatMap fun s => (b.stmtExprs s).toList
    | .labelScope _ body => body.toList.flatMap fun s => (b.stmtExprs s).toList
    | _ => []

/-- The names an expression hands on with `move name`, wherever in it
(`Elab.movedExpr`). -/
partial def movedExpr (b : Body) (e : ExprId) : List String :=
  let here := match b.expr e with
    | .call _ f #[a] =>
      match b.bare? f, b.bare? a with
      | some mark, some x => if mark == moveMark then some [x] else none
      | _, _ => none
    | _ => none
  match here with
  | some xs => xs
  | none => (b.children e).flatMap b.movedExpr

def movedStmt (b : Body) (s : StmtId) : List String := (b.stmtExprs s).toList.flatMap b.movedExpr

/-- Where a body starts (`Elab.firstPlace`). -/
def firstPlace (b : Body) (body : List StmtId) : Nat × Nat :=
  match body with
  | s :: _ =>
    match b.stmt s with
    | .located line col _ => (line, col)
    | _ => (0, 0)
  | [] => (0, 0)

/-- The place a clause's names are known by (`Elab.clausePlace`): its first
statement's, or the hash of its body as a tree. -/
def clausePlace (b : Body) (body : List StmtId) : Nat × Nat :=
  match b.firstPlace body with
  | (0, 0) => ((hash (body.map (treeStmt b))).toNat, 0)
  | place => place

/-- A block written in braces, without parameters (`Elab.plainBlock`). -/
def plainBlock (b : Body) (e : ExprId) : Option (Nat × Array StmtId) :=
  match b.expr e with
  | .closure id #[c] =>
    let ⟨pats, body⟩ := b.clause c
    if id == 0 || !pats.isEmpty then none else some (id, body)
  | _ => none

/-- Does a body end with a value that can be given to a coercion
(`(Elab.wrapResult fn body).isSome`)? -/
partial def wrapsResult (b : Body) : List StmtId → Bool
  | [] => false
  | [s] =>
    match b.stmt s with
    | .expr e => match b.expr e with
      | .tailCall .. => false
      | _ => true
    | .located _ _ s => b.wrapsResult [s]
    | _ => false
  | _ :: rest => b.wrapsResult rest

/-- The variable a place assigned to is a place of (`Syntax.placeRoot`). -/
partial def placeRoot (b : Body) (e : ExprId) : Option String :=
  match b.expr e with
  | .name none x => some x
  | .fieldOf _ e _ | .proj e _ => b.placeRoot e
  | _ => none

mutual

/-- How an expression uses the name `x` (`Syntax.nameUseExpr`). With
`noDefers`, a cleanup at any depth is left out. -/
partial def nameUseExpr (b : Body) (noDefers : Bool) (x : String) (e : ExprId) : NameUse :=
  match b.expr e with
  | .name none y => if y == x then { valued := true } else {}
  | .ref uniq y => if y != x then {} else if uniq then { changed := true } else { shared := true }
  | .refField _ uniq y _ _ => if y == x then { fielded := true, changed := uniq } else {}
  | .call _ f args | .tailCall _ f args =>
    args.foldl (fun u e => u.or (b.nameUseExpr noDefers x e)) (b.nameUseExpr noDefers x f)
  | .tuple args => args.foldl (fun u e => u.or (b.nameUseExpr noDefers x e)) {}
  | .proj e _ | .fieldOf _ e _ => if b.placeRoot e == some x then { looked := true } else b.nameUseExpr noDefers x e
  | .deref e | .reborrow _ e => b.nameUseExpr noDefers x e
  | .closure _ cs =>
    NameUse.inside (cs.foldl (fun u c => u.or (b.nameUseClause noDefers x c)) ({} : NameUse))
  | .handle subject arms =>
    (NameUse.inside (arms.foldl (fun u c => u.or (b.nameUseClause noDefers x c)) ({} : NameUse))).or
      (b.nameUseExpr noDefers x subject)
  | .labelScope _ body => b.nameUseStmts noDefers x body.toList
  | _ => {}

partial def nameUseClause (b : Body) (noDefers : Bool) (x : String) (c : ClauseId) : NameUse :=
  let ⟨pats, body⟩ := b.clause c
  if (pats.flatMap patternNames).contains x then { rebound := true } else b.nameUseStmts noDefers x body.toList

partial def nameUseStmts (b : Body) (noDefers : Bool) (x : String) : List StmtId → NameUse
  | [] => {}
  | s :: rest =>
    let u := b.nameUseStmt noDefers x s
    if b.bindsAgain x s then u else u.or (b.nameUseStmts noDefers x rest)

partial def bindsAgain (b : Body) (x : String) (s : StmtId) : Bool :=
  match b.stmt s with
  | .let_ pat _ => (patternNames pat).contains x
  | .letMut y _ => y == x
  | .located _ _ s => b.bindsAgain x s
  | _ => false

partial def nameUseStmt (b : Body) (noDefers : Bool) (x : String) (s : StmtId) : NameUse :=
  match b.stmt s with
  | .let_ pat e =>
    let u := b.nameUseExpr noDefers x e
    if (patternNames pat).contains x then { u with rebound := true } else u
  | .letMut y e =>
    let u := b.nameUseExpr noDefers x e
    if y == x then { u with rebound := true } else u
  | .expr e => b.nameUseExpr noDefers x e
  | .defer e => if noDefers then {} else b.nameUseExpr noDefers x e
  | .located _ _ s => b.nameUseStmt noDefers x s
  | .assign target e =>
    if b.placeRoot target == some x then { b.nameUseExpr noDefers x e with changed := true }
    else (b.nameUseExpr noDefers x target).or (b.nameUseExpr noDefers x e)

end

/-- How clauses use `x`. -/
def nameUseClauses (b : Body) (x : String) (cs : Array ClauseId) : NameUse :=
  cs.foldl (fun u c => u.or (b.nameUseClause false x c)) ({} : NameUse)

mutual

/-- Is the name borrowed once its value has been used
(`Syntax.borrowAfterValue`)? -/
partial def borrowAfterValue (b : Body) (x : String) (seen : Bool) (e : ExprId) : Bool × Bool :=
  match b.expr e with
  | .name none y => (seen || y == x, false)
  | .ref _ y | .refField _ _ y _ _ => (seen, seen && y == x)
  | .call _ f args | .tailCall _ f args => b.borrowAfterValues x seen (#[f] ++ args).toList
  | .tuple args => b.borrowAfterValues x seen args.toList
  | .proj e _ | .fieldOf _ e _ => if b.placeRoot e == some x then (seen, seen) else b.borrowAfterValue x seen e
  | .deref e | .reborrow _ e => b.borrowAfterValue x seen e
  | .closure _ _ =>
    let u := b.nameUseExpr false x e
    (seen || u.valuedInside,
      (seen || u.valuedInside) && (u.shared || u.changed || u.fielded || u.looked))
  | .handle subject arms =>
    let (seen, bad) := b.borrowAfterValue x seen subject
    let u := arms.foldl (fun u c => u.or (b.nameUseClause false x c)) ({} : NameUse)
    (seen || u.valued || u.valuedInside, bad || u.shared || u.changed || u.fielded || u.looked)
  | .labelScope _ body =>
    body.foldl (fun (seen, bad) s =>
      let (seen', bad') := b.borrowAfterValueStmt x seen s
      (seen', bad || bad')) (seen, false)
  | _ => (seen, false)

partial def borrowAfterValues (b : Body) (x : String) (seen : Bool) (es : List ExprId) : Bool × Bool :=
  es.foldl (fun (seen, bad) e =>
    let (seen', bad') := b.borrowAfterValue x seen e
    (seen', bad || bad')) (seen, false)

partial def borrowAfterValueStmt (b : Body) (x : String) (seen : Bool) (s : StmtId) : Bool × Bool :=
  match b.stmt s with
  | .let_ _ e | .letMut _ e | .expr e => b.borrowAfterValue x seen e
  | .defer e =>
    let runNow : Option (Array StmtId) := match b.expr e with
      | .call _ f #[] => match b.expr f with
        | .closure _ #[c] => let ⟨ps, body⟩ := b.clause c; if ps.isEmpty then some body else none
        | _ => none
      | _ => none
    match runNow with
    | some body =>
      let (_, bad) := body.foldl (fun (seen, bad) s =>
        let (seen', bad') := b.borrowAfterValueStmt x seen s
        (seen', bad || bad')) (seen, false)
      (seen, bad)
    | none =>
      let (_, bad) := b.borrowAfterValue x seen e
      (seen, bad)
  | .located _ _ s => b.borrowAfterValueStmt x seen s
  | .assign target e =>
    if b.placeRoot target == some x then
      let (seen, bad) := b.borrowAfterValue x seen e
      (seen, bad || seen)
    else b.borrowAfterValues x seen [e, target]

end

mutual

/-- The cleanups written in an expression, at any depth (what
`Syntax.splitDefersM` takes out). -/
partial def defersExpr (b : Body) (e : ExprId) : List StmtId :=
  match b.expr e with
  | .closure _ cs => cs.toList.flatMap fun c => b.defersStmts (b.clause c).body.toList
  | .handle s cs => b.defersExpr s ++ cs.toList.flatMap fun c => b.defersStmts (b.clause c).body.toList
  | .labelScope _ body => b.defersStmts body.toList
  | _ => (b.direct e).toList.flatMap b.defersExpr

partial def defersStmts (b : Body) (body : List StmtId) : List StmtId :=
  body.flatMap fun s =>
    match b.stmt (b.unlocated s) with
    | .defer _ => [b.unlocated s]
    | _ => (b.stmtExprs s).toList.flatMap b.defersExpr

end

/-- Is the value a name holds used as it is, with no borrow of the name and
nothing written to it after (`Syntax.givenAway`)? -/
def givenAway (b : Body) (x : String) (rest : List StmtId) : Bool :=
  let cleanups := b.defersStmts rest
  let late := cleanups.any fun d =>
    let v := b.nameUseStmt false x d
    v.shared || v.fielded || v.changed || v.looked
  let early := b.nameUseStmts true x rest
  if late && (early.valued || early.valuedInside) then false else
  let u := b.nameUseStmts false x rest
  let (_, bad) := rest.foldl (fun (seen, bad) s =>
    let (seen', bad') := b.borrowAfterValueStmt x seen s
    (seen', bad || bad')) (false, false)
  !u.rebound && (u.valued || u.valuedInside) && !bad

/-- Is a name used other than by reading a part of it (`Syntax.usedWhole`)? -/
partial def usedWhole (b : Body) (x : String) (e : ExprId) : Bool :=
  match b.expr e with
  | .name none y | .ref _ y | .refField _ _ y _ _ => y == x
  | .fieldOf _ e' _ | .proj e' _ =>
    match b.expr e' with
    | .name none _ => false
    | _ => (b.children e).any (b.usedWhole x)
  | _ => (b.children e).any (b.usedWhole x)

def usedWholeStmt (b : Body) (x : String) (s : StmtId) : Bool := (b.stmtExprs s).any (b.usedWhole x)

/-- The identities of an expression's calls (`Syntax.callIdsExpr`). -/
partial def callIdsExpr (b : Body) (acc : List Nat) (e : ExprId) : List Nat :=
  match b.expr e with
  | .call id f args | .tailCall id f args => (#[f] ++ args).foldl (b.callIdsExpr) (id :: acc)
  | _ => (b.children e).foldl (b.callIdsExpr) acc

/-- The identities of the calls in clauses. -/
def callIdsClauses (b : Body) (cs : Array ClauseId) : List Nat :=
  cs.foldl (fun acc c => (b.clause c).body.foldl (fun acc s => (b.stmtExprs s).foldl b.callIdsExpr acc) acc) []

/-- The part of a name an expression reads (`Syntax.partRead`). -/
def partRead (b : Body) (x : String) (e : ExprId) : Option String :=
  match b.expr e with
  | .fieldOf _ e' f => if b.bare? e' == some x then some f else none
  | .proj e' i => if b.bare? e' == some x then some (toString i) else none
  | _ => none

end Body

/-! ## Rewrites: copies of what changes, the rest left where it is -/

/-- A rewrite of a body: an expression made otherwise (`some`, whose parts are
not looked at again), or a statement. What does not change keeps its place;
what has a part that changed is a node made anew. -/
structure FGo where
  ex : ExprId → Build ExprId
  st : StmtId → Build StmtId
  stmts : List StmtId → Build (List StmtId)
  clause : ClauseId → Build ClauseId

instance : Inhabited FGo := ⟨⟨pure, pure, pure, pure⟩⟩

structure FRewrite where
  /-- (Given how the rest is rewritten.) -/
  onExpr : FGo → Body → ExprId → Option (Build ExprId) := fun _ _ _ => none
  onStmt : FGo → Body → StmtId → Option (Build StmtId) := fun _ _ _ => none
  /-- A block's statements from one on (`Rewrite.onStmts`). -/
  onStmts : FGo → Body → List StmtId → Option (Build (List StmtId)) := fun _ _ _ => none
  onClause : FGo → Body → ClauseId → Option (Build ClauseId) := fun _ _ _ => none

mutual

partial def FRewrite.ex (r : FRewrite) (e : ExprId) : Build ExprId := do
  let b ← get
  if let some made := r.onExpr r.go b e then return ← made
  match b.expr e with
  | .call id f args => do
    let f' ← r.ex f
    let args' ← args.mapM r.ex
    if f' == f && args' == args then pure e else pushExpr (.call id f' args')
  | .tailCall id f args => do
    let f' ← r.ex f
    let args' ← args.mapM r.ex
    if f' == f && args' == args then pure e else pushExpr (.tailCall id f' args')
  | .tuple args => do
    let args' ← args.mapM r.ex
    if args' == args then pure e else pushExpr (.tuple args')
  | .proj x i => do
    let x' ← r.ex x
    if x' == x then pure e else pushExpr (.proj x' i)
  | .closure id cs => do
    let cs' ← cs.mapM r.clause
    if cs' == cs then pure e else pushExpr (.closure id cs')
  | .handle s cs => do
    let s' ← r.ex s
    let cs' ← cs.mapM r.clause
    if s' == s && cs' == cs then pure e else pushExpr (.handle s' cs')
  | .labelScope l body => do
    let body' := (← r.stmtList body.toList).toArray
    if body' == body then pure e else pushExpr (.labelScope l body')
  | .deref x => do
    let x' ← r.ex x
    if x' == x then pure e else pushExpr (.deref x')
  | .reborrow u x => do
    let x' ← r.ex x
    if x' == x then pure e else pushExpr (.reborrow u x')
  | .fieldOf id x n => do
    let x' ← r.ex x
    if x' == x then pure e else pushExpr (.fieldOf id x' n)
  | _ => pure e

partial def FRewrite.clause (r : FRewrite) (c : ClauseId) : Build ClauseId := do
  if let some made := r.onClause r.go (← get) c then return ← made
  let ⟨pats, body⟩ := (← get).clause c
  let body' := (← r.stmtList body.toList).toArray
  if body' == body then pure c else pushClause ⟨pats, body'⟩

partial def FRewrite.stmtList (r : FRewrite) (ss : List StmtId) : Build (List StmtId) := do
  if let some made := r.onStmts r.go (← get) ss then return ← made
  match ss with
  | [] => pure []
  | s :: rest => pure ((← r.st s) :: (← r.stmtList rest))

/-- How the rest is rewritten, for a hook. -/
partial def FRewrite.go (r : FRewrite) : FGo := ⟨r.ex, r.st, r.stmtList, r.clause⟩

partial def FRewrite.st (r : FRewrite) (s : StmtId) : Build StmtId := do
  let b ← get
  if let some made := r.onStmt r.go b s then return ← made
  match b.stmt s with
  | .let_ p v => do
    let v' ← r.ex v
    if v' == v then pure s else pushStmt (.let_ p v')
  | .expr v => do
    let v' ← r.ex v
    if v' == v then pure s else pushStmt (.expr v')
  | .defer v => do
    let v' ← r.ex v
    if v' == v then pure s else pushStmt (.defer v')
  | .letMut x v => do
    let v' ← r.ex v
    if v' == v then pure s else pushStmt (.letMut x v')
  | .assign t v => do
    let t' ← r.ex t
    let v' ← r.ex v
    if t' == t && v' == v then pure s else pushStmt (.assign t' v')
  | .located l c inner => do
    let inner' ← r.st inner
    if inner' == inner then pure s else pushStmt (.located l c inner')

end

/-- A body's own clauses rewritten, in the body grown by what is made. -/
def FRewrite.body (r : FRewrite) (b : Body) : Body :=
  let (roots, b) := (b.roots.mapM r.clause).run b
  { b with roots }

/-- Statements rewritten, in a body that grows by what is made. -/
def FRewrite.stmts (r : FRewrite) (b : Body) (ss : List StmtId) : Body × List StmtId :=
  let (out, b) := (r.stmtList ss).run b
  (b, out)

/-- What follows a variable with each read of a part of it left out
(`Syntax.lessPartsStmts`). -/
def lessPartsStmts (b : Body) (x : String) (ss : List StmtId) : Body × List StmtId :=
  let r : FRewrite :=
    { onExpr := fun _ b e => match b.expr e with
        | .proj e' _ | .fieldOf _ e' _ => if b.placeRoot e' == some x then some (pushExpr (.int 0)) else none
        | _ => none
      onStmt := fun go b s => match b.stmt s with
        | .assign target e =>
          if b.placeRoot target == some x then some (do
            let place ← pushExpr (.name none "%place")
            let e' ← go.ex e
            pushStmt (.assign place e'))
          else none
        | _ => none }
  r.stmts b ss

/-- What follows a name with every read of a part of it but one left out
(`Syntax.onlyPartStmts`). -/
def onlyPartStmts (b : Body) (x part : String) (ss : List StmtId) : Body × List StmtId :=
  let r : FRewrite :=
    { onExpr := fun _ b e => (b.partRead x e).map fun p => pushExpr (if p == part then .name none x else .int 0) }
  r.stmts b ss

end Glorious.Syntax.Flat
