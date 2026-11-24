module

public import Glorious.Syntax.Flat
public import Std.Data.HashMap

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

mutual

/-- The names free in an expression, added in front of `acc`: the same names,
each where it is first met (`fvExpr`). -/
partial def fvExprAcc (b : Body) (bound : List String) (e : ExprId) (acc : List String) : List String :=
  match b.expr e with
  | .name qual x => if qual.isNone && !bound.contains x then x :: acc else acc
  | .label l => if bound.contains (labelName l) then acc else labelName l :: acc
  | .labelScope l body => b.fvStmtsAcc (labelName l :: bound) body.toList acc
  | .ref _ x | .refField _ _ x _ _ => if bound.contains x then acc else x :: acc
  | .closure _ cs => cs.foldr (fun c acc => b.fvClauseAcc bound c acc) acc
  | .handle s cs => b.fvExprAcc bound s (cs.foldr (fun c acc => b.fvClauseAcc bound c acc) acc)
  | _ => b.foldrDirect (b.fvExprAcc bound) acc e

partial def fvClauseAcc (b : Body) (bound : List String) (c : ClauseId) (acc : List String) : List String :=
  let ⟨pats, body⟩ := b.clause c
  b.fvStmtsAcc (pats.flatMap patternNames ++ bound) body.toList acc

partial def fvStmtsAcc (b : Body) (bound : List String) (ss : List StmtId) (acc : List String) : List String :=
  match ss with
  | [] => acc
  | s :: rest =>
    match b.stmt s with
    | .let_ pat value => b.fvExprAcc bound value (b.fvStmtsAcc (patternNames pat ++ bound) rest acc)
    | .expr e | .defer e => b.fvExprAcc bound e (b.fvStmtsAcc bound rest acc)
    | .located _ _ s => b.fvStmtsAcc bound (s :: rest) acc
    | .letMut x value => b.fvExprAcc bound value (b.fvStmtsAcc (x :: bound) rest acc)
    | .assign target value => b.fvExprAcc bound target (b.fvExprAcc bound value (b.fvStmtsAcc bound rest acc))

end

/-- The names free in an expression (`Elab.fvExpr`). -/
@[inline] def fvExpr (b : Body) (bound : List String) (e : ExprId) : List String := b.fvExprAcc bound e []
@[inline] def fvClause (b : Body) (bound : List String) (c : ClauseId) : List String := b.fvClauseAcc bound c []
@[inline] def fvStmts (b : Body) (bound : List String) (ss : List StmtId) : List String := b.fvStmtsAcc bound ss []

/-- The names free in clauses. -/
def fvClauses (b : Body) (cs : Array ClauseId) : List String := cs.toList.flatMap (b.fvClause [])

/-- The names an expression hands on with `move name`, wherever in it
. -/
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

mutual

/-- A hash of an expression as it is written, whatever places its nodes are
at: two written alike hash alike. -/
partial def hashExpr (b : Body) (e : ExprId) : UInt64 :=
  let many := fun (tag : UInt64) (es : Array ExprId) => es.foldl (fun h e => mixHash h (b.hashExpr e)) tag
  match b.expr e with
  | .int n => mixHash 1 (hash n)
  | .name q x => mixHash 2 (hash (q, x))
  | .label x => mixHash 3 (hash x)
  | .call id f args => many (mixHash 4 (mixHash (hash id) (b.hashExpr f))) args
  | .tailCall id f args => many (mixHash 5 (mixHash (hash id) (b.hashExpr f))) args
  | .tuple args => many 6 args
  | .proj x i => mixHash 7 (mixHash (hash i) (b.hashExpr x))
  | .closure id cs => b.hashClosure id cs
  | .handle s cs => cs.foldl (fun h c => mixHash h (b.hashClause c)) (mixHash 9 (b.hashExpr s))
  | .labelScope l body => mixHash (mixHash 10 (hash l)) (b.hashStmts body.toList)
  | .ref u x => mixHash 11 (hash (u, x))
  | .deref x => mixHash 12 (b.hashExpr x)
  | .reborrow u x => mixHash 13 (mixHash (hash u) (b.hashExpr x))
  | .refField id u x path star => mixHash 14 (hash (id, u, x, path, star))
  | .fieldOf id x n => mixHash 15 (mixHash (hash (id, n)) (b.hashExpr x))

/-- A callable written with these clauses. -/
partial def hashClosure (b : Body) (id : Nat) (cs : Array ClauseId) : UInt64 :=
  cs.foldl (fun h c => mixHash h (b.hashClause c)) (mixHash 8 (hash id))

partial def hashClause (b : Body) (c : ClauseId) : UInt64 :=
  let ⟨pats, body⟩ := b.clause c
  mixHash (hash pats) (b.hashStmts body.toList)

partial def hashStmt (b : Body) (s : StmtId) : UInt64 :=
  match b.stmt s with
  | .let_ p v => mixHash 21 (mixHash (hash p) (b.hashExpr v))
  | .expr v => mixHash 22 (b.hashExpr v)
  | .defer v => mixHash 23 (b.hashExpr v)
  | .letMut x v => mixHash 24 (mixHash (hash x) (b.hashExpr v))
  | .assign t v => mixHash 25 (mixHash (b.hashExpr t) (b.hashExpr v))
  | .located l c inner => mixHash 26 (mixHash (hash (l, c)) (b.hashStmt inner))

partial def hashStmts (b : Body) (ss : List StmtId) : UInt64 :=
  ss.foldl (fun h s => mixHash h (b.hashStmt s)) 20

end

/-- Where a body starts. -/
def firstPlace (b : Body) (body : List StmtId) : Nat × Nat :=
  match body with
  | s :: _ =>
    match b.stmt s with
    | .located line col _ => (line, col)
    | _ => (0, 0)
  | [] => (0, 0)

/-- The place a clause's names and `_` are known by, for what destroys them:
its first statement's, or, where that has none, the clause's body as written
(its hash), so that two such clauses of one function are not taken for one. -/
def clausePlace (b : Body) (body : List StmtId) : Nat × Nat :=
  match b.firstPlace body with
  | (0, 0) => ((b.hashStmts body).toNat, 0)
  | place => place

/-- A block written in braces, without parameters. -/
def plainBlock (b : Body) (e : ExprId) : Option (Nat × Array StmtId) :=
  match b.expr e with
  | .closure id #[c] =>
    let ⟨pats, body⟩ := b.clause c
    if id == 0 || !pats.isEmpty then none else some (id, body)
  | _ => none

/-- Does a body end with a value that can be given to a coercion: not a
statement, nor a `tail` call, which must stay the last thing done? -/
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
  | .proj e _ | .fieldOf _ e _ => if b.placeRoot e == some x then { looked := true } else b.nameUseExpr noDefers x e
  -- (`x[i]`: the element read where it is, through a borrow of `x`.)
  | .call _ f #[a, i] =>
    match b.expr f, b.expr a with
    | .name _ "index", .name none y =>
      if y == x then ({ indexed := true } : NameUse).or (b.nameUseExpr noDefers x i)
      else b.foldDirect (fun u e => u.or (b.nameUseExpr noDefers x e)) {} e
    | _, _ => b.foldDirect (fun u e => u.or (b.nameUseExpr noDefers x e)) {} e
  | .closure _ cs =>
    NameUse.inside (cs.foldl (fun u c => u.or (b.nameUseClause noDefers x c)) ({} : NameUse))
  | .handle subject arms =>
    (NameUse.inside (arms.foldl (fun u c => u.or (b.nameUseClause noDefers x c)) ({} : NameUse))).or
      (b.nameUseExpr noDefers x subject)
  | .labelScope _ body => b.nameUseStmts noDefers x body.toList
  | _ => b.foldDirect (fun u e => u.or (b.nameUseExpr noDefers x e)) {} e

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
? -/
partial def borrowAfterValue (b : Body) (x : String) (seen : Bool) (e : ExprId) : Bool × Bool :=
  match b.expr e with
  | .name none y => (seen || y == x, false)
  | .ref _ y | .refField _ _ y _ _ => (seen, seen && y == x)
  | .proj e _ | .fieldOf _ e _ => if b.placeRoot e == some x then (seen, seen) else b.borrowAfterValue x seen e
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
  | _ => b.foldDirect (fun (seen, bad) e =>
      let (seen', bad') := b.borrowAfterValue x seen e
      (seen', bad || bad')) (seen, false) e

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

/-- The cleanups written in an expression, at any depth. -/
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

/-- The characters of a text written out (`"..."`, the prelude's `StrChar`s
ending in `StrEnd`, as the parser writes it), if it is one. -/
partial def textCodes (b : Body) (e : ExprId) : Option (List Nat) :=
  match b.expr e with
  | .name _ x => if lastSegment x == "StrEnd" then some [] else none
  | .call _ f #[c, rest] =>
    match b.expr f, b.expr c with
    | .name _ x, .call _ g #[n] =>
      if lastSegment x != "StrChar" then none else
      match b.expr g, b.expr n with
      | .name _ y, .int code => if lastSegment y == "char_of" then (textCodes b rest).map (code.toNat :: ·) else none
      | _, _ => none
    | _, _ => none
  | _ => none

/-- Is the value a name holds used as it is, with no borrow of the name and
nothing written to it after? -/
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

/-- Is a name used other than by reading a part of it? -/
partial def usedWhole (b : Body) (x : String) (e : ExprId) : Bool :=
  match b.expr e with
  | .name none y | .ref _ y | .refField _ _ y _ _ => y == x
  | .fieldOf _ e' _ | .proj e' _ =>
    match b.expr e' with
    | .name none _ => false
    | _ => (b.children e).any (b.usedWhole x)
  | _ => (b.children e).any (b.usedWhole x)

def usedWholeStmt (b : Body) (x : String) (s : StmtId) : Bool := (b.stmtExprs s).any (b.usedWhole x)

/-- The identities of an expression's calls. -/
partial def callIdsExpr (b : Body) (acc : List Nat) (e : ExprId) : List Nat :=
  match b.expr e with
  | .call id f args | .tailCall id f args => (#[f] ++ args).foldl (b.callIdsExpr) (id :: acc)
  | _ => (b.children e).foldl (b.callIdsExpr) acc

/-- The identities of the calls in clauses. -/
def callIdsClauses (b : Body) (cs : Array ClauseId) : List Nat :=
  cs.foldl (fun acc c => (b.clause c).body.foldl (fun acc s => (b.stmtExprs s).foldl b.callIdsExpr acc) acc) []

/-- The part of a name an expression reads. -/
def partRead (b : Body) (x : String) (e : ExprId) : Option String :=
  match b.expr e with
  | .fieldOf _ e' f => if b.bare? e' == some x then some f else none
  | .proj e' i => if b.bare? e' == some x then some (toString i) else none
  | _ => none

end Body

/-! ## Rewrites: copies of what changes, the rest left where it is -/

/-- A rewrite of a body, in `StateT Body m`: an expression made otherwise
(`some`, whose parts are not looked at again), or a statement. What does not
change keeps its place; what has a part that changed is a node made anew.
(`FRewrite`: in `Build`, which is `m` nothing more.) -/
structure FGoM (m : Type → Type) where
  ex : ExprId → StateT Body m ExprId
  st : StmtId → StateT Body m StmtId
  stmts : List StmtId → StateT Body m (List StmtId)
  clause : ClauseId → StateT Body m ClauseId

instance {m : Type → Type} [Monad m] : Inhabited (FGoM m) := ⟨⟨pure, pure, pure, pure⟩⟩

structure FRewriteM (m : Type → Type) where
  /-- (Given how the rest is rewritten.) -/
  onExpr : FGoM m → Body → ExprId → Option (StateT Body m ExprId) := fun _ _ _ => none
  onStmt : FGoM m → Body → StmtId → Option (StateT Body m StmtId) := fun _ _ _ => none
  /-- A block's statements from one on (`Rewrite.onStmts`). -/
  onStmts : FGoM m → Body → List StmtId → Option (StateT Body m (List StmtId)) := fun _ _ _ => none
  onClause : FGoM m → Body → ClauseId → Option (StateT Body m ClauseId) := fun _ _ _ => none
  /-- Each pattern: a clause's and a `let`'s. -/
  onPat : Pattern → Pattern := id

abbrev FGo := FGoM Id
abbrev FRewrite := FRewriteM Id

section
variable {m : Type → Type} [Monad m]

private def pushE (e : FExpr) : StateT Body m ExprId := modifyGet fun b => (b.exprs.size, { b with exprs := b.exprs.push e })
private def pushS (s : FStmt) : StateT Body m StmtId := modifyGet fun b => (b.stmts.size, { b with stmts := b.stmts.push s })
private def pushC (c : FClause) : StateT Body m ClauseId := modifyGet fun b => (b.clauses.size, { b with clauses := b.clauses.push c })

mutual

partial def FRewriteM.ex (r : FRewriteM m) (e : ExprId) : StateT Body m ExprId := do
  let b ← get
  if let some made := r.onExpr r.go b e then return ← made
  let n := b.expr e
  let n' ← n.mapIds r.ex r.clause fun body => do pure (← r.stmtList body.toList).toArray
  if n' == n then pure e else pushE n'

partial def FRewriteM.clause (r : FRewriteM m) (c : ClauseId) : StateT Body m ClauseId := do
  if let some made := r.onClause r.go (← get) c then return ← made
  let ⟨pats, body⟩ := (← get).clause c
  let pats' := pats.map r.onPat
  let body' := (← r.stmtList body.toList).toArray
  if body' == body && pats' == pats then pure c else pushC ⟨pats', body'⟩

partial def FRewriteM.stmtList (r : FRewriteM m) (ss : List StmtId) : StateT Body m (List StmtId) := do
  if let some made := r.onStmts r.go (← get) ss then return ← made
  match ss with
  | [] => pure []
  | s :: rest => pure ((← r.st s) :: (← r.stmtList rest))

/-- How the rest is rewritten, for a hook. -/
partial def FRewriteM.go (r : FRewriteM m) : FGoM m := ⟨r.ex, r.st, r.stmtList, r.clause⟩

partial def FRewriteM.st (r : FRewriteM m) (s : StmtId) : StateT Body m StmtId := do
  let b ← get
  if let some made := r.onStmt r.go b s then return ← made
  let n := b.stmt s
  let n' ← n.mapIds r.ex r.st r.onPat
  if n' == n then pure s else pushS n'

end

end

/-- A body's own clauses rewritten, in the body grown by what is made. -/
def FRewriteM.body (r : FRewrite) (b : Body) : Body :=
  let (roots, b) := (b.roots.mapM r.clause).run b
  { b with roots }

/-- Statements rewritten, in a body that grows by what is made. -/
def FRewriteM.stmts (r : FRewrite) (b : Body) (ss : List StmtId) : Body × List StmtId :=
  let (out, b) := (r.stmtList ss).run b
  (b, out)

/-- What follows a variable with each read of a part of it left out
. -/
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
. -/
def onlyPartStmts (b : Body) (x part : String) (ss : List StmtId) : Body × List StmtId :=
  let r : FRewrite :=
    { onExpr := fun _ b e => (b.partRead x e).map fun p => pushExpr (if p == part then .name none x else .int 0) }
  r.stmts b ss

/-! ## What the front end writes out, flat -/

/-- Every identity moved on by `k`: a copy of a function is then told apart
from the function and from every other copy. -/
def shiftRewrite (k : Nat) : FRewrite where
  onExpr go b e :=
    match b.expr e with
    | .call id g args => some (do pushExpr (.call (id + k) (← go.ex g) (← args.mapM go.ex)))
    | .tailCall id g args => some (do pushExpr (.tailCall (id + k) (← go.ex g) (← args.mapM go.ex)))
    | .fieldOf id x name => some (do pushExpr (.fieldOf (id + k) (← go.ex x) name))
    | .refField id uniq name path star => some (pushExpr (.refField (id + k) uniq name path star))
    | .closure id clauses => some (do pushExpr (.closure (id + k) (← clauses.mapM go.clause)))
    | _ => none

/-- `Self` written out as the type an implementation is for
(`Syntax.selfRewrite`). -/
def selfRewrite (self : String) (trait : Option (String × Expr)) : FRewrite where
  onExpr go b e :=
    match b.expr e with
    | .name qual z =>
      some (pushExpr (.name (if qual == some "Self" then some ((trait.map (·.1)).getD self) else qual)
        (if z == "Self" then self else z)))
    | .call id f args =>
      match b.expr f, trait with
      | .name (some "Self") z, some (tr, at_) => some (do
        let callee ← pushExpr (.name (some tr) z)
        let call ← pushExpr (.call id callee (← args.mapM go.ex))
        let ty ← flatExpr at_
        pushExpr (.call 0 (← pushExpr (.name none instMark)) #[call, ty]))
      | _, _ => none
    | _ => none
  onPat := selfPattern self

/-- Is an ascription, `let x: Type = ..`, among a body's nodes (reached or
not)? Asked first: most bodies have none. -/
def Body.anyAscription (b : Body) : Bool :=
  b.exprs.any fun
    | .call _ f #[_, _] =>
      match b.bare? f with
      | some mark => mark == ascribeMark || mark == instMark
      | none => false
    | _ => false

/-- The ascriptions an expression has, `let x: Type = ..`: the places of the
types written, added in front of `acc`. -/
partial def Body.ascriptionsExpr (b : Body) (e : ExprId) (acc : List ExprId) : List ExprId :=
  let rest := fun (_ : Unit) => (b.children e).foldr (fun x acc => b.ascriptionsExpr x acc) acc
  match b.expr e with
  | .call _ f #[v, ty] =>
    match b.bare? f with
    -- (The type itself is not looked in.)
    | some mark => if mark == ascribeMark || mark == instMark then ty :: b.ascriptionsExpr v acc else rest ()
    | none => rest ()
  | _ => rest ()

/-- The ascriptions of a body, `let x: Type = ..`: each with the place of the
type written. Only those reached from the body's own clauses. -/
def Body.ascriptions (b : Body) : List ExprId :=
  if !b.anyAscription then [] else b.roots.toList.flatMap fun c => (b.clause c).body.toList.flatMap fun s => (b.stmtExprs s).toList.flatMap (b.ascriptionsExpr · [])

/-- A body with each type written in it, `let x: Type = ..`, changed: the
types are worked out first, which may fail, and then written in. -/
def mapTypes (f : TypeExpr → Except String TypeExpr) (b : Body) : Except String Body := do
  let places := b.ascriptions
  if places.isEmpty then return b
  pure ((← typesRewrite f b places).body b)
where
  typesRewrite (f : TypeExpr → Except String TypeExpr) (b : Body) (places : List ExprId) :
      Except String FRewrite := do
    let mut made : Std.HashMap ExprId Expr := {}
    for ty in places do
      made := made.insert ty (← f (TypeExpr.ofExpr (treeExpr b ty))).asExpr
    pure { onExpr := fun _ _ e => (made[e]?).map fun t => flatExpr t }

/-- An expression with each type written in it changed (`mapTypes`). -/
def mapTypesOf (f : TypeExpr → Except String TypeExpr) (b : Body) (e : ExprId) : Except String (Body × ExprId) := do
  let places := if b.anyAscription then b.ascriptionsExpr e [] else []
  if places.isEmpty then return (b, e)
  let (e, b) := ((← mapTypes.typesRewrite f b places).ex e).run b
  pure (b, e)

mutual

/-- A value that is borrowed where it is made, `&f(x)`, given a name first
(`Syntax.nameBorrowsM`): the statements that bind the names, made before it. -/
partial def nameBorrowsE (e : ExprId) : StateT (Array StmtId) Build ExprId := do
  let b ← getThe Body
  match b.expr e with
  | .call id f #[x] =>
    match b.bare? f with
    | some mark =>
      let x' ← nameBorrowsE x
      if mark != borrowMark && mark != borrowMutMark then
        return ← if x' == x then pure e else (pushExpr (.call id f #[x']) : Build ExprId)
      let name := s!"borrowed%{id}"
      let uniq := mark == borrowMutMark
      let st ← (pushStmt (if uniq then .letMut name x' else .let_ (.var name) x') : Build StmtId)
      modify (·.push st)
      (pushExpr (.ref uniq name) : Build ExprId)
    | none => nameBorrowsChildren e
  | .handle subject arms =>
    -- What is handled is run under the handler: so is what it borrows.
    let (subject', before) ← ((nameBorrowsE subject).run #[] : Build _)
    let subject' ← if before.isEmpty then pure subject' else (do
      let st ← pushStmt (.expr subject')
      pushExpr (.labelScope "%block" (before.push st)) : Build ExprId)
    let arms' ← arms.mapM fun c => (nameBorrowsClause c : Build ClauseId)
    (pushExpr (.handle subject' arms') : Build ExprId)
  | _ => nameBorrowsChildren e

/-- The parts directly inside, and the blocks inside, made so. -/
partial def nameBorrowsChildren (e : ExprId) : StateT (Array StmtId) Build ExprId := do
  let b ← getThe Body
  match b.expr e with
  | .call i g args => do (pushExpr (.call i (← nameBorrowsE g) (← args.mapM nameBorrowsE)) : Build _)
  | .tailCall i g args => do (pushExpr (.tailCall i (← nameBorrowsE g) (← args.mapM nameBorrowsE)) : Build _)
  | .tuple args => do (pushExpr (.tuple (← args.mapM nameBorrowsE)) : Build _)
  | .proj x n => do (pushExpr (.proj (← nameBorrowsE x) n) : Build _)
  | .deref x => do (pushExpr (.deref (← nameBorrowsE x)) : Build _)
  | .reborrow u x => do (pushExpr (.reborrow u (← nameBorrowsE x)) : Build _)
  | .fieldOf i x n => do (pushExpr (.fieldOf i (← nameBorrowsE x) n) : Build _)
  | .closure i cs => do (pushExpr (.closure i (← cs.mapM fun c => nameBorrowsClause c)) : Build _)
  | .labelScope l body => do (pushExpr (.labelScope l (← nameBorrowsStmts body.toList).toArray) : Build _)
  | _ => pure e

partial def nameBorrowsClause (c : ClauseId) : Build ClauseId := do
  let ⟨pats, body⟩ := (← get).clause c
  pushClause ⟨pats, (← nameBorrowsStmts body.toList).toArray⟩

partial def nameBorrowsStmt (s : StmtId) : Build (List StmtId) := do
  let named := fun (e : ExprId) => ((nameBorrowsE e).run #[] : Build (ExprId × Array StmtId))
  match (← get).stmt s with
  | .let_ pat e => let (e, before) ← named e; pure (before.toList ++ [← pushStmt (.let_ pat e)])
  | .letMut x e => let (e, before) ← named e; pure (before.toList ++ [← pushStmt (.letMut x e)])
  -- (Of a statement that is an expression, the values named are let go
  -- where it ends: a block of its own.)
  | .expr e =>
    let (e, before) ← named e
    if before.isEmpty then pure [← pushStmt (.expr e)]
    else
      let last ← pushStmt (.expr e)
      pure [← pushStmt (.expr (← pushExpr (.labelScope "%block" (before.push last))))]
  | .defer e => let (e, before) ← named e; pure (before.toList ++ [← pushStmt (.defer e)])
  | .assign target e =>
    let (target, first) ← named target
    let (e, second) ← named e
    pure (first.toList ++ second.toList ++ [← pushStmt (.assign target e)])
  | .located line col inner =>
    -- (Each `let` made where the statement is: what a value so named holds
    -- is let go where its block ends, found by that place.)
    let made ← nameBorrowsStmt inner
    made.mapM fun s => do
      let b ← get
      match b.stmt s with
      | .expr e =>
        match b.expr e with
        | .labelScope "%block" body =>
          let placed ← body.mapM fun s => pushStmt (.located line col s)
          let scope ← pushExpr (.labelScope "%block" placed)
          pushStmt (.located line col (← pushStmt (.expr scope)))
        | _ => pushStmt (.located line col s)
      | _ => pushStmt (.located line col s)

partial def nameBorrowsStmts (body : List StmtId) : Build (List StmtId) :=
  return (← body.mapM nameBorrowsStmt).flatten

end

mutual

/-- An expression with `x` written `y` wherever it means what it means
outside (`Syntax.renameExpr`). -/
partial def renameExpr (x y : String) (bound : List String) (e : ExprId) : Build ExprId := do
  let b ← get
  let here := !bound.contains x
  match b.expr e with
  | .name none z => if z == x && here then pushExpr (.name none y) else pure e
  | .ref uniq z => if z == x && here then pushExpr (.ref uniq y) else pure e
  | .refField id uniq z path star => if z == x && here then pushExpr (.refField id uniq y path star) else pure e
  | .call i g args => do pushExpr (.call i (← renameExpr x y bound g) (← args.mapM (renameExpr x y bound)))
  | .tailCall i g args => do pushExpr (.tailCall i (← renameExpr x y bound g) (← args.mapM (renameExpr x y bound)))
  | .tuple args => do pushExpr (.tuple (← args.mapM (renameExpr x y bound)))
  | .proj a n => do pushExpr (.proj (← renameExpr x y bound a) n)
  | .deref a => do pushExpr (.deref (← renameExpr x y bound a))
  | .reborrow u a => do pushExpr (.reborrow u (← renameExpr x y bound a))
  | .fieldOf i a n => do pushExpr (.fieldOf i (← renameExpr x y bound a) n)
  | .closure i cs => do pushExpr (.closure i (← cs.mapM (renameClause x y bound)))
  | .handle s cs => do pushExpr (.handle (← renameExpr x y bound s) (← cs.mapM (renameClause x y bound)))
  | .labelScope l body => do pushExpr (.labelScope l (← renameStmts x y bound body.toList).toArray)
  | _ => pure e

partial def renameClause (x y : String) (bound : List String) (c : ClauseId) : Build ClauseId := do
  let ⟨pats, body⟩ := (← get).clause c
  pushClause ⟨pats, (← renameStmts x y (pats.flatMap patternNames ++ bound) body.toList).toArray⟩

partial def renameStmts (x y : String) (bound : List String) : List StmtId → Build (List StmtId)
  | [] => pure []
  | s :: rest => do
    match (← get).stmt s with
    | .let_ pat value => do
      let v ← renameExpr x y bound value
      pure ((← pushStmt (.let_ pat v)) :: (← renameStmts x y (patternNames pat ++ bound) rest))
    | .letMut z value => do
      let v ← renameExpr x y bound value
      pure ((← pushStmt (.letMut z v)) :: (← renameStmts x y (z :: bound) rest))
    | .expr e => do
      let e ← renameExpr x y bound e
      pure ((← pushStmt (.expr e)) :: (← renameStmts x y bound rest))
    | .defer e => do
      let e ← renameExpr x y bound e
      pure ((← pushStmt (.defer e)) :: (← renameStmts x y bound rest))
    | .located line col inner => do
      match ← renameStmts x y bound (inner :: rest) with
      | first :: more => pure ((← pushStmt (.located line col first)) :: more)
      | [] => pure []
    | .assign target value => do
      let t ← renameExpr x y bound target
      let v ← renameExpr x y bound value
      pure ((← pushStmt (.assign t v)) :: (← renameStmts x y bound rest))

end

/-- A body with each of `pairs`' first names written as its second in its
clauses, where no pattern of the clause binds it (`renameStmts`). -/
def renameInBody (pairs : List (String × String)) (b : Body) : Body :=
  let (roots, b) := (b.roots.mapM fun (c : ClauseId) => (do
    let cl := (← get).clause c
    let body ← pairs.foldlM (fun body (x, y) => renameStmts x y (cl.pats.flatMap patternNames) body) cl.body.toList
    pushClause ⟨cl.pats, body.toArray⟩ : Build ClauseId)).run b
  { b with roots }

/-- `&list[i]` of a parameter `list` written with a reference's type
(`Syntax.throughParamsRewrite`). -/
def throughParamsRewrite (refs : List String) : FRewrite where
  onExpr go b e :=
    match b.expr e with
    | .call id f args => some (do
      let args ← args.mapM go.ex
      let b ← get
      let args ← match (b.name? f).map (·.2), args.toList with
        | some "element_at", [r, i] =>
          match b.expr r with
          | .ref false x => if refs.contains x then pure #[← pushExpr (.name none x), i] else pure args
          | _ => pure args
        | some "place_at", [i, r] =>
          match b.expr r with
          | .ref true x => if refs.contains x then pure #[i, ← pushExpr (.name none x)] else pure args
          | _ => pure args
        | _, _ => pure args
      pushExpr (.call id (← go.ex f) args))
    | _ => none

/-- May what an expression gives be a value and not a reference, by how it is
written (`Syntax.valueLike`)? -/
def Body.valueLike (b : Body) (e : ExprId) : Bool :=
  match b.expr e with
  | .tuple args => !args.isEmpty
  | .int _ => true
  | .name _ x => (lastSegment x).front.isUpper
  | .call _ f args =>
    match b.bare? f, args.toList with
    | some mark, [_, ty] =>
      mark != ascribeMark || (match TypeExpr.ofExpr (treeExpr b ty) with
        | .ref _ _ _ => false
        | _ => true)
    | _, _ => true
  | _ => false

/-- Is a name bound here one that what follows borrows with `&` and never
changes (`Syntax.borrowedOnly`)? -/
def Body.borrowedOnly (b : Body) (x : String) (after : List StmtId) : Bool :=
  let u := b.nameUseStmts false x after
  -- (One whose elements alone are read, `x[i]`, is borrowed for each.)
  !x.startsWith "%" && (u.shared || (u.indexed && !u.valued && !u.valuedInside)) && !u.changed

def Body.fieldBorrowedOnly (b : Body) (x : String) (after : List StmtId) : Bool :=
  let u := b.nameUseStmts false x after
  !x.startsWith "%" && u.fielded && !u.changed

/-- `let mut x = x` for each name, where the body starts. -/
def heldStmts (held : List String) (body : List StmtId) : Build (List StmtId) := do
  let b ← get
  let first := match body.head? with
    | some s => match b.stmt s with
      | .located line col _ => some (line, col)
      | _ => none
    | none => none
  held.mapM fun x => do
    let v ← pushStmt (.letMut x (← pushExpr (.name none x)))
    match first with
    | some (line, col) => pushStmt (.located line col v)
    | none => pure v

/-- The names a clause binds that are only borrowed in it, or (of `values`)
only borrowed by field, each kept in a variable of the same name where the
clause starts (`Syntax.promoteHeld`). -/
def promoteHeld (values : List String) (c : ClauseId) : Build ClauseId := do
  let b ← get
  let ⟨pats, body⟩ := b.clause c
  let body := body.toList
  let held := ((pats.flatMap patternNames).eraseDups).filter fun x =>
    b.borrowedOnly x body || (values.contains x && b.fieldBorrowedOnly x body)
  if held.isEmpty then return c
  pushClause ⟨pats, ((← heldStmts held body) ++ body).toArray⟩

/-- A value that is given a name and then borrowed with `&` kept where a
reference can point (`Syntax.promoteRewrite`). -/
def promoteRewrite : FRewrite where
  onExpr go b e :=
    match b.expr e with
    | .call id f args => some (do
      -- (`if(e is Some(n)) { .. &n .. }`: the names an `is` among the
      -- arguments binds are the blocks' after it, and are kept where a
      -- reference can point as a clause's are.)
      let isOf := fun (a : ExprId) =>
        match b.expr a with
        | .call _ m #[_, cl] =>
          if b.bare? m == some isMark then
            match b.expr cl with
            | .closure _ #[c] =>
              let ⟨ps, body⟩ := b.clause c
              match ps with
              | [pat] => if body.isEmpty then patternNames pat else []
              | _ => []
            | _ => []
          else []
        | _ => []
      let isNames := fun (a : ExprId) =>
        match b.expr a with
        | .closure _ #[c] =>
          let ⟨ps, body⟩ := b.clause c
          if !ps.isEmpty then isOf a else
          match body.toList with
          | [s] => match b.stmt s with
            | .expr e => isOf e
            | _ => []
          | _ => isOf a
        | _ => isOf a
      let named := args.toList.flatMap isNames
      let args ← args.mapM go.ex
      let args ← if named.isEmpty then pure args else args.mapM fun a => do
        let b ← get
        match b.expr a with
        | .closure cid #[c] =>
          let ⟨ps, body⟩ := b.clause c
          if !ps.isEmpty then pure a else
          let held := named.eraseDups.filter (b.borrowedOnly · body.toList)
          let made := ((← heldStmts held body.toList) ++ body.toList).toArray
          pushExpr (.closure cid #[← pushClause ⟨[], made⟩])
        | _ => pure a
      pushExpr (.call id (← go.ex f) args))
    | _ => none
  onClause go b c := some (do
    let ⟨pats, body⟩ := b.clause c
    let made ← pushClause ⟨pats, (← go.stmts body.toList).toArray⟩
    promoteHeld [] made)
  onStmts go _ ss :=
    match ss with
    | [] => none
    | s :: rest => some (do
      let rest ← go.stmts rest
      let rec here (s : StmtId) (fuel : Nat) : Build (List StmtId) := do
        let b ← get
        match fuel, b.stmt s with
        | 0, _ => pure [← go.st s]
        | fuel + 1, .located line col inner =>
          (← here inner fuel).mapM fun s => pushStmt (.located line col s)
        | _, .let_ (.var x) e =>
          if b.borrowedOnly x rest || (b.valueLike e && b.fieldBorrowedOnly x rest) then
            pure [← pushStmt (.letMut x (← go.ex e))]
          else pure [← pushStmt (.let_ (.var x) (← go.ex e))]
        | _, .let_ pat e =>
          let held := (patternNames pat).eraseDups.filter (b.borrowedOnly · rest)
          let first ← pushStmt (.let_ pat (← go.ex e))
          let more ← held.mapM fun x => do pushStmt (.letMut x (← pushExpr (.name none x)))
          pure (first :: more)
        | _, _ => pure [← go.st s]
      pure ((← here s 64) ++ rest))

/-- A clause made so, with `values` as its parameters whose written types
are not references' (`Syntax.promoteClause`). -/
def promoteClause (values : List String) (c : ClauseId) : Build ClauseId := do
  let ⟨pats, body⟩ := (← get).clause c
  let body ← promoteRewrite.stmtList body.toList
  promoteHeld values (← pushClause ⟨pats, body.toArray⟩)

/-- The parameters of a clause written with `annots` that are values (written
with a type that is no reference's) and those that are references. -/
def paramsOf (pats : List Pattern) (annots : List (Option TypeExpr)) : List String × List String :=
  ((pats.zip annots).filterMap fun
    | (.var _, some (.ref _ _ _)) => none
    | (.var x, some _) => some x
    | _ => none,
   (pats.zip annots).filterMap fun
    | (.var x, some (.ref _ _ _)) => some x
    | _ => none)

/-- A clause of a function whose parameters are written with `annots`, made
so (`promoteClause`). (One written with a reference's type, `list: &[T]`:
`&list[0]` is the element through that reference, not through one to it.) -/
def promoteFnClause (annots : List (Option TypeExpr)) (c : ClauseId) : Build ClauseId := do
  let (values, refs) := paramsOf ((← get).clause c).pats annots
  let c ← if refs.isEmpty then pure c else (throughParamsRewrite refs).clause c
  promoteClause values (← nameBorrowsClause c)

/-- Each name a pattern binds with `mut` a variable of the same name where
what the pattern is of starts: `Some(mut n) => n = n + 1` as `Some(n) => let
mut n = n; n = n + 1`; in a `let`, after it. -/
def unmutRewrite : FRewrite where
  onClause go b c :=
    let cl := b.clause c
    let parts := cl.pats.map unmutPat
    let names := parts.flatMap (·.2)
    if names.isEmpty then none else some do
      let lets ← names.mapM fun x => do pushStmt (.letMut x (← pushExpr (.name none x)))
      let rest ← go.stmts cl.body.toList
      pushClause ⟨parts.map (·.1), (lets ++ rest).toArray⟩
  onStmts go b ss :=
    match ss with
    | [] => none
    | s :: rest =>
      -- (Through the places it is written at, to a `let`.)
      let rec find (s : StmtId) (fuel : Nat) (locs : List (Nat × Nat)) :
          Option (List (Nat × Nat) × Pattern × ExprId × List String) :=
        match fuel, b.stmt s with
        | fuel + 1, .located l c inner => find inner fuel (locs ++ [(l, c)])
        | _, .let_ pat value =>
          let (pat, names) := unmutPat pat
          if names.isEmpty then none else some (locs, pat, value, names)
        | _, _ => none
      (find s 64 []).map fun (locs, pat, value, names) => do
        let placed := fun (st : FStmt) => do
          let mut id ← pushStmt st
          for (l, c) in locs.reverse do id ← pushStmt (.located l c id)
          pure id
        let first ← placed (.let_ pat (← go.ex value))
        let more ← names.mapM fun x => do placed (.letMut x (← pushExpr (.name none x)))
        pure (first :: more ++ (← go.stmts rest))

end Glorious.Syntax.Flat

namespace Glorious.Syntax

/-- Every function of these items with its `mut` patterns made variables
(`Flat.unmutRewrite`). -/
def unmutItems (items : List Item) : List Item := items.map (·.mapBodies Flat.unmutRewrite.body)

end Glorious.Syntax
