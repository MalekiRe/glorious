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
      match b.mark? f, b.bare? a with
      | some .move, some x => some [x]
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
  | .mark m => mixHash 16 (hash m)
  | .type t => mixHash 17 (hash t)

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
  -- (A dot call's receiver, `x.f()`: borrowed, as the function's type will
  -- most often say, `Check.receiverByType`.)
  | .call _ m #[r] =>
    if b.mark? m == some .receiver && b.bare? r == some x then { shared := true }
    else b.foldDirect (fun u e => u.or (b.nameUseExpr noDefers x e)) {} e
  -- (`x[i]`, or `x.f[i]`: the element read where it is, through a borrow
  -- of `x`.)
  | .call _ f #[a, i] =>
    match b.expr f with
    | .name _ "index" =>
      if b.placeRoot a == some x then ({ indexed := true } : NameUse).or (b.nameUseExpr noDefers x i)
      else b.foldDirect (fun u e => u.or (b.nameUseExpr noDefers x e)) {} e
    | _ => b.foldDirect (fun u e => u.or (b.nameUseExpr noDefers x e)) {} e
  | .closure _ cs =>
    NameUse.inside (cs.foldl (fun u c => u.or (b.nameUseClause noDefers x c)) ({} : NameUse))
  | .handle subject arms =>
    (NameUse.inside (arms.foldl (fun u c => u.or (b.nameUseClause noDefers x c)) ({} : NameUse))).or
      (b.nameUseExpr noDefers x subject)
  -- (A name bound again in a block is another name there, not after it.)
  | .labelScope _ body => { b.nameUseStmts noDefers x body.toList with rebound := false }
  | _ => b.foldDirect (fun u e => u.or (b.nameUseExpr noDefers x e)) {} e

partial def nameUseClause (b : Body) (noDefers : Bool) (x : String) (c : ClauseId) : NameUse :=
  let ⟨pats, body⟩ := b.clause c
  -- (A clause whose patterns bind the name again: none of its uses are of
  -- this one.)
  if (pats.flatMap patternNames).contains x then {} else b.nameUseStmts noDefers x body.toList

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
  -- (`if(c) { a } else { b }`: `a` and `b` are the one or the other, each
  -- from what was seen once `c` was.)
  let branches : Option (ExprId × ExprId × ExprId) := match b.expr e with
    | .call _ f #[i, other] =>
      match (b.name? f).map (·.2), b.expr i with
      | some "else", .call _ g #[c, first] => if (b.name? g).map (·.2) == some "if" then some (c, first, other) else none
      | _, _ => none
    | _ => none
  match branches with
  | some (c, first, other) =>
    let (seen, bad) := b.borrowAfterValue x seen c
    let (s1, b1) := b.borrowAfterValue x seen first
    let (s2, b2) := b.borrowAfterValue x seen other
    (s1 || s2, bad || b1 || b2)
  | none =>
  match b.expr e with
  | .name none y => (seen || y == x, false)
  | .ref _ y | .refField _ _ y _ _ => (seen, seen && y == x)
  | .proj e _ | .fieldOf _ e _ => if b.placeRoot e == some x then (seen, seen) else b.borrowAfterValue x seen e
  | .closure _ cs =>
    -- (Within each clause in the order it is written, from what was seen
    -- before the callable: `&mut v; v` in one arm borrows before the value
    -- goes. A callable run again counts its uses again, which the count of
    -- them sees.)
    let u := b.nameUseExpr false x e
    let inner := cs.toList.any fun c =>
      let ⟨pats, body⟩ := b.clause c
      if (pats.flatMap patternNames).contains x then false
      else (body.foldl (fun (seen, bad) s =>
        let (seen', bad') := b.borrowAfterValueStmt x seen s
        (seen', bad || bad')) (seen, false)).2
    (seen || u.valuedInside, inner)
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
  | .name _ x => if lastSegment x == textEndName then some [] else none
  | .call _ f #[c, rest] =>
    match b.expr f, b.expr c with
    | .name _ x, .call _ g #[n] =>
      if lastSegment x != textCharName then none else
      match b.expr g, b.expr n with
      | .name _ y, .int code => if lastSegment y == "char_of" then (textCodes b rest).map (code.toNat :: ·) else none
      | _, _ => none
    | _, _ => none
  | _ => none

/-- Is the value a name holds used as it is, with no borrow of the name and
nothing written to it after? -/
def givenAway (b : Body) (x : String) (rest : List StmtId) : Bool :=
  -- (Up to where the name is bound again, `let mut batch = ..` once more:
  -- another variable from there, and what this one held is given away
  -- before it.)
  let upTo := rest.takeWhile (!b.bindsAgain x ·)
  let rest := upTo ++ (rest.drop upTo.length).take 1
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
  (u.valued || u.valuedInside) && !bad

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

abbrev FRewrite := FRewriteM Id

section
variable {m : Type → Type} [Monad m]

private def pushE (e : FExpr) (id : Option Nat := none) : StateT Body m ExprId := modifyGet fun b => b.add e id
private def pushS (s : FStmt) : StateT Body m StmtId := modifyGet fun b => (b.stmts.size, { b with stmts := b.stmts.push s })
private def pushC (c : FClause) : StateT Body m ClauseId := modifyGet fun b => (b.clauses.size, { b with clauses := b.clauses.push c })

mutual

partial def FRewriteM.ex (r : FRewriteM m) (e : ExprId) : StateT Body m ExprId := do
  let b ← get
  if let some made := r.onExpr r.go b e then return ← made
  let n := b.expr e
  let n' ← n.mapIds r.ex r.clause fun body => do pure (← r.stmtList body.toList).toArray
  if n' == n then pure e else pushE n' (some ((← get).idOf e))

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
        pushExpr (.call 0 (← pushExpr (.mark .inst)) #[call, ty]))
      | _, _ => none
    | _ => none
  onPat := selfPattern self

/-- Is an ascription, `let x: Type = ..`, among a body's nodes (reached or
not)? Asked first: most bodies have none. -/
def Body.anyAscription (b : Body) : Bool :=
  b.exprs.any fun
    | .call _ f #[_, _] => b.mark? f == some .ascribe || b.mark? f == some .inst
    | _ => false

/-- The ascriptions an expression has, `let x: Type = ..`: the places of the
types written, added in front of `acc`. -/
partial def Body.ascriptionsExpr (b : Body) (e : ExprId) (acc : List ExprId) : List ExprId :=
  let rest := fun (_ : Unit) => (b.children e).foldr (fun x acc => b.ascriptionsExpr x acc) acc
  match b.expr e with
  | .call _ f #[v, ty] =>
    -- (The type itself is not looked in.)
    if b.mark? f == some .ascribe || b.mark? f == some .inst then ty :: b.ascriptionsExpr v acc else rest ()
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
      made := made.insert ty (.type (← f (b.typeAt ty)))
    pure { onExpr := fun _ _ e => (made[e]?).map fun t => flatExpr t }

/-- An expression with each type written in it changed (`mapTypes`). -/
def mapTypesOf (f : TypeExpr → Except String TypeExpr) (b : Body) (e : ExprId) : Except String (Body × ExprId) := do
  let places := if b.anyAscription then b.ascriptionsExpr e [] else []
  if places.isEmpty then return (b, e)
  let (e, b) := ((← mapTypes.typesRewrite f b places).ex e).run b
  pure (b, e)

/-- Does naming what is borrowed name something of this first, outside its
blocks (`nameBorrowsE`)? -/
partial def Body.hoists (b : Body) (e : ExprId) : Bool :=
  match b.expr e with
  | .call _ f args =>
    (match b.mark? f with
      | some .held | some .borrow | some .borrowMut | some .through => true
      | _ => b.hoists f) || args.any b.hoists
  | .tailCall _ f args => b.hoists f || args.any b.hoists
  | .tuple args => args.any b.hoists
  | .proj x _ | .deref x | .reborrow _ x | .fieldOf _ x _ => b.hoists x
  | _ => false

/-- Does this compute something where it is: a call, a handler or a block
(not a name, a number, a borrow of a name or a callable)? -/
partial def Body.computes (b : Body) (e : ExprId) : Bool :=
  match b.expr e with
  | .call _ f _ => (b.mark? f).isNone || (b.direct e).any b.computes
  | .tailCall .. | .handle .. | .labelScope .. => true
  | .tuple args => args.any b.computes
  | .proj x _ | .deref x | .reborrow _ x | .fieldOf _ x _ => b.computes x
  | _ => false

mutual

/-- A value that is borrowed where it is made, `&f(x)`, given a name first
(`Syntax.nameBorrowsM`): the statements that bind the names, made before it. -/
partial def nameBorrowsE (e : ExprId) : StateT (Array StmtId) Build ExprId := do
  let b ← getThe Body
  match b.expr e with
  -- (A field borrowed through what an expression points to,
  -- `%through(base, (steps), uniq)`: the base named first.)
  | .call id f #[base, steps, uniq] =>
    if b.mark? f != some .through then return ← nameBorrowsChildren e
    let (.tuple steps, .int uniq) := (b.expr steps, b.expr uniq) | nameBorrowsChildren e
    let base' ← nameBorrowsE base
    let name := s!"%through{id}"
    let st ← (pushStmt (.let_ (.var name) base') : Build StmtId)
    modify (·.push st)
    let path := steps.toList.filterMap b.bare?
    (pushExpr (.refField id (uniq == 1) name path true) : Build ExprId)
  | .call id f #[x] =>
    match b.mark? f with
    | some mark =>
      let x' ← nameBorrowsE x
      -- (A value named where a dot call is made on it: the variable, given
      -- by name, `Syntax.Mark.held`.)
      if mark == .held then
        let name := s!"borrowed%{id}"
        let st ← (pushStmt (.let_ (.var name) x') : Build StmtId)
        modify (·.push st)
        return ← (pushExpr (.name none name) : Build ExprId)
      if mark != .borrow && mark != .borrowMut then
        return ← if x' == x then pure e else (pushExpr (.call id f #[x']) : Build ExprId)
      let name := s!"borrowed%{id}"
      let uniq := mark == .borrowMut
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

/-- Arguments made so, in the order they are computed: one before another
that names something first (`hoists`), that computes something (`computes`),
is named first itself, so that what it computes is not computed after what
the later one names. `key` tells the names made apart. -/
partial def nameInOrder (key : Nat) (args : Array ExprId) : StateT (Array StmtId) Build (Array ExprId) := do
  let b ← getThe Body
  let last := ((List.range args.size).filter fun j => b.hoists args[j]!).getLast?
  let mut out := #[]
  for (a, j) in args.zipIdx do
    if last.any (j < ·) && !b.hoists a && b.computes a then
      let a' ← nameBorrowsE a
      let name := s!"%ordered{key}_{j}"
      let st ← (pushStmt (.let_ (.var name) a') : Build StmtId)
      modify (·.push st)
      out := out.push (← (pushExpr (.name none name) : Build ExprId))
    else out := out.push (← nameBorrowsE a)
  pure out

/-- The parts directly inside, and the blocks inside, made so. -/
partial def nameBorrowsChildren (e : ExprId) : StateT (Array StmtId) Build ExprId := do
  let b ← getThe Body
  match b.expr e with
  | .call i g args => do (pushExpr (.call i (← nameBorrowsE g) (← nameInOrder i args)) : Build _)
  | .tailCall i g args => do (pushExpr (.tailCall i (← nameBorrowsE g) (← nameInOrder i args)) : Build _)
  | .tuple args => do (pushExpr (.tuple (← nameInOrder (b.idOf e + (1 <<< 40)) args)) : Build _)
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

/-- The number of the call a handler handles: the call itself, or the last
of the block made around it where what it borrows is named first
(`nameBorrowsE`); `0` where it is no call. -/
partial def Body.subjectCall (b : Body) (e : ExprId) (fuel : Nat := 8) : Nat :=
  match fuel, b.expr e with
  | _, .call id _ _ => id
  | fuel + 1, .labelScope "%block" body =>
    let rec last (s : StmtId) (fuel : Nat) : Nat := match fuel, b.stmt s with
      | _, .expr e => b.subjectCall e fuel
      | fuel + 1, .located _ _ inner => last inner fuel
      | _, _ => 0
    match body.back? with
    | some s => last s fuel
    | none => 0
  | _, _ => 0

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

/-- `a[i]` of a place that is not copied for it: what reads the element
where it is, `*element_at(&a, i)`; none where `a` is not such a place. -/
def elementRead (b : Body) (id : Nat) (a i : ExprId) : Build (Option ExprId) := do
  -- (`a[i][j]`: the element of the element, where it is.)
  let isElement : ExprId → Bool := fun e => match b.expr e with
    | .call _ g _ => (b.name? g).map (·.2) == some "element_at"
    | _ => false
  if let .deref inner := b.expr a then
    if isElement inner then
      return some (← pushExpr (.deref (← pushExpr (.call id (← pushExpr (.name none "element_at")) #[inner, i]))))
  -- (`a[i].f[j]`: the element of a field of the element, through the
  -- element's reference, held for it.)
  let rec fieldsOfElement (e : ExprId) (fuel : Nat) : Option (ExprId × List String × Nat) :=
    match fuel, b.expr e with
    | fuel + 1, .fieldOf fid inner field =>
      match b.expr inner with
      | .deref r => if isElement r then some (r, [field], fid) else none
      -- (Read through the element's reference already, `receiverExpr`.)
      | _ =>
        if isElement inner then some (inner, [field], fid)
        else (fieldsOfElement inner fuel).map fun (r, path, _) => (r, path ++ [field], fid)
    | _, _ => none
  if let some (r, path, fid) := fieldsOfElement a 64 then
    if fid != 0 then
      let held := s!"%element{id}"
      let first ← pushStmt (.let_ (.var held) r)
      let base ← pushExpr (.refField fid false held path true)
      let read ← pushExpr (.deref (← pushExpr (.call id (← pushExpr (.name none "element_at")) #[base, i])))
      return some (← pushExpr (.labelScope "%block" #[first, ← pushStmt (.expr read)]))
  -- (A name, or a path of fields from one, borrowed where it is, as Rust's
  -- `x[i]` is `*x.index(i)`: through the reference it holds where it holds
  -- one, `Check.elementBase`.)
  let rec chain (e : ExprId) (fuel : Nat) : Option (String × List String × Nat) :=
    match fuel, b.expr e with
    | fuel + 1, .fieldOf fid inner field =>
      match b.expr inner with
      | .name none x => some (x, [field], fid)
      | _ => (chain inner fuel).map fun (x, path, _) => (x, path ++ [field], fid)
    | fuel + 1, .proj inner n =>
      match b.expr inner with
      | .name none x => some (x, [toString n], 0)
      | _ => (chain inner fuel).map fun (x, path, fid) => (x, path ++ [toString n], fid)
    | _, _ => none
  let base ← match b.expr a, chain a 64 with
    | .name none x, _ =>
      if (lastSegment x).front.isUpper then pure none else some <$> pushExpr (.ref false x)
    | _, some (x, path, fid) => if fid != 0 then some <$> pushExpr (.refField fid false x path false) else pure none
    | _, none => pure none
  match base with
  | some r => some <$> pushExpr (.deref (← pushExpr (.call id (← pushExpr (.name none "element_at")) #[r, i])))
  | none => pure none

mutual

/-- A dot call's receiver, `value.f(a)`, as the checker is to find how `f`
takes it (`%receiver(value)`, `Check.receiverByName`): a name, a path of
fields from one, an element read where it is, or a value made where it is
called on, given a name for the statement (`Mark.held`). (A field of an
element, and what an operation gives, borrowed here as `f` is declared to
take it, `taken`.) And `a[i]`, read where it is (`elementRead`). -/
partial def receiverExpr (e : ExprId) : Build ExprId := do
  let b ← get
  match b.expr e with
  | .call id f args =>
    let f ← receiverExpr f
    let args ← args.mapM (receiverExpr)
    let b ← get
    let plain := fun (_ : Unit) => pushExpr (.call id f args)
    match b.expr f, args.toList with
    -- `a[i]` of a mutable variable, or of a field of a value or of what a
    -- reference points to: the element read where it is, nothing copied.
    -- (Also where a variable of the program is named `index`: the call is
    -- then still the prelude's, `%prelude::index`.)
    | .name q "index", [a, i] =>
      if q.isSome && q != some "%prelude" then plain () else
      -- (`v.index(i)` as `v[i]` is.)
      let a := match b.expr a with
        | .call _ rm #[r] => if b.mark? rm == some .receiver then r else a
        | _ => a
      match ← elementRead b id a i with
      | some e => pure e
      | none => plain ()
    | .name q name, args0 =>
      -- (A comparison: each operand that is no name nor a whole number
      -- named first, so that the checker, which compares by reference what
      -- is not copied, knows what it compares before it reads the
      -- comparison, `Check.compareByType`.)
      if let [l, r] := args0 then
        if (compareOps.lookup name).isSome then
          -- (A name, or a literal: a whole number, or one of a type made of
          -- whole numbers, `'c'`, `"text"`, `5u8`.)
          let named := fun (a : ExprId) => match b.expr a with
            | .int _ => true
            | .name none x => !(lastSegment x).front.isUpper
            | .call _ g args => ((b.bare? g).any fun n => (lastSegment n).endsWith "_of") && args.all fun a => match b.expr a with
              | .int _ => true
              | _ => false
            | _ => false
          if named l && named r then return ← plain ()
          -- (In a block of its own where the comparison is: computed where
          -- it is, and let go once compared.)
          let mut lets : Array StmtId := #[]
          let mut operands : Array ExprId := #[]
          for (a, k) in [(l, 0), (r, 1)] do
            if named a then operands := operands.push a
            else
              let x := s!"%compared{id}_{k}"
              lets := lets.push (← pushStmt (.let_ (.var x) a))
              operands := operands.push (← pushExpr (.name none x))
          let compared ← pushStmt (.expr (← pushExpr (.call id f operands)))
          return ← pushExpr (.labelScope "%block" (lets.push compared))
      -- (Each argument marked `%receiver(..)`: a dot call's receiver, or each
      -- of a comparison's two (`Decision.compareByRef`), borrowed as `name`
      -- takes it.)
      let marked := fun (a : ExprId) => match b.expr a with
        | .call _ rm #[r] => if b.mark? rm == some .receiver then some r else none
        | _ => none
      if args0.all (marked · |>.isNone) then return ← plain ()
      -- (A path of fields from a name, `p.items`.)
      let rec fieldOfName (e : ExprId) (fuel : Nat) : Bool :=
        match fuel, b.expr e with
        | fuel + 1, .fieldOf fid inner _ => fid != 0 && ((b.bare? inner).isSome || fieldOfName inner fuel)
        | _, _ => false
      let isElement := fun (e : ExprId) => match b.expr e with
        | .deref inner => match b.expr inner with
          | .call _ g _ => (b.name? g).map (·.2) == some "element_at"
          | _ => false
        | _ => false
      let givenOf := fun (k : Nat) (receiver : ExprId) => (do
        let mark := fun (r : ExprId) => (do pushExpr (.call 0 (← pushExpr (.mark .receiver)) #[r]) : Build ExprId)
        -- (A name, a path of fields from one, or an element read where it
        -- is, `v[i]`: borrowed where the call is read, as the function in
        -- scope takes it, `Check.receiverByName`.)
        if let some x := b.bare? receiver then
          if !(lastSegment x).front.isUpper then return ← mark receiver
        if fieldOfName receiver 64 || isElement receiver then return ← mark receiver
        -- (A value made where it is called on, `half(4).is_ok()`, or a
        -- constructor without fields or a constant, `D.greet()`: given a
        -- name of its own for the statement, a variable, for the checker
        -- to say how the call takes it, `Mark.held`.)
        let made : Bool := match b.expr receiver with
          | .call _ g _ => (b.name? g).map (·.2) != some "element_at"
          | .name none x => (lastSegment x).front.isUpper
          | _ => false
        if made then
          return ← mark (← pushExpr (.call (if k == 0 then id else id + 500000 * k) (← pushExpr (.mark .held)) #[receiver]))
        -- (A field of an element, `v[0].i.to_string()`: the element's
        -- reference named first, `Mark.held`, the field read through it,
        -- and the checker to say how the call takes it; for writing, it
        -- names the element's place, `Check.elementPlaceFor`.)
        let rec ofElement (e : ExprId) (fuel : Nat) : Build (Option ExprId) := do
          match fuel, b.expr e with
          | 0, _ => pure none
          | fuel + 1, .fieldOf fid inner field =>
            let r := match b.expr inner with
              | .deref r => r
              | _ => inner
            let atElement : Bool := match b.expr r with
              | .call _ g _ => (b.name? g).map (·.2) == some "element_at"
              | _ => false
            let inner' ← if atElement then
                some <$> pushExpr (.call (id + 600000 + k) (← pushExpr (.mark .held)) #[r])
              else ofElement inner fuel
            match inner' with
            | some i' => some <$> pushExpr (.fieldOf fid i' field)
            | none => pure none
          | _, _ => pure none
        match ← ofElement receiver 16 with
        | some r => mark r
        | none => pure receiver : Build ExprId)
      let given ← args0.toArray.zipIdx.mapM fun (a, k) => match marked a with
        | some r => givenOf k r
        | none => pure a
      pushExpr (.call id (← pushExpr (.name q name)) given)
    | _, _ => plain ()
  -- (`a[i].f`: the field read through the element's reference, the rest of
  -- the element not copied.)
  | .fieldOf fid inner field => do
    let inner' ← receiverExpr inner
    let b ← get
    match b.expr inner' with
    | .deref r =>
      match b.expr r with
      | .call _ g _ =>
        -- (By name: a numbered field, `.0`, is read of the element as it is.)
        if (b.name? g).map (·.2) == some "element_at" && field.toNat?.isNone then pushExpr (.fieldOf fid r field)
        else if inner' == inner then pure e else pushExpr (.fieldOf fid inner' field)
      | _ => if inner' == inner then pure e else pushExpr (.fieldOf fid inner' field)
    | _ => if inner' == inner then pure e else pushExpr (.fieldOf fid inner' field)
  | n => do
    let n' ← n.mapIds (receiverExpr) (receiverClause)
      fun body => do pure (← receiverStmts body.toList).toArray
    if n' == n then pure e else pushExpr n'

partial def receiverClause (c : ClauseId) : Build ClauseId := do
  let ⟨pats, body⟩ := (← get).clause c
  pushClause ⟨pats, (← receiverStmts body.toList).toArray⟩

partial def receiverStmts : List StmtId → Build (List StmtId)
  | [] => pure []
  | s :: rest => do
    let rec here (s : StmtId) (fuel : Nat) : Build StmtId := do
      let b ← get
      match fuel, b.stmt s with
      | 0, _ => pure s
      | _, .let_ pat value => pushStmt (.let_ pat (← receiverExpr value))
      | _, .letMut x value => pushStmt (.letMut x (← receiverExpr value))
      | _, .expr e => pushStmt (.expr (← receiverExpr e))
      | _, .defer e => pushStmt (.defer (← receiverExpr e))
      | _, .assign target value =>
        -- (`a[i] = v` is written where it is: what is below it is looked at.)
        let t ← match b.expr target with
          | .call id f #[a, i] =>
            if (b.name? f).map (·.2) == some "index" then do
              pushExpr (.call id f #[← receiverExpr a, ← receiverExpr i])
            else receiverExpr target
          | _ => receiverExpr target
        let v ← receiverExpr value
        pushStmt (.assign t v)
      | fuel + 1, .located line col inner => pushStmt (.located line col (← here inner fuel))
    pure ((← here s 64) :: (← receiverStmts rest))

end

/-- A clause of a function as name resolution leaves it, desugared: each
dot call's receiver marked for the checker and `a[i]` read where it is
(`receiverClause`), and what is then borrowed named first
(`nameBorrowsClause`). -/
def desugarClause (c : ClauseId) : Build ClauseId := do nameBorrowsClause (← receiverClause c)

end Glorious.Syntax.Flat

namespace Glorious.Syntax

/-- Every function of these items with its `mut` patterns made variables
(`Flat.unmutRewrite`). -/
def unmutItems (items : List Item) : List Item := items.map (·.mapBodies Flat.unmutRewrite.body)

end Glorious.Syntax
