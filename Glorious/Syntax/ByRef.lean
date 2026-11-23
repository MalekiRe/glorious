module

public import Glorious.Syntax.Ast
public import Glorious.Syntax.Flat

/-!
# Patterns that bind by reference

`&mut Circle(r) => ..`: the callable takes the reference, looks at what it
points to to choose a clause, and in the clause each name of the pattern is a
borrow of the part it names. Written out here once for two readers: the
resolver, for what a program writes, with names not yet resolved; and the
checker, for patterns of a value it finds a match of a reference has
(`Elab.Decision.refPats`), with names resolved, in a body of their own. What each knows of names is
`RefNames`.
-/

public section

namespace Glorious.Syntax

/-- Is this pattern one that binds by reference, and for writing? -/
def byRef? : Pattern → Option (Bool × Pattern)
  | .ctor name none [p] =>
    if name == byRefMark true then some (true, p)
    else if name == byRefMark false then some (false, p)
    else none
  | _ => none

/-- What the writing out needs to know of the names in patterns. -/
structure RefNames (m : Type → Type) where
  /-- What a name in a pattern is: `0` a new name, `1` a constructor, `2` a
  constant. -/
  kind : String → m Nat
  /-- A constructor pattern's constructor, as a step names it, and its fields'
  patterns, every one written (records in order, `..` written out). -/
  ctor : String → Option String → List Pattern → m (String × List Pattern)
  /-- The constructor a shape asks for, as it is named where it is asked, if
  this is one. -/
  ctorTest : String → Option String → m (Option Expr)
  /-- A number not given out before. -/
  fresh : m Nat

variable {m : Type → Type} [Monad m] [MonadExceptOf String m]

/-- A pattern as the test of a value's shape that it is, its names left out;
and for each name, the way to the part it names: through tuples by number,
through constructors by constructor and number. -/
partial def shapeOf (rn : RefNames m) (way : List String) : Pattern → m (Pattern × List (String × List String))
  | .wild => pure (.wild, [])
  | .int n => pure (.int n, [])
  | .var x => do
    -- A constructor or a constant is a test; a new name names this part.
    if (← rn.kind x) != 0 then pure (.var x, []) else pure (.wild, [(x, way)])
  | .tuple args => do
    let mut pats : Array Pattern := #[]
    let mut names : List (String × List String) := []
    for (p, i) in args.zipIdx do
      let (p, ns) ← shapeOf rn (way ++ [toString i]) p
      pats := pats.push p
      names := names ++ ns
    pure (.tuple pats.toList, names)
  | .ctor name qual args => do
    if (byRef? (.ctor name qual args)).isSome then
      throw "a pattern that binds by reference is written once, around the whole pattern"
    let (global, args) ← rn.ctor name qual args
    let mut pats : Array Pattern := #[]
    let mut names : List (String × List String) := []
    for (p, i) in args.zipIdx do
      let (p, ns) ← shapeOf rn (way ++ [ctorStep global i]) p
      pats := pats.push p
      names := names ++ ns
    pure (.ctor name qual pats.toList, names)

/-- What a shape asks of a value: at each path of field numbers where it names
a constructor, that constructor. None if it asks for a number, which has to be
read to be compared. -/
partial def shapeTests (rn : RefNames m) (path : List Nat) :
    Pattern → m (Option (List (List Nat × Expr)))
  | .wild => pure (some [])
  | .int _ => pure none
  | .var x => do
    match ← rn.kind x with
    | 0 => pure (some [])
    | 1 => pure ((← rn.ctorTest x none).map fun e => [(path, e)])
    | _ => pure none
  | .tuple args => parts [] args
  | .ctor name qual args => do
    let some named ← rn.ctorTest name qual | return none
    parts [(path, named)] args
where
  /-- Each part's tests after `out`, none where one has none. -/
  parts (out : List (List Nat × Expr)) (args : List Pattern) : m (Option (List (List Nat × Expr))) := do
    let mut out := out
    for (p, i) in args.zipIdx do
      match ← shapeTests rn (path ++ [i]) p with
      | some more => out := out ++ more
      | none => return none
    pure (some out)

/-- The clauses of a callable in which a parameter binds by reference,
`&mut Circle(r) => ..`: the callable takes the reference, looks at what it
points to to choose a clause, and in the clause each name of the pattern is a
borrow of the part it names, through the reference. So a part of one of a
type's several constructors can be borrowed, once the value is known to be
made by that one. Clauses without such a parameter are as they are; the
clause that takes the references and asks the cells is made in the body. -/
def Flat.byReference [MonadStateOf Flat.Body m] (rn : RefNames m) (clauses : Array Flat.ClauseId) :
    m (Array Flat.ClauseId) := do
  let b ← getThe Flat.Body
  let cls := clauses.toList.map b.clause
  let arity := match cls.head? with
    | some c => c.pats.length
    | none => 0
  let places := (List.range arity).filter fun i => cls.any fun c => ((c.pats[i]?).bind byRef?).isSome
  if places.isEmpty then return clauses
  let push := fun (n : Flat.FExpr) => (modifyGet fun (b : Flat.Body) => (b.exprs.size, { b with exprs := b.exprs.push n }) : m Flat.ExprId)
  let pushS := fun (n : Flat.FStmt) => (modifyGet fun (b : Flat.Body) => (b.stmts.size, { b with stmts := b.stmts.push n }) : m Flat.StmtId)
  let pushC := fun (n : Flat.FClause) => (modifyGet fun (b : Flat.Body) => (b.clauses.size, { b with clauses := b.clauses.push n }) : m Flat.ClauseId)
  let pushTree := fun (e : Expr) => (modifyGet fun (b : Flat.Body) => (Flat.flatExpr e).run b : m Flat.ExprId)
  let k ← rn.fresh
  let outer := (List.range arity).map fun i => s!"%given{k}_{i}"
  -- What the clauses ask of what each reference points to: each constructor
  -- at each place.
  let mut asked : List (Nat × List (List Nat × Expr)) := []
  let mut byTest := true
  let same := fun (a b : List Nat × Expr) =>
    a.1 == b.1 && (match a.2, b.2 with
      | .name q x, .name q' x' => q == q' && x == x'
      | _, _ => false)
  for c in cls do
    for (p, i) in c.pats.zip (List.range arity) do
      if places.contains i then
        if let some (_, p) := byRef? p then
          let (shape, _) ← shapeOf rn [] p
          match ← shapeTests rn [] shape with
          | some found =>
            let so := (asked.lookup i).getD []
            let more := found.filter fun f => !so.any (same f)
            asked := (i, so ++ more) :: asked.filter (·.1 != i)
          | none => byTest := false
  let mut inner : Array Flat.ClauseId := #[]
  for c in cls do
    let ⟨pats, body⟩ := c
    unless pats.length == arity do
      throw "the clauses of a callable take different numbers of arguments"
    let mut tests : Array Pattern := #[]
    let mut binds : Array Flat.StmtId := #[]
    for (p, i) in pats.zip (List.range arity) do
      if places.contains i then
        match byRef? p with
        | some (uniq, p) =>
          let (test, names) ← shapeOf rn [] p
          if byTest then
            let mine := ((← shapeTests rn [] test).getD [])
            tests := tests.push (.tuple (((asked.lookup i).getD []).map fun a =>
              if mine.any (same a) then Pattern.int 1 else Pattern.wild))
          else tests := tests.push test
          for (x, way) in names do
            let id := 900000000 + (← rn.fresh)
            if way.isEmpty then
              -- The whole of what is pointed to: the reference itself, lent.
              let given ← push (.name none s!"%given{k}_{i}")
              binds := binds.push (← pushS (.let_ (.var x) (← push (.reborrow uniq given))))
            else
              binds := binds.push (← pushS (.let_ (.var x) (← push (.refField id uniq s!"%given{k}_{i}" way true))))
        | none =>
          -- A clause that takes the reference as it is, or lets it go.
          match p with
          | .wild => tests := tests.push .wild
          | .var x =>
            if (← rn.kind x) != 0 then
              throw "where one clause binds a parameter by reference, `&mut Pattern`, every clause does, or takes the reference whole"
            tests := tests.push .wild
            binds := binds.push (← pushS (.let_ (.var x) (← push (.name none s!"%given{k}_{i}"))))
          | _ =>
            throw "where one clause binds a parameter by reference, `&mut Pattern`, every clause does, or takes the reference whole"
      else tests := tests.push p
    -- (Chosen by looking at a copy of what is pointed to: the copy is not
    -- the clause's, and what its patterns let go is not destroyed.)
    let observed ← if byTest then pure #[] else pure #[← pushS (.expr (← push (.name none observedMark)))]
    inner := inner.push (← pushC ⟨tests.toList, observed ++ binds ++ body⟩)
  -- Asked of the cells, the clauses' tests are of numbers, which say nothing
  -- of whether every case is covered: the patterns as written say that, to
  -- the checker; and a last clause, never reached, stands for the rest.
  let shapes ← if byTest then do
      let mut rows : Array Flat.ClauseId := #[]
      for c in cls do
        let mut row : Array Pattern := #[]
        for (p, i) in c.pats.zip (List.range arity) do
          match (if places.contains i then byRef? p else none) with
          | some (_, p) => row := row.push (← shapeOf rn [] p).1
          | none => row := row.push (if places.contains i then Pattern.wild else p)
        rows := rows.push (← pushC ⟨row.toList, #[]⟩)
      let mut args : Array Flat.ExprId := #[]
      for (x, i) in outer.zip (List.range arity) do
        let n ← push (.name none x)
        args := args.push (← if places.contains i then push (.deref n) else pure n)
      let callable ← push (.closure 0 rows)
      let call ← push (.call 0 (← push (.name none "%shapes")) (args.push callable))
      pure #[← pushS (.expr call)]
    else pure #[]
  if byTest then
    let never ← push (.tailCall 0 (← push (.name none "%never")) #[])
    inner := inner.push (← pushC ⟨List.replicate arity Pattern.wild, #[← pushS (.expr never)]⟩)
  let mut args : Array Flat.ExprId := #[]
  for (x, i) in outer.zip (List.range arity) do
    if !places.contains i then args := args.push (← push (.name none x))
    else if byTest then
      let tests ← ((asked.lookup i).getD []).mapM fun (path, ctor) =>
        pushTree (.call 0 (.name none ctorIsMark)
          ([Expr.name none x] ++ path.map (fun (n : Nat) => Expr.int (n : Int)) ++ [ctor]))
      args := args.push (← push (.tuple tests.toArray))
    else args := args.push (← push (.deref (← push (.name none x))))
  let callable ← push (.closure 0 inner)
  let run ← pushS (.expr (← push (.call 0 callable args)))
  pure #[← pushC ⟨outer.map Pattern.var, shapes ++ #[run]⟩]

end Glorious.Syntax
