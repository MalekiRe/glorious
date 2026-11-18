module

public import Glorious.Syntax.Ast

/-!
# Patterns that bind by reference

`&mut Circle(r) => ..`: the callable takes the reference, looks at what it
points to to choose a clause, and in the clause each name of the pattern is a
borrow of the part it names. Written out here once for two readers: the
resolver, for what a program writes, with names not yet resolved; and the
checker, for patterns of a value it finds a match of a reference has
(`Elab.Decision.refPats`), with names resolved. What each knows of names is
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
  | .tuple args => do
    let mut out : List (List Nat × Expr) := []
    for (p, i) in args.zipIdx do
      match ← shapeTests rn (path ++ [i]) p with
      | some more => out := out ++ more
      | none => return none
    pure (some out)
  | .ctor name qual args => do
    let some named ← rn.ctorTest name qual | return none
    let mut out : List (List Nat × Expr) := [(path, named)]
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
made by that one. Clauses without such a parameter are as they are. -/
def byReference (rn : RefNames m) (clauses : List Clause) : m (List Clause) := do
  let arity := match clauses.head? with
    | some (.mk pats _) => pats.length
    | none => 0
  let places := (List.range arity).filter fun i => clauses.any fun
    | .mk pats _ => ((pats[i]?).bind byRef?).isSome
  if places.isEmpty then return clauses
  let k ← rn.fresh
  let outer := (List.range arity).map fun i => s!"%given{k}_{i}"
  -- What the clauses ask of what each reference points to: each constructor
  -- at each place. A clause is chosen by asking the cell, which reads
  -- nothing out of it, so what is pointed to need not be a value that can be
  -- copied. Where a clause asks for a number, the value is read instead.
  let mut asked : List (Nat × List (List Nat × Expr)) := []
  let mut byTest := true
  let same := fun (a b : List Nat × Expr) =>
    a.1 == b.1 && (match a.2, b.2 with
      | .name q x, .name q' x' => q == q' && x == x'
      | _, _ => false)
  for clause in clauses do
    let .mk pats _ := clause
    for (p, i) in pats.zip (List.range arity) do
      if places.contains i then
        if let some (_, p) := byRef? p then
          let (shape, _) ← shapeOf rn [] p
          match ← shapeTests rn [] shape with
          | some found =>
            let so := (asked.lookup i).getD []
            let more := found.filter fun f => !so.any (same f)
            asked := (i, so ++ more) :: asked.filter (·.1 != i)
          | none => byTest := false
  let mut inner : Array Clause := #[]
  for clause in clauses do
    let .mk pats body := clause
    unless pats.length == arity do
      throw "the clauses of a callable take different numbers of arguments"
    let mut tests : Array Pattern := #[]
    let mut binds : Array Stmt := #[]
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
              binds := binds.push (.let_ (.var x) (.reborrow uniq (.name none s!"%given{k}_{i}")))
            else
              binds := binds.push (.let_ (.var x) (.refField id uniq s!"%given{k}_{i}" way true))
        | none =>
          -- A clause that takes the reference as it is, or lets it go.
          match p with
          | .wild => tests := tests.push .wild
          | .var x =>
            if (← rn.kind x) != 0 then
              throw "where one clause binds a parameter by reference, `&mut Pattern`, every clause does, or takes the reference whole"
            tests := tests.push .wild
            binds := binds.push (.let_ (.var x) (.name none s!"%given{k}_{i}"))
          | _ =>
            throw "where one clause binds a parameter by reference, `&mut Pattern`, every clause does, or takes the reference whole"
      else tests := tests.push p
    -- (Chosen by looking at a copy of what is pointed to: the copy is not
    -- the clause's, and what its patterns let go is not destroyed.)
    let observed := if byTest then [] else [Stmt.expr (.name none observedMark)]
    inner := inner.push (.mk tests.toList (observed ++ binds.toList ++ body))
  -- Asked of the cells, the clauses' tests are of numbers, which say nothing
  -- of whether every case is covered: the patterns as written say that, to
  -- the checker; and a last clause, never reached, stands for the rest.
  let shapes ← if byTest then do
      let mut rows : Array Clause := #[]
      for clause in clauses do
        let .mk pats _ := clause
        let mut row : Array Pattern := #[]
        for (p, i) in pats.zip (List.range arity) do
          match (if places.contains i then byRef? p else none) with
          | some (_, p) => row := row.push (← shapeOf rn [] p).1
          | none => row := row.push (if places.contains i then Pattern.wild else p)
        rows := rows.push (.mk row.toList [])
      pure [Stmt.expr (.call 0 (.name none "%shapes")
        ((outer.zip (List.range arity)).map (fun (x, i) =>
          if places.contains i then Expr.deref (.name none x) else Expr.name none x)
          ++ [.closure 0 rows.toList]))]
    else pure []
  if byTest then
    inner := inner.push (.mk (List.replicate arity Pattern.wild)
      [.expr (.tailCall 0 (.name none "%never") [])])
  let args := (outer.zip (List.range arity)).map fun (x, i) =>
    if !places.contains i then Expr.name none x
    else if byTest then
      .tuple (((asked.lookup i).getD []).map fun (path, ctor) =>
        .call 0 (.name none ctorIsMark)
          ([Expr.name none x] ++ path.map (fun (n : Nat) => Expr.int (n : Int)) ++ [ctor]))
    else Expr.deref (.name none x)
  pure [.mk (outer.map Pattern.var) (shapes ++ [.expr (.call 0 (.closure 0 inner.toList) args)])]

end Glorious.Syntax
