import Std.Data.HashMap
import Std.Data.HashSet
import Glorious.Syntax.Ast
import Glorious.Core.Ast

/-!
# Elaboration: surface syntax to Core

Resolves names, converts closures to closed functions with explicit captures,
names every intermediate result, and lowers handler arms and label scopes to
the Core forms. This pass is not proved; Core is where meaning starts.

Braces are always callables, and a clause takes exactly one argument. One
rule is directed by types, which the checker supplies: a block written without
parameters takes an argument if one is expected of it, and if that argument is
a block that was not run, it runs in that block's environment (`elabGiven`).
-/

namespace Glorious.Elab

open Syntax

structure CtorInfo where
  owner : String
  tag : Nat
  arity : Nat
  /-- The only constructor of its type, so matching it cannot fail. -/
  single : Bool

structure OpInfo where
  owner : String
  id : Nat
  arity : Nat
  terminal : Bool

/-- A place where a function a program declares as a coercion can be applied
without being written: an argument of a call, or the result of a clause of a
callable literal or of a top-level function. -/
inductive Site where
  | arg (call index : Nat)
  | result (closure clause : Nat)
  | fnResult (fn : String) (clause : Nat)
  deriving BEq

/-- How a trait bound is met, for the elaborator: by the `k`-th of the bounds
the function being elaborated is given, or by an implementation, named by the
function that makes it a value, given how each of its conditions is met. -/
inductive DictE where
  | param (k : Nat)
  | impl (fn : String) (subs : List DictE)
  deriving Inhabited

/-- An implementation of a trait: the function that makes it a value, how many
conditions it has, and the function for each of the trait's, in the trait's
order, with how many arguments it takes. -/
structure ImplE where
  dictFn : String
  conditions : Nat
  methods : List (String × Nat)

/-- The name a `_` has where what it takes is destroyed: its number among
the `_` of its clause's patterns, read in order. -/
def wildName (k : Nat) : String := s!"%wild{k}"

/-- The name the value of a statement has where it is destroyed. -/
def stmtValue : String := "%stmt"

/-- A place where what a variable holds is destroyed: where the variable is
declared, for the end of its block, or where it is assigned, for what it held. -/
structure DropSite where
  owner : String
  line : Nat
  col : Nat
  name : String
  assign : Bool
  deriving BEq

/-- The identity given to the calls of `Drop`'s function that the compiler
writes, so that the borrow each passes is not taken for one the program wrote. -/
def dropCallId : Nat := 4000000000

/-- How the values of a type are destroyed: the type, how many things its
function is given beside the value (how each type parameter is destroyed, and
what the type's `Drop` asks), how its own `Drop` is found if it has one,
whether it is the type of arrays, and for each constructor (the empty name for
a tuple) how each field is destroyed, none for a field with nothing to do. -/
structure Destroy where
  head : String
  given : Nat
  hook : Option DictE
  array : Bool
  ctors : List (String × List (Option DictE))

/-- What the checker tells the elaborator about a program's traits. -/
structure TraitInfo where
  /-- For a call, by its identity: how the bounds it needs are met. -/
  dicts : List (Nat × List DictE) := []
  /-- The calls of a trait's function, each with which of the trait's it is. -/
  methods : List (Nat × Nat) := []
  /-- The functions that need bounds of their type parameters, and how many. -/
  bounded : List (String × Nat) := []
  impls : List ImplE := []
  /-- Where a value is destroyed, each with the identity under which `dicts`
  says how its type is. -/
  drops : List (DropSite × Nat) := []
  /-- How each type is destroyed. -/
  destroys : List Destroy := []

/-- The function that makes an implementation a value. -/
def implDictName (trait head : String) : String := s!"impl {trait} for {head}"

/-- What the checker tells the elaborator about the blocks of a program, each
named by its identity. -/
structure Blocks where
  /-- Blocks written without parameters where a callable taking one argument is
  expected: they take the argument without naming it. -/
  given : List Nat := []
  /-- Those of them whose argument is a block that was not run: each with the
  identity of that block, whose environment it can take over. -/
  links : List (Nat × Nat) := []
  /-- The coercions to apply, each with the place it is applied at. -/
  coercions : List (Site × String) := []
  traits : TraitInfo := {}
  /-- For each borrow of a field, what is gone through to reach the field: at
  each step the constructor, or none for a tuple, and how many fields it has. -/
  fields : List (Nat × Bool × List Nat × List (Option String × Nat)) := []
  /-- For each field read by name, which field it is. -/
  fieldReads : List (Nat × Nat) := []
  /-- The blocks given what an `is` found, each with the names it then has. -/
  packs : List (Nat × List String) := []
  /-- For a function whose callables share an environment: each group of
  them by name, the first the one that holds it. -/
  envFns : List (String × List (List String)) := []
  /-- Calls that give a name where such a callable is wanted, and where. -/
  envWraps : List (Nat × List Nat) := []
  /-- The fields read by name of what a named reference points to. -/
  derefReads : List Nat := []

structure Globals where
  ctors : List (String × CtorInfo) := []
  ops : List (String × OpInfo) := []
  fns : List (String × Nat) := []
  aliases : List (String × Expr) := []
  /-- The clauses of each top-level function, by name. -/
  bodies : List (String × List Clause) := []
  /-- The prelude's type of arrays, its function that adds an element, and
  the trait of `a[i]`, by the names they have in this program. -/
  arrays : Option (String × String × String) := none
  /-- What the checker learnt about the program's blocks, if it was run. -/
  blocks : Option Blocks := none
  /-- How each place a borrow is written, counted in the order they are
  elaborated, is made a scope of its own in Core. `0`: it is not; the borrow is
  the reference it borrows. For a call of a function with borrows as arguments,
  `1`: each is a scope that lasts as long as the call; `2`: each is a scope
  that lasts while what the call gave is used. For `let p = &x`, `1`: a scope
  that lasts while `p` is mentioned; `2`: while `p` or anything made from it
  is. -/
  lends : Nat → Nat := fun _ => 0

/-- A borrow written in the source: where, of which variable, and whether for
writing. -/
structure Borrow where
  owner : String
  line : Nat
  col : Nat
  name : String
  uniq : Bool
  deriving BEq, Repr

def Borrow.show (b : Borrow) : String :=
  s!"{b.line}:{b.col}: in `{b.owner}`: `{if b.uniq then "&mut " else "&"}{b.name}`"

/-- Machine intrinsics by surface name, with their argument counts. -/
def prims : List (String × Prim × Nat) :=
  [("int_add", .intAdd, 2), ("int_sub", .intSub, 2), ("int_mul", .intMul, 2),
   ("int_lt", .intLt, 2), ("int_eq", .intEq, 2),
   ("int_div", .intDiv, 2), ("int_rem", .intRem, 2), ("int_fit", .intFit, 2),
   ("f64_add", .f64Add, 2), ("f64_sub", .f64Sub, 2), ("f64_mul", .f64Mul, 2),
   ("f64_div", .f64Div, 2), ("f64_lt", .f64Lt, 2), ("f64_eq", .f64Eq, 2),
   ("f64_of_int", .f64OfInt, 2), ("f64_to_int", .f64ToInt, 2),
   ("f64_narrow", .f64Narrow, 2), ("f64_widen", .f64Widen, 2),
   ("f64_of_decimal", .f64OfDecimal, 2), ("f64_digits", .f64Digits, 2),
   ("f64_exp10", .f64Exp10, 2), ("f64_sqrt", .f64Sqrt, 2), ("f64_round", .f64Round, 2),
   ("wide_add", .wideAdd, 2), ("wide_sub", .wideSub, 2), ("wide_mul", .wideMul, 2),
   ("int_and", .intAnd, 2), ("int_or", .intOr, 2), ("int_xor", .intXor, 2),
   ("int_shl", .intShl, 2), ("int_shr", .intShr, 2),
   ("uw_add", .uwAdd, 2), ("uw_sub", .uwSub, 2), ("uw_mul", .uwMul, 2),
   ("uw_div", .uwDiv, 2), ("uw_rem", .uwRem, 2), ("uw_lt", .uwLt, 2),
   ("uw_shl", .uwShl, 2), ("uw_shr", .uwShr, 2), ("int_below", .intBelow, 2),
   -- Arrays. `arr_new` is not an intrinsic of the machines: it is the array of
   -- no elements, built like any value.
   ("arr_get", .arrGet, 2), ("arr_set", .arrSet, 3), ("arr_len", .arrLen, 2),
   ("arr_push", .arrPush, 2), ("arr_pop", .arrPop, 2), ("arr_new", .arrLen, 0),
   -- The reference to a place of an array, from a reference to the array:
   -- not an intrinsic of the machines either, but an operation on memory.
   ("arr_at", .arrLen, 2),
   -- How many elements the array a reference points to has: the cell is
   -- asked, and nothing is read out of it.
   ("arr_len_at", .arrLen, 1)]

/-- The names that take a scalar to the integer it is held as, and back. -/
def casts : List String :=
  Syntax.scalars.flatMap fun (t, _) => [t ++ "_of", t ++ "_bits"]

/-- Host operations by surface name: their identity and argument count. -/
def hosts : List (String × Nat × Nat) :=
  [("host_write", 0, 1), ("host_read", 1, 0),
   -- Unsafe: the bits at an address, read and written, so many of them.
   ("ptr_read", 3, 2), ("ptr_write", 4, 3),
   -- Unsafe: an address C can call, which runs a callable of so many whole
   -- numbers, at most five, that gives one.
   ("c_callback", 5, 2)]

/-- The Core computation under construction: binding forms awaiting their
continuation, the number of locals so far, and the terminator once one is known. -/
structure Builder where
  ops : Array (Core.Tm → Core.Tm)
  depth : Nat
  done : Option Core.Tm
  /-- The locals that hold a callable literal: its function and what it captured. -/
  literals : List (Nat × Nat × List Atom) := []
  /-- Those of them no name has referred to yet. -/
  unused : List Nat := []
  /-- Which activation this is, among those elaborated so far. -/
  uid : Nat := 0
  /-- Locals of this activation that stand for a local of an activation around
  it, because a block that runs in another's place took them from what the
  other captured: each such activation and the local there, nearest first. -/
  origins : List (Atom × List (Nat × Atom)) := []

structure St where
  fns : Array Core.Fn
  /-- A description of each function, for diagnostics. -/
  names : Array String
  /-- The top-level function being elaborated. -/
  owner : String
  b : Builder
  /-- Why a `tail` call is not allowed at this point, if it is not: something
  still has to happen in this activation after the call returns. -/
  noTail : Option String
  /-- How many activations have been started. -/
  activations : Nat := 0
  /-- What each callable literal captured, by its identity: the activation it
  was built in, and each captured name with the local it stood for there. -/
  layouts : List (Nat × Nat × List (String × Atom × List (Nat × Atom))) := []
  /-- Functions that are only ever given the environment of another, with how
  many values that environment has and how many arguments the other took. -/
  envSizes : List (Nat × Nat × Nat) := []
  /-- How many borrows were made scopes of their own. -/
  lent : Nat := 0
  /-- How many places a borrow could be made a scope there were. -/
  sites : Nat := 0
  /-- How many of the next `let p = &x` are scopes that last while anything
  made from `p` is used, whatever `lends` says: they were written by the
  elaborator for the arguments of a call, and are not places of their own. -/
  hoisted : Nat := 0
  /-- Where the statement being elaborated starts. -/
  pos : Nat × Nat := (0, 0)
  /-- The borrows that are not scopes of their own: each is the reference it
  borrows. -/
  plain : List Borrow := []
  /-- Does the program call a foreign function, or read or write memory at an
  address? -/
  foreign : Bool := false

abbrev M := ReaderT Globals (StateT St (Except String))

instance {α : Type} : Inhabited (M α) := ⟨throw "elaborator: unreachable"⟩

/-- The local names in scope and where their values live. -/
abbrev Scope := List (String × Atom)

/-- Append a binding form; its result is the next local. -/
def emit (op : Core.Tm → Core.Tm) : M Atom := do
  let s ← get
  match s.b.done with
  | some _ => pure (.int 0)
  | none =>
    set { s with b := { s.b with ops := s.b.ops.push op, depth := s.b.depth + 1 } }
    pure (.var s.b.depth)

/-- End the computation with a form that does not return; later code is unreachable. -/
def terminate (t : Core.Tm) : M Unit :=
  modify fun s =>
    match s.b.done with
    | some _ => s
    | none => { s with b := { s.b with done := some t } }

def finish (result : Atom) : M Core.Tm := do
  let s ← get
  pure (s.b.ops.foldr (fun op k => op k) (s.b.done.getD (.ret result)))

/-- Build a computation whose locals start at `depth`, then restore the outer one. -/
def withBuilder {α : Type} (depth : Nat) (k : M α) : M α := do
  let outer := (← get).b
  modify fun s =>
    { s with
      b := { ops := #[], depth := depth, done := none, uid := s.activations + 1 }
      activations := s.activations + 1 }
  let r ← k
  modify fun s => { s with b := outer }
  pure r

/-- Run `k` with `tail` calls allowed or forbidden, then restore the setting. -/
def withNoTail {α : Type} (why : Option String) (k : M α) : M α := do
  let outer := (← get).noTail
  modify fun s => { s with noTail := why }
  let r ← k
  modify fun s => { s with noTail := outer }
  pure r

/--
The value of a local as a name refers to it. A local that holds a callable
literal is used as it is the first time, and built again from the same function
and captures each time after: each use of the name is then a value of its own.
The name can be used at several types, as the checker allows for a `let` of a
callable literal, while each Core value keeps a single type; and a literal
named and used once is built once, so that what it captured is moved once.
-/
def useLocal (a : Atom) : M Atom := do
  match a with
  | .var i =>
    let b := (← get).b
    if b.unused.contains i then
      modify fun s => { s with b := { s.b with unused := s.b.unused.erase i } }
      pure a
    else
      match b.literals.lookup i with
      | some (idx, captures) => emit (.let_ (.closure idx captures))
      | none => pure a
  | .int _ => pure a

def addFn (f : Core.Fn) (name : String) : M Nat := do
  modifyGet fun s => (s.fns.size, { s with fns := s.fns.push f, names := s.names.push name })

private def indexed (names : List String) (base : Nat) : Scope :=
  (names.zip (List.range names.length)).map fun (x, k) => (x, .var (base + k))

private def labelName (l : String) : String := "@" ++ l

/-- A mutable variable `x` is in scope under this key, bound to its cell. -/
private def cellKey (x : String) : String := "&" ++ x

/-- The nearest binding of `x`: whether it is a mutable variable, the key it is
in scope under, and its value or cell. -/
private def lookupVar (scope : Scope) (x : String) : Option (Bool × String × Atom) :=
  scope.findSome? fun (k, a) =>
    if k == x then some (false, k, a)
    else if k == cellKey x then some (true, k, a)
    else none

/-- The scope keys a callable must capture for the names free in it. -/
private def captureNames (scope : Scope) (free : List String) : List String :=
  (free.filterMap fun x => (lookupVar scope x).map (·.2.1)).eraseDups

private def sameAtom : Atom → Atom → Bool
  | .var i, .var j => i == j
  | .int m, .int n => m == n
  | _, _ => false

/-! ## Free names -/

partial def patVars : Pattern → List String
  | .wild => []
  | .var x => [x]
  | .int _ => []
  | .ctor _ _ args => args.flatMap patVars
  | .tuple args => args.flatMap patVars

mutual

partial def fvExpr (bound : List String) : Expr → List String
  | .int _ => []
  | .name qual x => if qual.isNone && !bound.contains x then [x] else []
  | .label l => if bound.contains (labelName l) then [] else [labelName l]
  | .call _ f args => fvExpr bound f ++ args.flatMap (fvExpr bound)
  | .tailCall _ f args => fvExpr bound f ++ args.flatMap (fvExpr bound)
  | .tuple args => args.flatMap (fvExpr bound)
  | .proj e _ => fvExpr bound e
  | .closure _ clauses => clauses.flatMap (fvClause bound)
  | .handle subject arms => fvExpr bound subject ++ arms.flatMap (fvClause bound)
  | .labelScope l body => fvStmts (labelName l :: bound) body
  | .ref _ x => if bound.contains x then [] else [x]
  | .deref e => fvExpr bound e
  | .reborrow _ e => fvExpr bound e
  | .refField _ _ x _ _ => if bound.contains x then [] else [x]
  | .fieldOf _ e _ => fvExpr bound e

partial def fvClause (bound : List String) : Clause → List String
  | .mk pats body => fvStmts (pats.flatMap patVars ++ bound) body

partial def fvStmts (bound : List String) : List Stmt → List String
  | [] => []
  | .let_ pat value :: rest => fvExpr bound value ++ fvStmts (patVars pat ++ bound) rest
  | .expr e :: rest => fvExpr bound e ++ fvStmts bound rest
  | .defer e :: rest => fvExpr bound e ++ fvStmts bound rest
  | .located _ _ s :: rest => fvStmts bound (s :: rest)
  | .letMut x value :: rest => fvExpr bound value ++ fvStmts (x :: bound) rest
  | .assign target value :: rest =>
    fvExpr bound target ++ fvExpr bound value ++ fvStmts bound rest

end

mutual

/-- The names an expression hands on with `move name`, wherever in it. -/
partial def movedExpr : Expr → List String
  | .call _ (.name none mark) [.name none x] =>
    if mark == Syntax.moveMark then [x] else []
  | .call _ f args => movedExpr f ++ args.flatMap movedExpr
  | .tailCall _ f args => movedExpr f ++ args.flatMap movedExpr
  | .tuple args => args.flatMap movedExpr
  | .proj e _ => movedExpr e
  | .closure _ clauses => clauses.flatMap fun
    | .mk _ body => body.flatMap movedStmt
  | .handle subject arms => movedExpr subject ++ arms.flatMap fun
    | .mk _ body => body.flatMap movedStmt
  | .labelScope _ body => body.flatMap movedStmt
  | .deref e => movedExpr e
  | .reborrow _ e => movedExpr e
  | .fieldOf _ e _ => movedExpr e
  | _ => []

partial def movedStmt : Stmt → List String
  | .let_ _ value => movedExpr value
  | .expr e => movedExpr e
  | .defer e => movedExpr e
  | .located _ _ s => movedStmt s
  | .letMut _ value => movedExpr value
  | .assign target value => movedExpr target ++ movedExpr value

end

/-- Where a body starts: the place of its first statement, by which what
its clause is given is known. -/
def firstPlace : List Stmt → Nat × Nat
  | .located line col _ :: _ => (line, col)
  | _ => (0, 0)

/-! ## How long a borrow lasts -/

partial def unlocated : Stmt → Stmt
  | .located _ _ s => unlocated s
  | s => s

/-- The names a statement gives values that may hold what `tracked` names hold. -/
private def madeFrom (tracked : List String) (s : Stmt) : List String :=
  match unlocated s with
  | .let_ pat value => if (fvExpr [] value).any tracked.contains then patVars pat else []
  | .letMut y value => if (fvExpr [] value).any tracked.contains then [y] else []
  | .assign (.name none y) value => if (fvExpr [] value).any tracked.contains then [y] else []
  | _ => []

/--
How many of the statements after `let p = &x` the borrow's scope takes in: up
to the last that mentions `p`, and with `wide`, anything made from `p`. A
mutable variable declared inside the scope ends with it, so the scope also
takes in every statement that mentions one; and a `defer` inside it would run
when the scope ends, so a scope that has one takes in the whole block.
-/
partial def scopeExtent (p : String) (rest : List Stmt) (wide : Bool) : Nat :=
  go [p] 0
where
  go (tracked : List String) (k : Nat) : Nat :=
    let inner := (rest.take k).map unlocated
    let defers := inner.any fun
      | .defer _ => true
      | _ => false
    if defers then rest.length
    else
      let muts := inner.filterMap fun
        | .letMut y _ => some y
        | _ => none
      let made :=
        if wide then inner.foldl (fun acc s => acc ++ madeFrom acc s) tracked else tracked
      let tracked' := (made ++ muts).eraseDups
      let k' := ((List.range (rest.length + 1)).drop k).find? fun j =>
        !(fvStmts [] (rest.drop j)).any tracked'.contains
      let k' := k'.getD rest.length
      if k' == k && tracked'.length == tracked.length then k else go tracked' k'

/-- The statements of a block with each `let p = &x` moved to just before the
first statement that mentions `p`. Making a reference does nothing, and the
later it is made the less its scope has to take in: two borrows that overlapped
need not, and a `defer` between a borrow and its use is no longer inside the
borrow's scope. One that nothing mentions, or that would pass a statement
giving `p` or `x` another meaning, stays. Doing this twice changes nothing. -/
partial def sinkBorrows (stmts : List Stmt) : List Stmt :=
  let arr := stmts.toArray
  -- Where each statement is to go: before the statement at this index.
  let target := fun (i : Nat) =>
    match arr[i]?.map unlocated with
    | some (.let_ (.var p) (.ref _ x)) =>
      let later := (List.range arr.size).drop (i + 1)
      match later.find? fun j => (fvStmts [] [arr.getD j (.expr (.tuple []))]).contains p with
      | none => none
      | some j =>
        let between := (later.takeWhile (· < j)).map fun k => unlocated (arr.getD k (.expr (.tuple [])))
        let rebinds := between.any fun
          | .let_ pat _ => (patVars pat).contains p || (patVars pat).contains x
          | .letMut y _ => y == p || y == x
          | _ => false
        if rebinds || j == i + 1 then none else some j
    | _ => none
  let targets := (List.range arr.size).map target
  if targets.all Option.isNone then stmts
  else
    -- The statements moved to before `j`, each after those moved to before it.
    let rec before (j : Nat) : List Stmt :=
      (List.range j).flatMap fun i =>
        if targets.getD i none == some j then before i ++ [arr.getD i (.expr (.tuple []))] else []
    (List.range arr.size).flatMap fun j =>
      if (targets.getD j none).isSome then [] else before j ++ [arr.getD j (.expr (.tuple []))]

/-- A statement that ends in a call some of whose arguments mention `p` and are
followed by arguments that do not: those up to the last that does, each given a
name, and the statement with the names in their place. -/
private def splitCallOn (p : String) (site : Nat) (s : Stmt) : Option (List Stmt × Stmt) :=
  let split := fun (e : Expr) =>
    match e with
    | .call id (.name q g) args =>
      if g == p then none
      else
        let last := (List.range args.length).reverse.find? fun i =>
          (fvExpr [] (args.getD i (.int 0))).contains p
        match last with
        | none => none
        | some j =>
          if j + 1 == args.length then none
          else
            let named : List (Expr × Option (String × Expr)) :=
              (args.zip (List.range args.length)).map fun (a, i) =>
                let plain := match a with
                  | Expr.name _ _ => true
                  | Expr.int _ => true
                  | _ => false
                if i ≤ j && !plain then
                  (Expr.name none s!"%part{site}.{i}", some (s!"%part{site}.{i}", a))
                else (a, none)
            -- An argument that is `p` itself would still be mentioned.
            if (named.take (j + 1)).any fun (x : Expr × Option (String × Expr)) =>
                (fvExpr [] x.1).contains p then none
            else
              let lets : List Stmt := named.filterMap fun (x : Expr × Option (String × Expr)) =>
                x.2.map fun (na : String × Expr) => Stmt.let_ (.var na.1) na.2
              some (lets, Expr.call id (.name q g) (named.map fun (x : Expr × Option (String × Expr)) => x.1))
    | _ => none
  let rec go (s : Stmt) : Option (List Stmt × Stmt) :=
    match s with
    | .located line col s => (go s).map fun (lets, last) => (lets, .located line col last)
    | .expr e => (split e).map fun (lets, e) => (lets, .expr e)
    | .let_ pat e => (split e).map fun (lets, e) => (lets, .let_ pat e)
    | .assign target e =>
      if (fvExpr [] target).contains p then none
      else (split e).map fun (lets, e) => (lets, .assign target e)
    | _ => none
  go s

/-- The names the statements of a block bind with `let`. -/
private def letNames (ss : List Stmt) : List String :=
  ss.flatMap fun s =>
    match unlocated s with
    | .let_ pat _ => patVars pat
    | _ => []

/-! ## What a function gives a callable it is passed -/

mutual

/-- With how many arguments the name `p` is applied, at each place it is. -/
partial def appliedExpr (p : String) : Expr → List Nat
  | .int _ => []
  | .name _ _ => []
  | .label _ => []
  | .call _ f args => appliedCall p f args
  | .tailCall _ f args => appliedCall p f args
  | .tuple args => args.flatMap (appliedExpr p)
  | .proj e _ => appliedExpr p e
  | .closure _ clauses => clauses.flatMap (appliedClause p)
  | .handle subject arms => appliedExpr p subject ++ arms.flatMap (appliedClause p)
  | .labelScope _ body => appliedStmts p body
  | .ref _ _ => []
  | .deref e => appliedExpr p e
  | .reborrow _ e => appliedExpr p e
  | .refField _ _ _ _ _ => []
  | .fieldOf _ e _ => appliedExpr p e

partial def appliedCall (p : String) (f : Expr) (args : List Expr) : List Nat :=
  let here := match f with
    | .name none x => if x == p then [args.length] else []
    | _ => appliedExpr p f
  here ++ args.flatMap (appliedExpr p)

partial def appliedClause (p : String) : Clause → List Nat
  | .mk pats body => if (pats.flatMap patVars).contains p then [] else appliedStmts p body

partial def appliedStmts (p : String) : List Stmt → List Nat
  | [] => []
  | .let_ pat value :: rest =>
    appliedExpr p value ++ (if (patVars pat).contains p then [] else appliedStmts p rest)
  | .expr e :: rest => appliedExpr p e ++ appliedStmts p rest
  | .defer e :: rest => appliedExpr p e ++ appliedStmts p rest
  | .located _ _ s :: rest => appliedStmts p (s :: rest)
  | .letMut x value :: rest =>
    appliedExpr p value ++ (if x == p then [] else appliedStmts p rest)
  | .assign target value :: rest =>
    appliedExpr p target ++ appliedExpr p value ++ appliedStmts p rest

end

/--
Does a function give the callable passed as its `i`-th argument exactly one
argument, wherever it applies it? Whether a block written without parameters
takes an argument is decided by the type expected of it, which the checker
knows. A program the checker rejects can still be elaborated, to be run and
seen to go wrong; there are no types then, and this reading of the function's
definition stands in for them.
-/
def givesOne (clauses : List Clause) (i : Nat) : Bool :=
  !clauses.isEmpty && clauses.all fun
    | .mk pats body =>
      match pats[i]? with
      | some (.var p) =>
        let counts := appliedStmts p body
        !counts.isEmpty && counts.all (· == 1)
      | _ => false

/-- A block written in braces, without parameters. -/
def plainBlock : Expr → Option (Nat × List Stmt)
  | .closure id [.mk [] body] => if id == 0 then none else some (id, body)
  | _ => none

/-! ## Coercions -/

/-- Apply `fn` to the value a body ends with. A body that ends with a statement,
or with a `tail` call, which must stay the last thing done, has no such value. -/
partial def wrapResult (fn : String) : List Stmt → Option (List Stmt)
  | [] => none
  | [.expr (.tailCall _ _ _)] => none
  | [.expr e] => some [.expr (.call 0 (.name none fn) [e])]
  | [.located line col s] => (wrapResult fn [s]).map fun ss => ss.map (.located line col)
  | [_] => none
  | s :: rest => (wrapResult fn rest).map (s :: ·)

mutual

/-- Write out the coercions the checker decided on, as the calls they are. -/
partial def coerceExpr (cs : List (Site × String)) : Expr → Expr
  | .call id f args => .call id (coerceExpr cs f) (coerceArgs cs id args)
  | .tailCall id f args => .tailCall id (coerceExpr cs f) (coerceArgs cs id args)
  | .tuple args => .tuple (args.map (coerceExpr cs))
  | .proj e idx => .proj (coerceExpr cs e) idx
  | .closure id clauses =>
    .closure id ((clauses.zip (List.range clauses.length)).map fun (c, j) =>
      coerceClause cs (cs.lookup (.result id j)) c)
  | .handle subject arms => .handle (coerceExpr cs subject) (arms.map (coerceClause cs none))
  | .labelScope l body => .labelScope l (coerceStmts cs body)
  | .deref e => .deref (coerceExpr cs e)
  | .reborrow uniq e => .reborrow uniq (coerceExpr cs e)
  | .fieldOf id e name => .fieldOf id (coerceExpr cs e) name
  | e => e

partial def coerceArgs (cs : List (Site × String)) (call : Nat) (args : List Expr) : List Expr :=
  (args.zip (List.range args.length)).map fun (a, i) =>
    let a := coerceExpr cs a
    match cs.lookup (.arg call i) with
    | some fn => .call 0 (.name none fn) [a]
    | none => a

partial def coerceClause (cs : List (Site × String)) (result : Option String) : Clause → Clause
  | .mk pats body =>
    let body := coerceStmts cs body
    .mk pats ((result.bind fun fn => wrapResult fn body).getD body)

partial def coerceStmts (cs : List (Site × String)) (body : List Stmt) : List Stmt :=
  body.map (coerceStmt cs)

partial def coerceStmt (cs : List (Site × String)) : Stmt → Stmt
  | .let_ pat value => .let_ pat (coerceExpr cs value)
  | .expr e => .expr (coerceExpr cs e)
  | .defer e => .defer (coerceExpr cs e)
  | .letMut x value => .letMut x (coerceExpr cs value)
  | .assign target value => .assign (coerceExpr cs target) (coerceExpr cs value)
  | .located line col s => .located line col (coerceStmt cs s)

end

/-- The clauses of a top-level function with its coercions written out. -/
def coerceFn (cs : List (Site × String)) (name : String) (clauses : List Clause) : List Clause :=
  if cs.isEmpty then clauses
  else (clauses.zip (List.range clauses.length)).map fun (c, j) =>
    coerceClause cs (cs.lookup (.fnResult name j)) c

/-! ## Names and patterns -/

/-- Resolve a name to a constructor, following constructor aliases. -/
partial def resolveCtor (name : String) (qual : Option String) : M (Option CtorInfo) := do
  let g ← read
  match g.ctors.lookup name with
  | some info =>
    match qual with
    | some q =>
      if q == info.owner then pure (some info)
      else throw s!"`{name}` is not a constructor of `{q}`"
    | none => pure (some info)
  | none =>
    -- `[a, b, c]` in a pattern: the constructor that builds an array of so
    -- many elements.
    if let some n := Syntax.arrayPatLen name then
      return some { owner := "", tag := arrayBase + n, arity := n, single := false }
    match g.aliases.lookup name with
    | some (.name q y) => resolveCtor y q
    | _ => pure none

/-- Does a bare name in a pattern bind a variable? -/
def isBinder (x : String) : M Bool := do
  if (← resolveCtor x none).isSome then return false
  return ((← read).aliases.lookup x).isNone

/-- Does this pattern match every value? Decided from its shape alone, as the
checker decides it. -/
partial def irrefutable : Pattern → M Bool
  | .wild => pure true
  | .int _ => pure false
  | .tuple ps => ps.allM irrefutable
  | .var x => isBinder x
  | .ctor _ _ _ => pure false

/-- Read a constant expression as a pattern. -/
partial def exprToPat : Expr → M Pattern
  | .int n => pure (.int n)
  | .name q x => pure (if q.isSome then .ctor x q [] else .var x)
  | .call _ (.name q x) args => do
    -- A constant written with its type is its value.
    if q.isNone && x == Syntax.ascribeMark then
      if let value :: _ := args then return ← exprToPat value
    pure (.ctor x q (← args.mapM exprToPat))
  | .tuple args => do
    pure (.tuple (← args.mapM exprToPat))
  | _ => throw "this constant cannot be used as a pattern"

mutual

/-- A Core pattern and the names it binds, in binder order. -/
partial def toCorePat : Pattern → M (Core.Pat × List String)
  | .wild => pure (.wild, [])
  | .int n => pure (.int n, [])
  | .tuple args => do
    let (ps, names) ← toCorePats args
    pure (.ctor 0 ps, names)
  | .var x => do
    match ← resolveCtor x none with
    | some info =>
      if info.arity == 0 then pure (.ctor info.tag [], [])
      else throw s!"constructor `{x}` takes {info.arity} arguments"
    | none =>
      match (← read).aliases.lookup x with
      | some e => do toCorePat (← exprToPat e)
      | none => pure (.bind, [x])
  | .ctor x q args => do
    -- A scalar is the integer it is held as.
    if let some (_, n) := Syntax.scalarPattern (.ctor x q args) then return (.int n, [])
    match ← resolveCtor x q with
    | some info =>
      if info.arity != args.length then
        throw s!"constructor `{x}` takes {info.arity} arguments, but the pattern has {args.length}"
      let (ps, names) ← toCorePats args
      pure (.ctor info.tag ps, names)
    | none => throw s!"unknown constructor `{x}` in a pattern"

partial def toCorePats : List Pattern → M (List Core.Pat × List String)
  | [] => pure ([], [])
  | p :: ps => do
    let (cp, names) ← toCorePat p
    let (cps, rest) ← toCorePats ps
    pure (cp :: cps, names ++ rest)

end

/-- What a name in an expression refers to. -/
inductive Head where
  | local (a : Atom)
  /-- A mutable variable: its cell. -/
  | cell (c : Atom)
  | fn (idx : Nat)
  | ctor (info : CtorInfo)
  | op (info : OpInfo)
  | prim (p : Prim) (arity : Nat)
  /-- A scalar as the integer it is held as, or back: nothing is done. -/
  | cast
  /-- What an `is` found: the values, together. -/
  | pack
  | host (id : Nat) (arity : Nat)
  | cancel
  | replace
  | const (e : Expr)

def resolveName (scope : Scope) (qual : Option String) (x : String) : M Head := do
  if qual.isNone then
    match lookupVar scope x with
    | some (false, _, a) => return .local a
    | some (true, _, c) => return .cell c
    | none => pure ()
  if let some info ← resolveCtor x qual then return .ctor info
  let g ← read
  if let some info := g.ops.lookup x then
    if let some q := qual then
      unless q == info.owner do throw s!"`{x}` is not an operation of `{q}`"
    return .op info
  if let some idx := g.fns.lookup x then return .fn idx
  if let some (p, n) := prims.lookup x then return .prim p n
  if (Syntax.scalarCast x).isSome then return .cast
  if (Syntax.packNames x).isSome then return .pack
  if let some (id, n) := hosts.lookup x then return .host id n
  if x == Syntax.foreignCall then return .host 2 0
  if x == "cancel" then return .cancel
  if x == "replace" then return .replace
  if let some e := g.aliases.lookup x then return .const e
  throw s!"unknown name `{x}`"

/-! ## Expressions -/

mutual

partial def elabExpr (scope : Scope) (tailPos : Bool) : Expr → M Atom
  | .int n =>
    -- What holds an integer holds 128 bits; a literal's own type was asked
    -- of it where it was read.
    if -170141183460469231731687303715884105728 ≤ n ∧ n ≤ 170141183460469231731687303715884105727
    then pure (.int n)
    else throw s!"integer literal `{n}` does not fit in 128 bits"
  | .name q x => do
    match ← resolveName scope q x with
    | .local a => useLocal a
    | .cell c => emit (.mem .load [c])
    | .fn idx => emit (.let_ (.closure idx []))
    | .ctor info =>
      if info.arity == 0 then emit (.let_ (.construct info.tag []))
      else throw s!"constructor `{x}` takes {info.arity} arguments"
    | .op _ => throw s!"operation `{x}` must be called"
    | .prim _ _ => throw s!"intrinsic `{x}` must be called"
    | .cast => throw s!"intrinsic `{x}` must be called"
    | .pack => throw "what an `is` found is built where it is found"
    | .host _ _ => throw s!"host operation `{x}` must be called"
    | .cancel => throw "`cancel` must be applied to a resumption"
    | .replace => throw "`replace` must be called"
    | .const e => elabExpr [] false e
  | .label l =>
    match scope.lookup (labelName l) with
    | some a => pure a
    | none => throw s!"unknown label `@{l}`"
  | .tuple args => do
    let atoms ← args.mapM (elabExpr scope false)
    emit (.let_ (.construct 0 atoms))
  | .proj e idx => do
    match ← elabExpr scope false e with
    | .var i => emit (.let_ (.place ⟨i, [idx]⟩))
    | .int _ => throw "an integer has no fields"
  | .call id f args => do
    -- A value written with its type is the value: the type was the checker's.
    if let (.name none mark, [value, _]) := (f, args) then
      if mark == Syntax.ascribeMark || mark == Syntax.instMark then
        return ← elabExpr scope tailPos value
    if let (.name none mark, [value]) := (f, args) then
      if mark == Syntax.moveMark then return ← elabExpr scope tailPos value
    let before := (← get).plain.length
    let r ← elabCall scope false f args
    -- The borrow a destruction passes is the compiler's, not the program's.
    if id == dropCallId then
      modify fun s => { s with plain := s.plain.drop (s.plain.length - before) }
    pure r
  | .tailCall _ f args => do
    unless tailPos do throw "`tail` call is not in tail position"
    if let some why := (← get).noTail then
      throw s!"`tail` cannot be used here: {why}"
    elabCall scope true f args
  | .closure id clauses => elabClosure scope clauses id
  | .handle subject arms => elabHandle scope tailPos subject arms
  | .labelScope l body => do
    let thunk ← elabClosure scope [.mk [.var (labelName l)] body]
    if tailPos then
      terminate (.labelTail thunk)
      pure (.int 0)
    else emit (.label thunk)
  | .ref uniq x =>
    match lookupVar scope x with
    | some (true, _, c) => do
      modify fun s => { s with plain := ⟨s.owner, s.pos.1, s.pos.2, x, uniq⟩ :: s.plain }
      pure c
    | some (false, _, _) => throw s!"`{x}` is not a mutable variable, so it cannot be borrowed"
    | none => throw s!"unknown name `{x}`"
  -- A reference borrowed from a reference is, to the machine, that reference.
  | .reborrow _ e => elabExpr scope false e
  | .refField _ _ x _ _ =>
    throw s!"a borrow of a field of `{x}` is elaborated only after the program is checked"
  | .fieldOf id e name =>
    -- A field by number needs no checker to be found.
    match name.toNat? with
    | some n => elabExpr scope tailPos (.proj e n)
    | none => throw s!"the field `{name}` is found by the checker: the program is elaborated only after it (read {id})"
  | .deref e => do
    let p ← elabExpr scope false e
    emit (.mem .load [p])

/-- The arguments of a call. A block written without parameters, where a
callable taking one argument is expected, takes that argument. -/
partial def elabArgs (scope : Scope) (args : List Expr) (gives : Nat → Bool := fun _ => false) :
    M (List Atom) := do
  let blocks := (← read).blocks
  (args.zip (List.range args.length)).mapM fun (a, i) =>
    match plainBlock a with
    | some (id, body) =>
      let given := match blocks with
        | some b => b.given.contains id
        | none => gives i
      if given then elabGiven scope id body else elabExpr scope false a
    | none => elabExpr scope false a

partial def elabApply (scope : Scope) (isTail : Bool) (callee : Atom) (args : List Expr)
    (gives : Nat → Bool := fun _ => false) : M Atom := do
  let atoms ← elabArgs scope args gives
  if isTail then
    terminate (.tail callee atoms)
    pure (.int 0)
  else emit (.call callee atoms)

/-- A call of function `idx` some of whose arguments are borrows: each borrow
is a scope that lasts as long as the call. The last borrow's scope is the call
itself, with the borrow among the arguments. The scope of one before it runs a
callable that captured the arguments and is given that borrow. -/
partial def lendCall (idx : Nat) (atoms : List Atom) : List (Nat × Bool) → M Atom
  | [] => do
    let callee ← emit (.let_ (.closure idx []))
    terminate (.tail callee atoms)
    pure (.int 0)
  | [(i, uniq)] => do
    let callee ← emit (.let_ (.closure idx []))
    modify fun s => { s with lent := s.lent + 1 }
    emit (.lend uniq (atoms[i]?.getD (.int 0)) callee (atoms.take i) (atoms.drop (i + 1)))
  | (i, uniq) :: rest => do
    let lentRef := atoms[i]?.getD (.int 0)
    let inner := (atoms.zip (List.range atoms.length)).map fun (a, j) =>
      if j == i then Atom.var 0
      else match a with
        | .int n => .int n
        | .var _ => .var (1 + j)
    let tm ← withBuilder (1 + atoms.length) do
      let r ← withNoTail none (lendCall idx inner rest)
      finish r
    let f ← addFn ⟨[⟨[.wild], tm⟩]⟩ s!"a borrow in `{(← get).owner}`"
    modify fun s => { s with lent := s.lent + 1 }
    let thunk ← emit (.let_ (.closure f atoms))
    emit (.lend uniq lentRef thunk [] [])

partial def elabCall (scope : Scope) (isTail : Bool) (f : Expr) (args : List Expr) : M Atom := do
  -- Whether what a reference points to was built by a constructor, at a
  -- path of field numbers: the cell is asked, and nothing is read out of it.
  -- What the clauses of a callable that binds by reference ask of the values:
  -- the checker's to read, and nothing to do.
  if let .name none "%shapes" := f then
    return ← emit (.let_ (.construct 0 []))
  if let (.name none mark, r :: rest) := (f, args) then
    -- A reference to a field of what a reference points to: the reference,
    -- one field further in at each step.
    if mark == Syntax.focusMark then
      let mut at_ ← elabExpr scope false r
      for step in rest do
        if let .int i := step then at_ ← emit (.mem .focus [at_, .int i])
      return at_
    if mark == Syntax.ctorIsMark then
      let cell ← elabExpr scope false r
      let path := rest.dropLast.filterMap fun
        | .int n => some (Atom.int n)
        | _ => none
      let tag ← match rest.getLast? with
        | some (.name q c) =>
          match ← resolveCtor c q with
          | some info => pure (info.tag : Int)
          | none => throw s!"`{c}` is not a constructor"
        | _ => throw "a test of a constructor names the constructor"
      let found ← emit (.mem .tag (cell :: path))
      return ← emit (.let_ (.prim .intEq [found, .int tag]))
  match f with
  | .name q x =>
    match ← resolveName scope q x with
    | .local a => do elabApply scope isTail (← useLocal a) args
    | .cell c => do
      let callee ← emit (.mem .load [c])
      elabApply scope isTail callee args
    | .fn idx => do
      let gives := givesOne (((← read).bodies.lookup x).getD [])
      let borrows := (args.zip (List.range args.length)).filterMap fun (a, i) =>
        match a with
        | .ref uniq _ => some (i, uniq)
        | _ => none
      let site := (← get).sites
      if !isTail && !borrows.isEmpty then modify fun s => { s with sites := s.sites + 1 }
      if !isTail && !borrows.isEmpty && (← read).lends site != 0 then
        let atoms ← elabArgs scope args gives
        -- These borrows are scopes: take back what elaborating them noted.
        for a in args do
          if let .ref uniq y := a then
            modify fun s =>
              { s with plain := s.plain.erase ⟨s.owner, s.pos.1, s.pos.2, y, uniq⟩ }
        if (← get).b.done.isSome then pure (.int 0) else lendCall idx atoms borrows
      else
        let callee ← emit (.let_ (.closure idx []))
        elabApply scope isTail callee args gives
    | .ctor info => do
      if isTail then throw s!"`tail` applies to calls, not to the constructor `{x}`"
      if info.arity != args.length then
        throw s!"constructor `{x}` takes {info.arity} arguments, but is given {args.length}"
      let atoms ← elabArgs scope args
      emit (.let_ (.construct info.tag atoms))
    | .op info => do
      if isTail then throw s!"`tail` applies to calls, not to the operation `{x}`"
      if info.arity != args.length then
        throw s!"operation `{x}` takes {info.arity} arguments, but is given {args.length}"
      let atoms ← elabArgs scope args
      if info.terminal then
        terminate (.raise info.id atoms)
        pure (.int 0)
      else emit (.perform info.id atoms)
    | .prim p n => do
      if isTail then throw s!"`tail` applies to calls, not to the intrinsic `{x}`"
      if n != args.length then
        throw s!"intrinsic `{x}` takes {n} arguments, but is given {args.length}"
      let atoms ← elabArgs scope args
      if x == "arr_new" then emit (.let_ (.construct arrayBase []))
      else if x == "arr_at" then
        -- The place is a local, so that it is plainly one found when the
        -- program runs, and not a field's number.
        match atoms with
        | [r, i] =>
          let at_ ← match i with
            | .int _ => emit (.let_ (.atom i))
            | _ => pure i
          emit (.mem .focus [r, at_])
        | _ => throw "intrinsic `arr_at` takes 2 arguments"
      else if x == "arr_len_at" then
        -- The constructor that builds an array of `n` elements is the first
        -- of them and `n`.
        let built ← emit (.mem .tag atoms)
        emit (.let_ (.prim .intSub [built, .int arrayBase]))
      else emit (.let_ (.prim p atoms))
    | .pack => do
      let atoms ← elabArgs scope args
      emit (.let_ (.construct 0 atoms))
    | .cast => do
      if isTail then throw s!"`tail` applies to calls, not to the intrinsic `{x}`"
      match ← elabArgs scope args with
      | [a] => emit (.let_ (.atom a))
      | _ => throw s!"intrinsic `{x}` takes 1 argument, but is given {args.length}"
    | .host id n => do
      if isTail then throw s!"`tail` applies to calls, not to the host operation `{x}`"
      if n != args.length && id != 2 then
        throw s!"host operation `{x}` takes {n} arguments, but is given {args.length}"
      let atoms ← elabArgs scope args
      -- What is unsafe is outside what Core's rules are about.
      if id ≥ 2 then modify fun s => { s with foreign := true }
      emit (.host id atoms)
    | .cancel => do
      if isTail then throw "`tail` applies to calls, not to `cancel`"
      match args with
      | [_] => do
        match ← elabArgs scope args with
        | [atom] => emit (.cancel atom)
        | _ => throw "`cancel` takes exactly one resumption"
      | _ => throw "`cancel` takes exactly one resumption"
    | .replace => do
      -- Take the value out of a cell and put another in its place.
      if isTail then throw "`tail` applies to calls, not to `replace`"
      match args with
      | [target, _] => do
        match ← elabArgs scope args with
        | [cell, new] =>
          -- Written on a variable this is an assignment that gives the old
          -- value back: the reference does not outlast it.
          if let .ref uniq y := target then
            modify fun s =>
              { s with plain := s.plain.erase ⟨s.owner, s.pos.1, s.pos.2, y, uniq⟩ }
          emit (.mem .swap [cell, new])
        | _ => throw "`replace` takes a reference and a value"
      | _ => throw "`replace` takes a reference and a value"
    | .const e => do
      let callee ← elabExpr [] false e
      elabApply scope isTail callee args
  | _ => do
    let callee ← elabExpr scope false f
    elabApply scope isTail callee args

/-- Statements in sequence; the value is that of the last expression, or unit. -/
partial def elabStmts (scope : Scope) (tailPos : Bool) : List Stmt → M Atom
  | [] => emit (.let_ (.construct 0 []))
  | .located line col s :: rest => do
    -- A borrow given a name is made where it is first used.
    match sinkBorrows (.located line col s :: rest) with
    | .located line col s :: rest =>
      modify fun st => { st with pos := (line, col) }
      try elabStmts scope tailPos (s :: rest)
      catch e => throw (positioned line col e)
    | other => elabStmts scope tailPos other
  -- Where `unsafe { .. }` begins: nothing to do.
  | [.expr (.name none "%unsafe")] => emit (.let_ (.construct 0 []))
  | .expr (.name none "%unsafe") :: rest => elabStmts scope tailPos rest
  | [.expr e] => elabExpr scope tailPos e
  | .expr e :: rest => do
    let _ ← elabExpr scope false e
    elabStmts scope tailPos rest
  | .let_ pat value :: rest => do
    -- A borrow given a name can be a scope of its own.
    if let (.var p, .ref uniq x) := (pat, value) then
      if let some (true, _, c) := lookupVar scope x then
        if ← isBinder p then
          if (← get).hoisted != 0 then
            modify fun s => { s with hoisted := s.hoisted - 1 }
            return ← elabBorrowScope scope tailPos p uniq c rest true
          let site := (← get).sites
          modify fun s => { s with sites := s.sites + 1 }
          let mode := (← read).lends site
          if mode != 0 then
            return ← elabBorrowScope scope tailPos p uniq c rest (mode == 2)
    -- So can the borrows given to a function whose result is given a name,
    -- lasting while the result is used: each is named first.
    if let .call id (.name q f) args := value then
      let borrows := args.filter fun
        | .ref _ _ => true
        | _ => false
      if !borrows.isEmpty && (← read).lends (← get).sites == 2 then
        if let .fn _ ← resolveName scope q f then
          let site := (← get).sites
          let named := (args.zip (List.range args.length)).map fun (a, i) =>
            match a with
            | .ref uniq y => (Expr.name none s!"%borrow{site}.{i}", some (uniq, y, i))
            | _ => (a, none)
          let lets := named.filterMap fun (_, b) =>
            b.map fun (uniq, y, i) => Stmt.let_ (.var s!"%borrow{site}.{i}") (.ref uniq y)
          modify fun s => { s with sites := s.sites + 1, hoisted := s.hoisted + lets.length }
          return ← elabStmts scope tailPos
            (lets ++ .let_ pat (.call id (.name q f) (named.map (·.1))) :: rest)
    -- And the borrows put straight into a tuple or a constructor that is given
    -- a name, lasting while it is used.
    let (value', found) ← nameBorrows scope (← get).sites value
    if !found.isEmpty then
      let site := (← get).sites
      modify fun s => { s with sites := s.sites + 1 }
      if (← read).lends site != 0 then
        let lets := found.map fun (n, uniq, y) => Stmt.let_ (.var n) (.ref uniq y)
        modify fun s => { s with hoisted := s.hoisted + lets.length }
        return ← elabStmts scope tailPos (lets ++ .let_ pat value' :: rest)
    let a ← elabExpr scope false value
    let scope ← bindLet scope pat a
    elabStmts scope tailPos rest
  | .letMut x value :: rest => do
    let a ← elabExpr scope false value
    -- The rest of the block runs in the scope of the variable's cell, which is
    -- released however the block is left. It is given the cell as its argument.
    -- A `tail` call written directly in it would leave the cell's scope behind
    -- on every iteration, so it is refused.
    let why := s!"`{x}` is released after the call returns"
    let captures := captureNames scope (fvStmts [x] rest)
    let body ← mkClause captures [.var (cellKey x)]
      (fun sc => withNoTail (some why) (elabStmts sc true rest))
    let idx ← addFn ⟨[body]⟩ s!"the scope of `{x}` in `{(← get).owner}`"
    let captured ← (captures.filterMap (fun y => scope.lookup y)).mapM useLocal
    let thunk ← emit (.let_ (.closure idx captured))
    if tailPos then
      terminate (.cellTail a thunk)
      pure (.int 0)
    else emit (.cell a thunk)
  | .assign target value :: rest => do
    let cell ← match target with
      | .name none x =>
        match lookupVar scope x with
        | some (true, _, c) => pure c
        | some (false, _, _) => throw s!"`{x}` is not a mutable variable"
        | none => throw s!"unknown name `{x}`"
      | .deref e => elabExpr scope false e
      | _ => throw "only a mutable variable or `*reference` can be assigned"
    -- `a[i] = v` and `a = push(a, v)`, of an array a variable holds: the
    -- array is taken out of the variable, an empty one left in its place,
    -- changed, and put back. Nothing else holds it meanwhile, so a machine
    -- that can change it where it is may.
    let inPlace : Option (Prim × List Expr) := match target, value, (← read).arrays with
      | .name none x, .call _ (.name none f) (.name none y :: more), some (array, push, index) =>
        if x == y && (lookupVar scope f).isNone then
          if f == push && more.length == 1 then some (.arrPush, more)
          else if f == Syntax.implFnName index array "index_set" && more.length == 2 then
            some (.arrSet, more)
          else none
        else none
      | _, _, _ => none
    match inPlace with
    | some (p, more) =>
      let atoms ← elabArgs scope more
      let empty ← emit (.let_ (.construct arrayBase []))
      let old ← emit (.mem .swap [cell, empty])
      let changed ← emit (.let_ (.prim p (old :: atoms)))
      let _ ← emit (.mem .store [cell, changed])
    | none =>
      let a ← elabExpr scope false value
      let _ ← emit (.mem .store [cell, a])
    elabStmts scope tailPos rest
  | .defer e :: rest => do
    -- The rest of the block runs under a guard whose cleanup is `e`.
    let cleanup ← elabClosure scope [.mk [] [.expr e]]
    elabGuarded scope tailPos cleanup rest "a `defer` runs after the call returns"

/-- An expression with each borrow written straight in a tuple or as an
argument of a constructor replaced by a name, and what each name is to be. -/
partial def nameBorrows (scope : Scope) (site : Nat) (e : Expr) :
    M (Expr × List (String × Bool × String)) := do
  let (e, found) ← go e []
  pure (e, found.reverse)
where
  go (e : Expr) (found : List (String × Bool × String)) :
      M (Expr × List (String × Bool × String)) := do
    match e with
    | .tuple args => do
      let (args, found) ← goArgs args found
      pure (.tuple args, found)
    | .call id (.name q f) args => do
      if (lookupVar scope f).isSome && q.isNone then return (e, found)
      match ← (resolveCtor f q) with
      | some _ =>
        let (args, found) ← goArgs args found
        pure (.call id (.name q f) args, found)
      | none => pure (e, found)
    | _ => pure (e, found)
  goArgs (args : List Expr) (found : List (String × Bool × String)) :
      M (List Expr × List (String × Bool × String)) := do
    let mut out : Array Expr := #[]
    let mut found := found
    for a in args do
      match a with
      | .ref uniq y =>
        if let some (true, _, _) := lookupVar scope y then
          let n := s!"%borrow{site}.{found.length}"
          out := out.push (.name none n)
          found := (n, uniq, y) :: found
        else out := out.push a
      | _ =>
        let (a', found') ← go a found
        out := out.push a'
        found := found'
    pure (out.toList, found)

/-- The scope of a borrow given a name: the statements it takes in run in a
callable that is given the borrow, and gives back what they bound that the
rest of the block uses. A `tail` call written directly in them would leave the
scope behind, so it is refused. -/
partial def elabBorrowScope (scope : Scope) (tailPos : Bool) (p : String) (uniq : Bool)
    (cell : Atom) (rest : List Stmt) (wide : Bool) : M Atom := do
  let k := scopeExtent p rest wide
  let inner := rest.take k
  let after := rest.drop k
  -- If the last statement of the scope is a call whose later arguments do not
  -- mention the borrow, the scope ends before them: the arguments up to the
  -- last that does are computed first and given names.
  let (inner, after) := match inner.getLast?.map (splitCallOn p (← get).sites) with
    | some (some (lets, last)) =>
      if wide then (inner, after) else (inner.dropLast ++ lets, last :: after)
    | _ => (inner, after)
  let used := fvStmts [] after
  let out := ((letNames inner).filter used.contains).eraseDups
  let (inner, pat) : List Stmt × Option Pattern :=
    if after.isEmpty then (inner, none)
    else match out with
      | [] => (inner ++ [.expr (.tuple [])], some .wild)
      | [n] => (inner ++ [.expr (.name none n)], some (.var n))
      | ns => (inner ++ [.expr (.tuple (ns.map (.name none)))], some (.tuple (ns.map .var)))
  let why := s!"the borrow `{p}` ends after the call returns"
  let captures := captureNames scope (fvStmts [p] inner)
  let body ← mkClause captures [.var p] (fun sc => withNoTail (some why) (elabStmts sc true inner))
  let idx ← addFn ⟨[body]⟩ s!"the scope of the borrow `{p}` in `{(← get).owner}`"
  let captured ← (captures.filterMap (fun y => scope.lookup y)).mapM useLocal
  let thunk ← emit (.let_ (.closure idx captured))
  modify fun s => { s with lent := s.lent + 1 }
  let r ← emit (.lend uniq cell thunk [] [])
  match pat with
  | none => pure r
  | some pat =>
    let scope ← bindLet scope pat r
    elabStmts scope tailPos after

/-- Run the rest of a block under a guard. A `tail` call written directly in
that rest would leave the guard behind on every iteration, so it is refused. -/
partial def elabGuarded (scope : Scope) (tailPos : Bool) (cleanup : Atom) (rest : List Stmt)
    (why : String) : M Atom := do
  let captures := captureNames scope (fvStmts [] rest)
  let body ← mkClause captures [] (fun sc => withNoTail (some why) (elabStmts sc true rest))
  let idx ← addFn ⟨[body]⟩ s!"a guarded block in `{(← get).owner}`"
  let captured ← (captures.filterMap (fun x => scope.lookup x)).mapM useLocal
  let thunk ← emit (.let_ (.closure idx captured))
  if tailPos then
    terminate (.guardTail cleanup thunk)
    pure (.int 0)
  else emit (.guard cleanup thunk)

/-- Bind an irrefutable pattern to a value. -/
partial def bindLet (scope : Scope) (pat : Pattern) (a : Atom) : M Scope := do
  match pat with
  | .wild => pure scope
  | .var x =>
    if ← isBinder x then pure ((x, a) :: scope)
    else throw s!"`{x}` is a constant; a `let` pattern must not be able to fail"
  | _ =>
    match a with
    | .var i => destructure scope pat i []
    | .int _ => throw "an integer cannot be destructured"

/-- Bind the variables of an irrefutable pattern to fields of local `i`. -/
partial def destructure (scope : Scope) (pat : Pattern) (i : Nat) (path : List Nat) : M Scope := do
  match pat with
  | .wild => pure scope
  | .int _ => throw "a `let` pattern must not be able to fail"
  | .var x =>
    if ← isBinder x then
      let a ← emit (.let_ (.place ⟨i, path⟩))
      pure ((x, a) :: scope)
    else throw s!"`{x}` is a constant; a `let` pattern must not be able to fail"
  | .tuple args => destructureAll scope args i path 0
  | .ctor x q args =>
    match ← resolveCtor x q with
    | some info =>
      if !info.single then
        throw s!"`{x}` is not the only constructor of `{info.owner}`; use a pattern callable"
      if info.arity != args.length then
        throw s!"constructor `{x}` takes {info.arity} arguments, but the pattern has {args.length}"
      destructureAll scope args i path 0
    | none => throw s!"unknown constructor `{x}` in a pattern"

partial def destructureAll (scope : Scope) (pats : List Pattern) (i : Nat) (path : List Nat)
    (k : Nat) : M Scope := do
  match pats with
  | [] => pure scope
  | p :: ps =>
    let scope ← destructure scope p i (path ++ [k])
    destructureAll scope ps i path (k + 1)

/--
One Core clause. Its body runs in `arguments ++ captures ++ pattern bindings`.
A parameter that is a plain variable is the argument itself.
-/
partial def mkClause (captures : List String) (pats : List Pattern) (body : Scope → M Atom) :
    M Core.Clause := do
  let mut corePats : Array Core.Pat := #[]
  let mut params : Scope := []
  let mut binders : List String := []
  let mut i := 0
  for p in pats do
    let simple ← match p with
      | .var x => isBinder x
      | _ => pure false
    match p, simple with
    | .var x, true =>
      corePats := corePats.push .wild
      params := (x, .var i) :: params
    | _, _ =>
      let (cp, names) ← toCorePat p
      corePats := corePats.push cp
      binders := binders ++ names
    i := i + 1
  let bindBase := pats.length + captures.length
  let scope := (indexed binders bindBase).reverse ++ params ++ indexed captures pats.length
  let tm ← withBuilder (bindBase + binders.length) do
    -- A callable's own body may end in a `tail` call, whatever surrounds it.
    let r ← withNoTail none (body scope)
    finish r
  pure ⟨corePats.toList, tm⟩

/-- A callable literal: a new closed function and a closure over its captures. -/
partial def elabClosure (scope : Scope) (clauses : List Clause) (id : Nat := 0) : M Atom := do
  let arities := clauses.map fun
    | .mk pats _ => pats.length
  match arities with
  | [] => throw "a callable needs at least one clause"
  | n :: rest =>
    unless rest.all (· == n) do
      throw "the clauses of a callable take different numbers of arguments"
  let captures := captureNames scope (clauses.flatMap (fvClause []))
  let coreClauses ← clauses.mapM fun
    | .mk pats body => mkClause captures pats (fun sc => elabStmts sc true body)
  let idx ← addFn ⟨coreClauses⟩ s!"a callable in `{(← get).owner}`"
  unless id == 0 do
    let origins := (← get).b.origins
    let layout := captures.filterMap fun x => (scope.lookup x).map fun a =>
      (x, a, ((origins.find? fun o => sameAtom o.1 a).map (·.2)).getD [])
    modify fun s => { s with layouts := (id, s.b.uid, layout) :: s.layouts }
  -- Capturing a name is a use of it, like any other.
  let captured ← (captures.filterMap (fun x => scope.lookup x)).mapM useLocal
  bindLiteral idx captured

/-- Build a closure and remember it as the literal it is. -/
partial def bindLiteral (idx : Nat) (captured : List Atom) : M Atom := do
  let a ← emit (.let_ (.closure idx captured))
  if let .var i := a then
    modify fun s =>
      { s with b := { s.b with literals := (i, idx, captured) :: s.b.literals, unused := i :: s.b.unused } }
  pure a

/--
A block that takes an argument it does not name. If the checker found the
argument to be another block of this activation that was not run, this block
runs in that one's environment: the names both mention are taken from what the
other captured, instead of being captured a second time. So the two are two
bodies over one environment, of which at most one runs, and a value that can be
used once can be used by each. Otherwise the argument is dropped.
-/
partial def elabGiven (scope : Scope) (id : Nat) (body : List Stmt) : M Atom := do
  let s ← get
  -- What the other block captured: each name with the local of this
  -- activation it stood for, if it was captured here or taken, in an
  -- activation inside this one, from what a block of this one captured.
  let layout : List (String × Option Atom) :=
    match ((← read).blocks.getD {}).links.lookup id with
    | some owner =>
      match s.layouts.lookup owner with
      | some (uid, layout) =>
        layout.map fun (y, a, origins) =>
          (y, if uid == s.b.uid then some a else (origins.find? (·.1 == s.b.uid)).map (·.2))
      | none => []
    | none => []
  -- A name is shared if it still stands for the local the other block captured.
  let shared := fun (x : String) (a : Option Atom) =>
    match a, scope.lookup x with
    | some a, some b => sameAtom a b
    | _, _ => false
  let free := captureNames scope (fvStmts [] body)
  let taken := free.filter fun x => layout.any fun (y, a) => x == y && shared y a
  if taken.isEmpty then elabClosure scope [.mk [.wild] body] id
  else
    let own := free.filter fun x => !taken.contains x
    -- The body, as a function over the other block's environment: what this
    -- block needs besides is passed to it.
    let slots := (layout.zip (List.range layout.length)).map fun ((y, a), k) =>
      if shared y a then y else s!"\x00{k}"
    let names := own ++ slots
    -- Inside it, a name taken from the other block still stands for the local
    -- it stood for here, and for whatever that stood for further out.
    let outer := s.b
    let origins := (slots.zip (List.range slots.length)).filterMap fun (y, k) =>
      match scope.lookup y with
      | some a =>
        if taken.contains y then
          some (Atom.var (own.length + k),
            (outer.uid, a) :: ((outer.origins.find? fun o => sameAtom o.1 a).map (·.2)).getD [])
        else none
      | none => none
    let tm ← withBuilder names.length do
      modify fun st => { st with b := { st.b with origins := origins } }
      let r ← withNoTail none (elabStmts (indexed names 0) true body)
      finish r
    let code ← addFn ⟨[⟨own.map fun _ => .wild, tm⟩]⟩ s!"a block in `{s.owner}`"
    -- The block given up took what it was given, if it was itself given
    -- something it did not name.
    let blocks := (← read).blocks.getD {}
    let arity := match blocks.links.lookup id with
      | some owner =>
        if blocks.given.contains owner
            || ((blocks.packs.lookup owner).map
                  (fun names => names != [Syntax.spreadMark] && names != [Syntax.nowMark])).getD false then 1
        else 0
      | none => 0
    modify fun s => { s with envSizes := (code, layout.length, arity) :: s.envSizes }
    -- The callable passed along: given the block that was not run, it runs the
    -- body in that block's place.
    let n := own.length
    let run : Core.Tm :=
      .let_ (.rebind (.var 0) code) (.tail (.var (n + 1)) ((List.range n).map fun k => .var (k + 1)))
    let idx ← addFn ⟨[⟨[.wild], run⟩]⟩ s!"a block in `{s.owner}`"
    let captured ← (own.filterMap (fun x => scope.lookup x)).mapM useLocal
    bindLiteral idx captured

/--
`handle subject { arms }`. The subject becomes a callable run under the handler.
Arms whose head names an operation serve that operation; the others are
completion clauses. An arm for a resumptive operation either binds the
resumption as an extra final pattern, or omits it and resumes with its value.
Unless one of an operation's arms matches every payload, its function ends with
a clause that performs the operation again outside the handler, so a payload no
arm matches is forwarded; the operation must then be handled outside as well.
In tail position the handler keeps no caller frame.
-/
partial def elabHandle (scope : Scope) (tailPos : Bool) (subject : Expr) (arms : List Clause) :
    M Atom := do
  let g ← read
  let thunk ← elabClosure scope [.mk [] [.expr subject]]
  let captures := captureNames scope (arms.flatMap (fvClause []))
  let mut completions : Array (Pattern × List Stmt) := #[]
  let mut opArms : Array (OpInfo × List Pattern × List Stmt) := #[]
  let mut opNames : List (Nat × String) := []
  for arm in arms do
    match arm with
    | .mk [.ctor x q ps] body =>
      match g.ops.lookup x with
      | some info =>
        if let some owner := q then
          unless owner == info.owner do throw s!"`{x}` is not an operation of `{owner}`"
        opArms := opArms.push (info, ps, body)
        opNames := (info.id, x) :: opNames
      | none => completions := completions.push (.ctor x q ps, body)
    | .mk [p] body => completions := completions.push (p, body)
    | .mk _ _ => throw "a handler arm has exactly one head pattern"
  let identity : List Core.Clause := [⟨[.wild], .ret (.var 0)⟩]
  let retClauses ←
    if completions.isEmpty then pure identity
    else completions.toList.mapM fun (p, body) =>
      mkClause captures [p] (fun sc => elabStmts sc true body)
  let owner := (← get).owner
  let retIdx ← addFn ⟨retClauses⟩ s!"the completion clauses of a handler in `{owner}`"
  let mut table : Array (Nat × Nat) := #[]
  for id in (opArms.toList.map (·.1.id)).eraseDups do
    let mine := opArms.toList.filter (·.1.id == id)
    match mine with
    | [] => pure ()
    | (info, _, _) :: _ =>
      let n := info.arity
      let clauses ← mine.mapM fun (_, ps, body) => do
        if info.terminal then
          unless ps.length == n do
            throw s!"an arm for a terminal operation with {n} arguments has {ps.length} patterns"
          mkClause captures ps (fun sc => elabStmts sc true body)
        else if ps.length == n + 1 then
          -- An arm that does not use its resumption gives it up first: the
          -- computation it suspended is left as an exit would leave it, and
          -- its cleanups run. Otherwise it would simply be forgotten.
          let unused := match ps.getLast? with
            | some .wild => true
            | some (.var k) => !(fvStmts [] body).contains k
            | _ => false
          if unused then
            mkClause captures ps (fun sc => do
              let _ ← emit (.cancel (.var n))
              elabStmts sc true body)
          else mkClause captures ps (fun sc => elabStmts sc true body)
        else if ps.length == n then
          mkClause captures (ps ++ [.wild]) (fun sc => do
            let r ← elabStmts sc false body
            terminate (.tail (.var n) [r])
            pure (.int 0))
        else
          throw s!"an arm for an operation with {n} arguments has {ps.length} patterns"
      let payload := (List.range n).map Atom.var
      let forward : Core.Clause :=
        if info.terminal then ⟨List.replicate n .wild, .raise info.id payload⟩
        else ⟨List.replicate (n + 1) .wild,
          .perform info.id payload
            (.tail (.var n) [.var (n + 1 + captures.length)])⟩
      let opName := (opNames.lookup id).getD "an operation"
      -- With an arm that cannot fail the forwarding clause would never run, and
      -- it would still make the function need the operation from outside.
      let covered ← mine.anyM fun (_, ps, _) => ps.allM irrefutable
      let idx ← addFn ⟨if covered then clauses else clauses ++ [forward]⟩
        s!"the handler arm for `{opName}` in `{owner}`"
      table := table.push (id, idx)
  let caps ← (captures.filterMap (fun x => scope.lookup x)).mapM useLocal
  if tailPos then
    terminate (.handleTail retIdx table.toList caps thunk)
    pure (.int 0)
  else emit (.handle retIdx table.toList caps thunk)

end

/-! ## Programs -/

structure Output where
  program : Core.Program
  /-- Constructor names by tag, for printing values. Tag 0 is the tuple. -/
  ctorNames : Array String
  /-- A description of each function, for diagnostics. -/
  fnNames : Array String
  /-- Operation names by identity, for diagnostics. -/
  opNames : Array String
  /-- Functions that are only ever given the environment of another, with how
  many values that environment has and how many arguments the other took. -/
  envSizes : List (Nat × Nat × Nat)
  /-- How many borrows were made scopes of their own. -/
  lent : Nat := 0
  /-- How many calls of functions with borrows written as arguments there were. -/
  sites : Nat := 0
  /-- The borrows that are not scopes of their own, in the order written. -/
  plain : List Borrow := []
  /-- Does the program do what is unsafe? Core's rules say nothing of it. -/
  foreign : Bool := false

/-! ## Traits

A trait bound is met by a value: a tuple of the implementation's functions. A
function that needs a bound of one of its type parameters takes that value as
an argument, before its own; a call of it passes the value; a call of one of a
trait's functions takes the function out of the value. The checker said, for
each call, which value. After this rewriting a program has no traits. -/

private partial def dictExpr : DictE → Expr
  | .param k => .name none s!"%dict{k}"
  | .impl fn subs => .call 0 (.name none fn) (subs.map dictExpr)

/-- The function an implementation gives for the trait's function `idx`, and
the evidence its conditions need, if the evidence is an implementation and not
something the enclosing function was given. -/
def staticMethod (tr : TraitInfo) (d : DictE) (idx : Nat) : Option (String × List DictE) :=
  match d with
  | .impl dictFn subs =>
    match tr.impls.find? (·.dictFn == dictFn) with
    | some im => (im.methods[idx]?).map fun (fn, _) => (fn, subs)
    | none => none
  | .param _ => none

/-- The call that destroys a value, given how its type is destroyed: the
type's function by name where the type is known, and else the function the
enclosing one was given. -/
private def destroyCall (tr : TraitInfo) (d : DictE) (value : Expr) : Expr :=
  match staticMethod tr d 0 with
  | some (fn, subs) => .call dropCallId (.name none fn) (subs.map dictExpr ++ [value])
  | none => .call dropCallId (.proj (dictExpr d) 0) [value]

/-- The call that destroys what `x` holds, if this is a place where that
happens and its type has something to destroy. -/
private def dropHook (tr : TraitInfo) (site : DropSite) : Option Expr :=
  match (tr.drops.lookup site).bind fun id => tr.dicts.lookup id with
  | some [d] => some (destroyCall tr d (.name none site.name))
  | _ => none

/-- The functions that destroy values, for each type: the one that does it,
given how each of the type's parameters is destroyed and then the value, and
the one that makes it a value to hand to a function generic in the type. The
type's own `Drop` runs first, if it has one, and then each field that has
something to destroy, the last declared first. -/
def destroyers (tr : TraitInfo) : List Item :=
  tr.destroys.flatMap fun D =>
    let unit := Expr.tuple []
    let name := fun (x : String) => Expr.name none x
    let dicts := (List.range D.given).map fun k => s!"%dict{k}"
    let given := dicts.map Pattern.var
    let passed := dicts.map name
    let method := Syntax.implFnName Syntax.destroyTrait D.head Syntax.destroyFn
    let blank := List.replicate (D.given + 1) (none : Option TypeExpr)
    -- As a value: the function, given the value.
    let asValue := Item.fn (implDictName Syntax.destroyTrait D.head) [] (blank.drop 1) none
      [.mk given [.expr (.tuple [.closure 0 [.mk [.var "%arg0"]
        [.expr (.call dropCallId (name method) (passed ++ [name "%arg0"]))]]])]]
    -- An array: its elements one by one, from the last.
    if let (true, [(_, [some element])]) := (D.array, D.ctors) then
      let from_ := "%destroy from " ++ D.head
      let before := Expr.call dropCallId (name "int_sub") [name "%n", .int 1]
      [asValue,
        Item.fn method [] blank none
          [.mk (given ++ [.var "%value"])
            [.expr (.call dropCallId (name from_)
              (passed ++ [name "%value", .call dropCallId (name "arr_len") [name "%value", .int 0]]))]],
        Item.fn from_ [] (blank ++ [none]) none
          [.mk (given ++ [.wild, .int 0]) [.expr unit],
            .mk (given ++ [.var "%value", .var "%n"])
              [.expr (destroyCall tr element (.call dropCallId (name "arr_get") [name "%value", before])),
                .expr (.tailCall dropCallId (name from_) (passed ++ [name "%value", before]))]]]
    else
    let clauses := D.ctors.map fun (ctor, parts) =>
      let names := (List.range parts.length).map fun k => s!"%part{k}"
      let pats := (names.zip parts).map fun (x, part) =>
        if part.isSome then Pattern.var x else Pattern.wild
      let calls := ((names.zip parts).reverse.filterMap fun (x, part) =>
        part.map fun d => Stmt.expr (destroyCall tr d (name x)))
      Clause.mk (given ++ [if ctor.isEmpty then .tuple pats else .ctor ctor none pats])
        (calls ++ [.expr unit])
    -- A type with nothing inside it to look at: nothing to do.
    let clauses := if clauses.isEmpty then [Clause.mk (given ++ [.wild]) [.expr unit]] else clauses
    let inner := D.ctors.any fun (_, parts) => parts.any (·.isSome)
    match D.hook with
    | some d =>
      let hook := match staticMethod tr d 0 with
        | some (fn, subs) => fun (args : List Expr) =>
          Expr.call dropCallId (.name none fn) (subs.map dictExpr ++ args)
        | none => fun args => Expr.call dropCallId (.proj (dictExpr d) 0) args
      let fields := s!"%fields {D.head}"
      [asValue,
        Item.fn method [] blank none
          [.mk (given ++ [.var "%value"])
            ([.letMut "%held" (name "%value"), .expr (hook [.ref true "%held"])]
              ++ (if inner then [.expr (.call dropCallId (name fields) (passed ++ [name "%held"]))]
                  else [.expr unit]))]]
        ++ (if inner then [Item.fn fields [] blank none clauses] else [])
    | none => [asValue, Item.fn method [] blank none clauses]

mutual

/-- Patterns with each `_` whose number `named` picks written as a name: the
`_` are numbered in the order they are read, from `k`. Gives the number after
the last. -/
partial def nameWilds (named : Nat → Bool) : List Pattern → Nat → List Pattern × Nat
  | [], k => ([], k)
  | p :: rest, k =>
    let (p, k) := nameWild named p k
    let (rest, k) := nameWilds named rest k
    (p :: rest, k)

partial def nameWild (named : Nat → Bool) : Pattern → Nat → Pattern × Nat
  | .wild, k => (if named k then .var (wildName k) else .wild, k + 1)
  | .tuple ps, k =>
    let (ps, k) := nameWilds named ps k
    (.tuple ps, k)
  | .ctor c q ps, k =>
    let (ps, k) := nameWilds named ps k
    (.ctor c q ps, k)
  | p, k => (p, k)

end

mutual

private partial def untraitExpr (tr : TraitInfo) (owner : String) : Expr → Expr
  | .call id f args => untraitCall tr owner id f args false
  | .tailCall id f args => untraitCall tr owner id f args true
  | .tuple args => .tuple (args.map (untraitExpr tr owner))
  | .proj e idx => .proj (untraitExpr tr owner e) idx
  | .closure id clauses => .closure id (clauses.map (untraitClause tr owner))
  | .handle subject arms =>
    .handle (untraitExpr tr owner subject) (arms.map (untraitClause tr owner))
  | .labelScope l body => .labelScope l (untraitStmts tr owner (0, 0) body)
  | .deref e => .deref (untraitExpr tr owner e)
  | .reborrow uniq e => .reborrow uniq (untraitExpr tr owner e)
  | .fieldOf id e name => .fieldOf id (untraitExpr tr owner e) name
  | e => e

private partial def untraitCall (tr : TraitInfo) (owner : String) (id : Nat) (f : Expr)
    (args : List Expr) (isTail : Bool) : Expr :=
  let args := args.map (untraitExpr tr owner)
  let mk := fun (f : Expr) (args : List Expr) =>
    if isTail then Expr.tailCall id f args else Expr.call id f args
  match tr.dicts.lookup id, tr.methods.lookup id with
  | some [d], some idx =>
    -- Where the implementation is known, its function is called by name,
    -- given what the implementation's conditions need: a call like any other,
    -- so that a borrow passed to it can be a scope.
    match staticMethod tr d idx with
    | some (fn, subs) => mk (.name none fn) (subs.map dictExpr ++ args)
    | none => mk (.proj (dictExpr d) idx) args
  | some ds, none => mk (untraitExpr tr owner f) (ds.map dictExpr ++ args)
  | _, _ => mk (untraitExpr tr owner f) args

private partial def untraitClause (tr : TraitInfo) (owner : String) : Clause → Clause
  | .mk pats body =>
    -- What the clause is given under a name and does not mention is
    -- destroyed when the clause is done; and so is what a `_` takes, which
    -- is given a name for it.
    let first := firstPlace body
    let (pats, _) := nameWilds (fun k => (dropHook tr ⟨owner, first.1, first.2, wildName k, false⟩).isSome) pats 0
    let hooks := (pats.flatMap patVars).filterMap fun x =>
      (dropHook tr ⟨owner, first.1, first.2, x, false⟩).map Stmt.defer
    .mk pats (hooks ++ untraitStmts tr owner (0, 0) body)

/-- The statements of a block. A variable whose value is to be destroyed is
followed by a cleanup that does it when the block is left; an assignment to one
destroys what it held, once the new value is computed. -/
private partial def untraitStmts (tr : TraitInfo) (owner : String) (pos : Nat × Nat) :
    List Stmt → List Stmt
  | [] => []
  | .located line col s :: rest =>
    match untraitStmts tr owner (line, col) (s :: rest) with
    | first :: more => .located line col first :: more
    | [] => []
  | .letMut x value :: rest =>
    let value := untraitExpr tr owner value
    let rest := untraitStmts tr owner pos rest
    match dropHook tr ⟨owner, pos.1, pos.2, x, false⟩ with
    | some hook => .letMut x value :: .defer hook :: rest
    | none => .letMut x value :: rest
  | .let_ pat value :: rest =>
    let value := untraitExpr tr owner value
    let rest := untraitStmts tr owner pos rest
    match pat with
    | .var x =>
      match dropHook tr ⟨owner, pos.1, pos.2, x, false⟩ with
      | some hook => .let_ pat value :: .defer hook :: rest
      | none => .let_ pat value :: rest
    | _ => .let_ pat value :: rest
  | .assign target value :: rest =>
    let value := untraitExpr tr owner value
    let target := untraitExpr tr owner target
    let rest := untraitStmts tr owner pos rest
    match target with
    | .name none x =>
      match dropHook tr ⟨owner, pos.1, pos.2, x, true⟩ with
      | some hook =>
        .let_ (.var "%assigned") value :: .expr hook
          :: .assign target (.name none "%assigned") :: rest
      | none => .assign target value :: rest
    | _ => .assign target value :: rest
  | .expr e :: rest =>
    let e := untraitExpr tr owner e
    let rest := untraitStmts tr owner pos rest
    -- A value nothing takes, of a type to destroy, is destroyed there.
    match (if rest.isEmpty then none else dropHook tr ⟨owner, pos.1, pos.2, stmtValue, false⟩) with
    | some hook => .let_ (.var stmtValue) e :: .expr hook :: rest
    | none => .expr e :: rest
  | .defer e :: rest => .defer (untraitExpr tr owner e) :: untraitStmts tr owner pos rest

end

/-- The clauses of a function that is given `n` bounds: each takes them first. -/
private def withDicts (n : Nat) (clauses : List Clause) : List Clause :=
  clauses.map fun
    | .mk pats body => .mk ((List.range n).map (fun k => Pattern.var s!"%dict{k}") ++ pats) body

/-- A program without its traits, and what the checker said of it with the
places of arguments moved to where they now are. -/
def untrait (blocks : Blocks) (items : List Item) : List Item × Blocks :=
  let tr := blocks.traits
  let fnItem := fun (name : String) (params : List String) (annots : List (Option TypeExpr))
      (ret : Option TypeExpr) (clauses : List Clause) =>
    let n := (tr.bounded.lookup name).getD 0
    Item.fn name params ((List.replicate n none) ++ annots) ret
      (withDicts n (clauses.map (untraitClause tr name)))
  let out := items.flatMap fun
    | .trait _ _ => []
    | .impl params trait head _ context methods =>
      let own := methods.filterMap fun
        | .fn m _ annots ret clauses =>
          some (fnItem (implFnName trait head m) params annots ret clauses)
        | _ => none
      let dictFn := implDictName trait head
      -- (as many as the checker says: how each type parameter is destroyed
      -- is among them, written or not)
      let conditions := ((tr.impls.find? (·.dictFn == dictFn)).map (·.conditions)).getD context.length
      let dicts := (List.range conditions).map fun k => s!"%dict{k}"
      let fns := ((tr.impls.find? (·.dictFn == dictFn)).map (·.methods)).getD []
      let closures := fns.map fun (fn, arity) =>
        let argNames := (List.range arity).map fun k => s!"%arg{k}"
        Expr.closure 0 [.mk (argNames.map Pattern.var)
          [.expr (.call 0 (.name none fn) ((dicts ++ argNames).map (Expr.name none)))]]
      own ++ [Item.fn dictFn [] [] none [.mk (dicts.map Pattern.var) [.expr (.tuple closures)]]]
    | .fn name params annots ret clauses => [fnItem name params annots ret clauses]
    | item => [item]
  let out := out ++ destroyers tr
  let coercions := blocks.coercions.map fun (site, fn) =>
    match site with
    | .arg call index =>
      match tr.dicts.lookup call, tr.methods.lookup call with
      | some ds, none => (Site.arg call (index + ds.length), fn)
      | some [d], some idx =>
        match staticMethod tr d idx with
        | some (_, subs) => (Site.arg call (index + subs.length), fn)
        | none => (site, fn)
      | _, _ => (site, fn)
    | _ => (site, fn)
  (out, { blocks with coercions := coercions })

/-! ## Lifetimes

Lifetimes are the checker's. Once a program is checked they are taken out of
it: nothing after the checker reads one.
-/

private partial def eraseLifetimesTy : TypeExpr → TypeExpr
  | .name x args =>
    -- A callable for every lifetime is, without them, the callable.
    if x == Syntax.rankedMark then
      match args.getLast? with
      | some inner => eraseLifetimesTy inner
      | none => .name x []
    else
    .name x ((args.filter fun
      | .name n [] => !n.startsWith "'"
      | _ => true).map eraseLifetimesTy)
  | .tuple args => .tuple (args.map eraseLifetimesTy)
  | .fn ps r => .fn (ps.map eraseLifetimesTy) (eraseLifetimesTy r)
  | .performs r effects =>
    .performs (eraseLifetimesTy r) (effects.map fun (e, args) => (e, args.map eraseLifetimesTy))
  | .ref uniq t _ => .ref uniq (eraseLifetimesTy t) none
  | t => t

partial def eraseLifetimes (items : List Item) : List Item :=
  let params := fun (ps : List String) => ps.filter fun p => !p.startsWith "'"
  items.map fun
    | .enum name ps ctors =>
      .enum name (params ps) (ctors.map fun (c, fields) => (c, fields.map eraseLifetimesTy))
    | .struct name ps fields => .struct name (params ps) (fields.map eraseLifetimesTy)
    | .effect name ps ops =>
      .effect name (params ps) (ops.map fun op =>
        { op with payload := op.payload.map eraseLifetimesTy,
                  result := op.result.map eraseLifetimesTy })
    | .fn name ps annots ret clauses =>
      .fn name (params ps) (annots.map (·.map eraseLifetimesTy)) (ret.map eraseLifetimesTy) clauses
    | .trait name methods =>
      .trait name (methods.map fun (m, ps, r) =>
        (m, ps.map eraseLifetimesTy, r.map eraseLifetimesTy))
    | .impl ps tr head args context methods =>
      .impl (params ps) tr head (params args) context (eraseLifetimes methods)
    | item => item

/-- The items with each declared type and effect as it was written, lifetimes
and all: the regions of Core are found from those. -/
def withDeclared (written items : List Item) : List Item :=
  items.map fun
    | .enum name ps ctors =>
      (written.find? fun
        | .enum n _ _ => n == name
        | _ => false).getD (.enum name ps ctors)
    | .struct name ps fields =>
      (written.find? fun
        | .struct n _ _ => n == name
        | _ => false).getD (.struct name ps fields)
    | .effect name ps ops =>
      (written.find? fun
        | .effect n _ _ => n == name
        | _ => false).getD (.effect name ps ops)
    | item => item

/-! ## Borrows of a field

The machine's references are to whole variables. A borrow of a field,
`&mut x.0`, is written out before elaboration as a variable of its own that
holds the field for as long as the borrow lasts: the field is copied in, the
borrow is of that variable, and a cleanup puts what the variable then holds
back into `x`, rebuilt around it, however the borrow's extent is left. The
checker has made sure that nothing else uses the field meanwhile, so nothing
can tell.
-/

/-- A function that never comes back, for the case that cannot be. -/
def neverName : String := "%never"

/-- Field `i` of a value, which `step` says is a tuple, a value of a type with
one constructor, or (marked `#`) a value made by one of several: that one's
field is taken by matching, since which constructor made a value cannot be
read off it. -/
private def fieldStep (step : Option String × Nat) (e : Expr) (i : Nat) : Expr :=
  match step with
  | (some c, n) =>
    if c.startsWith "#" then
      -- The value is made by this constructor: the checker saw it found so,
      -- and nothing else could change it since. What stands for the other
      -- case never comes back, so it can be of the field's type.
      let pats := (List.range n).map fun j => if j == i then Pattern.var "%part" else .wild
      .call 0 (.closure 0
        [.mk [.ctor (c.drop 1).toString none pats] [.expr (.name none "%part")],
         .mk [.wild] [.expr (.tailCall 0 (.name none neverName) [])]]) [e]
    else .proj e i
  | _ => .proj e i

private def fieldPath (root : Expr) (path : List Nat) (shape : List (Option String × Nat)) : Expr :=
  (path.zip (shape ++ path.map fun _ => (none, 0))).foldl (fun e (i, step) => fieldStep step e i) root

/-- The value at `root`, with the field reached by `rest` (after `done`, which
went through `gone`) replaced by `new` and everything else as it is. -/
private def rebuildField (root : Expr) :
    List Nat → List (Option String × Nat) → List Nat → List (Option String × Nat) → Expr → Expr
  | done, gone, i :: rest, (ctor, n) :: shape, new =>
    let parts := (List.range n).map fun j =>
      if j == i then rebuildField root (done ++ [i]) (gone ++ [(ctor, n)]) rest shape new
      else fieldPath root (done ++ [j]) (gone ++ [(ctor, n)])
    match ctor with
    | none => .tuple parts
    | some c => .call 0 (.name none (if c.startsWith "#" then (c.drop 1).toString else c)) parts
  | _, _, _, _, new => new

private def plainExpr : Expr → Bool
  | .name _ _ => true
  | .int _ => true
  | .label _ => true
  | .closure _ _ => true
  | .ref _ _ => true
  | _ => false

private def fieldRefName (id : Nat) : String := s!"%fieldref{id}"

/-- A borrow of a field: its identity, whether for writing, the variable, and
the way to the field. -/
private abbrev FieldBorrow := Nat × Bool × String

mutual

/-- The first borrow of a field that evaluating this expression comes to, the
expression with a name in its place, and the parts of the expression that are
evaluated before it and do something, each given a name so that they still
are. -/
private partial def liftField : Expr → Option (List Stmt × Expr × FieldBorrow)
  | .refField id uniq x _ _ => some ([], .name none (fieldRefName id), (id, uniq, x))
  | .call cid f args =>
    (liftParts (f :: args)).map fun (lets, parts, b) =>
      (lets, .call cid (parts.headD f) (parts.drop 1), b)
  | .tailCall cid f args =>
    (liftParts (f :: args)).map fun (lets, parts, b) =>
      (lets, .call cid (parts.headD f) (parts.drop 1), b)
  | .tuple es => (liftParts es).map fun (lets, parts, b) => (lets, .tuple parts, b)
  | .proj e i => (liftField e).map fun (lets, e, b) => (lets, .proj e i, b)
  | .fieldOf id e name => (liftField e).map fun (lets, e, b) => (lets, .fieldOf id e name, b)
  | .deref e => (liftField e).map fun (lets, e, b) => (lets, .deref e, b)
  | .reborrow u e => (liftField e).map fun (lets, e, b) => (lets, .reborrow u e, b)
  | _ => none

private partial def liftParts (parts : List Expr) : Option (List Stmt × List Expr × FieldBorrow) :=
  let rec go (before : List Expr) : List Expr → Option (List Stmt × List Expr × FieldBorrow)
    | [] => none
    | e :: rest =>
      match liftField e with
      | some (lets, e', b) =>
        let named : List (Expr × Option Stmt) := (before.zip (List.range before.length)).map
          fun (a, j) =>
            if plainExpr a then (a, none)
            else
              let n := s!"%before{b.1}.{j}"
              (Expr.name none n, some (Stmt.let_ (.var n) a))
        some (named.filterMap (·.2) ++ lets, named.map (·.1) ++ e' :: rest, b)
      | none => go (before ++ [e]) rest
  go [] parts

end

/-- The same for a statement. -/
private def liftFieldStmt : Stmt → Option (List Stmt × Stmt × FieldBorrow)
  | .expr e => (liftField e).map fun (lets, e, b) => (lets, .expr e, b)
  | .let_ pat e => (liftField e).map fun (lets, e, b) => (lets, .let_ pat e, b)
  | .letMut y e => (liftField e).map fun (lets, e, b) => (lets, .letMut y e, b)
  | .assign target e =>
    match liftField e with
    | some (lets, e, b) => some (lets, .assign target e, b)
    | none =>
      -- The value is computed before the place is found.
      match target with
      | .deref place =>
        (liftField place).map fun (lets, place, b) =>
          let n := s!"%value{b.1}"
          (Stmt.let_ (.var n) e :: lets, .assign (.deref place) (.name none n), b)
      | _ => none
  | _ => none

/-- What the checker found about fields: for each borrow of one, whether it
goes through a reference, the way to the field by number, and what is gone
through; and for each field read by name, which field it is. -/
structure FieldInfo where
  shapes : List (Nat × Bool × List Nat × List (Option String × Nat))
  reads : List (Nat × Nat)
  /-- The blocks given what an `is` found, each with the names it then has. -/
  packs : List (Nat × List String) := []
  /-- In the function being written out: each callable that runs in an
  environment another holds, with the one that holds it. -/
  members : List (String × String) := []
  /-- Calls that give a name where a callable sharing an environment is
  wanted, and where. -/
  wraps : List (Nat × List Nat) := []
  /-- The fields read by name of what a named reference points to. -/
  derefs : List Nat := []

/-- A call as it is where callables share an environment. In a function given
such callables, a call of one that does not hold the environment gives it the
one that does, to run in its place. And where a name is given for such a
callable, it is given as a callable that takes what holds the environment and
calls the name. -/
def shareEnv (info : FieldInfo) (id : Nat) (f : Expr) (args : List Expr) : Expr × List Expr :=
  let args := match info.wraps.lookup id with
    | some places =>
      (args.zip (List.range args.length)).map fun (a, i) =>
        if places.contains i then Expr.closure 0 [.mk [.wild] [.expr (.call 0 a [])]] else a
    | none => args
  match f, args with
  | .name none b, [] =>
    match info.members.lookup b with
    | some holder => (f, [.name none holder])
    | none => (f, args)
  | _, _ => (f, args)

mutual

/-- The callables and scopes written inside an expression, with the borrows of
fields in them written out. -/
private partial def unfieldExpr (info : FieldInfo) : Expr → Expr
  | .call id f args =>
    let (f, args) := shareEnv info id f args
    .call id (unfieldExpr info f) (args.map (unfieldExpr info))
  | .tailCall id f args =>
    let (f, args) := shareEnv info id f args
    .tailCall id (unfieldExpr info f) (args.map (unfieldExpr info))
  | .tuple es => .tuple (es.map (unfieldExpr info))
  | .proj e i => .proj (unfieldExpr info e) i
  | .fieldOf id e name =>
    -- The checker said which field the name is.
    match info.reads.lookup id with
    | some i =>
      -- Of what a reference points to, if the checker found it so.
      if info.derefs.contains id then .proj (.deref (unfieldExpr info e)) i
      else .proj (unfieldExpr info e) i
    | none => .fieldOf id (unfieldExpr info e) name
  | .deref e => .deref (unfieldExpr info e)
  | .reborrow u e => .reborrow u (unfieldExpr info e)
  | .closure id clauses =>
    -- A block given what an `is` found takes it apart under its names.
    match info.packs.lookup id, clauses with
    | some names, [.mk [] body] =>
      -- A block that is run where it is written.
      if names == [Syntax.nowMark] then .call 0 (.closure id [.mk [] (unfieldStmts info body)]) []
      else .closure id [.mk [.tuple (names.map Pattern.var)] (unfieldStmts info body)]
    | some names, _ =>
      -- Clauses of one tuple given several arguments: the tuple's parts are
      -- the parameters.
      if names == [Syntax.spreadMark] then
        .closure id (clauses.map fun
          | .mk [.tuple parts] body => unfieldClause info (.mk parts body)
          | c => unfieldClause info c)
      -- A block that is run where it is written.
      else if names == [Syntax.nowMark] then .call 0 (.closure id (clauses.map (unfieldClause info))) []
      else .closure id (clauses.map (unfieldClause info))
    | _, _ => .closure id (clauses.map (unfieldClause info))
  | .labelScope l body => .labelScope l (unfieldStmts info body)
  | .handle subject arms =>
    .handle (unfieldBlock info subject) (arms.map (unfieldClause info))
  | e => e

/-- An expression that is run as a body of its own: if it borrows a field, it
becomes a block. -/
private partial def unfieldBlock (info : FieldInfo) (e : Expr) :
    Expr :=
  let e := unfieldExpr info e
  if (liftField e).isSome then .labelScope "%block" (unfieldStmts info [.expr e]) else e

private partial def unfieldClause (info : FieldInfo) :
    Clause → Clause
  | .mk pats body => .mk pats (unfieldStmts info body)

private partial def unfieldStmts (info : FieldInfo) :
    List Stmt → List Stmt
  | [] => []
  | s :: rest =>
    let rec peel : Stmt → (Stmt → Stmt) × Stmt
      | .located line col s =>
        let (wrap, inner) := peel s
        (fun x => .located line col (wrap x), inner)
      | s => (id, s)
    -- Borrows of fields written one straight after another: the one that
    -- lasts longest is made first, so that the time each lasts is inside
    -- that of the one before. None of them does anything but borrow.
    let borrowed := fun (s : Stmt) =>
      match (peel s).2 with
      | .let_ (.var p) (.refField _ _ _ _ _) => some p
      | _ => none
    let run := (s :: rest).takeWhile fun s => (borrowed s).isSome
    let more := (s :: rest).drop run.length
    let lasts := run.map fun s => scopeExtent ((borrowed s).getD "") more true
    let longest := lasts.foldl max 0
    let swapped :=
      if run.length ≥ 2 && lasts.head? != some longest then
        match (run.zip lasts).find? (·.2 == longest) with
        | some (first, _) =>
          -- The first of those that last longest, then the others as they were.
          let k := ((run.zip lasts).findIdx? (·.2 == longest)).getD 0
          some (first :: (run.take k ++ run.drop (k + 1)) ++ more)
        | none => none
      else none
    if let some reordered := swapped then unfieldStmts info reordered else
    let (wrap, s) := peel s
    let s := match s with
      | .expr e => Stmt.expr (unfieldExpr info e)
      | .let_ pat e => .let_ pat (unfieldExpr info e)
      | .letMut y e => .letMut y (unfieldExpr info e)
      | .assign target e => .assign (unfieldExpr info target) (unfieldExpr info e)
      | .defer e => .defer (unfieldBlock info e)
      | s => s
    match liftFieldStmt s with
    | none => wrap s :: unfieldStmts info rest
    | some (before, s, (id, uniq, x)) =>
      match info.shapes.lookup id with
      | none => wrap s :: unfieldStmts info rest
      | some (viaRef, path, shape) =>
        -- A field of what a reference points to, found without asking which
        -- constructor built anything on the way: the reference, further in.
        -- Nothing is taken out, so the borrow can outlive the function.
        if viaRef && !shape.any (fun (c, _) => (c.getD "").startsWith "#") then
          unfieldStmts info (before ++ Stmt.let_ (.var (fieldRefName id))
            (.call 0 (.name none Syntax.focusMark)
              (.name none x :: path.map fun n => Expr.int (Int.ofNat n)))
            :: s :: rest)
        else
        -- What the field is a field of: what the variable holds, or what the
        -- reference points to.
        let root := if viaRef then Expr.deref (.name none x) else Expr.name none x
        let cell := s!"%field{id}"
        let ref := fieldRefName id
        -- The borrow lasts while anything made from it is still used.
        let following := wrap s :: rest
        let k0 := scopeExtent ref following true
        -- A borrow of a field made while this one lasts and used after it is
        -- done with: this one is kept until that one is done with too, if
        -- nothing in between looks at the variable itself, which holds the
        -- old value of this field until the borrow ends.
        let rec widen (fuel : Nat) (k : Nat) : Nat :=
          match fuel with
          | 0 => k
          | fuel + 1 =>
            let later := fvStmts [] (following.drop k)
            let crossing := (following.take k).filterMap fun s =>
              match unlocated s with
              | .let_ (.var q) (.refField _ _ _ _ _) => if later.contains q then some q else none
              | _ => none
            match crossing with
            | [] => k
            | qs =>
              let need := qs.foldl (fun acc q => max acc (k + scopeExtent q (following.drop k) true)) k
              if need == k || (fvStmts [] ((following.take need).drop k)).contains x then k
              else widen fuel need
        let k := widen 8 k0
        let inner := (following.take k).map fun
          | .expr (.tailCall cid f args) => Stmt.expr (.call cid f args)
          | .located line col (.expr (.tailCall cid f args)) =>
            .located line col (.expr (.call cid f args))
          | s => s
        let after := following.drop k
        let used := fvStmts [] after
        let out := ((letNames inner).filter used.contains).eraseDups
        -- A borrow of a field made while this one lasts and used after it:
        -- neither lasts inside the other. Left as a mark, to be refused.
        let crossing := (following.take k).filterMap fun s =>
          match unlocated s with
          | .let_ (.var q) (.refField _ _ _ _ _) => if used.contains q then some q else none
          | _ => none
        let before := match crossing.head? with
          | some q => before ++ [.expr (.name none s!"%crossing:{q}")]
          | none => before
        let (result, pat) : List Stmt × Option Pattern :=
          if after.isEmpty then ([], none)
          else match out with
            | [] => ([.expr (.tuple [])], some .wild)
            | [n] => ([.expr (.name none n)], some (.var n))
            | ns => ([.expr (.tuple (ns.map (.name none)))], some (.tuple (ns.map .var)))
        let putBack : List Stmt :=
          if uniq then
            [.defer (.call 0 (.closure 0 [.mk []
              [.assign root (rebuildField root [] [] path shape (.name none cell))]]) [])]
          else []
        let block := .letMut cell (fieldPath root path shape) :: putBack
          ++ .let_ (.var ref) (.ref uniq cell) :: unfieldStmts info inner ++ result
        let scope := Expr.labelScope s!"%field{id}" block
        match pat with
        | none => before ++ [.expr scope]
        | some pat => before ++ .let_ pat scope :: unfieldStmts info after

end

/-- Write out every borrow of a field: see above. `shapes` is what the checker
found each borrow goes through. -/
def unfield (b : Blocks) (items : List Item) : Except String (List Item) := do
  if b.fields.isEmpty && b.fieldReads.isEmpty && b.packs.isEmpty && b.envFns.isEmpty then
    return items
  -- Where a field of one of several constructors is taken, the function for
  -- the case that cannot be.
  let several := b.fields.any fun (_, _, _, shape) =>
    shape.any fun (c, _) => ((c.map (·.startsWith "#")).getD false)
  let never : List Item :=
    if several then [.fn neverName [] [] none [.mk [] [.expr (.tailCall 0 (.name none neverName) [])]]]
    else []
  let out := never ++ items.map fun
    | .fn name params annots ret clauses =>
      -- Each callable that does not hold its environment, with the one that does.
      let members := ((b.envFns.lookup name).getD []).flatMap fun group =>
        match group with
        | holder :: rest => rest.map (·, holder)
        | [] => []
      .fn name params annots ret
        (clauses.map (unfieldClause ⟨b.fields, b.fieldReads, b.packs, members, b.envWraps, b.derefReads⟩))
    | item => item
  -- Two borrows of fields that overlap, neither lasting inside the other and
  -- with other statements between them, cannot be written out as blocks.
  for item in out do
    if let .fn name _ _ _ clauses := item then
      for x in clauses.flatMap (fvClause []) do
        if x.startsWith "%crossing:" then
          throw (Syntax.inFunction name s!"the borrow of a field kept in `{(x.drop 10).toString}` is made while another lasts and is used after that one is done with: make it before the other, or straight after it")
  pure out

/-- Collect the global declarations. -/
def collect (items : List Item) :
    Except String (Globals × List (String × List Clause) × Array String) := do
  let mut g : Globals := {}
  let mut fns : Array (String × List Clause) := #[]
  let mut names : Array String := #["tuple"]
  let mut nextOp := 0
  for item in items do
    match item with
    | .enum owner _ ctors =>
      for (c, fields) in ctors do
        if (g.ctors.lookup c).isSome then throw s!"constructor `{c}` is declared twice"
        g := { g with
          ctors := (c, ⟨owner, names.size, fields.length, ctors.length == 1⟩) :: g.ctors }
        names := names.push c
    | .struct owner _ fields =>
      if (g.ctors.lookup owner).isSome then throw s!"constructor `{owner}` is declared twice"
      g := { g with ctors := (owner, ⟨owner, names.size, fields.length, true⟩) :: g.ctors }
      names := names.push owner
    | .effect owner _ ops =>
      for op in ops do
        if (g.ops.lookup op.name).isSome then
          throw s!"operation `{op.name}` is declared twice"
        g := { g with
          ops := (op.name, ⟨owner, nextOp, op.payload.length, op.terminal⟩) :: g.ops }
        nextOp := nextOp + 1
    | .fn name _ _ _ clauses =>
      if (g.fns.lookup name).isSome then throw s!"function `{name}` is declared twice"
      g := { g with fns := (name, fns.size) :: g.fns, bodies := (name, clauses) :: g.bodies }
      fns := fns.push (name, clauses)
    | .alias name value => g := { g with aliases := (name, value) :: g.aliases }
    | .fixity => pure ()
    | .coerce _ => pure ()
    -- How often a value is to be used is the checker's business.
    | .use _ _ _ => pure ()
    -- So are the names of fields, and by now every field is a number.
    | .fieldNames mark known _ =>
      if mark == Syntax.arrayMark then
        if let [array, push, index] := known then g := { g with arrays := some (array, push, index) }
    | .typeAlias _ _ _ => pure ()
    -- And modules: every name is one name of the whole program by now.
    | .pub _ _ => pure ()
    | .unsafeFn _ => pure ()
    | .bounds _ _ => pure ()
    | .traitInfo _ _ _ _ _ => pure ()
    | .module _ _ => pure ()
    | .import _ _ _ => pure ()
    | .trait name _ =>
      throw s!"trait `{name}`: a program with traits is elaborated only after it is checked"
    | .impl _ tr _ _ _ _ =>
      throw s!"an implementation of `{tr}`: a program with traits is elaborated only after it is checked"
  pure (g, fns.toList, names)

/-- A function whose body mentions its own label `@name` runs inside that label's
scope, so applying the label returns from the function. -/
private def withSelfLabel (name : String) : Clause → Clause
  | .mk pats body =>
    if (fvStmts (pats.flatMap patVars) body).contains (labelName name) then
      .mk pats [.expr (.labelScope name body)]
    else .mk pats body

/-- The program without the functions nothing reaches from `main` or from a
coercion, which a call may be given without its being written. -/
def reachable (roots : List String) (items : List Item) : List Item := Id.run do
  -- The function for a case that cannot be, if something is written with it
  -- and it is not yet there.
  let defined := items.any fun
    | .fn name _ _ _ _ => name == neverName
    | _ => false
  let wanted := items.any fun
    | .fn _ _ _ _ clauses => (clauses.flatMap (fvClause [])).contains neverName
    | _ => false
  let items := if wanted && !defined then
      Item.fn neverName [] [] none [.mk [] [.expr (.tailCall 0 (.name none neverName) [])]] :: items
    else items
  let bodies : Std.HashMap String (List String) := items.foldl (init := {}) fun acc item =>
    match item with
    | .fn name _ _ _ clauses =>
      acc.insert name ((acc.getD name []) ++ clauses.flatMap (fvClause []))
    | _ => acc
  let mut seen : Std.HashSet String := {}
  let mut todo := roots
  let mut fuel := items.length + roots.length + 1
  while fuel > 0 && !todo.isEmpty do
    fuel := fuel - 1
    let mut next : List String := []
    for name in todo do
      unless seen.contains name do
        seen := seen.insert name
        for m in bodies.getD name [] do
          if bodies.contains m && !seen.contains m then next := m :: next
    todo := next
  items.filter fun
    | .fn name _ _ _ _ => seen.contains name
    | _ => true

/-- Elaborate a program. `blocks` is what the checker learnt about its blocks;
without it, every block captures what it mentions for itself. -/
def elabProgram (items : List Item) (blocks : Option Blocks := none)
    (lends : Nat → Nat := fun _ => 0) : Except String Output := do
  let (g, fns, names) ← collect items
  let g := { g with blocks := blocks, lends := lends }
  let coercions := (blocks.getD {}).coercions
  let fns := fns.map fun (name, clauses) => (name, coerceFn coercions name clauses)
  let mainIdx ← match g.fns.lookup "main" with
    | some idx => pure idx
    | none => throw "the program has no `main` function"
  let action : M Unit := do
    let mut idx := 0
    for (name, clauses) in fns do
      let arities := clauses.map fun
        | .mk pats _ => pats.length
      match arities with
      | [] => throw s!"function `{name}` has no clauses"
      | n :: rest =>
        unless rest.all (· == n) do
          throw s!"the clauses of `{name}` take different numbers of arguments"
      modify fun s => { s with owner := name }
      let coreClauses ← (clauses.map (withSelfLabel name)).mapM fun
        | .mk pats body => mkClause [] pats (fun sc => elabStmts sc true body)
      modify fun s => { s with fns := s.fns.set! idx ⟨coreClauses⟩ }
      idx := idx + 1
  let fnNames := (fns.map fun (name, _) => s!"`{name}`").toArray
  let init : St :=
    { fns := Array.replicate fns.length ⟨[]⟩, names := fnNames, owner := ""
      b := { ops := #[], depth := 0, done := none }, noTail := none }
  let (_, st) ← (action.run g).run init
  let opNames := Id.run do
    let mut out := Array.replicate g.ops.length ""
    for (name, info) in g.ops do
      out := out.set! info.id name
    pure out
  pure ⟨⟨st.fns.toList, .let_ (.closure mainIdx []) (.tail (.var 0) [])⟩, names, st.names,
    opNames, st.envSizes, st.lent, st.sites, st.plain.reverse, st.foreign⟩

end Glorious.Elab
