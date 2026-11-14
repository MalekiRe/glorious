module

public import Std.Data.HashMap
public import Std.Data.HashSet
public import Glorious.Syntax.Ast
public import Glorious.Core.Ast

/-!
# What the elaborator and the checker share

What the checker tells the elaborator about a program, the names the two
agree on, the free names of an expression, how long a borrow lasts, and the
elaborator's own state. The checker reads this file and not the elaborator:
a change to how a program is written out does not have the checker built
again.
-/

public section

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

/-- The name a `_` in the pattern of a `let` has, likewise: with the
statement's place, as a block has many. -/
def letWildName (line col k : Nat) : String := s!"{wildName k}@{line}:{col}"

/-- The name the value of a statement has where it is destroyed. -/
def stmtValue : String := "%stmt"

/-- The name what a reference points to has where it is written over, and
what was there is destroyed. -/
def derefSite : String := "%deref"

/-- A place where what a variable holds is destroyed: where the variable is
declared, for the end of its block, or where it is assigned, for what it held. -/
structure DropSite where
  owner : String
  line : Nat
  col : Nat
  name : String
  assign : Bool
  deriving BEq

/-- The site under which the checker says how what `x` holds is destroyed when
the callable written as `written` (its hash), which captured it, is let go. -/
def captureDropSite (owner : String) (written : UInt64) (x : String) : DropSite :=
  ⟨owner, written.toNat, 0, Syntax.captureSite x, false⟩

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
  /-- For each function that performs or handles an operation of an effect
  with type parameters, or calls one that does: the places, by the number of
  the call, with which of `op`, `handle`, `call`, `ref` each is, the effect or
  the function called, and where its types are among the function's. -/
  sites : List (String × List (Nat × String × String × Nat × Nat)) := []
  /-- Those types, each where it is known without knowing who calls the
  function. -/
  siteTypes : List (String × List (Option Syntax.TypeExpr)) := []

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
  /-- A place that is a call inside a statement that is a place itself, with
  the statement's: where the statement's borrows are made scopes, the call's
  are among them. -/
  under : List (Nat × Nat) := []
  /-- The places that can be tried two ways, the second with the borrow
  lasting longer: the others are a call's, and a call's lasts as long as
  the call. -/
  twoWays : List Nat := []
  /-- The function each place is in, by place. -/
  siteOwners : Array String := #[]
  /-- The place being elaborated as a scope of its own, while it is. -/
  curSite : Option Nat := none
  /-- For each function made, the place being elaborated as a scope of its
  own when it was made, if one was. -/
  fnSites : Array (Option Nat) := #[]
  /-- Where the statement being elaborated starts. -/
  pos : Nat × Nat := (0, 0)
  /-- The borrows that are not scopes of their own: each is the reference it
  borrows. -/
  plain : List Borrow := []
  /-- Does the program call a foreign function, or read or write memory at an
  address? -/
  foreign : Bool := false
  /-- Each function whose closures say how they are destroyed, with the
  function that destroys what one captured. -/
  drops : List (Nat × Nat) := []

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
  modifyGet fun s =>
    (s.fns.size, { s with fns := s.fns.push f, names := s.names.push name, fnSites := s.fnSites.push s.curSite })

/-- Elaborate as part of the place `site`, which is a scope of its own: what
functions are made are that place's. -/
def atSite {α : Type} (site : Nat) (act : M α) : M α := do
  let outer := (← get).curSite
  modify fun s => { s with curSite := some site }
  let r ← act
  modify fun s => { s with curSite := outer }
  pure r

def indexed (names : List String) (base : Nat) : Scope :=
  (names.zip (List.range names.length)).map fun (x, k) => (x, .var (base + k))

def labelName (l : String) : String := "@" ++ l

/-- A mutable variable `x` is in scope under this key, bound to its cell. -/
def cellKey (x : String) : String := "&" ++ x

/-- The nearest binding of `x`: whether it is a mutable variable, the key it is
in scope under, and its value or cell. -/
def lookupVar (scope : Scope) (x : String) : Option (Bool × String × Atom) :=
  scope.findSome? fun (k, a) =>
    if k == x then some (false, k, a)
    else if k == cellKey x then some (true, k, a)
    else none

/-- The scope keys a callable must capture for the names free in it. -/
def captureNames (scope : Scope) (free : List String) : List String :=
  (free.filterMap fun x => (lookupVar scope x).map (·.2.1)).eraseDups

def sameAtom : Atom → Atom → Bool
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
def madeFrom (tracked : List String) (s : Stmt) : List String :=
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

/-- Is this the name of a borrow the elaborator made before a statement that
had it written in it? Such a `let p = &x` is a scope, and not a place of its
own: the statement was the place. -/
def madeBorrow (p : String) : Bool :=
  p.startsWith "%lend" || p.startsWith "%held" || p.startsWith "%borrow"

/-- A statement's expression with what is worked out before its first borrow
is used taken out and named, in the order it is worked out: so that a borrow
made a scope around the statement does not last while that runs, which may
read the variable borrowed. (`a[len(a) - 1] = v`.)

Only what comes first can be taken out without changing the order: once a
call that is given a borrow has run, what follows stays where it is. Nothing
is taken out of what a handler watches: it would then run unwatched. -/
partial def pullFirst (site : Nat) (isCell : String → Bool) (e : Expr) :
    Expr × List (String × Expr) :=
  let (e, pulled, _) := go e [] true
  (e, pulled.reverse)
where
  has : Expr → Bool
    | .name none n => madeBorrow n
    | .call _ f args => has f || args.any has
    | .tuple args => args.any has
    | .deref e => has e
    | .proj e _ => has e
    | .handle subject _ => has subject
    | _ => false
  /-- Is it worked out at all: not a number, a callable written out, or a
  name that is not a variable's. -/
  worth : Expr → Bool
    | .int _ => false
    | .closure _ _ => false
    | .label _ => false
    | .name none n => isCell n
    | .name (some _) _ => false
    | _ => true
  operand (e : Expr) (pulled : List (String × Expr)) (first : Bool) :
      Expr × List (String × Expr) × Bool :=
    if has e then go e pulled first
    else if first && worth e then
      let n := s!"%pre{site}.{pulled.length}"
      (.name none n, (n, e) :: pulled, first)
    else (e, pulled, first)
  operands (es : List Expr) (pulled : List (String × Expr)) (first : Bool) :
      List Expr × List (String × Expr) × Bool :=
    es.foldl (fun (out, pulled, first) e =>
      let (e, pulled, first) := operand e pulled first
      (out ++ [e], pulled, first)) ([], pulled, first)
  go (e : Expr) (pulled : List (String × Expr)) (first : Bool) :
      Expr × List (String × Expr) × Bool :=
    match e with
    | .call id f args =>
      let (f, pulled, first) := match f with
        | .name _ _ => (f, pulled, first)
        | _ => operand f pulled first
      let (args, pulled, _) := operands args pulled first
      -- (The call runs now: nothing after it is first.)
      (.call id f args, pulled, false)
    | .tuple args =>
      let (args, pulled, first) := operands args pulled first
      (.tuple args, pulled, first)
    | .deref e =>
      let (e, pulled, first) := operand e pulled first
      (.deref e, pulled, first)
    | .proj e n =>
      let (e, pulled, first) := operand e pulled first
      (.proj e n, pulled, first)
    | other => (other, pulled, false)

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
def splitCallOn (p : String) (site : Nat) (s : Stmt) : Option (List Stmt × Stmt) :=
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
def letNames (ss : List Stmt) : List String :=
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
    match (g.aliases.lookup name).map Syntax.aliasValue with
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

end Glorious.Elab
