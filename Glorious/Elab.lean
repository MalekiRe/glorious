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

structure Globals where
  ctors : List (String × CtorInfo) := []
  ops : List (String × OpInfo) := []
  fns : List (String × Nat) := []
  aliases : List (String × Expr) := []
  /-- The clauses of each top-level function, by name. -/
  bodies : List (String × List Clause) := []
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
   ("int_lt", .intLt, 2), ("int_eq", .intEq, 2)]

/-- Host operations by surface name: their identity and argument count. -/
def hosts : List (String × Nat × Nat) :=
  [("host_write", 0, 1), ("host_read", 1, 0)]

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
  layouts : List (Nat × Nat × List (String × Atom)) := []
  /-- Functions that are only ever given the environment of another, with how
  many values that environment has. -/
  envSizes : List (Nat × Nat) := []
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
  let s ← get
  set { s with fns := s.fns.push f, names := s.names.push name }
  pure s.fns.size

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

/-! ## How long a borrow lasts -/

private partial def unlocated : Stmt → Stmt
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
  if let some (id, n) := hosts.lookup x then return .host id n
  if x == "cancel" then return .cancel
  if x == "replace" then return .replace
  if let some e := g.aliases.lookup x then return .const e
  throw s!"unknown name `{x}`"

/-! ## Expressions -/

mutual

partial def elabExpr (scope : Scope) (tailPos : Bool) : Expr → M Atom
  | .int n =>
    if -9223372036854775808 ≤ n ∧ n ≤ 9223372036854775807 then pure (.int n)
    else throw s!"integer literal `{n}` does not fit in 64 bits"
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
  | .call _ f args => elabCall scope false f args
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

/-- A call of function `idx` some of whose arguments are borrows: each borrow,
from the first, is a scope that lasts as long as the call. The callable a scope
runs captured the arguments and is given the borrow; the innermost one makes
the call. The function is named inside it, so that the function can be used at
a type that mentions the borrows. -/
partial def lendCall (idx : Nat) (atoms : List Atom) : List (Nat × Bool) → M Atom
  | [] => do
    let callee ← emit (.let_ (.closure idx []))
    terminate (.tail callee atoms)
    pure (.int 0)
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
    emit (.lend uniq lentRef thunk)

partial def elabCall (scope : Scope) (isTail : Bool) (f : Expr) (args : List Expr) : M Atom := do
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
      emit (.let_ (.prim p atoms))
    | .host id n => do
      if isTail then throw s!"`tail` applies to calls, not to the host operation `{x}`"
      if n != args.length then
        throw s!"host operation `{x}` takes {n} arguments, but is given {args.length}"
      let atoms ← elabArgs scope args
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
    modify fun st => { st with pos := (line, col) }
    try elabStmts scope tailPos (s :: rest)
    catch e => throw (positioned line col e)
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
  let r ← emit (.lend uniq cell thunk)
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
    let layout := captures.filterMap fun x => (scope.lookup x).map fun a => (x, a)
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
  let layout := match ((← read).blocks.getD {}).links.lookup id with
    | some owner =>
      match s.layouts.lookup owner with
      | some (uid, layout) => if uid == s.b.uid then layout else []
      | none => []
    | none => []
  -- A name is shared if it still stands for the local the other block captured.
  let shared := fun (x : String) (a : Atom) =>
    match scope.lookup x with
    | some b => sameAtom a b
    | none => false
  let free := captureNames scope (fvStmts [] body)
  let taken := free.filter fun x => layout.any fun (y, a) => x == y && shared y a
  if taken.isEmpty then elabClosure scope [.mk [.wild] body]
  else
    let own := free.filter fun x => !taken.contains x
    -- The body, as a function over the other block's environment: what this
    -- block needs besides is passed to it.
    let slots := (layout.zip (List.range layout.length)).map fun ((y, a), k) =>
      if shared y a then y else s!"\x00{k}"
    let names := own ++ slots
    let tm ← withBuilder names.length do
      let r ← withNoTail none (elabStmts (indexed names 0) true body)
      finish r
    let code ← addFn ⟨[⟨own.map fun _ => .wild, tm⟩]⟩ s!"a block in `{s.owner}`"
    modify fun s => { s with envSizes := (code, layout.length) :: s.envSizes }
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
          mkClause captures ps (fun sc => elabStmts sc true body)
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
  many values that environment has. -/
  envSizes : List (Nat × Nat)
  /-- How many borrows were made scopes of their own. -/
  lent : Nat := 0
  /-- How many calls of functions with borrows written as arguments there were. -/
  sites : Nat := 0
  /-- The borrows that are not scopes of their own, in the order written. -/
  plain : List Borrow := []

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
  pure (g, fns.toList, names)

/-- A function whose body mentions its own label `@name` runs inside that label's
scope, so applying the label returns from the function. -/
private def withSelfLabel (name : String) : Clause → Clause
  | .mk pats body =>
    if (fvStmts (pats.flatMap patVars) body).contains (labelName name) then
      .mk pats [.expr (.labelScope name body)]
    else .mk pats body

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
    opNames, st.envSizes, st.lent, st.sites, st.plain.reverse⟩

end Glorious.Elab
