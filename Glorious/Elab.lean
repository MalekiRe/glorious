module

public import Glorious.Elab.Base

/-!
# Elaboration: surface syntax to Core

Resolves names, converts closures to closed functions with explicit captures,
names every intermediate result, and lowers handler arms and label scopes to
the Core forms. This pass is not proved; Core is where meaning starts.

Braces are always callables, and a clause takes exactly one argument. One
rule is directed by types, which the checker supplies: a block written without
parameters takes an argument if one is expected of it, and lets it go
(`elabGiven`).

What the checker shares with this pass is in `Glorious/Elab/Base.lean`.
-/

public section

namespace Glorious.Elab

open Syntax

/-! ## The body being elaborated -/

/-- Nodes made in the body being elaborated. -/
def ebuild {α : Type} (act : Flat.Build α) : M α :=
  modifyGet fun s =>
    let (a, b) := act.run s.body
    (a, { s with body := b })

def epush (n : Flat.FExpr) : M Flat.ExprId := ebuild (Flat.pushExpr n)
def epushS (n : Flat.FStmt) : M Flat.StmtId := ebuild (Flat.pushStmt n)
def epushC (c : Flat.FClause) : M Flat.ClauseId := ebuild (Flat.pushClause c)

/-- `act` elaborated with another body (a constant's), the one being
elaborated after as it was. -/
def withElabBody {α : Type} (b : Flat.Body) (act : M α) : M α := do
  let before := (← get).body
  modify fun s => { s with body := b }
  try
    let r ← act
    modify fun s => { s with body := before }
    pure r
  catch e =>
    modify fun s => { s with body := before }
    throw e

/-- A borrow as it is written: of a variable, or of a part of one, which is
a borrow of the variable narrowed. Whether for writing, and the variable. -/
def borrowOf (b : Flat.Body) (e : Flat.ExprId) : Option (Bool × String) :=
  match b.expr e with
  | .ref uniq y => some (uniq, y)
  | .call _ f args =>
    match b.mark? f, args[0]?.map b.expr with
    | some .focus, some (.ref uniq y) => some (uniq, y)
    | _, _ => none
  | _ => none

mutual

/-- A Core pattern and the names it binds, in binder order. -/
partial def toCorePat : Pattern → M (Core.Pat × List String)
  | .wild => pure (.wild, [])
  | .marked m _ => throw s!"`{m.shown}` in a pattern the checker passed; this is a compiler defect"
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
      match (← read).aliases[x]? with
      | some e => do toCorePat (← Syntax.exprToPat e)
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
  | swap
  | overwrite
  | readOut
  | transmute
  | const (e : Expr)

def resolveName (scope : Scope) (asked : Option String) (x : String) : M Head := do
  -- (`%prelude`: the prelude's function, whatever is named the same here.)
  let qual := if asked == some "%prelude" then none else asked
  if asked.isNone then
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
  -- (A spread whose length the copier did not find: its function in the
  -- prelude only stands for the one written out for a length,
  -- `spreadItem`.)
  if ["spread_split", "spread_cons", "spread_snoc", "spread_call"].any (fun p => x.startsWith p) && (← fnAt x).isNone then
    throw s!"a list of values is spread here (`{x}`) whose length is not known when the program is compiled"
  if let some idx ← fnAt x then return .fn idx
  if let some (p, n) := prims.lookup x then return .prim p n
  if (Syntax.scalarCast x).isSome then return .cast
  if (Syntax.packNames x).isSome then return .pack
  if let some (id, n) := hosts.lookup x then return .host id n
  if x == Syntax.foreignCall then return .host 2 0
  if x == "static_bytes" then return .host 19 0
  if x == "cancel" then return .cancel
  if x == "replace" then return .replace
  if x == "swap" then return .swap
  if x == "overwrite" then return .overwrite
  if x == "read_out" then return .readOut
  if x == "transmute" then return .transmute
  if let some e := g.aliases[x]? then return .const e
  throw s!"unknown name `{x}`"

/-! ## Expressions -/

mutual

partial def elabExpr (scope : Scope) (tailPos : Bool) (e0 : Flat.ExprId) : M Atom := do
  let b := (← get).body
  match b.expr e0 with
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
    | .swap => throw "`swap` must be called"
    | .overwrite => throw "`overwrite` must be called"
    | .readOut => throw "`read_out` must be called"
    | .transmute => throw "`transmute` must be called"
    | .const e =>
      let (cb, ce) := Flat.ofExpr e
      withElabBody cb (elabExpr [] false ce)
  | .label l =>
    match scope.lookup (labelName l) with
    | some a => pure a
    | none => throw s!"unknown label `@{l}`"
  | .tuple args => do
    let atoms ← args.toList.mapM (elabExpr scope false)
    emit (.let_ (.construct 0 atoms))
  | .proj e idx => do
    match ← elabExpr scope false e with
    | .var i => emit (.let_ (.place ⟨i, [idx]⟩))
    | .int _ => throw "an integer has no fields"
  | .call _ f args => do
    -- A value written with its type is the value: the type was the checker's.
    match b.mark? f, args with
    | some .ascribe, #[value, _] | some .inst, #[value, _] | some .move, #[value] | some .receiver, #[value] =>
      return ← elabExpr scope tailPos value
    -- A callable with what destroys what it captured if it is let go.
    | some .destroyed, #[c, d] =>
      if let (.closure _ clauses, .closure _ #[dc]) := (b.expr c, b.expr d) then
        let ⟨dps, destroy⟩ := b.clause dc
        if dps.isEmpty then return ← elabClosure scope clauses destroy.toList
    | _, _ => pure ()
    elabCall scope false f args
  | .tailCall _ f args => do
    unless tailPos do throw "`tail` call is not in tail position"
    if let some why := (← get).noTail then
      throw s!"`tail` cannot be used here: {why}"
    elabCall scope true f args
  | .closure _ clauses => elabClosure scope clauses
  | .handle subject arms => elabHandle scope tailPos subject arms
  | .mark m => throw s!"`{m.shown}` is the compiler's mark of a call, not a value"
  | .type _ => throw "a type written among expressions is no value"
  | .labelScope l body => do
    let thunk ← elabClosure scope #[← epushC ⟨[.var (labelName l)], body⟩]
    if tailPos then
      terminate (.labelTail thunk)
      pure (.int 0)
    else emit (.label thunk)
  | .ref uniq x =>
    match lookupVar scope x with
    | some (true, _, c) => pure c
    -- (One the checker let through holds a `&mut` reference: borrowed
    -- through, it is that reference.)
    | some (false, _, _) =>
      if uniq then elabExpr scope false (← epush (.name none x))
      else throw s!"`{x}` is not a mutable variable, so it cannot be borrowed"
    | none => throw s!"unknown name `{x}`"
  -- A reference borrowed from a reference is, to the machine, that reference.
  | .reborrow _ e => elabExpr scope false e
  | .refField _ _ x _ _ =>
    throw s!"a borrow of a field of `{x}` is elaborated only after the program is checked"
  | .fieldOf id e name =>
    -- A field by number needs no checker to be found.
    match name.toNat? with
    | some n => elabExpr scope tailPos (← epush (.proj e n))
    | none => throw s!"the field `{name}` is found by the checker: the program is elaborated only after it (read {id})"
  | .deref e => do
    let p ← elabExpr scope false e
    emit (.mem .load [p])

/-- The arguments of a call. A block written without parameters, where a
callable taking one argument is expected, takes that argument. -/
partial def elabArgs (scope : Scope) (args : Array Flat.ExprId) (gives : Nat → Bool := fun _ => false) :
    M (List Atom) := do
  let blocks := (← read).blocks
  (args.toList.zip (List.range args.size)).mapM fun (a, i) => do
    match (← get).body.plainBlock a with
    | some (_, body) =>
      -- (Of a checked program, the checker wrote it so where it does,
      -- `Elab.givenBody`.)
      let given := blocks.isNone && gives i
      if given then elabGiven scope body.toList else elabExpr scope false a
    | none => elabExpr scope false a

partial def elabApply (scope : Scope) (isTail : Bool) (callee : Atom) (args : Array Flat.ExprId)
    (gives : Nat → Bool := fun _ => false) : M Atom := do
  let atoms ← elabArgs scope args gives
  if isTail then
    terminate (.tail callee atoms)
    pure (.int 0)
  else emit (.call callee atoms)

partial def elabCall (scope : Scope) (isTail : Bool) (f : Flat.ExprId) (args : Array Flat.ExprId) : M Atom := do
  let b := (← get).body
  -- Whether what a reference points to was built by a constructor, at a
  -- path of field numbers: the cell is asked, and nothing is read out of it.
  -- What the clauses of a callable that binds by reference ask of the values:
  -- the checker's to read, and nothing to do.
  if b.mark? f == some .shapes then
    return ← emit (.let_ (.construct 0 []))
  if let (some mark, r :: rest) := (b.mark? f, args.toList) then
    let rest := rest.map b.expr
    -- A reference to a field of what a reference points to: the reference,
    -- one field further in at each step.
    if mark == .focus then
      let mut at_ ← elabExpr scope false r
      -- A step into one of a type's several constructors is followed by the
      -- constructor's name.
      for (step, next) in rest.zip (rest.drop 1 ++ [Flat.FExpr.int 0]) do
        if let .int i := step then
          match next with
          | .name q c =>
            match ← resolveCtor c q with
            | some info => at_ ← emit (.mem .focus [at_, .int i, .int (info.tag : Int)])
            | none => throw s!"`{c}` is not a constructor"
          | _ => at_ ← emit (.mem .focus [at_, .int i])
      return at_
    if mark == .ctorIs then
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
  match b.expr f with
  | .name q x =>
    match ← resolveName scope q x with
    | .local a => do elabApply scope isTail (← useLocal a) args
    | .cell c => do
      let callee ← emit (.mem .load [c])
      elabApply scope isTail callee args
    | .fn idx => do
      let gives := match (← read).bodies[x]? with
        | some fb => givesOne fb
        | none => fun _ => false
      let callee ← emit (.let_ (.closure idx []))
      elabApply scope isTail callee args gives
    | .ctor info => do
      if isTail then throw s!"`tail` applies to calls, not to the constructor `{x}`"
      if info.arity != args.size then
        throw s!"constructor `{x}` takes {info.arity} arguments, but is given {args.size}"
      let atoms ← elabArgs scope args
      emit (.let_ (.construct info.tag atoms))
    | .op info => do
      if isTail then throw s!"`tail` applies to calls, not to the operation `{x}`"
      if info.arity != args.size then
        throw s!"operation `{x}` takes {info.arity} arguments, but is given {args.size}"
      let atoms ← elabArgs scope args
      if info.terminal then
        terminate (.raise info.id atoms)
        pure (.int 0)
      else emit (.perform info.id atoms)
    | .prim p n => do
      if isTail then throw s!"`tail` applies to calls, not to the intrinsic `{x}`"
      -- (A `[T; N]` is its elements, built as one constructor's fields.)
      if x == "fixed_make" then
        let atoms ← elabArgs scope args
        return ← emit (.let_ (.construct (fixedBase + atoms.length) atoms))
      if n != args.size then
        throw s!"intrinsic `{x}` takes {n} arguments, but is given {args.size}"
      let atoms ← elabArgs scope args
      if x == "fixed_at" then
        -- (A place in a `[T; N]`: `-1` says so.)
        match atoms with
        | [r, i] =>
          let at_ ← match i with
            | .int _ => emit (.let_ (.atom i))
            | _ => pure i
          emit (.mem .focus [r, at_, .int (-1)])
        | _ => throw "intrinsic `fixed_at` takes 2 arguments"
      else if x == "fixed_len_at" then
        -- (The constructor that builds a `[T; N]` is the first of them and
        -- `N`.)
        let built ← emit (.mem .tag atoms)
        emit (.let_ (.prim .intSub [built, .int fixedBase]))
      else emit (.let_ (.prim p atoms))
    | .pack => do
      let atoms ← elabArgs scope args
      emit (.let_ (.construct 0 atoms))
    | .cast => do
      if isTail then throw s!"`tail` applies to calls, not to the intrinsic `{x}`"
      match ← elabArgs scope args, Syntax.scalarCast x with
      | [a], some (t, into) =>
        -- (Of so many bits, with a sign if positive: a float or a `char`
        -- as the bits it is held in.)
        emit (.let_ (.prim (.cast (Syntax.scalarBits t) into) [a]))
      | _, _ => throw s!"intrinsic `{x}` takes 1 argument, but is given {args.size}"
    | .host id n => do
      if isTail then throw s!"`tail` applies to calls, not to the host operation `{x}`"
      if n != args.size && id != 2 && id != 19 then
        throw s!"host operation `{x}` takes {n} arguments, but is given {args.size}"
      let atoms ← elabArgs scope args
      -- What is unsafe is outside what Core's rules are about.
      -- (Memory by address is the machine's, not the host's.)
      -- (Bytes the program has from its start, written out: put in its
      -- static blocks once it is elaborated, `Core.Program.internStatics`.)
      if id == 19 then
        unless atoms.all (fun a => match a with | .int b => 0 ≤ b && b < 256 | _ => false) do
          throw "`static_bytes` takes the bytes, each written out"
        return ← emit (.mem .staticAt atoms)
      match memOfHost id with
      | some .addressOf =>
        let tag := ((← read).ctors["PtrMut"]?).map (·.tag) |>.getD 0
        emit (.mem .addressOf (atoms ++ [.int tag]))
      | some .deref =>
        -- (With the pointer type's constructor, for the type it points to.)
        let tag := ((← read).ctors["PtrMut"]?).map (·.tag) |>.getD 0
        emit (.mem .deref (atoms ++ [.int tag]))
      | some op => emit (.mem op atoms)
      | none => emit (.host id atoms)
    | .cancel => do
      if isTail then throw "`tail` applies to calls, not to `cancel`"
      match args.toList with
      | [_] => do
        match ← elabArgs scope args with
        | [atom] => emit (.cancel atom)
        | _ => throw "`cancel` takes exactly one resumption"
      | _ => throw "`cancel` takes exactly one resumption"
    | .replace => do
      -- Take the value out of a cell and put another in its place.
      if isTail then throw "`tail` applies to calls, not to `replace`"
      match args.toList with
      | [_, _] => do
        match ← elabArgs scope args with
        | [cell, new] =>
          emit (.mem .swap [cell, new])
        | _ => throw "`replace` takes a reference and a value"
      | _ => throw "`replace` takes a reference and a value"
    | .swap => do
      -- What two references point to, exchanged: the second is read, put
      -- where the first points, and what was there put where it was read.
      if isTail then throw "`tail` applies to calls, not to `swap`"
      match ← elabArgs scope args with
      | [first, second] =>
        let held ← emit (.mem .load [second])
        let was ← emit (.mem .swap [first, held])
        emit (.mem .store [second, was])
      | _ => throw "`swap` takes two references"
    | .overwrite => do
      -- A value put where a reference points, what was there neither read
      -- nor given back.
      if isTail then throw "`tail` applies to calls, not to `overwrite`"
      match ← elabArgs scope args with
      | [target, value] => emit (.mem .store [target, value])
      | _ => throw "`overwrite` takes a reference and a value"
    | .readOut => do
      -- What a reference points to, read out and left there as it is.
      if isTail then throw "`tail` applies to calls, not to `read_out`"
      match ← elabArgs scope args with
      | [target] => emit (.mem .load [target])
      | _ => throw "`read_out` takes a reference"
    | .transmute => do
      -- The value as it is: only its type is another.
      if isTail then throw "`tail` applies to calls, not to `transmute`"
      match ← elabArgs scope args with
      | [a] => emit (.host 14 [a])
      | _ => throw "`transmute` takes one value"
    | .const e => do
      let (cb, ce) := Flat.ofExpr e
      let callee ← withElabBody cb (elabExpr [] false ce)
      elabApply scope isTail callee args
  | _ => do
    let callee ← elabExpr scope false f
    elabApply scope isTail callee args

/-- Statements in sequence; the value is that of the last expression, or unit. -/
partial def elabStmts (scope : Scope) (tailPos : Bool) : List Flat.StmtId → M Atom
  | [] => emit (.let_ (.construct 0 []))
  | s0 :: rest => do
  let b := (← get).body
  match b.stmt s0 with
  | .located _ _ _ => do
    -- A borrow given a name is made where it is first used.
    let sunk := sinkBorrows b (s0 :: rest)
    match sunk with
    | first :: rest =>
      match b.stmt first with
      | .located line col s =>
        modify fun st => { st with pos := (line, col) }
        try elabStmts scope tailPos (s :: rest)
        catch e => throw (positioned line col e)
      | _ => elabStmts scope tailPos sunk
    | [] => elabStmts scope tailPos sunk
  | .expr e => do
    match b.mark? e, rest with
    -- Where `unsafe { .. }` begins: nothing to do.
    | some .unsafe_, [] | some .observed, [] => emit (.let_ (.construct 0 []))
    | some .unsafe_, rest | some .observed, rest => elabStmts scope tailPos rest
    | _, [] => elabExpr scope tailPos e
    | _, rest => do
      let _ ← elabExpr scope false e
      elabStmts scope tailPos rest
  | .let_ pat value => do
    -- A borrow the front end made, of a mutable variable, before a
    -- statement is a scope of its own: how long it lasts is in its name.
    if let (.var p, some (uniq, x)) := (pat, borrowOf b value) then
      if let some (true, _, _) := lookupVar scope x then
        if madeBorrow p then
          if ← isBinder p then
            return ← elabBorrowScope scope tailPos p uniq (← elabExpr scope false value) rest
              (p.startsWith "%borrow")
    let a ← elabExpr scope false value
    let scope ← bindLet scope pat a
    elabStmts scope tailPos rest
  | .letMut x value => do
    let a ← elabExpr scope false value
    -- The rest of the block runs in the scope of the variable's cell, which is
    -- released however the block is left. It is given the cell as its argument.
    -- A `tail` call written directly in it would leave the cell's scope behind
    -- on every iteration, so it is refused.
    let why := s!"`{x}` is released after the call returns"
    let captures := captureNames scope (b.fvStmts [x] rest)
    let body ← mkClause captures [.var (cellKey x)]
      (fun sc => withNoTail (some why) (elabStmts sc true rest))
    let idx ← addFn ⟨[body]⟩ s!"the scope of `{x}` in `{(← get).owner}`"
    let captured ← (captures.filterMap (fun y => scope.lookup y)).mapM useLocal
    let thunk ← emit (.let_ (.closure idx captured))
    if tailPos then
      terminate (.cellTail a thunk)
      pure (.int 0)
    else emit (.cell a thunk)
  | .assign target value => do
    -- What is assigned through a reference is computed first, and then the
    -- place it goes: a borrow the place is reached by need not last while
    -- the value is worked out, which may read the variable it is of.
    if let .deref _ := b.expr target then
      let atomic := match b.expr value with
        | .name none _ => true
        | .int _ => true
        | _ => false
      unless atomic do
        let first ← epushS (.let_ (.var "%assigned") value)
        let then_ ← epushS (.assign target (← epush (.name none "%assigned")))
        return ← elabStmts scope tailPos (first :: then_ :: rest)
    let cell ← match b.expr target with
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
  | .defer e => do
    -- The rest of the block runs under a guard whose cleanup is `e`.
    let st ← epushS (.expr e)
    let cleanup ← elabClosure scope #[← epushC ⟨[], #[st]⟩]
    elabGuarded scope tailPos cleanup rest "a `defer` runs after the call returns"

/-- The scope of the borrow `p` the front end made: the statements it lasts
over, run by a callable given the borrow. -/
partial def elabBorrowScope (scope : Scope) (tailPos : Bool) (p : String) (uniq : Bool)
    (cell : Atom) (rest : List Flat.StmtId) (wide : Bool) : M Atom := do
  let b := (← get).body
  let k := scopeExtent b p rest wide
  let inner := rest.take k
  let after := rest.drop k
  -- If the last statement of the scope is a call whose later arguments do not
  -- mention the borrow, the scope ends before them: the arguments up to the
  -- last that does are computed first and given names.
  let split ← match inner.getLast? with
    | some last => do
      let n ← modifyGet fun s => (s.splits, { s with splits := s.splits + 1 })
      ebuild (splitCallOn p n last)
    | none => pure none
  let (inner, after) := match split with
    | some (lets, last) =>
      -- (Not where the borrow is to last as long as the statement.)
      if wide || p.startsWith "%heldw" then (inner, after) else (inner.dropLast ++ lets, last :: after)
    | none => (inner, after)
  let b := (← get).body
  let used := b.fvStmts [] after
  let out := ((letNames b inner).filter used.contains).eraseDups
  let (inner, pat) : List Flat.StmtId × Option Pattern ←
    if after.isEmpty then pure (inner, none)
    else match out with
      | [] => pure (inner ++ [← epushS (.expr (← epush (.tuple #[])))], some .wild)
      | [n] => pure (inner ++ [← epushS (.expr (← epush (.name none n)))], some (.var n))
      | ns =>
        let parts ← ns.toArray.mapM fun n => epush (.name none n)
        pure (inner ++ [← epushS (.expr (← epush (.tuple parts)))], some (.tuple (ns.map .var)))
  let why := s!"the borrow `{p}` ends after the call returns"
  let captures := captureNames scope ((← get).body.fvStmts [p] inner)
  let body ← mkClause captures [.var p] (fun sc => withNoTail (some why) (elabStmts sc true inner))
  let idx ← addFn ⟨[body]⟩ s!"the scope of the borrow `{p}` in `{(← get).owner}`"
  let captured ← (captures.filterMap (fun y => scope.lookup y)).mapM useLocal
  let thunk ← emit (.let_ (.closure idx captured))
  let r ← emit (.lend uniq cell thunk [] [])
  match pat with
  | none => pure r
  | some pat =>
    let scope ← bindLet scope pat r
    elabStmts scope tailPos after

/-- Run the rest of a block under a guard. A `tail` call written directly in
that rest would leave the guard behind on every iteration, so it is refused. -/
partial def elabGuarded (scope : Scope) (tailPos : Bool) (cleanup : Atom) (rest : List Flat.StmtId)
    (why : String) : M Atom := do
  let captures := captureNames scope ((← get).body.fvStmts [] rest)
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
  | .marked m _ => throw s!"`{m.shown}` in a pattern the checker passed; this is a compiler defect"
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
partial def elabClosure (scope : Scope) (clauses : Array Flat.ClauseId)
    (destroy : List Flat.StmtId := []) : M Atom := do
  let b := (← get).body
  let arities := clauses.toList.map fun c => (b.clause c).pats.length
  match arities with
  | [] => throw "a callable needs at least one clause"
  | n :: rest =>
    unless rest.all (· == n) do
      throw "the clauses of a callable take different numbers of arguments"
  -- (What destroys the captures may need what the function was given to
  -- know how: the callable captures that too.)
  let captures := captureNames scope (b.fvClauses clauses ++ b.fvStmts [] destroy)
  let coreClauses ← clauses.toList.mapM fun c =>
    let ⟨pats, body⟩ := b.clause c
    mkClause captures pats (fun sc => elabStmts sc true body.toList)
  let idx ← addFn ⟨coreClauses⟩ s!"a callable in `{(← get).owner}`"
  -- The function that destroys a closure of it: given what the closure
  -- captured, in order, as its arguments.
  unless destroy.isEmpty do
    let clause ← mkClause [] (captures.map Pattern.var) fun sc => elabStmts sc true destroy
    let d ← addFn ⟨[clause]⟩ s!"what destroys a callable in `{(← get).owner}`"
    modify fun s => { s with drops := (idx, d) :: s.drops }
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

/-- A block that takes an argument it does not name: the argument is let go. -/
partial def elabGiven (scope : Scope) (body : List Flat.StmtId) : M Atom := do
  elabClosure scope #[← epushC ⟨[.wild], body.toArray⟩]

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
partial def elabHandle (scope : Scope) (tailPos : Bool) (subject : Flat.ExprId) (arms : Array Flat.ClauseId) :
    M Atom := do
  let g ← read
  let st ← epushS (.expr subject)
  let thunk ← elabClosure scope #[← epushC ⟨[], #[st]⟩]
  let b := (← get).body
  let captures := captureNames scope (b.fvClauses arms)
  let mut completions : Array (Pattern × List Flat.StmtId) := #[]
  let mut opArms : Array (OpInfo × List Pattern × List Flat.StmtId) := #[]
  let mut opNames : List (Nat × String) := []
  for arm in arms do
    let ⟨pats, body⟩ := b.clause arm
    let body := body.toList
    match pats with
    | [.ctor x q ps] =>
      match g.ops.lookup x with
      | some info =>
        if let some owner := q then
          unless owner == info.owner do throw s!"`{x}` is not an operation of `{owner}`"
        opArms := opArms.push (info, ps, body)
        opNames := (info.id, x) :: opNames
      | none => completions := completions.push (.ctor x q ps, body)
    | [p] => completions := completions.push (p, body)
    | _ => throw "a handler arm has exactly one head pattern"
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
          -- (What destroys it where the arm is done, written by the
          -- elaborator, is not a use: giving it up first does that.)
          let hookOf := fun (k : String) (s : Flat.StmtId) =>
            let call := fun (e : Flat.ExprId) => match b.expr e with
              | .call id _ args => id == dropCallId && args.any (fun a => b.fvExpr [] a == [k])
              | _ => false
            match b.stmt (b.unlocated s) with
            | .defer e | .expr e => call e
            | _ => false
          let (unused, body) := match ps.getLast? with
            | some .wild => (true, body)
            | some (.var k) =>
              let real := body.filter (!hookOf k ·)
              if (b.fvStmts [] real).contains k then (false, body) else (true, real)
            | _ => (false, body)
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
  /-- What elaborating each top-level function made, where `kept` was given:
  for the next compile (`ElabKept`). -/
  made : ElabMemo := {}

/-! ## Traits

A function given implementations, of the bounds of its type parameters or of
how they are destroyed, is written out for each set of them it is given,
from `main` on (as Rust and Zig copy a generic function for each use): no
implementation is a value when the program runs. `UntraitM` writes a
function for the implementations its bounds are (`env`, by their numbers in
the pool of those known, `Copies`): a call of a trait's function is a call
of the implementation's, and a call of a function given implementations a
call of its copy for them (`askCopy`), each asked as it is written. -/

/-- A body being written out for the implementations its function is given,
with the copies asked. -/
abbrev UntraitM := StateT Flat.Body (StateM Copies)

instance : MonadLift Flat.Build UntraitM where
  monadLift x := fun b => pure (x.run b)

/-- An implementation's number, of those the function written out is given
(`env`) or known (`TraitInfo.knownOf`); none where it is given none. -/
partial def resolveDict (tr : TraitInfo) (env : Array Nat) (d : DictE) : StateM Copies (Option Nat) := do
  if let some n := tr.knownOf[addrOf d]? then return some n
  match d with
  | .param k => pure env[k]?
  | .impl fn subs =>
    let mut ids : Array Nat := #[]
    for s in subs do
      let some n ← resolveDict tr env s | return none
      ids := ids.push n
    some <$> internId fn ids.toList

/-- The call `call` of a function given the implementations `ids`: of its
copy for them, once it is known which function it is of
(`Copies.calls`). -/
def copyAt (call : Nat) (ids : List Nat) : StateM Copies Unit :=
  unless ids.isEmpty do modify fun c => { c with calls := c.calls.push (call, ids) }

/-- The function an implementation gives for the trait's function `idx`, at
what its conditions are met by: called by name, or (at the call `call`, or
asked now where none) its copy for those. -/
def methodOf (tr : TraitInfo) (env : Array Nat) (d : DictE) (idx : Nat) (call : Option Nat := none) :
    StateM Copies (Option String) := do
  let some n ← resolveDict tr env d | return none
  let some (dictFn, subs) := (← get).byId[n]? | return none
  let some (fn, _) := (tr.implsAt[dictFn]?).bind (·.methods[idx]?) | return none
  if subs.isEmpty then return some fn
  match call with
  | some c => copyAt c subs; pure (some fn)
  | none => some <$> askCopy fn subs true

/-- The function `g` at the call `call`, given the implementations `ds`:
itself, or its copy for them (`copyAt`). -/
def copyFor (tr : TraitInfo) (env : Array Nat) (call : Nat) (g : String) (ds : List DictE) : StateM Copies String := do
  let mut ids : Array Nat := #[]
  for d in ds do
    let some n ← resolveDict tr env d | return g
    ids := ids.push n
  -- (A list of values spread, `Prelude`'s `spread_split`, `spread_cons`
  -- and `spread_snoc`: written out for its length, known from how the list
  -- has `Spread`: one implementation for each of its parts.)
  if let some kind := spreadKind g then
    for i in ids do
      if let some n := spreadLength (← get).byId i 4096 then
        let name := s!"{g} of {n}"
        modify fun c => { c with spreads := c.spreads.insert name (kind, n) }
        return name
  copyAt call ids.toList
  pure g

/-- Is there a `tail` call in statements, at any depth? -/
def tailsStmts (b : Flat.Body) (body : List Flat.StmtId) : Bool :=
  body.any (b.anyStmt fun | .tailCall .. => true | _ => false)

/-- The call that destroys a value, given how its type is destroyed: the
type's function, for how its parameters are destroyed. -/
def destroyCall (tr : TraitInfo) (env : Array Nat) (d : DictE) (value : Expr) : StateM Copies Expr := do
  match ← methodOf tr env d 0 with
  | some fn =>
    -- (A callable is given up where it is.)
    if fn == Syntax.implFnName Syntax.destroyTrait Syntax.callableHead Syntax.destroyFn then
      pure (.call dropCallId (.name none "cancel") [value])
    else pure (.call dropCallId (.name none fn) [value])
  | none => pure (.call dropCallId (.name none "%undestroyed") [value])

/-- The call that destroys what `x` holds, if this is a place where that
happens and its type has something to destroy. -/
def dropHook (tr : TraitInfo) (env : Array Nat) (site : DropSite) : StateM Copies (Option Expr) := do
  match (tr.dropsAt[site]?).bind fun id => tr.dictsAt[id]? with
  | some [d] =>
    -- (A part of a name's value that nothing reads: that part.)
    some <$> destroyCall tr env d (match site.name with
      | .part x i => .proj (.name none x) i
      | n => .name none n.var)
  | _ => pure none

/-- The cleanups of the parts of a name's value that are never read, where
the name is bound at a place. -/
def partHooks (tr : TraitInfo) (env : Array Nat) (owner : String) (pos : Nat × Nat) (x : String) :
    StateM Copies (List Expr) :=
  ((tr.partsAt[(owner, pos.1, pos.2, x)]?).getD #[]).toList.filterMapM (dropHook tr env)

/-- The functions that destroy values of one type `D`, for how its parameters
are destroyed (`env`): the one that does it, given the value, and the ones
it calls of its own, each called for the same (`askCopy`), as `names` says
each is called. The type's own `Drop` runs first, if it has one, and then
each field that has something to destroy, the last declared first. -/
def destroyersOf (tr : TraitInfo) (D : Destroy) (env : Array Nat) (names : String → String) :
    StateM Copies (List Item) := do
  let unit := Expr.tuple []
  let name := fun (x : String) => Expr.name none x
  let method := Syntax.implFnName Syntax.destroyTrait D.head Syntax.destroyFn
  let blank := [(none : Option TypeExpr)]
  -- A `[T; N]`: its elements one by one, from the last.
  if let (true, [(_, [some element])]) := (D.array, D.ctors) then
    let from_ := "%destroy from " ++ D.head
    let before := Expr.call dropCallId (name "int_sub") [name "%n", .int 1]
    let length := Expr.call dropCallId (name "fixed_len") [name "%value"]
    let one ← destroyCall tr env element (.call dropCallId (name "fixed_get") [name "%value", before])
    return [Item.fnOf (names method) [] blank none
        [.mk [.var "%value"] [.expr (.call dropCallId (name (names from_)) [name "%value", length])]],
      Item.fnOf (names from_) [] (blank ++ [none]) none
        [.mk [.wild, .int 0] [.expr unit],
          .mk [.var "%value", .var "%n"]
            [.expr one, .expr (.tailCall dropCallId (name (names from_)) [name "%value", before])]]]
  let mut clauses : List Clause := []
  for (ctor, parts) in D.ctors do
    let names' := (List.range parts.length).map fun k => s!"%part{k}"
    let pats := (names'.zip parts).map fun (x, part) =>
      if part.isSome then Pattern.var x else Pattern.wild
    let mut calls : List Stmt := []
    for (x, part) in (names'.zip parts).reverse do
      if let some d := part then calls := calls ++ [.expr (← destroyCall tr env d (name x))]
    clauses := clauses ++ [Clause.mk [if ctor.isEmpty then .tuple pats else .ctor ctor none pats] (calls ++ [.expr unit])]
  -- A type with nothing inside it to look at: nothing to do.
  if clauses.isEmpty then clauses := [Clause.mk [.wild] [.expr unit]]
  -- A callable is destroyed by giving it up: a closure of a function that
  -- says how it is destroyed then destroys what it captured.
  if D.head == Syntax.callableHead then
    clauses := [Clause.mk [.var "%value"] [.expr (.call 0 (name "cancel") [name "%value"])]]
  let inner := D.ctors.any fun (_, parts) => parts.any (·.isSome)
  match D.hook with
  | some d =>
    let hook ← match ← methodOf tr env d 0 with
      | some fn => pure fn
      | none => pure "%undestroyed"
    let fields := "%fields " ++ D.head
    pure ([Item.fnOf (names method) [] blank none
        [.mk [.var "%value"]
          ([.letMut "%held" (name "%value"), .expr (.call dropCallId (name hook) [.ref true "%held"])]
            ++ (if inner then [.expr (.call dropCallId (name (names fields)) [name "%held"])]
                else [.expr unit]))]]
      ++ (if inner then [Item.fnOf (names fields) [] blank none clauses] else []))
  | none => pure [Item.fnOf (names method) [] blank none clauses]

mutual

/-- Patterns with each `_` whose number `named` picks written as a name,
`name k` (`wildName`, or `letWildName` in a `let`'s pattern): the `_` are
numbered in the order they are read, from `k`. Gives the number after the
last. -/
partial def nameWilds (named : Nat → Bool) (name : Nat → String) : List Pattern → Nat → List Pattern × Nat
  | [], k => ([], k)
  | p :: rest, k =>
    let (p, k) := nameWild named name p k
    let (rest, k) := nameWilds named name rest k
    (p :: rest, k)

partial def nameWild (named : Nat → Bool) (name : Nat → String) : Pattern → Nat → Pattern × Nat
  | .wild, k => (if named k then .var (name k) else .wild, k + 1)
  | .tuple ps, k =>
    let (ps, k) := nameWilds named name ps k
    (.tuple ps, k)
  | .ctor c q ps, k =>
    let (ps, k) := nameWilds named name ps k
    (.ctor c q ps, k)
  | p, k => (p, k)

end

/-- Every use of a variable's value marked: the flag is set, and then the
value read. So is each read of a part of it with something to destroy
(`SiteName.taken`, `taken`), which takes it out and lets go of the rest. -/
def markMoves (x : String) (taken : Nat → Bool) : Flat.FRewrite where
  onExpr _ b e :=
    match b.expr e with
    | .name none y =>
      if y == x then some (Flat.flatExpr (.labelScope "%block"
        [.assign (.name none (Syntax.movedFlag x)) (.int 1), .expr (.name none x)]))
      else none
    | .proj e' _ | .fieldOf _ e' _ =>
      if b.placeRoot e' != some x then none
      -- (`x.a.b`: the part read of `x` is `x.a`.)
      else if b.bare? e' != some x then none
      else if !taken (b.idOf e) then some (pure e)
      else some (do
        let flag ← Flat.pushExpr (.name none (Syntax.movedFlag x))
        let set ← Flat.pushStmt (.assign flag (← Flat.pushExpr (.int 1)))
        let read ← Flat.pushStmt (.expr e)
        Flat.pushExpr (.labelScope "%block" #[set, read]))
    | _ => none
  onStmt go b s :=
    match b.stmt s with
    | .assign target e => some (do Flat.pushStmt (.assign target (← go.ex e)))
    | _ => none

/-- Where the checker says a name's value is given away on some path and not
on another (`SiteName.given`, at `pos`): `rest` with a flag of its own
before it, set wherever the value is used (`markMoves`), and what destroys
the value where its block is left if the flag is not set, as Rust's drop
flags do. None where it is not so. -/
def flagged (tr : TraitInfo) (env : Array Nat) (owner : String) (pos : Nat × Nat) (x : String)
    (rest : List Flat.StmtId) : UntraitM (Option (List Flat.StmtId)) := do
  let some [d] := (tr.dropsAt[(⟨owner, pos.1, pos.2, .given x, false⟩ : DropSite)]?).bind
      fun id => tr.dictsAt[id]? | return none
  let flag := Syntax.movedFlag x
  let destroy ← (destroyCall tr env d (.name none x) : StateM Copies _)
  let unless_moved := Expr.call 0 (.closure 0
    [.mk [.int 0] [.expr destroy],
     .mk [.wild] [.expr (.tuple [])]]) [.name none flag]
  let taken := fun (node : Nat) => tr.dropsAt.contains (takenSite owner node x)
  let marked ← rest.mapM fun s => ((markMoves x taken).st s : Flat.Build Flat.StmtId)
  let hook ← Flat.pushStmt (.defer (← Flat.flatExpr unless_moved))
  pure (some ((← Flat.pushStmt (.letMut flag (← Flat.pushExpr (.int 0)))) :: hook :: marked))

open Flat in
mutual

private partial def untraitExpr (tr : TraitInfo) (env : Array Nat) (owner : String) (e : ExprId) : UntraitM ExprId := do
  let b ← get
  match b.expr e with
  | .call id f args => untraitCall tr env owner id f args false
  | .tailCall id f args => untraitCall tr env owner id f args true
  | .closure id clauses => do
    -- What the callable captures is destroyed if it is let go uncalled.
    let written := b.hashClosure id clauses
    let hooks ← (b.fvClauses clauses).eraseDups.filterMapM fun x =>
      (dropHook tr env (captureDropSite owner written x) : StateM Copies _)
    let c ← pushExpr (.closure id (← clauses.mapM (untraitClause tr env owner)))
    if hooks.isEmpty then pure c
    else
      let mut stmts : Array StmtId := #[]
      for h in hooks do
        stmts := stmts.push (← pushStmt (.expr (← flatExpr h)))
      stmts := stmts.push (← pushStmt (.expr (← pushExpr (.tuple #[]))))
      let destroyer ← pushExpr (.closure 0 #[← pushClause ⟨[], stmts⟩])
      pushExpr (.call 0 (← pushExpr (.mark .destroyed)) #[c, destroyer])
  | n => do
    let n' ← n.mapIds (untraitExpr tr env owner) (untraitClause tr env owner)
      fun body => do pure (← untraitStmts tr env owner (0, 0) body.toList).toArray
    if n' == n then pure e else pushExpr n'

private partial def untraitCall (tr : TraitInfo) (env : Array Nat) (owner : String) (id : Nat) (f : ExprId)
    (args : Array ExprId) (isTail : Bool) : UntraitM ExprId := do
  let args ← args.mapM (untraitExpr tr env owner)
  let mk := fun (f : ExprId) (args : Array ExprId) =>
    (pushExpr (if isTail then .tailCall id f args else .call id f args) : UntraitM ExprId)
  match tr.dictsAt[id]?, tr.methodsAt[id]? with
  | some [d], some idx =>
    -- A trait's function: the implementation's, called by name, for what the
    -- implementation's conditions are met by.
    match ← (methodOf tr env d idx (some id) : StateM Copies _) with
    | some fn => mk (← pushExpr (.name none fn)) args
    | none => mk (← pushExpr (.name none "%unresolved")) args
  -- (A machine operation is given no implementation: it is no function.)
  | some ds, none =>
    match (← get).bare? f with
    | some g =>
      if isIntrinsic g then mk f args
      else mk (← pushExpr (.name none (← (copyFor tr env id g ds : StateM Copies _)))) args
    | none => mk (← untraitExpr tr env owner f) args
  | _, _ => mk (← untraitExpr tr env owner f) args

private partial def untraitClause (tr : TraitInfo) (env : Array Nat) (owner : String) (c : ClauseId) : UntraitM ClauseId := do
  let b ← get
  let ⟨pats, body⟩ := b.clause c
  let body := body.toList
  -- What the clause is given under a name and does not mention is
  -- destroyed when the clause is done; and so is what a `_` takes, which
  -- is given a name for it. Where the clause hands its place on with
  -- `tail`, nothing can be done after: what it does not use is destroyed
  -- before it starts, which is the cleanup a `tail` call has before it.
  let first := b.clausePlace body
  let named := tr.dropsAt
  let (pats, _) := nameWilds (fun k => named.contains ⟨owner, first.1, first.2, .name (wildName k), false⟩) wildName pats 0
  let early := tailsStmts b body
  -- (A name the clause straight away makes a variable of the same name,
  -- to be borrowed, is the variable's to destroy: the place and the name
  -- are the same for both.)
  let variables := (body.takeWhile fun s =>
    match b.stmt (b.unlocated s) with
    | .letMut y v => b.bare? v == some y
    | _ => false).filterMap fun s =>
      match b.stmt (b.unlocated s) with
      | .letMut y _ => some y
      | _ => none
  let mut found : List Expr := []
  for x in (pats.flatMap patVars).filter (!variables.contains ·) do
    found := found ++ (← (dropHook tr env ⟨owner, first.1, first.2, .name x, false⟩ : StateM Copies _)).toList
      ++ (← (partHooks tr env owner first x : StateM Copies _))
  let hooks ← found.mapM fun h => do
    let e ← flatExpr h
    pushStmt (if early then .expr e else .defer e)
  let mut rest ← untraitStmts tr env owner (0, 0) body
  -- (A name the clause binds that one path gives away and another does
  -- not: its flag where the clause starts.)
  for x in (pats.flatMap patVars).reverse do
    if let some flagged ← flagged tr env owner first x rest then rest := flagged
  pushClause ⟨pats, (hooks ++ rest).toArray⟩

/-- The statements of a block. A variable whose value is to be destroyed is
followed by a cleanup that does it when the block is left; an assignment to one
destroys what it held, once the new value is computed. -/
private partial def untraitStmts (tr : TraitInfo) (env : Array Nat) (owner : String) (pos : Nat × Nat) :
    List StmtId → UntraitM (List StmtId)
  | [] => pure []
  | s :: rest => do
    let b ← get
    let hookS := fun (h : Expr) (now : Bool) => (do
      let e ← flatExpr h
      pushStmt (if now then .expr e else .defer e) : Build StmtId)
    let hook := fun (site : DropSite) => (dropHook tr env site : StateM Copies _)
    match b.stmt s with
    | .located line col inner =>
      match ← untraitStmts tr env owner (line, col) (inner :: rest) with
      | first :: more => pure ((← pushStmt (.located line col first)) :: more)
      | [] => pure []
    | .letMut x value =>
      let value ← untraitExpr tr env owner value
      let rest ← untraitStmts tr env owner pos rest
      match ← hook ⟨owner, pos.1, pos.2, .name x, false⟩ with
      | some h => pure ((← pushStmt (.letMut x value)) :: (← hookS h false) :: rest)
      | none =>
        -- A variable that gives its value away where it is used: what it
        -- holds is destroyed when its block is left only if it was not. A
        -- flag says, set wherever the value is used.
        match ← flagged tr env owner pos x rest with
        | some flagged => pure ((← pushStmt (.letMut x value)) :: flagged)
        | none => pure ((← pushStmt (.letMut x value)) :: rest)
    | .let_ pat value =>
      let value ← untraitExpr tr env owner value
      let rest ← untraitStmts tr env owner pos rest
      -- (A value one path gives away and another does not: its flag, as a
      -- variable's.)
      let mut rest := rest
      let mut flaggedAny := false
      for x in (patVars pat).reverse do
        if let some f ← flagged tr env owner pos x rest then
          rest := f
          flaggedAny := true
      if flaggedAny then if let .var _ := pat then return (← pushStmt (.let_ pat value)) :: rest
      let (pat, hooks) ← match pat with
        | .var x => do
          pure (pat, (← hook ⟨owner, pos.1, pos.2, .name x, false⟩).toList
            ++ (← (partHooks tr env owner pos x : StateM Copies _)))
        | _ => do
          -- What the pattern takes under a name nothing uses, or under `_`
          -- (given a name for it), is destroyed likewise.
          let site := fun (x : String) => (⟨owner, pos.1, pos.2, .letBound x, false⟩ : DropSite)
          let (pats, _) := nameWilds (fun k => tr.dropsAt.contains (site (letWildName pos.1 pos.2 k)))
            (letWildName pos.1 pos.2) [pat] 0
          let pat := (pats.head?).getD pat
          let mut hooks : List Expr := []
          for x in patVars pat do
            hooks := hooks ++ (← hook (site x)).toList ++ (← (partHooks tr env owner pos x : StateM Copies _))
          pure (pat, hooks)
      -- (Before a `tail` call there is no later: see the clause's own.)
      let now := tailsStmts (← get) rest
      let hooks ← hooks.mapM fun h => hookS h now
      pure ((← pushStmt (.let_ pat value)) :: hooks ++ rest)
    | .assign target value =>
      let value ← untraitExpr tr env owner value
      let target ← untraitExpr tr env owner target
      let rest ← untraitStmts tr env owner pos rest
      let b ← get
      match b.expr target with
      | .name none x =>
        match ← hook ⟨owner, pos.1, pos.2, .name x, true⟩ with
        | some h =>
          pure ((← pushStmt (.let_ (.var "%assigned") value)) :: (← hookS h true)
            :: (← pushStmt (.assign target (← pushExpr (.name none "%assigned")))) :: rest)
        | none => pure ((← pushStmt (.assign target value)) :: rest)
      | .deref place =>
        -- What was there where the reference points is destroyed, once the new
        -- value is made and the place found.
        match (tr.dropsAt[(⟨owner, pos.1, pos.2, .deref, true⟩ : DropSite)]?).bind fun id => tr.dictsAt[id]? with
        | some [d] =>
          let first ← pushStmt (.let_ (.var "%assigned") value)
          let second ← pushStmt (.let_ (.var "%place") place)
          let destroy ← hookS (← (destroyCall tr env d (.deref (.name none "%place")) : StateM Copies _)) true
          let placeRef ← pushExpr (.deref (← pushExpr (.name none "%place")))
          let last ← pushStmt (.assign placeRef (← pushExpr (.name none "%assigned")))
          pure (first :: second :: destroy :: last :: rest)
        | _ => pure ((← pushStmt (.assign target value)) :: rest)
      | _ => pure ((← pushStmt (.assign target value)) :: rest)
    | .expr e =>
      let e ← untraitExpr tr env owner e
      let rest ← untraitStmts tr env owner pos rest
      -- A value nothing takes, of a type to destroy, is destroyed there.
      match ← (if rest.isEmpty then pure none else hook ⟨owner, pos.1, pos.2, .name stmtValue, false⟩) with
      | some h => pure ((← pushStmt (.let_ (.var stmtValue) e)) :: (← hookS h true) :: rest)
      | none => pure ((← pushStmt (.expr e)) :: rest)
    | .defer e =>
      let e ← untraitExpr tr env owner e
      pure ((← pushStmt (.defer e)) :: (← untraitStmts tr env owner pos rest))

end

/-- Does an expression name the label `l`? -/
partial def namesLabel (b : Flat.Body) (l : String) (e : Flat.ExprId) : Bool :=
  match b.expr e with
  | .label x => x == l
  | .labelScope x body => x != l && body.any fun s => (b.stmtExprs s).any (namesLabel b l)
  | _ => (b.children e).any (namesLabel b l)

/-- A function written out for the implementations it is given (`env`):
without traits, each call of a trait's function a call of the
implementation's, each call of a function given implementations one of its
copy. -/
def untraitFn (tr : TraitInfo) (env : Array Nat) (name : String) (params : List String)
    (annots : List (Option TypeExpr)) (ret : Option TypeExpr) (b : Flat.Body) : StateM Copies Syntax.Item := do
  let ((roots, b) : Array Flat.ClauseId × Flat.Body) ← (b.roots.mapM (untraitClause tr env name)).run b
  -- (Every node is made anew: what was there is reached by nothing.)
  pure (Syntax.Item.fn name params annots ret { b with roots }.compact)

/-- A function's calls of copies (`Copies.calls`) written as calls of them,
of the function each calls as it is now named (a copy for an effect's
instance, `name@<..>`, where it is one). -/
def callsCopied (calls : Std.HashMap Nat (List Nat)) : Syntax.Item → StateM Copies Syntax.Item
  | .fn name ps annots ret b => do
    if calls.isEmpty then return .fn name ps annots ret b
    let mut b := b
    for i in [0:b.exprs.size] do
      match b.exprs[i]! with
      | .call c f args | .tailCall c f args =>
        if let some ids := calls[c]? then
          if let some g := b.bare? f then
            let copy ← askCopy g ids true
            let (fe, b') := b.add (.name none copy)
            b := { b' with exprs := b'.exprs.set! i (match b'.exprs[i]! with
              | .tailCall .. => .tailCall c fe args
              | _ => .call c fe args) }
      | _ => pure ()
    pure (.fn name ps annots ret b)
  | item => pure item

/-- A function under the name of a copy of it, `as`: a body that leaves by
the function's label, `@find(..)`, given that label, as the copy's name is
another. -/
def renamed (as : String) : Syntax.Item → Syntax.Item
  | .fn name ps annots ret b =>
    if as == name then .fn name ps annots ret b else
    let (roots, b) := (b.roots.mapM fun c => (do
      let ⟨pats, body⟩ := (← get).clause c
      let b ← get
      if !body.any (fun s => (b.stmtExprs s).any (namesLabel b name)) then return c
      let scope ← Flat.pushExpr (.labelScope name body)
      Flat.pushClause ⟨pats, #[← Flat.pushStmt (.expr scope)]⟩ : Flat.Build Flat.ClauseId)).run b
    .fn as ps annots ret { b with roots }
  | item => item

/-- What an item is without traits: the functions it is made into, each by
its name and made only when asked, for the implementations it is given
(`fn`), or an item kept as it is (`item`). A trait is nothing; an
implementation its functions. -/
inductive Untraited where
  | fn (name : String) (make : Array Nat → StateM Copies Syntax.Item)
  | item (item : Syntax.Item)

/-- An item without traits (`Untraited`). -/
def untraitItem (tr : TraitInfo) : Syntax.Item → List Untraited
  | (.trait _ _) => []
  | .impl { params := params, trait := trait, head := head, methods := methods, .. } =>
    methods.filterMap fun
      | .fn m _ annots ret b =>
        let name := implFnName trait.spelled head m
        some (Untraited.fn name fun env => untraitFn tr env name params annots ret b)
      | _ => none
  | .fn name params annots ret b => [.fn name fun env => untraitFn tr env name params annots ret b]
  | item => [.item item]

/-- The functions a program without traits has besides its items': each
destroyer, made for how the type's parameters are destroyed. -/
def untraitExtra (tr : TraitInfo) : List Untraited :=
  tr.destroys.flatMap fun D =>
    let method := Syntax.implFnName Syntax.destroyTrait D.head Syntax.destroyFn
    let own := [method, "%destroy from " ++ D.head, "%fields " ++ D.head]
    own.map fun n => .fn n fun env => do
      -- (The others it calls, each for the same, as the copier names them.)
      let mut names : Std.HashMap String String := {}
      for o in own do
        let called ← if env.isEmpty then pure o else askCopy o env.toList true
        names := names.insert o called
      let items ← destroyersOf tr D env (fun o => names.getD o o)
      -- (Under its own name, as any function is made: named as the copy it
      -- is asked by after, `renamed`.)
      let mine := names.getD n n
      pure (match items.find? fun | .fn m .. => m == mine | _ => false with
        | some (.fn _ ps annots ret b) => .fn n ps annots ret b
        | _ => Item.fnOf n [] [] none [])

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
  | .ref uniq t _ => .ref uniq (eraseLifetimesTy t) none
  | t => t.mapParts eraseLifetimesTy

partial def eraseLifetimes (items : List Syntax.Item) : List Syntax.Item :=
  let params := fun (ps : List String) => ps.filter fun p => !p.startsWith "'"
  items.map fun
    | (.enum name ps ctors) =>
      (.enum name (params ps) (ctors.map fun (c, fields) => (c, fields.map eraseLifetimesTy)))
    | (.struct name ps fields) => (.struct name (params ps) (fields.map eraseLifetimesTy))
    | (.effect name ps ops) =>
      (.effect name (params ps) (ops.map fun op =>
        { op with payload := op.payload.map eraseLifetimesTy,
                  result := op.result.map eraseLifetimesTy }))
    | .fn name ps annots ret b =>
      .fn name (params ps) (annots.map (·.map eraseLifetimesTy)) (ret.map eraseLifetimesTy) b
    | (.trait name methods) =>
      (.trait name (methods.map fun md =>
        { md with params := md.params.map eraseLifetimesTy, ret := md.ret.map eraseLifetimesTy }))
    | .impl whole@{ params := ps, args := args, methods := methods, .. } =>
      .impl { whole with params := (params ps), args := (params args), methods := (eraseLifetimes methods) }
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


/-- A function that never comes back, for the case that cannot be. -/
def neverName : String := "%never"

/-- Collect the global declarations. -/
def collect (items : List Syntax.Item) :
    Except String (Globals × List (String × Flat.Body) × Array String) := do
  let mut g : Globals := {}
  let mut fns : Array (String × Flat.Body) := #[]
  let mut names : Array String := #["tuple"]
  let mut nextOp := 0
  for fitem in items do
    match fitem with
    | .fn name _ _ _ body =>
      if g.fns.contains name then throw s!"function `{name}` is declared twice"
      g := { g with fns := g.fns.insert name fns.size, bodies := g.bodies.insert name body }
      fns := fns.push (name, body)
    | .alias name b e => g := { g with aliases := g.aliases.insert name (Flat.treeExpr b e) }
    | .pub _ _ | .traitInfo .. | .module .. => pure ()
    | .impl { trait := tr, .. } =>
      throw s!"an implementation of `{tr}`: a program with traits is elaborated only after it is checked"
    | item =>
    match item with
    | .enum owner _ ctors =>
      for (c, fields) in ctors do
        if g.ctors.contains c then throw s!"constructor `{c}` is declared twice"
        g := { g with
          ctors := g.ctors.insert c ⟨owner, names.size, fields.length, ctors.length == 1⟩ }
        names := names.push c
    | .struct owner _ fields =>
      if g.ctors.contains owner then throw s!"constructor `{owner}` is declared twice"
      g := { g with ctors := g.ctors.insert owner ⟨owner, names.size, fields.length, true⟩ }
      names := names.push owner
    | .effect owner _ ops =>
      for op in ops do
        if (g.ops.lookup op.name).isSome then
          throw s!"operation `{op.name}` is declared twice"
        g := { g with
          ops := (op.name, ⟨owner, nextOp, op.payload.length, op.terminal⟩) :: g.ops }
        nextOp := nextOp + 1
    | .fixity | .fn .. | .alias .. => pure ()
    | .coerce _ => pure ()
    -- How often a value is to be used is the checker's business.
    | .use _ _ _ => pure ()
    -- So are the names of fields, and by now every field is a number.
    | .fieldNames _ _ _ => pure ()
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
    | .impl { trait := tr, .. } =>
      throw s!"an implementation of `{tr}`: a program with traits is elaborated only after it is checked"
  pure (g, fns.toList, names)

/-- Items as what they declare, for what reads declarations alone (the
certificate): each function without its body. -/
def declaredOf (items : List Syntax.Item) : List Item := items.map Item.declared

/-- What items declare, for what reads declarations alone (the certificate). -/
def collectDeclared (items : List Item) : Except String Globals := do
  pure (← collect (declaredOf items)).1

/-- A function whose body mentions its own label `@name` runs inside that label's
scope, so applying the label returns from the function. -/
private def withSelfLabel (name : String) (b : Flat.Body) : Flat.Body := Id.run do
  let short := Syntax.labelShort name
  let (roots, b) := (b.roots.mapM fun c => (do
      let b ← get
      let ⟨pats, body⟩ := b.clause c
      let free := b.fvStmts (pats.flatMap patVars) body.toList
      let wrap := fun (l : String) => (do
        let scope ← Flat.pushExpr (.labelScope l body)
        let st ← Flat.pushStmt (.expr scope)
        Flat.pushClause ⟨pats, #[st]⟩ : Flat.Build Flat.ClauseId)
      if free.contains (labelName name) then wrap name
      -- (`@f` of `m::f` or `T::f`.)
      else if short != name && free.contains (labelName short) then wrap short
      else pure c : Flat.Build Flat.ClauseId)).run b
  pure { b with roots }

/-- The program without the functions nothing reaches from `main` or from a
coercion, which a call may be given without its being written. -/
def reachable (roots : List String) (items : List Syntax.Item) : List Syntax.Item := Id.run do
  -- The function for a case that cannot be, if something is written with it
  -- and it is not yet there.
  let defined := items.any fun
    | .fn name _ _ _ _ => name == neverName
    | _ => false
  let wanted := items.any fun
    | .fn _ _ _ _ b => (b.fvClauses b.roots).contains neverName
    | _ => false
  let items := if wanted && !defined then
      Syntax.Item.fn neverName [] [] none (Flat.ofClauses [.mk [] [.expr (.tailCall 0 (.name none neverName) [])]]) :: items
    else items
  let bodies : Std.HashMap String (List String) := items.foldl (init := {}) fun acc item =>
    match item with
    | .fn name _ _ _ b =>
      acc.insert name ((acc.getD name []) ++ b.fvClauses b.roots)
    -- (A name for an expression, a constant's: what the expression uses.)
    | .alias name b e => acc.insert name ((acc.getD name []) ++ b.fvExpr [] e)
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
def elabProgram (items : List Syntax.Item) (blocks : Option Blocks := none)
    (root : String := "main") (kept : Option ElabMemo := none) :
    Except String Output := do
  let (g, fns, names) ← collect items
  let g := { g with blocks := blocks }
  let mainIdx ← match g.fns[root]? with
    | some idx => pure idx
    | none => throw s!"the program has no `{root}` function"
  -- (Each function as an earlier compile elaborated it, `kept`, where it was
  -- elaborated from the same: its body, what the program declares, where
  -- each count stood; and what it read of the rest is as it was. Only where
  -- the checker ran: without it, what a callee's body gives is read too.)
  let memo := if blocks.isSome then kept else none
  let declKey := if memo.isSome then hash (items.filter fun
      | .fn .. => false
      | _ => true) else 0
  let action : M ElabMemo := do
    let mut idx := 0
    let mut made : ElabMemo := {}
    for (name, b) in fns do
      let arities := b.roots.toList.map fun c => (b.clause c).pats.length
      match arities with
      | [] => throw s!"function `{name}` has no clauses"
      | n :: rest =>
        unless rest.all (· == n) do
          throw s!"the clauses of `{name}` take different numbers of arguments"
      let b := withSelfLabel name b
      -- (Where each part stood, not the state: held, its arrays would be
      -- copied by what is added to them.)
      let (nFns, nNames, pos0, noTail0, drops0) ← do
        let s ← get
        pure (s.fns.size, s.names.size, s.pos, s.noTail, s.drops)
      let key := if memo.isNone then 0 else
        mixHash (hash (name, b, declKey)) (hash (nFns, nNames, pos0, noTail0))
      let taken ← match (memo.getD {})[name]? with
        | some k =>
          if k.key == key && key != 0 then do
            if ← k.reads.allM readHolds then
              -- (Each array taken out of the state before it grows: held by
              -- the state too, it would be copied.)
              modify fun s =>
                let (fns, names) := (s.fns, s.names)
                let s := { s with fns := #[], names := #[] }
                { s with
                  fns := (fns.set! idx ⟨k.clauses⟩) ++ k.fns, names := names ++ k.names
                  drops := k.drops ++ s.drops, pos := k.pos }
              pure (some k)
            else pure none
          else pure none
        | none => pure none
      match taken with
      | some k => made := made.insert name k
      | none =>
        modify fun s => { s with owner := name, body := b, reads := #[], splits := 0 }
        let coreClauses ← b.roots.toList.mapM fun c =>
          let ⟨pats, body⟩ := b.clause c
          mkClause [] pats (fun sc => elabStmts sc true body.toList)
        modify fun s => { s with fns := s.fns.set! idx ⟨coreClauses⟩ }
        if memo.isSome then
          let s ← get
          if let some drops := prefixTo s.drops drops0 then
            if s.noTail == noTail0 then
              made := made.insert name
                { key, reads := s.reads, clauses := coreClauses
                  fns := s.fns.extract nFns s.fns.size, names := s.names.extract nNames s.names.size
                  drops, pos := s.pos }
      idx := idx + 1
    pure made
  let fnNames := (fns.map fun (name, _) => s!"`{name}`").toArray
  let init : St :=
    { fns := Array.replicate fns.length ⟨[]⟩
      names := fnNames, owner := ""
      b := { ops := #[], depth := 0, done := none }, noTail := none }
  let (made, st) ← (action.run g).run init
  let opNames := Id.run do
    let mut out := Array.replicate g.ops.length ""
    for (name, info) in g.ops do
      out := out.set! info.id name
    pure out
  pure ⟨⟨st.fns, .let_ (.closure mainIdx []) (.tail (.var 0) []), st.drops.reverse, fns.toArray.map (·.1), []⟩, names, st.names,
    opNames, made⟩

end Glorious.Elab
