module

public import Glorious.Elab.Base

/-!
# Elaboration: surface syntax to Core

Resolves names, converts closures to closed functions with explicit captures,
names every intermediate result, and lowers handler arms and label scopes to
the Core forms. This pass is not proved; Core is where meaning starts.

Braces are always callables, and a clause takes exactly one argument. One
rule is directed by types, which the checker supplies: a block written without
parameters takes an argument if one is expected of it, and if that argument is
a block that was not run, it runs in that block's environment (`elabGiven`).

What the checker shares with this pass is in `Glorious/Elab/Base.lean`.
-/

public section

namespace Glorious.Elab

open Syntax

/-- A borrow as it is written: of a variable, or of a part of one, which is
a borrow of the variable narrowed. Whether for writing, and the variable. -/
def borrowOf : Expr → Option (Bool × String)
  | .ref uniq y => some (uniq, y)
  | .call _ (.name none mark) (.ref uniq y :: _) =>
    if mark == Syntax.focusMark then some (uniq, y) else none
  | _ => none

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
  | swap
  | overwrite
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
  if x == "swap" then return .swap
  if x == "overwrite" then return .overwrite
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
    | .swap => throw "`swap` must be called"
    | .overwrite => throw "`overwrite` must be called"
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
      -- A step into one of a type's several constructors is followed by the
      -- constructor's name.
      for (step, next) in rest.zip (rest.drop 1 ++ [.int 0]) do
        if let .int i := step then
          match next with
          | .name q c =>
            match ← resolveCtor c q with
            | some info => at_ ← emit (.mem .focus [at_, .int i, .int (info.tag : Int)])
            | none => throw s!"`{c}` is not a constructor"
          | _ => at_ ← emit (.mem .focus [at_, .int i])
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
        (borrowOf a).map fun (uniq, _) => (i, uniq)
      let site := (← get).sites
      if !isTail && !borrows.isEmpty then modify fun s => { s with sites := s.sites + 1 }
      if !isTail && !borrows.isEmpty && (← read).lends site != 0 then
        let atoms ← elabArgs scope args gives
        -- These borrows are scopes: take back what elaborating them noted.
        for a in args do
          if let some (uniq, y) := borrowOf a then
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
    if let (.var p, some (uniq, x)) := (pat, borrowOf value) then
      if let some (true, _, _) := lookupVar scope x then
        if ← isBinder p then
          -- What is lent: the variable's reference, narrowed if the borrow
          -- is of a part. It is a scope, so it is not noted as one that is not.
          let lent := do
            let c ← elabExpr scope false value
            modify fun s =>
              { s with plain := s.plain.erase ⟨s.owner, s.pos.1, s.pos.2, x, uniq⟩ }
            pure c
          if (← get).hoisted != 0 then
            modify fun s => { s with hoisted := s.hoisted - 1 }
            return ← elabBorrowScope scope tailPos p uniq (← lent) rest true
          let site := (← get).sites
          modify fun s => { s with sites := s.sites + 1 }
          let mode := (← read).lends site
          if mode != 0 then
            return ← elabBorrowScope scope tailPos p uniq (← lent) rest (mode == 2)
    -- So can the borrows given to a function whose result is given a name,
    -- lasting while the result is used: each is named first.
    if let .call id (.name q f) args := value then
      let borrows := args.filter fun a => (borrowOf a).isSome
      if !borrows.isEmpty && (← read).lends (← get).sites == 2 then
        if let .fn _ ← resolveName scope q f then
          let site := (← get).sites
          let named := (args.zip (List.range args.length)).map fun (a, i) =>
            match borrowOf a with
            | some _ => (Expr.name none s!"%borrow{site}.{i}", some (i, a))
            | none => (a, none)
          let lets := named.filterMap fun (_, b) =>
            b.map fun (i, a) => Stmt.let_ (.var s!"%borrow{site}.{i}") a
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
        let lets := found.map fun (n, a) => Stmt.let_ (.var n) a
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
    M (Expr × List (String × Expr)) := do
  let (e, found) ← go e []
  pure (e, found.reverse)
where
  go (e : Expr) (found : List (String × Expr)) :
      M (Expr × List (String × Expr)) := do
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
  goArgs (args : List Expr) (found : List (String × Expr)) :
      M (List Expr × List (String × Expr)) := do
    let mut out : Array Expr := #[]
    let mut found := found
    for a in args do
      match borrowOf a with
      | some (_, y) =>
        if let some (true, _, _) := lookupVar scope y then
          let n := s!"%borrow{site}.{found.length}"
          out := out.push (.name none n)
          found := (n, a) :: found
        else out := out.push a
      | none =>
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

mutual

/-- Is there a `tail` call in an expression, at any depth? -/
partial def tailsExpr : Expr → Bool
  | .tailCall _ _ _ => true
  | .call _ f args => tailsExpr f || args.any tailsExpr
  | .tuple args => args.any tailsExpr
  | .proj e _ => tailsExpr e
  | .deref e => tailsExpr e
  | .reborrow _ e => tailsExpr e
  | .fieldOf _ e _ => tailsExpr e
  | .closure _ clauses => clauses.any fun
    | .mk _ body => tailsStmts body
  | .handle subject arms => tailsExpr subject || arms.any fun
    | .mk _ body => tailsStmts body
  | .labelScope _ body => tailsStmts body
  | _ => false

partial def tailsStmts (body : List Stmt) : Bool :=
  body.any fun s =>
    let rec one : Stmt → Bool
      | .let_ _ e => tailsExpr e
      | .letMut _ e => tailsExpr e
      | .expr e => tailsExpr e
      | .defer e => tailsExpr e
      | .located _ _ s => one s
      | .assign target e => tailsExpr target || tailsExpr e
    one s

end

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
  | some [d] =>
    -- (A part of a name's value that nothing reads: that part.)
    some (destroyCall tr d (match Syntax.partOf site.name with
      | some (x, i) => .proj (.name none x) i
      | none => .name none site.name))
  | _ => none

/-- The cleanups of the parts of a name's value that are never read, where
the name is bound at a place. -/
private def partHooks (tr : TraitInfo) (owner : String) (pos : Nat × Nat) (x : String) : List Expr :=
  tr.drops.filterMap fun (site, _) =>
    if site.owner == owner && site.line == pos.1 && site.col == pos.2 && !site.assign
        && (Syntax.partOf site.name).map (·.1) == some x then dropHook tr site
    else none

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
    -- is given a name for it. Where the clause hands its place on with
    -- `tail`, nothing can be done after: what it does not use is destroyed
    -- before it starts, which is the cleanup a `tail` call has before it.
    let first := firstPlace body
    let (pats, _) := nameWilds (fun k => (dropHook tr ⟨owner, first.1, first.2, wildName k, false⟩).isSome) pats 0
    let early := tailsStmts body
    -- (A name the clause straight away makes a variable of the same name,
    -- to be borrowed, is the variable's to destroy: the place and the name
    -- are the same for both.)
    let variables := (body.takeWhile fun s =>
      match unlocated s with
      | .letMut y (.name none y') => y == y'
      | _ => false).filterMap fun s =>
        match unlocated s with
        | .letMut y _ => some y
        | _ => none
    let hooks := ((pats.flatMap patVars).filter (!variables.contains ·)).flatMap fun x =>
      ((dropHook tr ⟨owner, first.1, first.2, x, false⟩).toList ++ partHooks tr owner first x).map
        (if early then Stmt.expr else Stmt.defer)
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
    | none =>
      -- A variable that gives its value away where it is used: what it
      -- holds is destroyed when its block is left only if it was not. A
      -- flag says, set wherever the value is used.
      match (tr.drops.lookup ⟨owner, pos.1, pos.2, Syntax.givenSite x, false⟩).bind
          fun id => tr.dicts.lookup id with
      | some [d] =>
        let flag := Syntax.movedFlag x
        let unless_moved := Expr.call 0 (.closure 0
          [.mk [.int 0] [.expr (destroyCall tr d (.name none x))],
           .mk [.wild] [.expr (.tuple [])]]) [.name none flag]
        .letMut x value :: .letMut flag (.int 0) :: .defer unless_moved
          :: Syntax.markMovesStmts x rest
      | _ => .letMut x value :: rest
  | .let_ pat value :: rest =>
    let value := untraitExpr tr owner value
    let rest := untraitStmts tr owner pos rest
    match pat with
    | .var x =>
      let hooks := (dropHook tr ⟨owner, pos.1, pos.2, x, false⟩).toList ++ partHooks tr owner pos x
      -- (Before a `tail` call there is no later: see the clause's own.)
      .let_ pat value :: hooks.map (if tailsStmts rest then Stmt.expr else Stmt.defer) ++ rest
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
    | .deref place =>
      -- What was where the reference points is destroyed, once the new
      -- value is made and the place found.
      match (tr.drops.lookup ⟨owner, pos.1, pos.2, derefSite, true⟩).bind fun id => tr.dicts.lookup id with
      | some [d] =>
        .let_ (.var "%assigned") value :: .let_ (.var "%place") place
          :: .expr (destroyCall tr d (.deref (.name none "%place")))
          :: .assign (.deref (.name none "%place")) (.name none "%assigned") :: rest
      | _ => .assign target value :: rest
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

A reference can be to a part of what a variable holds: the machine narrows a
reference to a field of what it points to (`focus`). So a borrow of a field,
`&mut x.0`, is a borrow of `x` narrowed to the field, and one of a field of
what a reference points to is that reference narrowed. The field stays where
it is: nothing is copied out to be lent and put back after, so nothing reads
an old copy. The checker says, for each borrow, what is gone through to
reach the field.
-/

/-- A function that never comes back, for the case that cannot be. -/
def neverName : String := "%never"

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
fields in them written out, each where it is written. -/
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
    .handle (unfieldExpr info subject) (arms.map (unfieldClause info))
  | .refField id uniq x way star =>
    match info.shapes.lookup id with
    | none => .refField id uniq x way star
    | some (viaRef, path, shape) =>
      -- A step into one of a type's several constructors is followed by
      -- the constructor's name.
      let steps := (path.zip (shape ++ path.map fun _ => (none, 0))).flatMap fun (n, c, _) =>
        match c with
        | some c =>
          if c.startsWith "#" then [Expr.int (Int.ofNat n), .name none (c.drop 1).toString]
          else [Expr.int (Int.ofNat n)]
        | none => [Expr.int (Int.ofNat n)]
      -- Of what a reference points to, that reference; of a variable, a
      -- borrow of the variable.
      .call 0 (.name none Syntax.focusMark) ((if viaRef then .name none x else .ref uniq x) :: steps)
  | e => e

private partial def unfieldClause (info : FieldInfo) : Clause → Clause
  | .mk pats body => .mk pats (unfieldStmts info body)

private partial def unfieldStmt (info : FieldInfo) : Stmt → Stmt
  | .expr e => .expr (unfieldExpr info e)
  | .let_ pat e => .let_ pat (unfieldExpr info e)
  | .letMut y e => .letMut y (unfieldExpr info e)
  | .assign target e => .assign (unfieldExpr info target) (unfieldExpr info e)
  | .defer e => .defer (unfieldExpr info e)
  | .located line col s => .located line col (unfieldStmt info s)

private partial def unfieldStmts (info : FieldInfo) (stmts : List Stmt) : List Stmt :=
  stmts.map (unfieldStmt info)

end

/-- Write out every borrow of a field, and every field read by name: see
above. What the checker found says how. -/
def unfield (b : Blocks) (items : List Item) : Except String (List Item) := do
  if b.fields.isEmpty && b.fieldReads.isEmpty && b.packs.isEmpty && b.envFns.isEmpty then
    return items
  pure (items.map fun
    | .fn name params annots ret clauses =>
      -- Each callable that does not hold its environment, with the one that does.
      let members := ((b.envFns.lookup name).getD []).flatMap fun group =>
        match group with
        | holder :: rest => rest.map (·, holder)
        | [] => []
      let info : FieldInfo :=
        { shapes := b.fields
          reads := b.fieldReads
          packs := b.packs
          members := members
          wraps := b.envWraps
          derefs := b.derefReads }
      .fn name params annots ret (clauses.map (unfieldClause info))
    | item => item)

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
