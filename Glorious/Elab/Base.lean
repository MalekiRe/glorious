module

public import Std.Data.HashMap
public import Std.Data.HashSet
public import Glorious.Syntax.Ast
public import Glorious.Syntax.FlatOps
public import Glorious.Core.Ast
public import Glorious.Addr

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
  deriving BEq, Hashable

/-- How a trait bound is met, for the elaborator: by the `k`-th of the bounds
the function being elaborated is given, or by an implementation, named by the
function that makes it a value, given how each of its conditions is met. -/
inductive DictE where
  | param (k : Nat)
  | impl (fn : String) (subs : List DictE)
  deriving Inhabited, Hashable

/-- An implementation of a trait: the function that makes it a value, how many
conditions it has, and the function for each of the trait's, in the trait's
order, with how many arguments it takes. -/
structure ImplE where
  dictFn : String
  conditions : Nat
  methods : List (String × Nat)
  deriving Hashable

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
  deriving BEq, Hashable

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
  deriving Hashable

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
  /-- `dicts`, `methods`, `bounded`, `impls` and `drops` by what they are
  looked up by (`index`): the first of each, as `lookup` finds it. -/
  dictsAt : Std.HashMap Nat (List DictE) := {}
  methodsAt : Std.HashMap Nat Nat := {}
  boundedAt : Std.HashMap String Nat := {}
  implsAt : Std.HashMap String ImplE := {}
  dropsAt : Std.HashMap DropSite Nat := {}
  /-- The sites of the parts of a name's value, by where the name is bound
  and the name, in the order `drops` has them. -/
  partsAt : Std.HashMap (String × Nat × Nat × String) (Array DropSite) := {}
  /-- The implementations with nothing left to be known, numbered once for
  the program: each its function and its parts' numbers (`knownPool`), and
  back (`knownIds`); and the number of each such dictionary object the
  checker gave (`knownOf`, by the object). A body given one has its number
  (`%known#n`) and not the implementation written out, so what follows walks
  a name where it would walk the implementation, of a size that grows with
  how deep the types are; the specializer starts from these numbers and
  writes out what is left of them. -/
  knownPool : Array (String × List Nat) := #[]
  knownIds : Std.HashMap (String × List Nat) Nat := {}
  knownOf : Std.HashMap USize Nat := {}

/-- Numbering the implementations with nothing left to be known: by object
(none for one with a parameter left), by function and parts, and back. -/
structure Numbering where
  byObject : Std.HashMap USize (DictE × Option Nat) := {}
  ids : Std.HashMap (String × List Nat) Nat := {}
  pool : Array (String × List Nat) := #[]

/-- A dictionary's number, and its parts', each object looked at once. -/
partial def numberDict (d : DictE) : StateM Numbering (Option Nat) := do
  if let some (_, r) := (← get).byObject[addrOf d]? then return r
  let r ← match d with
    | .param _ => pure none
    | .impl fn subs => do
      let mut ids : Array Nat := #[]
      let mut closed := true
      for s in subs do
        match ← numberDict s with
        | some n => ids := ids.push n
        | none => closed := false
      if !closed then pure none else
      let key := (fn, ids.toList)
      match (← get).ids[key]? with
      | some n => pure (some n)
      | none =>
        let n := (← get).pool.size
        modify fun s => { s with ids := s.ids.insert key n, pool := s.pool.push key }
        pure (some n)
  -- (The object is kept with its number, so no other comes to be where it is.)
  modify fun s => { s with byObject := s.byObject.insert (addrOf d) (d, r) }
  pure r

/-- The first value of each key. -/
def firstOf {κ ν : Type} [BEq κ] [Hashable κ] (l : List (κ × ν)) : Std.HashMap κ ν :=
  l.foldl (fun m (k, v) => if m.contains k then m else m.insert k v) {}

/-- What the elaborator looks up of a program's traits, by what it looks it
up by. -/
def TraitInfo.index (t : TraitInfo) : TraitInfo :=
  let every : List DictE := t.dicts.flatMap (·.2) ++ t.destroys.flatMap fun d =>
    d.hook.toList ++ d.ctors.flatMap fun (_, fs) => fs.filterMap id
  let numbered := ((every.forM fun d => discard (numberDict d)).run {}).2
  { t with
    knownPool := numbered.pool, knownIds := numbered.ids
    knownOf := numbered.byObject.fold (init := {}) fun m k (_, r) => match r with
      | some n => m.insert k n
      | none => m
    dictsAt := firstOf t.dicts, methodsAt := firstOf t.methods, boundedAt := firstOf t.bounded
    implsAt := firstOf (t.impls.map fun im => (im.dictFn, im)), dropsAt := firstOf t.drops
    partsAt := t.drops.foldl (fun m (site, _) =>
      match Syntax.partOf site.name, site.assign with
      | some (x, _), false =>
        m.alter (site.owner, site.line, site.col, x) fun
          | some sites => some (sites.push site)
          | none => some #[site]
      | _, _ => m) {} }

/-- The function that makes an implementation a value. -/
def implDictName (trait head : String) : String := s!"impl {trait} for {head}"

/-- Something the checker decides of how a program is to be read, which it
finds only once it knows types, decided where it is found: the function it
is in is checked again with it, not the program. -/
inductive Decision where
  /-- `..` in the tuple pattern `id` stands for `count` parts. -/
  | rest (id count : Nat)
  /-- The same, written where it is (`restNode`), not read again. -/
  | restHere (id count : Nat)
  /-- In `owner`, the function `x` named as a value is a block that calls it. -/
  | eta (owner x : String) (arity : Nat)
  /-- In `owner`, what the `let` of `x` at `line:col` binds is kept in a
  variable. -/
  | letMut (owner : String) (line col : Nat) (x : String)
  /-- The clauses of the callable `id` match what the reference they are
  given points to (`&Pattern`): as they are written out so
  (`Syntax.Flat.byReference`). -/
  | refPats (id : Nat) (clauses : List Clause)
  /-- The dot call `call` is of `fn` (the type's own function of the name),
  or of the function it is of, its receiver, a name, borrowed: given as the
  function takes it, borrowed (`&mut` where `some true`) or whole. -/
  | receiver (call : Nat) (fn : Option String) (borrow : Option Bool)
  /-- The dot call `call`, its receiver a name, written where it is as the
  checker read it on, not read again (`receiverNode`): of `fn` where given,
  the name borrowed (`some uniq`) or given as it is. -/
  | receiverHere (call : Nat) (fn : Option String) (borrow : Option Bool)
  /-- The dot call `call`, its receiver a field of a name (through a
  reference the name holds where `star`), borrowed where it is
  (`receiverFieldNode`). -/
  | receiverField (call : Nat) (fn : Option String) (uniq star : Bool)
  /-- The dot call `call`, its receiver no name and borrowed: kept in a
  variable of its own for the statement whose expression is the node
  `root` (its identity), and borrowed there (`receiverTempNode`). -/
  | receiverTemp (call : Nat) (fn : Option String) (uniq : Bool) (root : Nat)
  /-- The field read `id` of a name, of what `Deref::deref` gives of it,
  written where it is (`derefNode`): the name borrowed (`some false`) or
  given as it is, a reference. -/
  | derefHere (id : Nat) (borrow : Option Bool)
  /-- The assignment through the field borrow `id`, `x.f = v` of what
  `DerefMut::deref_mut` gives of `x`, written where it is
  (`derefAssignNode`): `x` borrowed `&mut` (`some true`) or given as it is,
  a reference. -/
  | derefAssignHere (id : Nat) (borrow : Option Bool)
  /-- The field borrow `id`, `&x.f` (`&mut` where `uniq`) of what `deref`
  (`deref_mut`) gives of `x`, written where it is (`derefRefNode`). -/
  | derefRefHere (id : Nat) (uniq : Bool) (borrow : Option Bool)
  /-- The comparison `call`, written where it is by reference
  (`compareNode`): `eq(&a, &b)`, an operand that is a name holding a
  reference given as it is (`refs`). -/
  | compareHere (call : Nat) (refs : List Bool)
  /-- In `owner`, the function `x` named as a value at the node `node` (its
  identity, `Flat.Body.idOf`), written where it is as a block that calls
  it, the block numbered `id` (`etaNode`). -/
  | etaHere (owner : String) (node : Nat) (x : String) (arity : Nat) (id : Nat)
  /-- The callable `id`'s clauses the checker's, `&Pattern` (`refPats`),
  written where it is (`refPatsNode`), not read again. -/
  | refPatsHere (id : Nat) (clauses : List Clause)
  /-- The field read `id` (or borrowed, `&mut` where `uniq`) is not one the
  value shows, and the value's type implements `Deref`: it is of what
  `Deref::deref` (`DerefMut::deref_mut`) gives (`Mut<T>` as its `T`). -/
  | derefField (id : Nat) (uniq : Bool)
  /-- The dot call `call`'s receiver, a reference, is of what it points to. -/
  | derefReceiver (call : Nat)
  /-- The comparison `call`, `a == b`, is of what `a` and `b` are, borrowed:
  `eq(&a, &b)` (`Syntax.compareOps`). -/
  | compareByRef (call : Nat)

/-- (Each of these finds the node by its identity from the last: a body
written again keeps what it was made of before it, which nothing reaches,
and the node read is the one made last.)

The dot call `call`'s node written where it is, as the checker reads it
on (`Check.receiverHere`) and the elaborator writes it: of `fn` where
given, its receiver a name borrowed (`some uniq`) or given as it is. None
where the receiver is no name: decided as before (`receiverBody`), where
written so, a chain of calls read again at each link cost more than reading
the function again (covey/fleet's `main`: 1.7 s from 1.1). -/
def receiverNode (call : Nat) (fn : Option String) (borrow : Option Bool) (b : Flat.Body) : Option Flat.Body := do
  let e ← (List.range b.exprs.size).reverse.find? fun i => match b.exprs[i]! with
    | .call i _ _ | .tailCall i _ _ => i == call
    | _ => false
  let (tail, f, args) ← match b.exprs[e]! with
    | .call _ f args => some (false, f, args)
    | .tailCall _ f args => some (true, f, args)
    | _ => none
  let (callee, recv, rest) ← match b.expr f, fn with
    | .fieldOf _ recv _, some g => some (Flat.FExpr.name none g, recv, args)
    | _, _ =>
      let callee := match fn with
        | some g => Flat.FExpr.name none g
        | none => b.expr f
      if h : 0 < args.size then some (callee, args[0], args.extract 1 args.size) else none
  let named := match b.expr recv with
    | .name none x => some x
    | .ref _ x => some x
    | _ => none
  -- (A receiver given whole that is no name is the node itself, as it is
  -- written; one borrowed is a name.)
  let given : Option Flat.FExpr ← match borrow, named with
    | some u, some x => some (some (.ref u x))
    | none, some x => some (some (.name none x))
    | none, none => some none
    | some _, none => none
  let (fe, b) := b.add callee
  let (ge, b) := match given with
    | some n => b.add n
    | none => (recv, b)
  let node : Flat.FExpr := if tail then .tailCall call fe (#[ge] ++ rest) else .call call fe (#[ge] ++ rest)
  pure { b with exprs := b.exprs.set! e node }

/-- A pattern with `..` of the tuple pattern `id` written as `count` `_`. -/
partial def restPat (id count : Nat) : Pattern → Pattern
  | .tuple ps => .tuple (ps.flatMap fun
      | .var x => if Syntax.tupleRestOf x == some id then List.replicate count Pattern.wild else [.var x]
      | p => [restPat id count p])
  | .ctor c q ps => .ctor c q (ps.map (restPat id count))
  | p => p

/-- Every pattern of the body with `..` of the tuple pattern `id` written as
`count` parts, where it is: the patterns of `let`s and of clauses, in place,
no node made anew (`Decision.restHere`). None where none has it. -/
def restNode (id count : Nat) (b : Flat.Body) : Option Flat.Body := do
  let has := fun (p : Pattern) => restPat id count p != p
  let stmts := b.stmts.map fun s => match s with
    | .let_ p v => if has p then .let_ (restPat id count p) v else s
    | s => s
  let clauses := b.clauses.map fun c =>
    if c.pats.any has then ⟨c.pats.map (restPat id count), c.body⟩ else c
  if stmts == b.stmts && clauses == b.clauses then none
  pure { b with stmts, clauses }

/-- The function `x` named as a value at the node whose identity is `node`,
written where it is as a block that calls it, `{ (a, b) => x(a, b) }`, the
block numbered `id` and its call `id + 1`: as the checker reads it on and
the elaborator writes it (`Decision.etaHere`). -/
def etaNode (node : Nat) (x : String) (arity : Nat) (id : Nat) (b : Flat.Body) : Option Flat.Body := do
  let e ← (List.range b.exprs.size).reverse.find? fun i => b.idOf i == node && match b.exprs[i]! with
    | .name _ y => y == x
    | _ => false
  let q ← match b.exprs[e]! with
    | .name q _ => some q
    | _ => none
  let ps := (List.range arity).map fun k => s!"%eta{k}"
  let (fe, b) := b.add (.name q x)
  let (args, b) := ps.foldl (fun (acc : Array Flat.ExprId × Flat.Body) p =>
    let (a, b) := acc.2.add (.name none p); (acc.1.push a, b)) (#[], b)
  let (ce, b) := b.add (.call (id + 1) fe args)
  let s := b.stmts.size
  let b := { b with stmts := b.stmts.push (.expr ce) }
  let c := b.clauses.size
  let b := { b with clauses := b.clauses.push ⟨ps.map Pattern.var, #[s]⟩ }
  pure { b with exprs := b.exprs.set! e (.closure id #[c]) }

/-- The dot call `call`, its receiver a field of a name, `p.x.len()`,
borrowed where it is, `len(&p.x)` (through the reference the name holds
where `star`), of `fn` where given: as the checker reads it on and the
elaborator writes it (`Decision.receiverField`). None where the receiver
is not such a field. -/
def receiverFieldNode (call : Nat) (fn : Option String) (uniq star : Bool) (b : Flat.Body) :
    Option Flat.Body := do
  let e ← (List.range b.exprs.size).reverse.find? fun i => match b.exprs[i]! with
    | .call i _ _ | .tailCall i _ _ => i == call
    | _ => false
  let (tail, f, args) ← match b.exprs[e]! with
    | .call _ f args => some (false, f, args)
    | .tailCall _ f args => some (true, f, args)
    | _ => none
  let (callee, recv, rest) ← match b.expr f, fn with
    | .fieldOf _ recv _, some g => some (Flat.FExpr.name none g, recv, args)
    | _, _ =>
      let callee := match fn with
        | some g => Flat.FExpr.name none g
        | none => b.expr f
      if h : 0 < args.size then some (callee, args[0], args.extract 1 args.size) else none
  -- (The way from the name to the field, and the outermost field's number.)
  let rec chain (x : Flat.ExprId) (fuel : Nat) : Option (String × List String × Nat) :=
    match fuel, b.expr x with
    | fuel + 1, .fieldOf fid inner name =>
      match b.bare? inner with
      | some root => some (root, [name], fid)
      | none => (chain inner fuel).map fun (root, path, _) => (root, path ++ [name], fid)
    | _, _ => none
  let (x, path, fid) ← chain recv 64
  if fid == 0 then none
  let (fe, b) := b.add callee
  let (ge, b) := b.add (.refField fid uniq x path star)
  pure { b with exprs := b.exprs.set! e (if tail then .tailCall call fe (#[ge] ++ rest) else .call call fe (#[ge] ++ rest)) }

/-- The dot call `call`, its receiver no name and borrowed (`&mut` where
`uniq`), of `fn` where given: the statement's expression it is in, the
node whose identity is `root`, made a block that keeps the receiver in a
variable of its own first and borrows that, `{ let mut r = make(); f(&r)
.. }`, as Rust keeps a temporary till its statement is done. As the checker
reads it on and the elaborator writes it (`Decision.receiverTemp`). None
where the call is not in that expression or its receiver is a name. -/
def receiverTempNode (call : Nat) (fn : Option String) (uniq : Bool) (root : Nat) (b : Flat.Body) :
    Option Flat.Body := do
  let r ← (List.range b.exprs.size).reverse.find? fun i => b.idOf i == root
  let e ← (List.range b.exprs.size).reverse.find? fun i => match b.exprs[i]! with
    | .call i _ _ | .tailCall i _ _ => i == call
    | _ => false
  let inRoot := b.anyExpr (fun n => match n with
    | .call i _ _ | .tailCall i _ _ => i == call
    | _ => false) r
  if !inRoot then none
  let (tail, f, args) ← match b.exprs[e]! with
    | .call _ f args => some (false, f, args)
    | .tailCall _ f args => some (true, f, args)
    | _ => none
  let (callee, recv, rest) ← match b.expr f, fn with
    | .fieldOf _ recv _, some g => some (Flat.FExpr.name none g, recv, args)
    | _, _ =>
      let callee := match fn with
        | some g => Flat.FExpr.name none g
        | none => b.expr f
      if h : 0 < args.size then some (callee, args[0], args.extract 1 args.size) else none
  -- (A temporary: what a call gives. A name or a field of one is a place,
  -- borrowed where it is.)
  match b.expr recv with
  | .call .. | .tailCall .. => pure ()
  | _ => none
  let held := s!"%receiver{call}"
  let (fe, b) := b.add callee
  let (ge, b) := b.add (.ref uniq held)
  let b := { b with exprs := b.exprs.set! e (if tail then .tailCall call fe (#[ge] ++ rest) else .call call fe (#[ge] ++ rest)) }
  -- (The statement's expression, now with the call so written, moved to a
  -- node of its own, known as it was.)
  let (moved, b) := b.add (b.exprs[r]!) (some root)
  let first := b.stmts.size
  let b := { b with stmts := b.stmts.push (.letMut held recv) }
  let last := b.stmts.size
  let b := { b with stmts := b.stmts.push (.expr moved) }
  pure { b with exprs := b.exprs.set! r (.labelScope "%block" #[first, last]) }

/-- The field read `id`, `x.f` of a name, written of what `deref` gives of
it where it is: `deref(&x).f` (`borrow` is `some false`) or `deref(x).f`
(`x` a reference), as the checker reads it on and the elaborator writes it
(`Decision.derefHere`). -/
def derefNode (id : Nat) (borrow : Option Bool) (b : Flat.Body) : Option Flat.Body := do
  let e ← (List.range b.exprs.size).reverse.find? fun i => match b.exprs[i]! with
    | .fieldOf i _ _ => i == id
    | _ => false
  let (x, f) ← match b.exprs[e]! with
    | .fieldOf _ s f => (b.bare? s).map (·, f)
    | _ => none
  let given : Flat.FExpr := match borrow with
    | some u => .ref u x
    | none => .name none x
  let (fe, b) := b.add (.name none "deref")
  let (ge, b) := b.add given
  let (ce, b) := b.add (.call (900000000000 + id) fe #[ge])
  pure { b with exprs := b.exprs.set! e (.fieldOf id ce f) }

/-- The field borrow `id`, `&x.f` of what `deref` gives of `x` (`deref_mut`
where `uniq`), written where it is as a block: `{ let r = deref(&x); &(*r).f }`
(`x` given as it is where `borrow` is none, a reference). As the checker
reads it on and the elaborator writes it (`Decision.derefRefHere`). -/
def derefRefNode (id : Nat) (uniq : Bool) (borrow : Option Bool) (b : Flat.Body) : Option Flat.Body := do
  let e ← (List.range b.exprs.size).reverse.find? fun i => match b.exprs[i]! with
    | .refField i _ _ _ false => i == id
    | _ => false
  let (x, path) ← match b.exprs[e]! with
    | .refField _ _ x path _ => some (x, path)
    | _ => none
  let held := s!"%derefb{id}"
  let given : Flat.FExpr := match borrow with
    | some u => .ref u x
    | none => .name none x
  let (fe, b) := b.add (.name none (if uniq then "deref_mut" else "deref"))
  let (ge, b) := b.add given
  let (ce, b) := b.add (.call (900000000000 + id) fe #[ge])
  let first := b.stmts.size
  let b := { b with stmts := b.stmts.push (.let_ (.var held) ce) }
  let (re, b) := b.add (.refField id uniq held path true)
  let last := b.stmts.size
  let b := { b with stmts := b.stmts.push (.expr re) }
  pure { b with exprs := b.exprs.set! e (.labelScope "%block" #[first, last]) }

/-- The assignment `*(&mut x.path) = v` through the field borrow `id`, of
what `deref_mut` gives of `x`, written where it is as a block: `{ let v' =
v; let r = deref_mut(&mut x); *(&mut r.path) = v' }` (`x` given as it is
where `borrow` is none, a reference): the value computed first, so that
reading it does not meet the borrow. As the checker reads it on and the
elaborator writes it (`Decision.derefAssignHere`). -/
def derefAssignNode (id : Nat) (borrow : Option Bool) (b : Flat.Body) : Option Flat.Body := do
  let s ← (List.range b.stmts.size).reverse.find? fun i => match b.stmts[i]! with
    | .assign t _ => match b.expr t with
      | .deref r => match b.expr r with
        | .refField i true _ _ false => i == id
        | _ => false
      | _ => false
    | _ => false
  let (path, x, value) ← match b.stmts[s]! with
    | .assign t v => match b.expr t with
      | .deref r => match b.expr r with
        | .refField _ _ x path _ => some (path, x, v)
        | _ => none
      | _ => none
    | _ => none
  let held := s!"%deref{id}"
  let named := held ++ "v"
  let given : Flat.FExpr := match borrow with
    | some u => .ref u x
    | none => .name none x
  let push := fun (b : Flat.Body) (n : Flat.FExpr) => b.add n
  let pushS := fun (b : Flat.Body) (n : Flat.FStmt) => (b.stmts.size, { b with stmts := b.stmts.push n })
  let (s1, b) := pushS b (.let_ (.var named) value)
  let (fe, b) := push b (.name none "deref_mut")
  let (ge, b) := push b given
  let (ce, b) := push b (.call (900000000000 + id) fe #[ge])
  let (s2, b) := pushS b (.let_ (.var held) ce)
  let (rf, b) := push b (.refField id true held path false)
  let (dr, b) := push b (.deref rf)
  let (ve, b) := push b (.name none named)
  let (s3, b) := pushS b (.assign dr ve)
  let (blk, b) := push b (.labelScope "%block" #[s1, s2, s3])
  pure { b with stmts := b.stmts.set! s (.expr blk) }

/-- The comparison `call`, `a == b`, written where it is by reference:
`eq(&a, &b)` (the function of `Syntax.compareOps`), as Rust's operators
compare; a name that holds a reference given as it is (`refs`); an
operand that is no name kept in a variable of its own first, `{ let mut
a' = f(); eq(&a', &b) }`. As the checker reads it on and the elaborator
writes it (`Decision.compareHere`). -/
def compareNode (call : Nat) (refs : List Bool) (b : Flat.Body) : Option Flat.Body := do
  let e ← (List.range b.exprs.size).reverse.find? fun i => match b.exprs[i]! with
    | .call i _ _ => i == call
    | _ => false
  let (f, l, r) ← match b.exprs[e]! with
    | .call _ f #[l, r] => some (f, l, r)
    | _ => none
  let fn ← (b.name? f).bind fun (_, op) => Syntax.compareOps.lookup op
  let named := fun (a : Flat.ExprId) => (b.bare? a).filter fun x => !(Syntax.lastSegment x).front.isUpper
  -- (An operand that is no name is kept in a variable of its own for the
  -- comparison, in the order written, and borrowed.)
  let operand := fun (b : Flat.Body) (a : Flat.ExprId) (k : Nat) =>
    match named a with
    | some x =>
      let (r, b) := b.add (if refs.getD k false then .name none x else .ref false x)
      (r, none, b)
    | none =>
      let held := s!"%compared{call}_{k}"
      let s := b.stmts.size
      let b := { b with stmts := b.stmts.push (.letMut held a) }
      let (r, b) := b.add (.ref false held)
      (r, some s, b)
  let (le, ls, b) := operand b l 0
  let (re, rs, b) := operand b r 1
  let (fe, b) := b.add (.name none fn)
  if ls.isNone && rs.isNone then
    return { b with exprs := b.exprs.set! e (.call call fe #[le, re]) }
  let (ce, b) := b.add (.call call fe #[le, re])
  let last := b.stmts.size
  let b := { b with stmts := b.stmts.push (.expr ce) }
  pure { b with exprs := b.exprs.set! e (.labelScope "%block" ((ls.toList ++ rs.toList).toArray.push last)) }

/-- The callable `id` with `clauses` in place of its own, where it is, as
the checker reads it on and the elaborator writes it
(`Decision.refPatsHere`). The nodes the clauses are made of are known in a
space of the callable's own (`Flat.Body.ids`): the same in the checker's
body as in the elaborator's, where what the checker found of a literal in
them is looked for. -/
def refPatsNode (id : Nat) (clauses : List Clause) (b : Flat.Body) : Option Flat.Body := do
  let e ← (List.range b.exprs.size).reverse.find? fun i => match b.exprs[i]! with
    | .closure i _ => i == id
    | _ => false
  let start := b.exprs.size
  let (cs, b) := (clauses.toArray.mapM Flat.flatClause).run b
  let space := (1 <<< 62) + id * 1000000
  let ids := (List.range' start (b.exprs.size - start)).foldl (fun ids k => ids.set! k (space + (k - start))) b.ids
  pure { b with exprs := b.exprs.set! e (.closure id cs), ids }

/-- What the checker says where it stops: why, and what it found to decide,
where it stops for that; `result`
where what does not fit is a clause's result. -/
structure Said where
  msg : String
  decision : Option Decision := none
  result : Bool := false
  /-- Of "has no field": the head of the type it is not a field of (a dot
  call's receiver's, `value.name(..)`), so that whoever looks for the type's
  own function of the name need not read the receiver again. -/
  subject : Option String := none

instance : Coe String Said := ⟨fun msg => { msg }⟩

/-- The same, said otherwise: what it found kept. -/
def Said.map (s : Said) (f : String → String) : Said := { s with msg := f s.msg }

/-- Is it what a speculative check passes on at once rather than trying
otherwise: a match found to be of a reference, or a dot call's function or
receiver found? -/
def Said.passOn (s : Said) : Bool :=
  match s.decision with
  | some (.refPats ..) | some (.receiver ..) | some (.derefField ..) | some (.derefReceiver _) => true
  | _ => false

/-- What the checker tells the elaborator about the blocks of a program, each
named by its identity. -/
structure Blocks where
  /-- Blocks written without parameters where a callable taking one argument is
  expected: they take the argument without naming it. -/
  given : Std.HashSet Nat := {}
  /-- Those of them whose argument is a block that was not run: each with the
  identity of that block, whose environment it can take over. -/
  links : Std.HashMap Nat Nat := {}
  /-- The coercions to apply, by the place each is applied at. -/
  coercions : Std.HashMap Site String := {}
  traits : TraitInfo := {}
  /-- For each borrow of a field, what is gone through to reach the field: at
  each step the constructor, or none for a tuple, and how many fields it has. -/
  fields : Std.HashMap Nat (Bool × List Nat × List (Option String × Nat)) := {}
  /-- For each field read by name, which field it is. -/
  fieldReads : Std.HashMap Nat Nat := {}
  /-- The blocks given what an `is` found, each with the names it then has. -/
  packs : Std.HashMap Nat (List String) := {}
  /-- The fields read by name of what a named reference points to. -/
  derefReads : Std.HashSet Nat := {}
  /-- For each function that performs or handles an operation of an effect
  with type parameters, or calls one that does: the places, by the number of
  the call, with which of `op`, `handle`, `call`, `ref` each is, the effect or
  the function called, and where its types are among the function's. -/
  sites : List (String × List (Nat × String × String × Nat × Nat)) := []
  /-- Those types, each where it is known without knowing who calls the
  function. -/
  siteTypes : List (String × List (Option Syntax.TypeExpr)) := []
  /-- Dot calls the checker found are of a type's own function, chosen by
  the value's type: by the call, the function, and how the receiver, a
  variable, is now given (`0` as it was, `1` borrowed, `2` borrowed `&mut`). -/
  dotChosen : Std.HashMap Nat (String × Nat) := {}
  /-- Each whole number written where a scalar type is wanted, by its
  function and its place there: the type's name. -/
  scalarLits : Std.HashMap (String × Nat) String := {}
  /-- Arguments given as other than written (`Check.argsChosen`), by the call
  and the place. -/
  argsChosen : Std.HashMap (Nat × Nat) Expr := {}
  /-- What the checker decided of how the program is written, where it found
  it, in the order decided: written into the program once it is checked. -/
  decided : List Decision := []

structure Globals where
  ctors : Std.HashMap String CtorInfo := {}
  ops : List (String × OpInfo) := []
  fns : Std.HashMap String Nat := {}
  aliases : Std.HashMap String Expr := {}
  /-- The body of each top-level function, by name. -/
  bodies : Std.HashMap String Flat.Body := {}
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
  deriving BEq

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
   -- Of `[T; N]`: `N` of one value, the element at a place, one with another
   -- there, the reference to a place from a reference to it (an operation
   -- on memory, not of the machines), and its length.
   ("fixed_fill", .fixed 0, 2), ("fixed_get", .fixed 2, 2),
   ("fixed_set", .fixed 3, 3), ("fixed_at", .fixed 2, 2), ("fixed_len", .fixed 4, 1),
   -- How many elements the `[T; N]` a reference points to has: its
   -- constructor says, and nothing is read out of it.
   ("fixed_len_at", .fixed 4, 1),
   -- `[a, b, c]`: a `[T; 3]` of them, as many as it is given.
   ("fixed_make", .fixed 4, 0)]

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
   ("c_callback", 5, 2),
   -- Unsafe: cells more than one holder reaches, by number: a new one
   -- holding a value, the value taken out of one, and one put in. What a
   -- cell holds is not seen by the checker: the library's shared values
   -- and threads, which are safe, are made of them.
   ("heap_new", 6, 2), ("heap_take", 7, 2), ("heap_put", 8, 3),
   -- Unsafe: a machine is to start for a thread of the system's the
   -- program is about to have C start (`pthread_create`); the Rust VM
   -- alone gives it meaning.
   ("heap_machine_coming", 10, 0),
   -- The name of the function a callable is of, and the callable back.
   ("host_fn_name", 9, 2),
   -- A character put at the end of the line being written; the line ended.
   ("host_put", 21, 1), ("host_line", 22, 0),
   -- Unsafe: memory, by address. A new block of so many bytes at a multiple
   -- of an alignment; a block freed; bytes copied.
   ("mem_alloc", 11, 2), ("mem_free", 12, 1), ("mem_copy", 13, 3),
   -- How many bytes a value of what a pointer is to takes, and at what
   -- alignment.
   ("size_of_at", 15, 1), ("align_of_at", 16, 1),
   -- What a raw pointer points to, as a reference.
   ("ptr_ref_at", 17, 2), ("ptr_mut_ref_at", 18, 2),
   -- Where a `[T; N]`'s elements are, as a `*mut T`.
   ("fixed_ptr", 20, 1)]

/-- The host operations that are the machine's memory by address: what each
is (`MemOp`). -/
def memOfHost : Nat → Option MemOp
  | 3 => some .readBits
  | 4 => some .writeBits
  | 11 => some .alloc
  | 12 => some .free
  | 13 => some .copy
  | 15 => some .sizeOf
  | 16 => some .alignOf
  | 17 | 18 => some .deref
  | 20 => some .addressOf
  | _ => none

/-- Is this the name of one of the machine's operations (declared
`#[intrinsic]` in the prelude)? -/
def isIntrinsic (x : String) : Bool :=
  (prims.lookup x).isSome || (hosts.lookup x).isSome || (Syntax.scalarCast x).isSome

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

/-- What elaborating one top-level function read that is not its own body:
kept with what it made (`ElabKept`), and read again before that is taken. -/
inductive ElabRead where
  | lend (site mode : Nat)
  | given (id : Nat) (v : Bool)
  | link (id : Nat) (v : Option Nat)
  | pack (id : Nat) (v : Option (List String))
  | fn (name : String) (v : Option Nat)
  | layout (owner : Nat) (v : UInt64)

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
  /-- The body of the function being elaborated: what an `ExprId` is a place
  of. What the elaborator writes out (a borrow named first, a block around a
  statement) is added to it. -/
  body : Flat.Body := {}
  /-- What the top-level function being elaborated read that is not its own,
  in order (`ElabRead`). -/
  reads : Array ElabRead := #[]
  /-- `layouts` as it was when the top-level function being elaborated began:
  what is in front of it is the function's own. -/
  layoutsAt : List (Nat × Nat × List (String × Atom × List (Nat × Atom))) := []

/-- What elaborating a top-level function made, kept for the next compile: by
the key of what it was elaborated from (its body, what the program declares,
and where each count stood), what else it read, and what it added to each
part of the state. Taken where the key is the same and each read is. -/
structure ElabKept where
  key : UInt64
  reads : Array ElabRead
  clauses : List Core.Clause
  fns : Array Core.Fn
  names : Array String
  fnSites : Array (Option Nat)
  siteOwners : Array String
  layouts : List (Nat × Nat × List (String × Atom × List (Nat × Atom)))
  envSizes : List (Nat × Nat × Nat)
  under : List (Nat × Nat)
  twoWays : List Nat
  plain : List Borrow
  drops : List (Nat × Nat)
  activations : Nat
  lent : Nat
  sites : Nat
  foreign : Bool
  pos : Nat × Nat

/-- Each top-level function's `ElabKept`, by its name. -/
abbrev ElabMemo := Std.HashMap String ElabKept

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

private unsafe def sameObjImpl {α : Type} (a b : α) : Bool := ptrAddrUnsafe a == ptrAddrUnsafe b

/-- Are two values the same object (never, as the logic sees it). -/
@[implemented_by sameObjImpl] def sameObj {α : Type} (_ _ : α) : Bool := false

def noteRead (r : ElabRead) : M Unit := modify fun s => { s with reads := s.reads.push r }

/-- How the place `site` is made a scope, noted. -/
def lendAt (site : Nat) : M Nat := do
  let m := (← read).lends site
  noteRead (.lend site m)
  pure m

/-- Whether the checker found block `id` takes the argument it does not name, noted. -/
def givenAt (id : Nat) : M Bool := do
  let v := ((← read).blocks.getD {}).given.contains id
  noteRead (.given id v)
  pure v

/-- The block that was not run whose environment block `id` takes, noted. -/
def linkAt (id : Nat) : M (Option Nat) := do
  let v := ((← read).blocks.getD {}).links[id]?
  noteRead (.link id v)
  pure v

/-- The names block `id` has from an `is`, noted. -/
def packAt (id : Nat) : M (Option (List String)) := do
  let v := ((← read).blocks.getD {}).packs[id]?
  noteRead (.pack id v)
  pure v

/-- The number of the top-level function `x`, noted. -/
def fnAt (x : String) : M (Option Nat) := do
  let v := (← read).fns[x]?
  noteRead (.fn x v)
  pure v

/-- What the callable literal `owner` captured, noted where a function before
this one made it (one this function made is its own). -/
def layoutAt (owner : Nat) : M (Option (Nat × List (String × Atom × List (Nat × Atom)))) := do
  let s ← get
  let v := s.layouts.lookup owner
  unless mine s.layoutsAt owner s.layouts do noteRead (.layout owner (hash v))
  pure v
where
  mine (start : List (Nat × Nat × List (String × Atom × List (Nat × Atom)))) (owner : Nat) :
      List (Nat × Nat × List (String × Atom × List (Nat × Atom))) → Bool
    | [] => false
    | l@((o, _) :: r) => if sameObj l start then false else if o == owner then true else mine start owner r

/-- Is what `r` read still what it is? -/
def readHolds : ElabRead → M Bool
  | .lend site mode => do pure ((← read).lends site == mode)
  | .given id v => do pure (((← read).blocks.getD {}).given.contains id == v)
  | .link id v => do pure (((← read).blocks.getD {}).links[id]? == v)
  | .pack id v => do pure (((← read).blocks.getD {}).packs[id]? == v)
  | .fn x v => do pure ((← read).fns[x]? == v)
  | .layout owner v => do pure (hash ((← get).layouts.lookup owner) == v)

/-- What `after` has in front of `before`, where it is `before` with more in
front of it (the same object after them); none where it is not. -/
def prefixTo {α : Type} (after before : List α) : Option (List α) :=
  go after []
where
  go : List α → List α → Option (List α)
    | [], acc => if sameObj ([] : List α) before then some acc.reverse else none
    | l@(x :: r), acc => if sameObj l before then some acc.reverse else go r (x :: acc)

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
  | .ctor _ _ args | .tuple args => args.flatMap patVars

open Flat in
/-- The names a statement gives values that may hold what `tracked` names hold. -/
def madeFrom (b : Body) (tracked : List String) (s : StmtId) : List String :=
  match b.stmt (b.unlocated s) with
  | .let_ pat value => if (b.fvExpr [] value).any tracked.contains then patVars pat else []
  | .letMut y value => if (b.fvExpr [] value).any tracked.contains then [y] else []
  | .assign t value =>
    match b.bare? t with
    | some y => if (b.fvExpr [] value).any tracked.contains then [y] else []
    | none => []
  | _ => []

open Flat in
/--
How many of the statements after `let p = &x` the borrow's scope takes in: up
to the last that mentions `p`, and with `wide`, anything made from `p`. A
mutable variable declared inside the scope ends with it, so the scope also
takes in every statement that mentions one; and a `defer` inside it would run
when the scope ends, so a scope that has one takes in the whole block.
-/
partial def scopeExtent (b : Body) (p : String) (rest : List StmtId) (wide : Bool) : Nat :=
  go [p] 0
where
  go (tracked : List String) (k : Nat) : Nat :=
    let inner := (rest.take k).map fun s => b.stmt (b.unlocated s)
    let defers := inner.any fun
      | .defer _ => true
      | _ => false
    if defers then rest.length
    else
      let muts := inner.filterMap fun
        | .letMut y _ => some y
        | _ => none
      let made :=
        if wide then (rest.take k).foldl (fun acc s => acc ++ madeFrom b acc s) tracked else tracked
      let tracked' := (made ++ muts).eraseDups
      let k' := ((List.range (rest.length + 1)).drop k).find? fun j =>
        !(b.fvStmts [] (rest.drop j)).any tracked'.contains
      let k' := k'.getD rest.length
      if k' == k && tracked'.length == tracked.length then k else go tracked' k'

/-- Is this the name of a borrow the elaborator made before a statement that
had it written in it? Such a `let p = &x` is a scope, and not a place of its
own: the statement was the place. -/
def madeBorrow (p : String) : Bool :=
  p.startsWith "%lend" || p.startsWith "%held" || p.startsWith "%borrow"

open Flat in
/-- A statement's expression with what is worked out before its first borrow
is used taken out and named, in the order it is worked out: so that a borrow
made a scope around the statement does not last while that runs, which may
read the variable borrowed. (`a[len(a) - 1] = v`.)

Only what comes first can be taken out without changing the order: once a
call that is given a borrow has run, what follows stays where it is. Nothing
is taken out of what a handler watches: it would then run unwatched. -/
partial def pullFirst (site : Nat) (isCell : String → Bool) (e : ExprId) :
    Build (ExprId × List (String × ExprId)) := do
  let (e, pulled, _) ← go e [] true
  pure (e, pulled.reverse)
where
  has (b : Body) (e : ExprId) : Bool :=
    match b.expr e with
    | .name none n => madeBorrow n
    | .call _ f args => has b f || args.any (has b)
    | .tuple args => args.any (has b)
    | .deref e | .proj e _ => has b e
    | .handle subject _ => has b subject
    | _ => false
  /-- Is it worked out at all: not a number, a callable written out, or a
  name that is not a variable's. -/
  worth (b : Body) (e : ExprId) : Bool :=
    match b.expr e with
    | .int _ | .closure _ _ | .label _ => false
    | .name none n => isCell n
    | .name (some _) _ => false
    | _ => true
  operand (e : ExprId) (pulled : List (String × ExprId)) (first : Bool) :
      Build (ExprId × List (String × ExprId) × Bool) := do
    let b ← get
    if has b e then go e pulled first
    else if first && worth b e then
      let n := s!"%pre{site}.{pulled.length}"
      pure (← pushExpr (.name none n), (n, e) :: pulled, first)
    else pure (e, pulled, first)
  operands (es : Array ExprId) (pulled : List (String × ExprId)) (first : Bool) :
      Build (Array ExprId × List (String × ExprId) × Bool) := do
    let mut out : Array ExprId := #[]
    let mut pulled := pulled
    let mut first := first
    for e in es do
      let (e', pulled', first') ← operand e pulled first
      out := out.push e'
      pulled := pulled'
      first := first'
    pure (out, pulled, first)
  go (e : ExprId) (pulled : List (String × ExprId)) (first : Bool) :
      Build (ExprId × List (String × ExprId) × Bool) := do
    match (← get).expr e with
    | .call id f args =>
      let (f, pulled, first) ← match (← get).expr f with
        | .name _ _ => pure (f, pulled, first)
        | _ => operand f pulled first
      let (args, pulled, _) ← operands args pulled first
      -- (The call runs now: nothing after it is first.)
      pure (← pushExpr (.call id f args), pulled, false)
    | .tuple args =>
      let (args, pulled, first) ← operands args pulled first
      pure (← pushExpr (.tuple args), pulled, first)
    | .deref x =>
      let (x, pulled, first) ← operand x pulled first
      pure (← pushExpr (.deref x), pulled, first)
    | .proj x n =>
      let (x, pulled, first) ← operand x pulled first
      pure (← pushExpr (.proj x n), pulled, first)
    | _ => pure (e, pulled, false)

open Flat in
/-- The statements of a block with each `let p = &x` moved to just before the
first statement that mentions `p`. Making a reference does nothing, and the
later it is made the less its scope has to take in: two borrows that overlapped
need not, and a `defer` between a borrow and its use is no longer inside the
borrow's scope. One that nothing mentions, or that would pass a statement
giving `p` or `x` another meaning, stays. Doing this twice changes nothing. -/
partial def sinkBorrows (b : Body) (stmts : List StmtId) : List StmtId :=
  let arr := stmts.toArray
  -- Where each statement is to go: before the statement at this index.
  let target := fun (i : Nat) =>
    match arr[i]?.map fun s => b.stmt (b.unlocated s) with
    | some (.let_ (.var p) value) =>
      match b.expr value with
      | .ref _ x =>
        let later := (List.range arr.size).drop (i + 1)
        match later.find? fun j => (b.fvStmts [] (arr[j]?.toList)).contains p with
        | none => none
        | some j =>
          let between := (later.takeWhile (· < j)).filterMap fun k => arr[k]?.map fun s => b.stmt (b.unlocated s)
          let rebinds := between.any fun
            | .let_ pat _ => (patVars pat).contains p || (patVars pat).contains x
            | .letMut y _ => y == p || y == x
            | _ => false
          if rebinds || j == i + 1 then none else some j
      | _ => none
    | _ => none
  let targets := (List.range arr.size).map target
  if targets.all Option.isNone then stmts
  else
    -- The statements moved to before `j`, each after those moved to before it.
    let rec before (j : Nat) : List StmtId :=
      (List.range j).flatMap fun i =>
        if targets.getD i none == some j then before i ++ arr[i]?.toList else []
    (List.range arr.size).flatMap fun j =>
      if (targets.getD j none).isSome then [] else before j ++ arr[j]?.toList

open Flat in
/-- A statement that ends in a call some of whose arguments mention `p` and are
followed by arguments that do not: those up to the last that does, each given a
name, and the statement with the names in their place. -/
def splitCallOn (p : String) (site : Nat) (s : StmtId) : Build (Option (List StmtId × StmtId)) := do
  let b ← get
  let split := fun (e : ExprId) => (do
    match b.expr e with
    | .call id g args =>
      match b.expr g with
      | .name q gn =>
        if gn == p then return none
        let last := (List.range args.size).reverse.find? fun i =>
          (b.fvExpr [] args[i]!).contains p
        match last with
        | none => return none
        | some j =>
          if j + 1 == args.size then return none
          let named : List (Option (String × ExprId)) := (List.range args.size).map fun i =>
            let a := args[i]!
            let plain := match b.expr a with
              | .name _ _ | .int _ => true
              | _ => false
            if i ≤ j && !plain then some (s!"%part{site}.{i}", a) else none
          -- An argument that is `p` itself would still be mentioned.
          if ((List.range (j + 1)).any fun i =>
              named[i]!.isNone && (b.fvExpr [] args[i]!).contains p) then return none
          let mut lets : List StmtId := []
          let mut newArgs : Array ExprId := #[]
          for (n, i) in named.zipIdx do
            match n with
            | some (name, a) =>
              lets := lets ++ [← pushStmt (.let_ (.var name) a)]
              newArgs := newArgs.push (← pushExpr (.name none name))
            | none => newArgs := newArgs.push args[i]!
          let g' ← pushExpr (.name q gn)
          return some (lets, ← pushExpr (.call id g' newArgs))
      | _ => return none
    | _ => return none : Build (Option (List StmtId × ExprId)))
  let rec go (s : StmtId) (fuel : Nat) : Build (Option (List StmtId × StmtId)) := do
    match fuel with
    | 0 => return none
    | fuel + 1 =>
    match b.stmt s with
    | .located line col inner =>
      match ← go inner fuel with
      | some (lets, last) => return some (lets, ← pushStmt (.located line col last))
      | none => return none
    | .expr e =>
      match ← split e with
      | some (lets, e) => return some (lets, ← pushStmt (.expr e))
      | none => return none
    | .let_ pat e =>
      match ← split e with
      | some (lets, e) => return some (lets, ← pushStmt (.let_ pat e))
      | none => return none
    | .assign target e =>
      if (b.fvExpr [] target).contains p then return none
      match ← split e with
      | some (lets, e) => return some (lets, ← pushStmt (.assign target e))
      | none => return none
    | _ => return none
  go s 64

open Flat in
/-- The names the statements of a block bind with `let`. -/
def letNames (b : Body) (ss : List StmtId) : List String :=
  ss.flatMap fun s =>
    match b.stmt (b.unlocated s) with
    | .let_ pat _ => patVars pat
    | _ => []

/-! ## What a function gives a callable it is passed -/

open Flat in
mutual

/-- With how many arguments the name `p` is applied, at each place it is,
up to where a name `p` is bound again. -/
partial def appliedExpr (b : Body) (p : String) (e : ExprId) : List Nat :=
  let here := match b.expr e with
    | .call _ f args | .tailCall _ f args => if b.bare? f == some p then [args.size] else []
    | _ => []
  let direct := match b.expr e with
    | .call _ f args | .tailCall _ f args =>
      match b.expr f with
      | .name none _ => args.toList
      | _ => (b.direct e).toList
    | _ => (b.direct e).toList
  let bodies : List (List Pattern × List StmtId) := match b.expr e with
    | .closure _ cs | .handle _ cs => cs.toList.map fun c => let cl := b.clause c; (cl.pats, cl.body.toList)
    | .labelScope _ body => [([], body.toList)]
    | _ => []
  here ++ direct.flatMap (appliedExpr b p) ++ bodies.flatMap fun (pats, body) =>
    if (pats.flatMap patVars).contains p then [] else appliedStmts b p body

partial def appliedStmts (b : Body) (p : String) : List StmtId → List Nat
  | [] => []
  | s :: rest =>
    match b.stmt s with
    | .located _ _ s => appliedStmts b p (s :: rest)
    | st =>
      let stops := match st with
        | .let_ pat _ => (patVars pat).contains p
        | .letMut x _ => x == p
        | _ => false
      (b.stmtExprs s).toList.flatMap (appliedExpr b p) ++ (if stops then [] else appliedStmts b p rest)

end

/--
Does a function give the callable passed as its `i`-th argument exactly one
argument, wherever it applies it? Whether a block written without parameters
takes an argument is decided by the type expected of it, which the checker
knows. A program the checker rejects can still be elaborated, to be run and
seen to go wrong; there are no types then, and this reading of the function's
definition stands in for them.
-/
def givesOne (b : Flat.Body) (i : Nat) : Bool :=
  !b.roots.isEmpty && b.roots.all fun c =>
    let ⟨pats, body⟩ := b.clause c
    match pats[i]? with
    | some (.var p) =>
      let counts := appliedStmts b p body.toList
      !counts.isEmpty && counts.all (· == 1)
    | _ => false

open Flat in
/-- Apply `fn` to the value a body ends with. A body that ends with a statement,
or with a `tail` call, which must stay the last thing done, has no such value. -/
partial def wrapResult (fn : String) : List StmtId → Build (Option (List StmtId))
  | [] => pure none
  | [s] => do
    match (← get).stmt s with
    | .expr e =>
      match (← get).expr e with
      | .tailCall .. => pure none
      | _ => pure (some [← pushStmt (.expr (← pushExpr (.call 0 (← pushExpr (.name none fn)) #[e])))])
    | .located line col inner =>
      match ← wrapResult fn [inner] with
      | some ss => some <$> ss.mapM fun s => pushStmt (.located line col s)
      | none => pure none
    | _ => pure none
  | s :: rest => do pure ((← wrapResult fn rest).map (s :: ·))

open Flat in
/-- A clause's value given to the coercion `fn`, where there is one. -/
def coercedClause (result : Option String) (c : ClauseId) : Build ClauseId := do
  let some fn := result | return c
  let ⟨pats, body⟩ := (← get).clause c
  match ← wrapResult fn body.toList with
  | some body => pushClause ⟨pats, body.toArray⟩
  | none => pure c

open Flat in
/-- The coercions the checker decided on, written out as the calls they are. -/
def coerceRewrite (cs : Std.HashMap Site String) : FRewrite where
  onExpr go b e :=
    let args := fun (call : Nat) (as : Array ExprId) => as.toList.zipIdx.toArray.mapM fun (a, i) => (do
      let a ← go.ex a
      match cs[Site.arg call i]? with
      | some fn => pushExpr (.call 0 (← pushExpr (.name none fn)) #[a])
      | none => pure a : Build ExprId)
    match b.expr e with
    | .call id f as => some (do pushExpr (.call id (← go.ex f) (← args id as)))
    | .tailCall id f as => some (do pushExpr (.tailCall id (← go.ex f) (← args id as)))
    | .closure id clauses => some (do
      let cs' ← clauses.toList.zipIdx.toArray.mapM fun (c, j) => do
        coercedClause cs[Site.result id j]? (← go.clause c)
      pushExpr (.closure id cs'))
    | _ => none

/-- A clause with the coercions in it written out, its value given to the
coercion `result`, where there is one. -/
def coerceClause (cs : Std.HashMap Site String) (result : Option String) (c : Flat.ClauseId) : Flat.Build Flat.ClauseId := do
  coercedClause result (← (coerceRewrite cs).clause c)

/-- A top-level function's body with its coercions written out. -/
def coerceFn (cs : Std.HashMap Site String) (name : String) (b : Flat.Body) : Flat.Body :=
  if cs.isEmpty then b else
  -- (A copy made for the types it is used at, `f⟨2,2⟩'`, is coerced as the
  -- function it is a copy of.)
  let name := (name.splitOn "⟨").headD name
  let (roots, b) := (b.roots.toList.zipIdx.toArray.mapM fun (c, j) => coerceClause cs cs[Site.fnResult name j]? c).run b
  { b with roots }

/-! ## Names and patterns -/

/-- Resolve a name to a constructor, following constructor aliases. -/
partial def resolveCtor (name : String) (qual : Option String) : M (Option CtorInfo) := do
  let g ← read
  match g.ctors[name]? with
  | some info =>
    match qual with
    | some q =>
      if q == info.owner then pure (some info)
      else throw s!"`{name}` is not a constructor of `{q}`"
    | none => pure (some info)
  | none =>
    -- `[a, b, c]` in a pattern: the constructor that builds an array of so
    -- many elements.
    if let some n := Syntax.fixedPatLen name then
      return some { owner := "", tag := fixedBase + n, arity := n, single := true }
    match (g.aliases[name]?).map Syntax.aliasValue with
    | some (.name q y) => resolveCtor y q
    | _ => pure none

/-- Does a bare name in a pattern bind a variable? -/
def isBinder (x : String) : M Bool := do
  if (← resolveCtor x none).isSome then return false
  return !(← read).aliases.contains x

/-- Does this pattern match every value? Decided from its shape alone, as the
checker decides it. -/
partial def irrefutable : Pattern → M Bool
  | .wild => pure true
  | .int _ | .ctor _ _ _ => pure false
  | .tuple ps => ps.allM irrefutable
  | .var x => isBinder x

end Glorious.Elab
