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

/-- What at a place is destroyed (`DropSite`). -/
inductive SiteName where
  /-- What the name `x` holds: a variable's, a clause's name's, or a name the
  elaborator makes (`wildName`, `stmtValue`). -/
  | name (x : String)
  /-- What a name bound by the pattern of a `let` holds: the place is the
  statement's, which a clause's own names are known by too when the
  statement is its first. -/
  | letBound (x : String)
  /-- What a callable captured of `x`, if it is let go without being called. -/
  | capture (x : String)
  /-- What `x` holds, where it is not given away on every path: the flag that
  says whether it was (`Syntax.movedFlag`). -/
  | given (x : String)
  /-- A part of `x` with something to destroy, taken at the node the site's
  place says (`takenSite`): `x`'s flag is set there too. -/
  | taken (x : String)
  /-- The part `i` of `x`'s value, where the part is never read. -/
  | part (x : String) (i : Nat)
  /-- What is written through a reference, `*r = v`: what it held. -/
  | deref
  deriving BEq, Hashable, Inhabited

/-- The name of what is destroyed, for the call that destroys it and for
messages. -/
def SiteName.var : SiteName → String
  | .name x | .letBound x | .capture x | .given x | .taken x | .part x _ => x
  | .deref => "*"

/-- A place where what a variable holds is destroyed: where the variable is
declared, for the end of its block, or where it is assigned, for what it held. -/
structure DropSite where
  owner : String
  line : Nat
  col : Nat
  name : SiteName
  assign : Bool
  deriving BEq, Hashable

/-- The site under which the checker says that the part of `x` read at the
node `node` (its identity, `Flat.Body.ids`) has something to destroy: where
it is taken, `x` is given away. -/
def takenSite (owner : String) (node : Nat) (x : String) : DropSite :=
  ⟨owner, 0, node, .taken x, false⟩

/-- The site under which the checker says how what `x` holds is destroyed when
the callable written as `written` (its hash), which captured it, is let go. -/
def captureDropSite (owner : String) (written : UInt64) (x : String) : DropSite :=
  ⟨owner, written.toNat, 0, .capture x, false⟩

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
  checker gave (`knownOf`, by the object): a function is written out for
  each set of them it is given (`Elab.untraitFn`), its calls of copies
  found by these numbers, and not by the implementations, of a size that
  grows with how deep the types are. -/
  knownPool : Array (String × List Nat) := #[]
  knownIds : Std.HashMap (String × List Nat) Nat := {}
  knownOf : Std.HashMap USize Nat := {}
  /-- What the type parameters of an implementation are, by its dictionary
  object, those the checker found (`Check.St.dictTypes`); and by its
  number (`index`): what a copy of its functions is written out at. -/
  dictTypes : Std.HashMap USize (List (String × TypeExpr)) := {}
  knownTypes : Std.HashMap Nat (List (String × TypeExpr)) := {}
  /-- What each implementation, by the function that makes it a value,
  gives what its trait leaves to it (`Check.implAssocs`). -/
  assocs : Std.HashMap String (List (String × TypeExpr)) := {}

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

/-- The function that makes an implementation a value. -/
def implDictName (trait head : String) : String := s!"impl {trait} for {head}"

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
    -- (None where two objects of one number say other types.)
    knownTypes := numbered.byObject.fold (init := {}) fun m k (_, r) => match r, t.dictTypes[k]? with
      | some n, some ts => match m[n]? with
        | some had => if had == ts then m else m.insert n []
        | none => m.insert n ts
      | _, _ => m
    dictsAt := firstOf t.dicts, methodsAt := firstOf t.methods
    -- (And each destroyer, given how its parts are destroyed: copied for
    -- those as any function for the implementations it is given.)
    boundedAt := firstOf (t.bounded ++ t.destroys.flatMap fun D =>
      if D.given == 0 then [] else
      [(Syntax.implFnName Syntax.destroyTrait D.head Syntax.destroyFn, D.given),
       ("%destroy from " ++ D.head, D.given), ("%fields " ++ D.head, D.given)])
    -- (And each destroyer's value: an implementation known as any other.)
    implsAt := firstOf ((t.impls.map fun im => (im.dictFn, im)) ++ t.destroys.map fun D =>
      let dictFn := implDictName Syntax.destroyTrait D.head
      (dictFn, ({ dictFn, conditions := D.given,
                  methods := [(Syntax.implFnName Syntax.destroyTrait D.head Syntax.destroyFn, 1)] } : ImplE)))
    dropsAt := firstOf t.drops
    partsAt := t.drops.foldl (fun m (site, _) =>
      match site.name, site.assign with
      | .part x _, false =>
        m.alter (site.owner, site.line, site.col, x) fun
          | some sites => some (sites.push site)
          | none => some #[site]
      | _, _ => m) {} }


/-- What the checker finds of how a program is to be read once it knows
types, kept by the node it is at (`St.adjust`, as rustc's `TypeckResults`)
where the elaborator or a later check needs to be told it: `..` in a
tuple, and the locals that are places, which the elaborator makes cells
(`Elab.promote`). Every other adjustment is written where it is found, in
the body the checker reads on and the elaborator elaborates
(`Blocks.bodies`): nothing is read again for one. -/
inductive Adjust where
  /-- `..` in the tuple pattern `id` stands for `count` parts, written where
  it is (`restNode`). -/
  | rest (id count : Nat)
  /-- In `owner`, what the `let` of `x` at `line:col` binds (or, at `0:0`, a
  clause binds) is a place: kept in a variable (`Elab.promote`). -/
  | place (owner : String) (line col : Nat) (x : String)

/-- `&mut x` of a name that holds a `&mut`, at the node whose identity is
`node`, written as the borrow again through it that it is, `&mut *x`, as
the checker reads it and the elaborator writes it
(`Check.inferExprRef`): where `x` is made a variable (borrowed
elsewhere), `&mut x` would be of the variable. -/
def reborrowNode (node : Nat) (x : String) (b : Flat.Body) : Option Flat.Body := do
  let e ← (List.range b.exprs.size).reverse.find? fun i => b.idOf i == node && match b.exprs[i]! with
    | .ref true y => y == x
    | _ => false
  let (n, b) := b.add (.name none x)
  pure { b with exprs := b.exprs.set! e (.reborrow true n) }

/-- Is `g` the function that reads an element where it is, `element_at`
or `place_at` (`Syntax.elementRead`), which gives a reference to it? -/
def elementCall (b : Flat.Body) (g : Flat.ExprId) : Bool :=
  match b.name? g with
  | some (_, x) => let n := Syntax.lastSegment x; n == "element_at" || n == "place_at"
  | none => false

/-- A receiver as written, the mark the resolver puts on one it could not
tell how to give (`Syntax.Mark.receiver`) taken off. -/
def unmarked (b : Flat.Body) (e : Flat.ExprId) : Flat.ExprId :=
  match b.expr e with
  | .call _ m #[r] => if b.mark? m == some .receiver then r else e
  | _ => e

/-- (Each of these finds the node by its identity from the last: a body
written again keeps what it was made of before it, which nothing reaches,
and the node read is the one made last.)

The dot call `call`'s node written where it is, as the checker reads it
on (`Check.receiverHere`) and the elaborator writes it: of `fn` where
given, its receiver a name borrowed (`some uniq`) or given as it is (what
is no name given whole, as it is written). None where what is borrowed is
no name (`receiverFieldNode`). -/
def receiverNode (call : Nat) (fn : Option String) (borrow : Option Bool) (b : Flat.Body)
    (at_ : Option Flat.ExprId := none) : Option Flat.Body := do
  -- (The checker says which node: its body has copies of nodes it made to
  -- read the call, with its number.)
  let e ← at_.orElse fun _ => (List.range b.exprs.size).reverse.find? fun i => match b.exprs[i]! with
    | .call i _ _ | .tailCall i _ _ => i == call
    | _ => false
  let (tail, f, args) ← match b.exprs[e]! with
    | .call _ f args => some (false, f, args)
    | .tailCall _ f args => some (true, f, args)
    | _ => none
  let (callee, recv, rest) ← match b.expr f, fn with
    | .fieldOf _ recv _, some g => some (Flat.FExpr.name none g, unmarked b recv, args)
    | _, _ =>
      let callee := match fn with
        | some g => Flat.FExpr.name none g
        | none => b.expr f
      if h : 0 < args.size then some (callee, unmarked b args[0], args.extract 1 args.size) else none
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
      | p@(.marked .rest [.int i]) => if i.toNat == id then List.replicate count Pattern.wild else [p]
      | p => [restPat id count p])
  | .ctor c q ps => .ctor c q (ps.map (restPat id count))
  | p => p

/-- Every pattern of the body with `..` of the tuple pattern `id` written as
`count` parts, where it is: the patterns of `let`s and of clauses, in place,
no node made anew (`Adjust.rest`). None where none has it. -/
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
the elaborator writes it (`Check.etaArity`). -/
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

/-- The dot call `call`, its receiver a value that is copied, given a copy
of it, borrowed: `{ let mut r = x; f(&r, ..) }`, written where it is
(`Check.checkLateReceivers`). For a receiver whose type was known only once
the call's function was (`Check.checkLateReceivers`): the copy is the
value, as a borrow of it would read it. -/
def receiverCopyNode (call : Nat) (b : Flat.Body) : Option Flat.Body := do
  let e ← (List.range b.exprs.size).reverse.find? fun i => match b.exprs[i]! with
    | .call i _ _ | .tailCall i _ _ => i == call
    | _ => false
  let (f, args) ← match b.exprs[e]! with
    | .call _ f args | .tailCall _ f args => some (f, args)
    | _ => none
  let some recv := args[0]? | none
  let held := s!"%copied{call}"
  let (ge, b) := b.add (.ref false held)
  let (ce, b) := b.add (.call call f (#[ge] ++ args.extract 1 args.size))
  let first := b.stmts.size
  let b := { b with stmts := b.stmts.push (.letMut held recv) }
  let last := b.stmts.size
  let b := { b with stmts := b.stmts.push (.expr ce) }
  pure { b with exprs := b.exprs.set! e (.labelScope "%block" #[first, last]) }

/-- The dot call `call`, its receiver a field of a name, `p.x.len()`,
borrowed where it is, `len(&p.x)` (through the reference the name holds
where `star`), of `fn` where given: as the checker reads it on and the
elaborator writes it (`Check.receiverHere`). None where the receiver
is not such a field. -/
def receiverFieldNode (call : Nat) (fn : Option String) (uniq star : Bool) (b : Flat.Body)
    (at_ : Option Flat.ExprId := none) : Option Flat.Body := do
  let e ← at_.orElse fun _ => (List.range b.exprs.size).reverse.find? fun i => match b.exprs[i]! with
    | .call i _ _ | .tailCall i _ _ => i == call
    | _ => false
  let (tail, f, args) ← match b.exprs[e]! with
    | .call _ f args => some (false, f, args)
    | .tailCall _ f args => some (true, f, args)
    | _ => none
  let (callee, recv, rest) ← match b.expr f, fn with
    | .fieldOf _ recv _, some g => some (Flat.FExpr.name none g, unmarked b recv, args)
    | _, _ =>
      let callee := match fn with
        | some g => Flat.FExpr.name none g
        | none => b.expr f
      if h : 0 < args.size then some (callee, unmarked b args[0], args.extract 1 args.size) else none
  -- (The way from the name to the field, and the outermost field's number;
  -- or from what a reference points to, `v[0].s` of `*element_at(&v, 0)`.)
  let rec chain (x : Flat.ExprId) (fuel : Nat) : Option (Sum String Flat.ExprId × List String × Nat) :=
    match fuel, b.expr x with
    | fuel + 1, .fieldOf fid inner name =>
      match b.bare? inner, b.expr inner with
      | some root, _ => some (.inl root, [name], fid)
      | none, .deref r => some (.inr r, [name], fid)
      -- (An element read where it is gives a reference to it.)
      | none, .call _ g _ =>
        if elementCall b g then some (.inr inner, [name], fid)
        else (chain inner fuel).map fun (root, path, _) => (root, path ++ [name], fid)
      | none, _ => (chain inner fuel).map fun (root, path, _) => (root, path ++ [name], fid)
    | _, _ => none
  let (root, path, fid) ← chain recv 64
  if fid == 0 then none
  let (fe, b) := b.add callee
  let node := fun (ge : Flat.ExprId) =>
    if tail then Flat.FExpr.tailCall call fe (#[ge] ++ rest) else .call call fe (#[ge] ++ rest)
  match root with
  | .inl x =>
    let (ge, b) := b.add (.refField fid uniq x path star)
    pure { b with exprs := b.exprs.set! e (node ge) }
  | .inr r =>
    -- (The reference kept for the call, the field borrowed through it:
    -- `{ let r = element_at(&v, 0); len(&(*r).s) }`.)
    let held := s!"%through{call}"
    let first := b.stmts.size
    let b := { b with stmts := b.stmts.push (.let_ (.var held) r) }
    let (ge, b) := b.add (.refField fid uniq held path true)
    let (ce, b) := b.add (node ge)
    let last := b.stmts.size
    let b := { b with stmts := b.stmts.push (.expr ce) }
    pure { b with exprs := b.exprs.set! e (.labelScope "%block" #[first, last]) }

/-- The field read `id`, `x.f` of a name, written of what `deref` gives of
it where it is: `deref(&x).f` (`borrow` is `some false`) or `deref(x).f`
(`x` a reference), as the checker reads it on and the elaborator writes it
(`Check.derefHere`). -/
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
reads it on and the elaborator writes it (`Check.derefRefHere`). -/
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
elaborator writes it (`Check.derefAssignHere`). -/
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
reads on (`Check.compareByType`). -/
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
(`Check.checkArgsIn`). The nodes the clauses are made of are known in a
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

/-- What a message the checker stops with is of, where what says it more
reads that: a type that would contain itself, an effect not handled there,
lifetimes that do not fit, a mismatch (`unifyAt`), a function used in its
group at another type, a field a type does not have. -/
inductive SaidKind where
  | occurs | unhandled | lifetime | mismatch | recursiveUse | noField
  deriving BEq

/-- What the checker says where it stops: why, and what it found to decide,
where it stops for that; `result` where what does not fit is a clause's
result; what it is of (`kinds`), and of a mismatch the types expected and
found, as said. -/
structure Said where
  msg : String
  result : Bool := false
  kinds : List SaidKind := []
  expected : String := ""
  found : String := ""

instance : Coe String Said := ⟨fun msg => { msg }⟩

/-- The same, said otherwise: what it found kept. -/
def Said.map (s : Said) (f : String → String) : Said := { s with msg := f s.msg }

/-- What the checker tells the elaborator about the blocks of a program, each
named by its identity. -/
structure Blocks where
  /-- The locals of each function the checker found to be places (borrowed
  where they are), by the `let` (`line:col`) or, at `0:0`, the clause that
  binds them: each made a cell where it is bound (`Elab.promote`). -/
  places : Std.HashMap String (List (Nat × Nat × String)) := {}
  /-- Each function's body as the checker read it, with what it wrote where
  it found it (`Adjust`), by the name it is checked by: what is
  elaborated in place of the body as written. -/
  bodies : Std.HashMap String Flat.Body := {}
  /-- Of each function, the type of each expression whose type the checker
  knows whole, by the node's identity. -/
  nodeTys : Std.HashMap String (Std.HashMap Nat Syntax.TypeExpr) := {}
  /-- Of each function, at each call of a named function, by the callee's
  node: what each of the callee's type parameters is there. -/
  nodeInsts : Std.HashMap String (Std.HashMap Nat (List (String × Option Syntax.TypeExpr))) := {}
  traits : TraitInfo := {}
  /-- For each function that performs or handles an operation of an effect
  with type parameters, or calls one that does: the places, by the number of
  the call, with which of `op`, `handle`, `call`, `ref` each is, the effect or
  the function called, and where its types are among the function's. -/
  sites : List (String × List (Nat × String × String × Nat × Nat)) := []
  /-- Those types, each where it is known without knowing who calls the
  function. -/
  siteTypes : List (String × List (Option Syntax.TypeExpr)) := []

structure Globals where
  ctors : Std.HashMap String CtorInfo := {}
  ops : List (String × OpInfo) := []
  fns : Std.HashMap String Nat := {}
  aliases : Std.HashMap String Expr := {}
  /-- The body of each top-level function, by name. -/
  bodies : Std.HashMap String Flat.Body := {}
  /-- What the checker learnt about the program's blocks, if it was run. -/
  blocks : Option Blocks := none

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
  /-- Each local made for an expression of the body, with the expression's
  identity. -/
  nodes : Array (Nat × Nat) := #[]
  /-- The locals that hold a callable literal: its function and what it captured. -/
  literals : List (Nat × Nat × List Atom) := []
  /-- Those of them no name has referred to yet. -/
  unused : List Nat := []

/-- What elaborating one top-level function read that is not its own body:
kept with what it made (`ElabKept`), and read again before that is taken. -/
inductive ElabRead where
  | fn (name : String) (v : Option Nat)

structure St where
  fns : Array Core.Fn
  /-- A description of each function, for diagnostics. -/
  names : Array String
  /-- The top-level function being elaborated. -/
  owner : String
  b : Builder
  /-- Of each clause made and not yet a function's, the locals made for
  expressions of the body (`Builder.nodes`). -/
  clauseNodes : Array (Array (Nat × Nat)) := #[]
  /-- Of each function, the top-level function whose body its expressions
  are of, and of each clause the locals made for them. -/
  fnNodes : Std.HashMap Nat (String × List (Array (Nat × Nat))) := {}
  /-- Whether the body elaborated is the top-level function's own. -/
  ownBody : Bool := true
  /-- Why a `tail` call is not allowed at this point, if it is not: something
  still has to happen in this activation after the call returns. -/
  noTail : Option String
  /-- Where the statement being elaborated starts. -/
  pos : Nat × Nat := (0, 0)
  /-- How many calls the top-level function being elaborated split at a
  borrow's end (`splitCallOn`): the names of the parts taken out are of it. -/
  splits : Nat := 0
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
  drops : List (Nat × Nat)
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
      b := { ops := #[], depth := depth, done := none } }
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

/-- The number of the top-level function `x`, noted. -/
def fnAt (x : String) : M (Option Nat) := do
  let v := (← read).fns[x]?
  noteRead (.fn x v)
  pure v

/-- Is what `r` read still what it is? -/
def readHolds : ElabRead → M Bool
  | .fn x v => do pure ((← read).fns[x]? == v)

/-- What `after` has in front of `before`, where it is `before` with more in
front of it (the same object after them); none where it is not. -/
def prefixTo {α : Type} (after before : List α) : Option (List α) :=
  go after []
where
  go : List α → List α → Option (List α)
    | [], acc => if sameObj ([] : List α) before then some acc.reverse else none
    | l@(x :: r), acc => if sameObj l before then some acc.reverse else go r (x :: acc)

def addFn (f : Core.Fn) (name : String) : M Nat := do
  let k := f.clauses.length
  modifyGet fun s =>
    let made := s.clauseNodes.extract (s.clauseNodes.size - k) s.clauseNodes.size
    (s.fns.size, { s with fns := s.fns.push f, names := s.names.push name
                          clauseNodes := s.clauseNodes.shrink (s.clauseNodes.size - k)
                          fnNodes := s.fnNodes.insert s.fns.size (s.owner, made.toList) })

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

/-! ## Free names -/

partial def patVars : Pattern → List String
  | .wild => []
  | .var x => [x]
  | .int _ => []
  | .ctor _ _ args | .tuple args | .marked _ args => args.flatMap patVars

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
    -- (Each node made again known as it was, `Body.idOf`: what is found of
    -- a node is kept by it, `scalarLits`.)
    let same := fun (n : FExpr) => (modifyGet fun (bb : Body) => bb.add n (some (b.idOf e)) : Build ExprId)
    match b.expr e with
    | .call id f as => some (do same (.call id (← go.ex f) (← args id as)))
    | .tailCall id f as => some (do same (.tailCall id (← go.ex f) (← args id as)))
    | .closure id clauses => some (do
      let cs' ← clauses.toList.zipIdx.toArray.mapM fun (c, j) => do
        coercedClause cs[Site.result id j]? (← go.clause c)
      same (.closure id cs'))
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
  | .int _ | .ctor _ _ _ | .marked _ _ => pure false
  | .tuple ps => ps.allM irrefutable
  | .var x => isBinder x

/-- The copies asked for: each by its name, with the function it is of, the
implementations it is for, and whether their places are dropped. An
implementation with nothing left to be known is a number here (`pool`: its
function and its parts' numbers; `byId` back): so a copy is found, and a
body written out, without implementations looked at again and again. -/
structure Copies where
  pool : Std.HashMap (String × List Nat) Nat := {}
  byId : Array (String × List Nat) := #[]
  byKey : Std.HashMap (String × List Nat × Bool) String := {}
  /-- Each copy by its name: the function it is of, the implementations it
  is for, and whether their places are dropped. -/
  byName : Std.HashMap String (String × List Nat × Bool) := {}
  /-- What `askCopy` added, in order (`LowerKept`). -/
  asked : Array ((String × List Nat × Bool) × String) := #[]
  /-- The calls of the function being written out that are of a copy, by
  their numbers, each with the implementations it is for: named once the
  function's copies for effects are made (`callsCopied`), which name the
  function called first. -/
  calls : Array (Nat × List Nat) := #[]
  /-- The spreads written out for a length (`spreadItem`), by the name each
  is called by: which, and the length. -/
  spreads : Std.HashMap String (String × Nat) := {}
  /-- What the type parameters of each implementation numbered here are,
  of those made from what a function is given (`resolveDict`), where the
  checker found them (`TraitInfo.dictTypes`). -/
  types : Std.HashMap Nat (List (String × TypeExpr)) := {}

def internId (f : String) (ids : List Nat) : StateM Copies Nat := do
  match (← get).pool[(f, ids)]? with
  | some n => pure n
  | none =>
    let n := (← get).byId.size
    modify fun c => { c with pool := c.pool.insert (f, ids) n, byId := c.byId.push (f, ids) }
    pure n

def askCopy (fn : String) (ids : List Nat) (drop : Bool) : StateM Copies String := do
  let key := (fn, ids, drop)
  if let some name := (← get).byKey[key]? then return name
  let name := s!"{fn}⟨{",".intercalate (ids.map toString)}⟩{if drop then "'" else ""}"
  modify fun c => { c with byKey := c.byKey.insert key name, byName := c.byName.insert name key
                           asked := c.asked.push (key, name) }
  pure name

/-- Which of the prelude's spreads `g` is. -/
def spreadKind (g : String) : Option String :=
  if g == "spread_split" || g == "spread_split_as" then some "split"
  else if g == "spread_cons" || g == "spread_cons_as" then some "cons"
  else if g == "spread_snoc" || g == "spread_snoc_as" then some "snoc"
  else if g == "spread_call" || g == "spread_call_as" then some "call"
  else none

/-- How long a list is, by the implementation of `Spread` it has: one for
`()`, or one for its first and rest given the rest's. -/
def spreadLength (byId : Array (String × List Nat)) (i : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    match byId[i]? with
    | some (f, []) => if f.startsWith (implDictName "Spread" "") then some 0 else none
    -- (The rest's `Spread` first; after it, how what is held is destroyed,
    -- where the program asks that of the parts too.)
    | some (f, j :: _) =>
      if f.startsWith (implDictName "Spread" "") then (spreadLength byId j fuel).map (· + 1) else none
    | _ => none

end Glorious.Elab
