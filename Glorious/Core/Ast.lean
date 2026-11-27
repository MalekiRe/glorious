module

public import Glorious.Control
public import Std.Data.HashSet

/-!
# Core syntax

Core is the elaborated kernel language: every intermediate result is named and
every callable is a closed function with an explicit capture list. This file
covers data, closures, calls, tail calls, pattern callables, and effects with
handlers and resumptions, label scopes, guaranteed cleanup, and host
operations.
-/

@[expose] public section

namespace Glorious.Core

/-- A structural pattern. Binders are positional: each `bind` appends the
matched value to the environment, left to right. -/
inductive Pat where
  /-- Matches anything and binds nothing. -/
  | wild
  /-- Matches anything and binds it. -/
  | bind
  /-- Matches one integer constant. -/
  | int (n : Int)
  /-- Matches a `struct` or `enum` value with this constructor tag and one
  sub-pattern per field. -/
  | ctor (tag : Nat) (args : List Pat)
  deriving Hashable, BEq

/-- A Core computation. Each binding form appends its result to the environment. -/
inductive Tm where
  /-- Return a value to the caller. -/
  | ret (a : Atom)
  /-- Bind the result of a control-free computation. -/
  | let_ (rhs : Rhs) (body : Tm)
  /-- Call a callable and bind its result. -/
  | call (f : Atom) (args : List Atom) (body : Tm)
  /-- Call a callable in place of the current activation. -/
  | tail (f : Atom) (args : List Atom)
  /-- Run the callable `thunk` under a handler and bind the handler's result.
  `ret` is the function run on normal completion; `ops` maps each handled
  operation to the function serving it; all of them share `captures`. -/
  | handle (ret : Nat) (ops : List (Nat × Nat)) (captures : List Atom) (thunk : Atom) (body : Tm)
  /-- Perform a terminal operation: the computation up to its handler is abandoned. -/
  | raise (op : Nat) (args : List Atom)
  /-- Perform a resumptive operation and bind the value it is resumed with. The
  serving function receives the arguments followed by the resumption, which can
  be used once. -/
  | perform (op : Nat) (args : List Atom) (body : Tm)
  /-- Run the callable `thunk` inside a fresh label scope, passing it the label,
  and bind the scope's result. Applying the label to a value leaves the scope
  with that value. -/
  | label (thunk : Atom) (body : Tm)
  /-- `handle` whose result is the result of the current activation: no caller
  frame is kept, so a handler re-installed by a tail call does not grow the stack. -/
  | handleTail (ret : Nat) (ops : List (Nat × Nat)) (captures : List Atom) (thunk : Atom)
  /-- `label` whose result is the result of the current activation. -/
  | labelTail (thunk : Atom)
  /-- Run the callable `thunk` and bind its result, with `cleanup` guaranteed to
  run when `thunk`'s computation is left by any path: a normal return, a label
  exit, a terminal operation, or cancellation of a resumption that captured it. -/
  | guard (cleanup : Atom) (thunk : Atom) (body : Tm)
  /-- `guard` whose result is the result of the current activation. -/
  | guardTail (cleanup : Atom) (thunk : Atom)
  /-- Give up a callable without calling it; the result is unit. For a
  resumption, the cleanups of the continuation it captured run, innermost
  first. For a function or a label there is nothing to do. -/
  | cancel (k : Atom) (body : Tm)
  /-- Run the callable `thunk` in the scope of a fresh memory cell holding
  `init`, passing it a reference to the cell, and bind the scope's result. The
  cell is released when the scope is left, by any path: nothing else releases
  a cell, so none is released twice. -/
  | cell (init : Atom) (thunk : Atom) (body : Tm)
  /-- `cell` whose result is the result of the current activation. -/
  | cellTail (init : Atom) (thunk : Atom)
  /-- `cell` and `cellTail` of a cell of memory, its value laid out so and its
  reference an address (the typed lowering's). -/
  | cellL (lay : Laid) (init : Atom) (thunk : Atom) (body : Tm)
  | cellTailL (lay : Laid) (init : Atom) (thunk : Atom)
  /-- Lend a reference: call `thunk` with a reference to the same cell that is
  a borrow of its own, between the arguments `pre` and `post`, and bind the
  result. The borrow lasts as long as the call does; `uniq` says whether it is
  for writing too. But for the borrow this is a call: the scope changes nothing
  the program computes. It is there, with the borrow a reference carries, so
  that respecting a borrow has a meaning. -/
  | lend (uniq : Bool) (r : Atom) (thunk : Atom) (pre post : List Atom) (body : Tm)
  /-- Perform a memory operation and bind its result. -/
  | mem (op : MemOp) (args : List Atom) (body : Tm)
  /-- Ask the host to perform operation `id` and bind its result. -/
  | host (id : Nat) (args : List Atom) (body : Tm)
  deriving Hashable, BEq

/-- One clause of a callable: one pattern per argument, and a body. The body
runs in the environment `arguments ++ captures ++ pattern bindings`. -/
structure Clause where
  pats : List Pat
  body : Tm
  deriving Hashable, BEq

/-- A callable: ordered clauses, the first matching one runs. -/
structure Fn where
  clauses : List Clause

structure Program where
  fns : Array Fn
  main : Tm
  /-- The functions that say how a closure of them is destroyed: for each such
  function, the function that destroys what a closure of it captured, given
  the captures as its arguments. `cancel` of such a closure calls it. -/
  drops : List (Nat × Nat) := []
  /-- Each function's name, by its index: what a program is told of a
  callable of its own (`Host.call` 9). -/
  names : Array String := #[]
  /-- Bytes the program has from its start, each in a block of its own that
  is never freed (`MemOp.staticAt`): its text literals. -/
  statics : List (List Nat) := []

/-- Each static operation that has its bytes written out (`MemOp.staticAt`,
as the elaborator writes it) made one of a block of the program's, the same
bytes one block: what a compile that took a function from an earlier one
makes alike. -/
partial def Program.internStatics (p : Program) : Program := Id.run do
  let mut table : List (List Nat) := p.statics
  let rec go (table : List (List Nat)) : Tm → Tm × List (List Nat)
    | .mem .staticAt args body =>
      let bytes := args.filterMap fun a => match a with | .int b => some b.toNat | _ => none
      let (table, i) := match table.idxOf? bytes with
        | some i => (table, i)
        | none => (table ++ [bytes], table.length)
      let (body, table) := go table body
      (.mem .staticAt [.int i] body, table)
    | .let_ rhs body => let (b, t) := go table body; (.let_ rhs b, t)
    | .call f args body => let (b, t) := go table body; (.call f args b, t)
    | .handle ret ops caps thunk body => let (b, t) := go table body; (.handle ret ops caps thunk b, t)
    | .perform op args body => let (b, t) := go table body; (.perform op args b, t)
    | .label thunk body => let (b, t) := go table body; (.label thunk b, t)
    | .guard c thunk body => let (b, t) := go table body; (.guard c thunk b, t)
    | .cancel k body => let (b, t) := go table body; (.cancel k b, t)
    | .cell i thunk body => let (b, t) := go table body; (.cell i thunk b, t)
    | .cellL l i thunk body => let (b, t) := go table body; (.cellL l i thunk b, t)
    | .lend u r thunk pre post body => let (b, t) := go table body; (.lend u r thunk pre post b, t)
    | .mem op args body => let (b, t) := go table body; (.mem op args b, t)
    | .host id args body => let (b, t) := go table body; (.host id args b, t)
    | tm => (tm, table)
  let mut fns : Array Fn := #[]
  for F in p.fns do
    let mut clauses : List Clause := []
    for c in F.clauses do
      let (body, t) := go table c.body
      table := t
      clauses := clauses ++ [{ c with body }]
    fns := fns.push { F with clauses }
  let (main, t) := go table p.main
  pure { p with fns, main, statics := t }

/-- The functions a computation uses, each made `f` of itself. -/
def Tm.mapFns (f : Nat → Nat) : Tm → Tm
  | .let_ (.closure fn cs) b => .let_ (.closure (f fn) cs) (b.mapFns f)
  | .let_ r b => .let_ r (b.mapFns f)
  | .handle back ops cs t b => .handle (f back) (ops.map fun (o, g) => (o, f g)) cs t (b.mapFns f)
  | .handleTail back ops cs t => .handleTail (f back) (ops.map fun (o, g) => (o, f g)) cs t
  | .call g as b => .call g as (b.mapFns f)
  | .perform o as b => .perform o as (b.mapFns f)
  | .label t b => .label t (b.mapFns f)
  | .guard c t b => .guard c t (b.mapFns f)
  | .cancel k b => .cancel k (b.mapFns f)
  | .cell i t b => .cell i t (b.mapFns f)
  | .cellL l i t b => .cellL l i t (b.mapFns f)
  | .lend u r t pre post b => .lend u r t pre post (b.mapFns f)
  | .mem op as b => .mem op as (b.mapFns f)
  | .host id as b => .host id as (b.mapFns f)
  | t => t

/-- The blocks of bytes a computation names (`MemOp.staticAt`), each made
`f` of itself. -/
def Tm.mapStatics (f : Int → Int) : Tm → Tm
  | .mem .staticAt [.int i] b => .mem .staticAt [.int (f i)] (b.mapStatics f)
  | .let_ r b => .let_ r (b.mapStatics f)
  | .handle back ops cs t b => .handle back ops cs t (b.mapStatics f)
  | .call g as b => .call g as (b.mapStatics f)
  | .perform o as b => .perform o as (b.mapStatics f)
  | .label t b => .label t (b.mapStatics f)
  | .guard c t b => .guard c t (b.mapStatics f)
  | .cancel k b => .cancel k (b.mapStatics f)
  | .cell i t b => .cell i t (b.mapStatics f)
  | .cellL l i t b => .cellL l i t (b.mapStatics f)
  | .lend u r t pre post b => .lend u r t pre post (b.mapStatics f)
  | .mem op as b => .mem op as (b.mapStatics f)
  | .host id as b => .host id as (b.mapStatics f)
  | t => t

/-- The functions a computation names, in order. -/
partial def Tm.fnRefs : Tm → List Nat
  | .ret _ => []
  | .let_ rhs body =>
    (match rhs with
      | .closure fn _ => [fn]
      | _ => []) ++ body.fnRefs
  | .call _ _ body => body.fnRefs
  | .tail _ _ => []
  | .handle back ops _ _ body => back :: ops.map (·.2) ++ body.fnRefs
  | .handleTail back ops _ _ => back :: ops.map (·.2)
  | .raise _ _ => []
  | .perform _ _ body | .label _ body => body.fnRefs
  | .labelTail _ => []
  | .cell _ _ body | .cellL _ _ _ body | .lend _ _ _ _ _ body => body.fnRefs
  | .cellTail _ _ | .cellTailL _ _ _ => []
  | .guard _ _ body => body.fnRefs
  | .guardTail _ _ => []
  | .cancel _ body | .mem _ _ body | .host _ _ body => body.fnRefs

/-- Each function as another compile of the program knows it, wherever it
stands there: by its name and which of those of the name it is; a closure,
which has none, by the function that first makes it and which of what that
one names it is; what destroys a closure of one, after what it names. So an
edit that moves the others, `main`'s reaching the copies in another order,
names none of them anew. -/
def Program.sids (p : Program) : Array UInt64 := Id.run do
  let top := p.names.size
  let mut sids : Array UInt64 := (p.names.foldl (fun (acc : Array UInt64 × Std.HashMap String Nat) nm =>
      let k := acc.2.getD nm 0
      (acc.1.push (hash (nm, k)), acc.2.insert nm (k + 1))) (#[], {})).1
  sids := sids ++ ((List.range (p.fns.size - top)).map fun k => hash (top + k)).toArray
  let dropsBy : Std.HashMap Nat Nat := p.drops.foldl (fun m (f, d) => m.insertIfNew f d) {}
  let mut known : Std.HashSet Nat := {}
  let mut queue : Array Nat := (List.range top).toArray
  let mut i := 0
  while i < queue.size do
    let f := queue[i]!
    i := i + 1
    let refs := (((p.fns[f]?).map fun F => F.clauses.flatMap fun c => c.body.fnRefs).getD [])
      ++ (dropsBy[f]?).toList
    for (g, j) in refs.zipIdx do
      if top ≤ g && !known.contains g then
        known := known.insert g
        sids := sids.set! g (mixHash sids[f]! (hash j))
        queue := queue.push g
  pure sids

/-- A computation as another compile of the program knows it: each function
it names by `sids` (`Program.sids`), each block of bytes by its bytes. -/
def Program.keyed (p : Program) (sids : Array UInt64) (t : Tm) : Tm :=
  let statics := p.statics.toArray
  (t.mapFns fun g => ((sids[g]?).getD (hash g)).toNat).mapStatics fun i => (hash (statics[i.toNat]?)).toNat

end Glorious.Core
