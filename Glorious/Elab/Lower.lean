module

public import Glorious.Elab
public import Glorious.Elab.Instances
public import Glorious.Elab.Specialize

/-!
# Lowering what is reached

Once a program is checked it is lowered for the elaborator: its traits made
values (`untraitFn`), its fields written out (`unfieldItem`), each function
about an effect's instance written for each (`instancesOf`), a copy of each
function for each known implementation it is called with (`specCopy`), and
its constants worked out (`foldConstants`). Of a program with its library,
most of that is what nothing the program runs reaches: on `covey/states2`,
3,190 of 18,403 functions.

So a function is lowered only when something lowered names it, from `main`
and the coercions on: a worklist, as the elaborator then reads them. What is
worked out for the whole program first is only what reads the checker's
tables (which functions are copied for effects, where coercions are), and
each function's way to be made, not made.
-/

public section

namespace Glorious.Elab

open Glorious.Syntax

/-- A checked program to lower: each function by the name it has once
lowered, made only when asked (`fns`). -/
structure Lowering where
  /-- What the checker said, with the places of arguments where they are
  once traits are values. -/
  blocks : Blocks
  /-- The items that are not functions, lowered, in their order. -/
  others : Array Flat.FItem
  /-- Each function without traits, with its fields written out and for the
  instances of its effects: made the first time it is asked, and once. -/
  fns : Std.HashMap String (Unit → Option Flat.FItem)
  /-- The functions declared again after the first, which the elaborator
  refuses if one is reached. -/
  twice : List (String × (Unit → Option Flat.FItem))
  /-- What each constant names. -/
  aliasUses : Std.HashMap String (List String)

/-- A program as it is lowered: what is lowered, and the copies asked. -/
structure Lowered where
  copies : Copies
  /-- Whether copies are made for known implementations: not once more would
  be made than `copyFuel` (a function that calls itself with an
  implementation made from the one it was given), and then the program is
  lowered again without them. -/
  spec : Bool := true
  /-- What it was asked to reach. -/
  roots : List String := []
  seen : Std.HashSet String := {}
  /-- The functions lowered, in the order they were reached. -/
  done : Array Flat.FItem := #[]
  made : Nat := 0

/-- How many copies are made at most. -/
def copyFuel : Nat := 50000

/-- A checked program to lower, with `written` its declarations (the
effects with the types they declare). -/
def lowering (b : Blocks) (written : List Item) (items : List Flat.FItem) : Except String Lowering := do
  let tr := b.traits
  let inst ← instancesOf b written
  let info := fieldInfo b
  let mut others : Array Flat.FItem := #[]
  let mut fns : Std.HashMap String (Unit → Option Flat.FItem) := {}
  let mut twice : List (String × (Unit → Option Flat.FItem)) := []
  let mut aliasUses : Std.HashMap String (List String) := {}
  for part in items.flatMap (untraitItem tr) ++ untraitExtra tr do
    match part with
    | .item item =>
      for o in inst.other item do
        others := others.push o
        if let .alias n ab e := o then aliasUses := aliasUses.insert n (ab.fvExpr [] e)
    | .fn name make =>
      -- (A function and every copy made of it for effects, made together.)
      let outs : Thunk (List Flat.FItem) := Thunk.mk fun _ => inst.fn (unfieldItem info (make ()))
      for n in inst.names name do
        let get := fun (_ : Unit) => outs.get.find? fun
          | .fn m .. => m == n
          | _ => false
        if fns.contains n then twice := (n, get) :: twice else fns := fns.insert n get
  pure { blocks := untraitBlocks b, others, fns, twice, aliasUses }

/-- Where lowering starts: no copy asked, the implementations numbered as the
checker numbered them. -/
def Lowering.start (L : Lowering) : Lowered :=
  { copies := { pool := L.blocks.traits.knownIds, byId := L.blocks.traits.knownPool } }

/-- Lowered on from `st`, through what `roots` reach; none if more copies
would be made than `copyFuel`. -/
def Lowering.reachWith (L : Lowering) (st : Lowered) (roots : List String) : Option Lowered := Id.run do
  let tr := L.blocks.traits
  let mut st := { st with roots := st.roots ++ roots }
  let mut todo : Array String := roots.reverse.toArray
  while !todo.isEmpty do
    let x := todo.back!
    todo := todo.pop
    if st.seen.contains x then continue
    st := { st with seen := st.seen.insert x }
    if let some uses := L.aliasUses[x]? then
      todo := todo ++ uses.reverse.toArray
      continue
    -- A copy for known implementations, made from the function it is of; or
    -- a function as it is, with the calls in it sent to copies if it is
    -- given no implementation.
    let (item, copies, made) := match st.copies.byName[x]? with
      | some (fn, ids, drop) =>
        match (L.fns[fn]?).bind (· ()) with
        | some item =>
          let (item, copies) := (specCopy tr x ids drop item).run st.copies
          (item, copies, st.made + 1)
        | none => (none, st.copies, st.made)
      | none =>
        match (L.fns[x]?).bind (· ()) with
        | some item =>
          if st.spec then
            let (item, copies) := (specRoot tr item).run st.copies
            (some item, copies, st.made)
          else (some item, st.copies, st.made)
        | none => (none, st.copies, st.made)
    if made > copyFuel then return none
    st := { st with copies, made }
    if let some (.fn name ps annots ret b) := item then
      -- (What is left of the implementations, as values: written out.)
      let b := unrefBody copies.byId b
      st := { st with done := st.done.push (.fn name ps annots ret b) }
      todo := todo ++ (b.fvClauses b.roots).reverse.toArray
  some st

/-- Lowered on from `st`, through what `roots` reach. -/
def Lowering.reach (L : Lowering) (st : Lowered) (roots : List String) : Lowered :=
  match L.reachWith st roots with
  | some st => st
  | none =>
    -- (Every function as it is, given its implementations as values.)
    let again := L.reachWith { L.start with spec := false } (st.roots ++ roots)
    again.getD { L.start with spec := false }

/-- What is lowered, as a program: its constants worked out, and each
function declared again where one is reached. -/
def Lowering.items (L : Lowering) (st : Lowered) : List Flat.FItem :=
  let again := L.twice.filterMap fun (n, get) => if st.seen.contains n then get () else none
  let items := foldConstants (L.others.toList ++ st.done.toList ++ again)
  if Glorious.Trace.groupsTraced then
    dbgTrace s!"lowered: {st.done.size} functions, {st.made} copies, {st.copies.byId.size} implementation values" fun _ => items
  else items

end Glorious.Elab
