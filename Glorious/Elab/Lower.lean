module

public import Glorious.Elab
public import Glorious.Elab.Instances
public import Glorious.Elab.Specialize

/-!
# Lowering what is reached

Once a program is checked it is lowered for the elaborator: its traits made
values (`untraitFn`), its fields written out (`unfieldItem`), each function
about an effect's instance written for each (`instancesOf`), a copy of each
function for each set of implementations it is given (`untraitFn` for them,
`askCopy`), and its constants worked out (`foldConstants`). Of a program with its library,
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
  others : Array Syntax.Item
  /-- Each function without traits, with its fields written out and for the
  instances of its effects: made for the implementations it is given, under
  the name it is asked by, when it is asked. -/
  fns : Std.HashMap String (Array Nat → String → StateM Copies (Option Syntax.Item))
  /-- The functions declared again after the first, which the elaborator
  refuses if one is reached. -/
  twice : List (String × (Array Nat → String → StateM Copies (Option Syntax.Item)))
  /-- What each constant names. -/
  aliasUses : Std.HashMap String (List String)
  /-- What each function is lowered from: the item it is written in, and its
  name (`LowerKept`). -/
  srcKeys : Std.HashMap String UInt64 := {}
  /-- What every function is lowered with: what the checker said of the
  program's traits, fields and effects, and the declarations (`LowerKept`). -/
  globalKey : UInt64 := 0

/-- What lowering one function made, kept for the next compile: by a key of
what it is lowered from (`Lowering.srcKeys`), of what every function is
lowered with (`Lowering.globalKey`), and of the copies asked before it in
order (`Lowered.chain`): the function as lowered, the implementations
numbered and the copies asked by it, in order, and whether it was a copy
made. Taken where the key is the same. -/
structure LowerKept where
  key : UInt64
  item : Option Syntax.Item
  pool : Array (String × List Nat)
  asked : Array ((String × List Nat × Bool) × String)
  made : Nat

/-- Each function's `LowerKept`, by its name once lowered. -/
abbrev LowerMemo := Std.HashMap String LowerKept

/-- A program as it is lowered: what is lowered, and the copies asked. -/
structure Lowered where
  copies : Copies
  /-- What it was asked to reach. -/
  roots : List String := []
  seen : Std.HashSet String := {}
  /-- The functions lowered, in the order they were reached. -/
  done : Array Syntax.Item := #[]
  made : Nat := 0
  /-- The copies asked so far and the implementations numbered, in order,
  as a hash (`LowerKept`). -/
  chain : UInt64 := 0
  /-- What an earlier compile kept of lowering each function. -/
  kept : LowerMemo := {}
  /-- What this one made, for the next. -/
  keptMade : LowerMemo := {}

/-- How many copies are made at most. -/
def copyFuel : Nat := 50000

private unsafe def dictHashU (d : DictE) : StateM (Std.HashMap USize UInt64) UInt64 := do
  let a := ptrAddrUnsafe d
  if let some h := (← get)[a]? then return h
  let h ← match d with
    | .param k => pure (hash (0, k))
    | .impl fn subs => subs.foldlM (fun h s => do pure (mixHash h (← dictHashU s))) (hash (1, fn))
  modify (·.insert a h)
  pure h

private unsafe def dictsKeyImpl (ds : List (Nat × List DictE)) : UInt64 :=
  (ds.foldlM (fun (acc : UInt64) ((n, es) : Nat × List DictE) => do
    pure (acc + (← es.foldlM (fun (h : UInt64) e => do pure (mixHash h (← dictHashU e))) (hash n)))) 0).run' {}

/-- How the bounds of each call are met, as a hash whatever order the calls
are in: each implementation hashed once however often it is shared (they are
shared, and hashed as trees they took half a second on covey/states2). -/
@[implemented_by dictsKeyImpl] def dictsKey (ds : List (Nat × List DictE)) : UInt64 :=
  ds.foldl (fun h x => h + hash x) 0

/-- A checked program to lower, with `written` its declarations (the
effects with the types they declare). -/
def lowering (b : Blocks) (written : List Item) (items : List Syntax.Item) : Except String Lowering := do
  let tr := b.traits
  let inst ← instancesOf b written
  let info := fieldInfo b
  let mut others : Array Syntax.Item := #[]
  let mut fns : Std.HashMap String (Array Nat → String → StateM Copies (Option Syntax.Item)) := {}
  let mut twice : List (String × (Array Nat → String → StateM Copies (Option Syntax.Item))) := []
  let mut aliasUses : Std.HashMap String (List String) := {}
  -- (Each function by the item it is written in; an implementation's by the
  -- implementation and its name.)
  let mut srcKeys : Std.HashMap String UInt64 := {}
  for item in items do
    let h := hash item
    match item with
    | .fn name .. => srcKeys := srcKeys.insert name h
    | .impl { trait := trait, head := head, methods := methods, .. } =>
      srcKeys := srcKeys.insert (implDictName trait.spelled head) h
      for m in methods do
        if let .fn mname .. := m then srcKeys := srcKeys.insert (implFnName trait.spelled head mname) (mixHash h (hash mname))
    | _ => pure ()
  -- (Of what the checker said, each part summed entry by entry: the same
  -- whatever order it was gathered in.)
  let sum := fun {α : Type} [Hashable α] (xs : List α) => xs.foldl (fun h x => h + hash x) (0 : UInt64)
  let globalKey := hash [dictsKey tr.dicts, sum tr.methods, sum tr.bounded, sum tr.impls, sum tr.drops,
    sum tr.destroys, hash tr.knownPool, sum b.fields.toList, sum b.fieldReads.toList, sum b.packs.toList,
    sum b.derefReads.toList, sum b.sites, sum b.siteTypes, hash written]
  for part in items.flatMap (untraitItem tr) ++ untraitExtra tr do
    match part with
    | .item item =>
      for o in inst.other item do
        others := others.push o
        if let .alias n ab e := o then aliasUses := aliasUses.insert n (ab.fvExpr [] e)
    | .fn name make =>
      -- (A function and every copy made of it for effects, made together,
      -- for the implementations it is given; its calls of copies named
      -- after, of what each calls as the copy for effects calls it.)
      for n in inst.names name do
        let get := fun (env : Array Nat) (as : String) => (do
          modify fun c => { c with calls := #[] }
          let item ← make env
          let calls := (← get).calls.foldl (fun m (c, ids) => m.insert c ids) ({} : Std.HashMap Nat (List Nat))
          modify fun c => { c with calls := #[] }
          match (inst.fn (unfieldItem info item)).find? fun | .fn m .. => m == n | _ => false with
          | some it => some <$> (renamed as <$> callsCopied calls it)
          | none => pure none : StateM Copies (Option Syntax.Item))
        if fns.contains n then twice := (n, get) :: twice else fns := fns.insert n get
  pure { blocks := b, others, fns, twice, aliasUses, srcKeys, globalKey }

/-- Where lowering starts: no copy asked, the implementations numbered as the
checker numbered them. -/
def Lowering.start (L : Lowering) : Lowered :=
  { copies := { pool := L.blocks.traits.knownIds, byId := L.blocks.traits.knownPool } }

/-- Lowered on from `st`, through what `roots` reach; none if more copies
would be made than `copyFuel`. -/
def Lowering.reachWith (L : Lowering) (st : Lowered) (roots : List String) : Option Lowered := Id.run do
  -- (The coercions applied in a function are reached with it: by the calls
  -- and callables they are applied at, and by its results.)
  let (byCall, byClosure, byFn) := L.blocks.coercions.fold
    (init := (({} : Std.HashMap Nat (List String)), ({} : Std.HashMap Nat (List String)), ({} : Std.HashMap String (List String))))
    fun (c, k, f) site fn => match site with
      | .arg call _ => (c.insert call (fn :: c.getD call []), k, f)
      | .result closure _ => (c, k.insert closure (fn :: k.getD closure []), f)
      | .fnResult name _ => (c, k, f.insert name (fn :: f.getD name []))
  let coercedIn := fun (name : String) (b : Flat.Body) =>
    (byFn.getD ((name.splitOn "⟨").headD name) []) ++ b.exprs.toList.flatMap fun
      | .call id _ _ | .tailCall id _ _ => byCall.getD id []
      | .closure id _ => byClosure.getD id []
      | _ => []
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
    -- (What was kept of lowering it, where it is lowered from the same, with
    -- the same, after the same copies.)
    let src := match st.copies.byName[x]? with
      | some (fn, ids, drop) => (L.srcKeys[fn]?).map fun h => hash (h, ids, drop, "copy")
      | none => (L.srcKeys[x]?).map fun h => hash h
    let key := match src with
      | some h => mixHash h (mixHash L.globalKey st.chain)
      | none => 0
    if key != 0 then
      if let some k := st.kept[x]? then
        if k.key == key then
          let copies0 := st.copies
          st := { st with copies := {} }
          let copies := k.pool.foldl (fun c e =>
            { c with pool := c.pool.insert e c.byId.size, byId := c.byId.push e }) copies0
          let copies := k.asked.foldl (fun c (key, name) =>
            { c with byKey := c.byKey.insert key name, byName := c.byName.insert name key
                     asked := c.asked.push (key, name) }) copies
          let chain := k.asked.foldl (fun h e => mixHash h (hash e)) (k.pool.foldl (fun h e => mixHash h (hash e)) st.chain)
          st := { st with copies, made := st.made + k.made, chain, keptMade := st.keptMade.insert x k }
          if let some (.fn name ps annots ret b) := k.item then
            st := { st with done := st.done.push (.fn name ps annots ret b) }
            todo := todo ++ (b.fvClauses b.roots).reverse.toArray ++ (coercedIn x b).toArray
          continue
    let (pool0, asked0) := (st.copies.byId.size, st.copies.asked.size)
    -- A copy for known implementations, made from the function it is of; or
    -- a function as it is, with the calls in it sent to copies if it is
    -- given no implementation.
    let (item, copies, made) := match st.copies.byName[x]? with
      | some (fn, ids, _) =>
        match L.fns[fn]? with
        | some make =>
          let (item, copies) := (make ids.toArray x).run st.copies
          (item, copies, st.made + 1)
        | none => (none, st.copies, st.made)
      | none =>
        match L.fns[x]? with
        | some make =>
          let (item, copies) := (make #[] x).run st.copies
          (item, copies, st.made)
        | none => (none, st.copies, st.made)
    if made > copyFuel then return none
    let pool := copies.byId.extract pool0 copies.byId.size
    let asked := copies.asked.extract asked0 copies.asked.size
    let chain := asked.foldl (fun h e => mixHash h (hash e)) (pool.foldl (fun h e => mixHash h (hash e)) st.chain)
    let madeHere := made - st.made
    st := { st with copies, made, chain }
    let lowered := match item with
      | some (.fn name ps annots ret b) => some (Syntax.Item.fn name ps annots ret b)
      | _ => none
    if key != 0 then
      st := { st with keptMade := st.keptMade.insert x { key, item := lowered, pool, asked, made := madeHere } }
    if let some (.fn name ps annots ret b) := lowered then
      st := { st with done := st.done.push (.fn name ps annots ret b) }
      todo := todo ++ (b.fvClauses b.roots).reverse.toArray ++ (coercedIn x b).toArray
  some st

/-- Lowered on from `st`, through what `roots` reach. Refused where more
copies would be made than `copyFuel`: a function that calls itself with an
implementation made from the one it was given, as Rust refuses it (no
implementation is a value when the program runs). -/
def Lowering.reach (L : Lowering) (st : Lowered) (roots : List String) : Except String Lowered :=
  match L.reachWith st roots with
  | some st => .ok st
  | none => .error s!"more than {copyFuel} copies of functions would be made for the implementations they are given: a function calls itself with an implementation made from the one it was given (`f::<(T, T)>` in `f::<T>`), which would need a copy for each, without end"

/-- What is lowered, as a program: its constants worked out, and each
function declared again where one is reached. -/
def Lowering.items (L : Lowering) (st : Lowered) : List Syntax.Item :=
  let again := L.twice.filterMap fun (n, get) => if st.seen.contains n then ((get #[] n).run' st.copies) else none
  let items := foldConstants (L.others.toList ++ st.done.toList ++ again)
  if Glorious.Trace.groupsTraced then
    dbgTrace s!"lowered: {st.done.size} functions, {st.made} copies, {st.copies.byId.size} implementation values" fun _ => items
  else items

end Glorious.Elab
