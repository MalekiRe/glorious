module

public import Glorious.Check.Group
public import Glorious.Check.Merge
public import Glorious.Elab.Specialize

public section

namespace Glorious.Check

open Syntax

/-- What one check keeps for the next of a program that changed a little: the
checker's state after the declarations and after each group of functions,
each under a key of everything it was made from, in order. -/
abbrev Kept := List (UInt64 × St)

/-- How often a state is kept among a unit's groups (or implementations'
functions), so that a unit keeps some 48 at most: each is the whole state. -/
def keptEvery (n : Nat) : Nat := max 1 ((n + 47) / 48)

/-- A state as it is kept: without what a group's bounds found, which the
next group's start anew (`settleBounds`). -/
def forKeeping (st : St) : St :=
  { st with solvedFit := {}, leavesFit := {}, leavesAt := {}, tyIds := {}, tyIdCount := 0, tyMemo := {}, dictShared := {} }

/-- An item as its declarations have it: its functions without their bodies. -/
partial def withoutBodies : Item → Item
  | .fn name params annots ret _ => .fn name params annots ret []
  | .impl params tr head args ctx methods => .impl params tr head args ctx (methods.map withoutBodies)
  | .pub parent item => .pub parent (withoutBodies item)
  | other => other

/-- A group of functions, as what its check is made from. -/
def groupKey (key : UInt64) (group : List FnDecl) : UInt64 :=
  group.foldl (fun h d => mixHash h (hash (d.name, d.params, d.annots, d.ret, d.clauses, d.bounds))) key

/-- A state kept from an earlier check, with the functions of the
implementations declared after the first `before` replaced by `written`
(each implementation's trait and functions, in the order written), where
those line up: none where they do not. -/
def withImplBodies (st : St) (before : Nat) (written : List (String × List Item)) : Option St :=
  let given := st.impls.toList.drop before
  if written.length ≤ given.length && (written.zip given).all (fun (w, im) => w.1 == im.trait) then
    let replaced : List ImplDecl := given.zipIdx.map fun (im, k) =>
      match written[k]? with
      | some w => { im with methods := w.2 }
      | none => im
    some { st with impls := ((st.impls.toList.take before) ++ replaced).toArray }
  else none

/-- Take a state kept from an earlier compile as this one's, but for what is
this program's: what the resolver said of its modules (the dot calls'
alternatives and the rest), and whether its own items are checked. -/
def adopt (st : St) : M Unit := do
  let now ← get
  set { st with modules := now.modules, ownItems := now.ownItems }

/-- The functions an implementation gives, as functions to check. -/
def implFnDecls (im : ImplDecl) : M (List FnDecl) := do
  let mut out : List FnDecl := []
  for item in im.methods do
    if let .fn m written annots ret clauses := item then
      if let some sig := (← get).methods[m]? then
        -- (Its type parameters: the head's arguments, and then those that
        -- are only inside one, or among the trait's own; and the lifetimes
        -- it writes of its own, `fn at<'a>(..)`.)
        let inner := (im.pvars.map (·.1)).filter (!im.params.contains ·)
        let lifetimes := (genericParams written).filter isLifetime
        -- (How often its functions use a value of a type parameter, where the
        -- implementation says it.)
        let uses := im.methods.filterMap fun
          | .typeAlias n _ _ => (Syntax.useMarked n).map fun (p, lo, hi) =>
              ({ subject := p, trait := "Use", quantity := some (lo, hi) } : Syntax.Bound)
          | _ => none
        -- (And of the trait's function's own, what the trait says.)
        let uses := uses ++ sig.uses.map fun (p, lo, hi) =>
          ({ subject := p, trait := "Use", quantity := some (lo, hi) } : Syntax.Bound)
        out := out ++ [{ name := Syntax.implFnName im.trait im.head m,
                         params := im.params ++ inner ++ sig.mparams.map (·.1) ++ lifetimes, annots,
                         ret, clauses, impl := some (im, sig), bounds := uses }]
  pure out

/-- Check a group, deciding where it is found what can be known only once
types are (`Elab.Decision`): the group is checked again with it, from where
it began, and it is kept for the program to be written with. What is said if
a value kept in a variable is then refused is why it could not be left
unused (`first`). -/
partial def checkDeciding (decls : List FnDecl) (fuel : Nat := 64) (first : Option String := none) :
    M Unit := do
  let before ← get
  tryCatchThe Elab.Said (checkGroup decls) fun e => do
    let isLetMut := match e.decision with
      | some (.letMut ..) => true
      | _ => false
    let said : Elab.Said := match first with
      | some f => if isLetMut then { e with decision := none } else f
      | none => { e with decision := none }
    match fuel, e.decision with
    | fuel + 1, some d =>
      if Glorious.Trace.groupsTraced then
        (dbgTrace s!"decision {fuel}: {e.msg.take 200}" fun _ => (pure () : M Unit))
      let items := decls.map fun d => Item.fn d.name d.params d.annots d.ret d.clauses
      let after := Elab.decidedItems [d] items
      let decls' := (decls.zip after).map fun
        | (d, .fn _ _ _ _ clauses) => { d with clauses }
        | (d, _) => d
      -- (Nothing changed: what was said stands.)
      if (decls'.map (·.clauses)).map hash == (decls.map (·.clauses)).map hash then throwThe Elab.Said said
      set before
      modify fun s =>
        { s with decided := s.decided ++ [d]
                 runFns := decls'.foldl (fun m d => m.insert d.name d.clauses) s.runFns }
      let first := match d with
        | .letMut .. => some (first.getD e.msg)
        | _ => first
      checkDeciding decls' fuel first
    | _, _ => throwThe Elab.Said said

/-- A group checked; where only what can be found of a program is asked
(`St.lenient`), one that is refused is let be. -/
def checkMaybe (decls : List FnDecl) : M Unit := do
  if (← get).lenient then
    tryCatchThe Elab.Said (checkDeciding decls) fun e => do
      modify fun s => { s with refusals := s.refusals.push e.msg }
  else checkDeciding decls

/-- How far apart the ids of units checked side by side start: room for the
runs of groups each checks side by side, a level after another
(`runGap`). -/
def unitGap : Nat := 1 <<< 40

/-- How far apart the ids of the runs of groups of one level start. -/
def runGap : Nat := 1 <<< 28

/-- The state each unit of a level is checked from, its ids numbered from a
place of its own: the `j`-th from `j` gaps on. -/
def jumpedFor (s : St) (j : Nat) (gap : Nat := unitGap) : St :=
  if j == 0 then s else
  let at_ := fun (n : Nat) => n + j * gap
  { s with
    tys := s.tys.jumpTo (at_ s.tys.size), rows := s.rows.jumpTo (at_ s.rows.size)
    caps := s.caps.jumpTo (at_ s.caps.size), capOut := s.capOut.jumpTo (at_ s.caps.size)
    capEdges := s.capEdges.jumpTo (at_ s.capEdges.size)
    capEdgeNames := s.capEdgeNames.jumpTo (at_ s.capEdges.size)
    loans := s.loans.jumpTo (at_ s.loans.size), rigidKeys := s.rigidKeys.jumpTo (at_ s.rigidKeys.size)
    brands := at_ s.brands, dropAsked := at_ s.dropAsked }

/-- Did the `j`-th unit of a level stay below where the next one's ids start? -/
def stayedBelow (s from_ : St) (j : Nat) (gap : Nat := unitGap) : Bool :=
  let below := fun (now start : Nat) => now ≤ start + (j + 1) * gap
  below s.tys.size from_.tys.size && below s.rows.size from_.rows.size
    && below s.caps.size from_.caps.size && below s.capEdges.size from_.capEdges.size
    && below s.loans.size from_.loans.size && below s.rigidKeys.size from_.rigidKeys.size
    && below s.brands from_.brands && below s.dropAsked from_.dropAsked

/-- How many threads the groups of one level are checked on, at most. -/
def sideThreads : Nat := 16

/-- The captures of a type, in the order it has them. -/
partial def capsOf : Ty → List Nat
  | .ref how t c => capsOf how ++ capsOf t ++ [c]
  | .fn ps r _ _ c => ps.flatMap capsOf ++ capsOf r ++ [c]
  | .con _ args => args.flatMap capsOf
  | .tuple args => args.flatMap capsOf
  | .var _ => []

/-- A function's type as callers see it: the type, with its variables
numbered in order; how many bounds, of what; and for each capture of the
type, what it holds in the end, through captures the type does not have
(by place among the type's, or what it is). The same of a signature and of
the body it says, whichever variables each was given. A borrow a callable
makes while it runs (`inner`) is the function's own, and not a caller's to
see where it performs nothing: then none can be held across a suspension. -/
def schemeShape (s : Scheme) : String :=
  let caps := capsOf s.ty
  let place := fun (c : Nat) => caps.idxOf? c
  let quiet := match s.ty with
    | .fn _ _ effs tail _ => effs.isEmpty && tail.isNone
    | _ => false
  let rec holds (fuel : Nat) (seen : List Nat) (c : Nat) : List String :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      (s.edges.filter (·.1 == c)).flatMap fun (_, w) => match w with
        | .ty (.ref (.con "'" []) (.tuple []) c') => match place c' with
          | some k => [s!"life#{k}"]
          | none => if seen.contains c' then [] else holds fuel (c' :: seen) c'
        | .ty t => [s!"ty {showTy t}"]
        | .inner _ => if quiet then [] else ["inner"]
        | .brand _ => ["brand"]
        | .once => ["once"]
        | .must => ["must"]
        | .loan _ => ["loan"]
        | .touch _ w => [s!"touch {w}"]
  let held := caps.map fun c => ((holds 32 [c] c).eraseDups.mergeSort (· ≤ ·))
  let n := fun (k : Nat) => String.ofList (List.replicate k '|')
  let text := s!"{showTy s.ty} b{n s.bounds.length} {(s.bounds.map (·.1)).mergeSort (· ≤ ·)} u{n s.dups.length} d{n s.drops.length} s{n s.stays.length} holds {held}"
  -- (The type's variables by their place among those before it.)
  let (out, _, cur) := text.foldl (fun (acc : String × List (String × Nat) × String) c =>
    let (out, seen, cur) := acc
    if c.isDigit then (out, seen, cur.push c)
    else if cur.isEmpty then (out.push c, seen, "")
    else
      let (k, seen) := match seen.lookup cur with
        | some k => (k, seen)
        | none => (seen.length, seen ++ [(cur, seen.length)])
      ((out ++ s!"#{k}").push c, seen, "")) ("", [], "")
  out ++ cur

/-- A type with its variables and captures numbered (to see where two differ). -/
partial def showTyCaps : Ty → String
  | .var id => s!"?{id}"
  | .con n args => if args.isEmpty then n else s!"{n}<{", ".intercalate (args.map showTyCaps)}>"
  | .tuple args => s!"({", ".intercalate (args.map showTyCaps)})"
  | .fn ps r _ _ cap => s!"fn^{cap}({", ".intercalate (ps.map showTyCaps)}) -> {showTyCaps r}"
  | .ref how t cap => s!"&^{cap}[{showTyCaps how}] {showTyCaps t}"

/-- What a scheme holds callers to, written out (to see where two differ). -/
def schemeDetail (s : Scheme) : String :=
  let dups := s.dups.map fun (t, w) => (showTy t, w)
  let drops := s.drops.map fun (t, w) => (showTy t, w)
  let what := fun (c : Captured) => match c with
    | .brand b => s!"brand {b}"
    | .ty t => s!"ty {showTy t}"
    | .once => "once"
    | .must => "must"
    | .loan l => s!"loan {l}"
    | .touch b w => s!"touch {b} {w}"
    | .inner l => s!"inner {l}"
  s!"bounds {s.bounds.map fun (tr, t) => (tr, showTy t)} dups {dups} drops {drops} edges {s.edges.map fun (c, w) => (c, what w)} cvars {s.cvars} tvars {s.tvars} ty {showTyCaps s.ty}"

/-- Groups none of which uses another, checked side by side: a few runs of
them, each on a thread of its own from the state before, its ids from a place
of its own (`jumpedFor`), and what each added put together (`mergeStates`),
as if one had been checked after another. A run that cannot be put with those
before it (both changed one thing that was there: a lifetime a declared type
has, which each binds), or that was refused, is checked again after them: what
is said is then the first refusal in their order, as one after another would
say it. -/
def checkSideBySide (groups : List (List FnDecl)) : M Unit := do
  if groups.length < 8 then
    for g in groups do checkMaybe g
    return
  let threads := min (groups.length / 4 + 1) sideThreads
  let size := (groups.length + threads - 1) / threads
  let runs := (List.range threads).filterMap fun t =>
    match (groups.drop (t * size)).take size with
    | [] => none
    | run => some run
  let start ← get
  let tasks := runs.zipIdx.map fun (run, j) =>
    (run, j, Task.spawn (prio := .dedicated) fun _ => (run.forM checkMaybe : M Unit).run (jumpedFor start j runGap))
  -- (In order: a run that cannot be put with those before it, or was
  -- refused, is checked again after them, as one after another would.)
  for (run, j, t) in tasks do
    let here ← get
    let got := Trace.timed "side: wait" fun _ => t.get
    let put := match got with
      | .ok ((), after) => if stayedBelow after start j runGap then Trace.timed "side: merge" fun _ => mergeStates start here after else none
      | .error _ => none
    match put with
    | some st => set st
    | none => timedM "side: again" (for g in run do checkMaybe g)

/-- Check items. With `kept` from an earlier check of a program that began
alike (`seed`: what was checked before them), the state after each step whose
key is among them is taken from there instead of checked again: the
declarations' key is of every item without the bodies of its functions, each
group's is of the key before it and the group's functions whole. A step
depends on no more than that: a group follows calls only into groups before
it. What the functions of later groups are is put back as this program has
them. Gives what this check kept, the state after all of it first, under a
key of every item whole: where that is kept, nothing else is looked at, and
nothing else is kept. -/
def checkItems (items : List Item) (seed : UInt64 := 0) (kept : Kept := []) : M Kept := do
  let written := items.filterMap fun
    | .bounds fn bounds => some (fn, bounds)
    | _ => none
  let decls : List FnDecl := items.filterMap fun
    | .fn name params annots ret clauses =>
      some { name, params, annots, ret, clauses, bounds := (written.lookup name).getD [] }
    | _ => none
  -- What is asked of a declared type's parameters: a trait without arguments
  -- of its own, of the parameter at a place.
  let asked := items.filterMap fun
    | .struct name params _ => (written.lookup name).map (name, params, ·)
    | .enum name params _ => (written.lookup name).map (name, params, ·)
    | .effect name params _ => (written.lookup name).map (name, params, ·)
    | _ => none
  modify fun s =>
    { s with typeBounds := s.typeBounds ++ asked.map fun (name, params, bounds) =>
        (name, bounds.filterMap fun b =>
          if b.trait.startsWith "'" || !b.args.isEmpty then none
          else (params.idxOf? b.subject).map (b.trait, ·)) }
  let names := decls.map (·.name)
  -- (A name that stands for an expression, a constant's, mentions what that
  -- does: the function that works the constant out.)
  let aliasOf : Std.HashMap String (List String) := Elab.firstOf (items.filterMap fun
    | .alias name value => some (name, Elab.fvExpr [] value)
    | .pub _ (.alias name value) => some (name, Elab.fvExpr [] value)
    | _ => none)
  let nameSet : Std.HashSet String := names.foldl (·.insert ·) {}
  -- (And the functions a dot call in it may turn out to be of, the types'
  -- own of the name: one is checked before what may call it.)
  let modules := (← get).modules
  -- (What each function mentions, found once for each.)
  let mentioned : Std.HashMap String (List String) := decls.foldl (fun m d =>
    let fvs := d.clauses.flatMap (Elab.fvClause [])
    let alts := if modules.dotAlts.isEmpty then [] else
      ((d.clauses.flatMap fun | .mk _ body => body.flatMap Stmt.exprs).foldl Syntax.callIdsExpr []).flatMap
        fun id => (dotAltsOf modules id).getD []
    if m.contains d.name then m
    else m.insert d.name ((fvs ++ alts ++ fvs.flatMap fun x => aliasOf.getD x []).filter nameSet.contains).eraseDups) {}
  let mentions := fun (name : String) => mentioned.getD name []
  let coercing := items.filterMap fun
    | .coerce name => some name
    | _ => none
  for c in coercing do
    unless nameSet.contains c do throw s!"`coerce {c}`: there is no function `{c}`"
  -- A coercion can be applied in any function, so the coercions are checked
  -- before all the others: all, that is, but the functions the coercions are
  -- themselves built from, in which none is applied.
  let builtFrom := Id.run do
    let mut seen := coercing
    if !coercing.isEmpty then
      for _ in [0:names.length] do
        let more := (seen ++ seen.flatMap mentions).eraseDups
        if more.length == seen.length then break
        seen := more
    pure seen
  let deps := fun (name : String) =>
    if builtFrom.contains name then mentions name else (mentions name ++ coercing).eraseDups
  do
    -- (The unit whole, as an earlier compile left it: every step taken from
    -- there at once. A unit that is the same keeps only this.)
    let whole := mixHash seed (hash items)
    if let some st := kept.lookup whole then
      adopt st
      return [(whole, st)]
    let before := (← get).impls.size
    let mut made : Kept := []
    -- (A function is declared by checking it, with its group: what is
    -- declared first is the rest, so a function added, or a signature
    -- changed, keeps what was found of the declarations and the groups
    -- before it.)
    let fnNames : Std.HashSet String := decls.foldl (fun s d => s.insert d.name) {}
    let declared := items.filter fun
      | .fn .. => false
      | .pub _ (.fn ..) => false
      | .bounds f _ => !fnNames.contains f
      | _ => true
    let mut key := mixHash seed (hash (declared.map withoutBodies))
    -- (A state kept from before has the implementations that program
    -- declared, each with its functions whole; the declarations do not
    -- depend on the bodies, so the ones put in their place are this
    -- program's, in the order its implementations are written. Where they
    -- do not line up, nothing kept is taken.)
    let written : List (String × List Item) := items.filterMap fun
      | .impl _ tr _ _ _ methods => some (tr, methods)
      | _ => none
    let ours := fun (st : St) => withImplBodies st before written
    let look := fun (k : UInt64) => (kept.lookup k).bind ours
    match look key with
    | some st => adopt st
    | none =>
      declare items
      computeVariances
      declareTraits items
      checkUseDecls
    made := (key, ← get) :: made
    modify fun s =>
      { s with runFns := decls.foldl (fun m d => m.insertIfNew d.name d.clauses) s.runFns }
    -- (A state kept from before has the bodies that program's later
    -- functions had: this one's are put in their place.)
    let restore := fun (st : St) (later : List FnDecl) => (do
      adopt st
      modify fun s =>
        { s with runFns := later.foldl (fun m d => m.insert d.name d.clauses) s.runFns } : M Unit)
    let declBy : Std.HashMap String FnDecl := decls.foldl (fun m d => if m.contains d.name then m else m.insert d.name d) {}
    let groups := (components names deps).map fun comp => comp.filterMap fun n => declBy[n]?
    -- Each group's level: groups of one level use none of each other, so
    -- they are checked side by side (`checkSideBySide`), each level after
    -- those before it.
    let groupOf : Std.HashMap String Nat := groups.zipIdx.foldl (fun m (g, i) =>
      g.foldl (fun m d => m.insert d.name i) m) {}
    -- Each group's level, one more than the highest of the groups it calls
    -- into; but one that nothing in the unit calls, as a function just added
    -- is, is of the last level, after every other, so that adding one leaves
    -- the rest as they were.
    let levelOf := groups.zipIdx.foldl (fun (acc : Array Nat) (g, i) =>
      acc.push (g.foldl (fun l d => (deps d.name).foldl (fun l n =>
        match groupOf[n]? with
        | some j => if j < i then max l ((acc[j]?).getD 0 + 1) else l
        | none => l) l) 0)) #[]
    let called := groups.zipIdx.foldl (fun (acc : Array Bool) (g, i) =>
      g.foldl (fun acc d => (deps d.name).foldl (fun acc n =>
        match groupOf[n]? with
        | some j => if j < i then acc.set! j true else acc
        | none => acc) acc) acc) (Array.replicate groups.length false)
    let last := levelOf.foldl max 0 + 1
    let sorted := (groups.zipIdx.map fun (g, i) =>
        (if (called[i]?).getD false then (levelOf[i]?).getD 0 else last, i, g)).mergeSort
      fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 ≤ b.2.1)
    let groups := sorted.map (·.2.2)
    let levels := (sorted.map (·.1)).toArray
    -- The functions of the copies of an implementation for every type
    -- (`impl<T> Requires for T`, one for each type the unit declares) that
    -- name none of the unit's functions, where no coercion is: checked
    -- before the others, so that what was found of them is kept where only
    -- a function's body changed.
    let blanket := fun (im : ImplDecl) => im.methods.any fun
      | .typeAlias n _ _ => (Syntax.blanketParam n).isSome
      | _ => false
    let implDecls ← ((← get).impls.toList.drop before).filter blanket |>.flatMapM implFnDecls
    let namesAny := fun (d : FnDecl) =>
      ((d.clauses.flatMap (Elab.fvClause [])).flatMap fun x => x :: aliasOf.getD x []).any nameSet.contains
    let early := if coercing.isEmpty then implDecls.filter (!namesAny ·) else []
    -- (Of those kept, the last is taken, and made this program's: the key
    -- has its implementations as written, so they line up. Kept now and
    -- then, as the groups are: a unit declaring many types has a copy of
    -- each for every one, and a state after each was most of what a
    -- program kept.)
    let earlyKeys := (early.foldl (fun (acc : List UInt64 × UInt64) d =>
      let k := groupKey acc.2 [d]
      (k :: acc.1, k)) ([], key)).1.reverse
    let earlyStart := ((earlyKeys.zipIdx.reverse.find? fun (k, _) => (kept.lookup k).isSome).map (·.2 + 1)).getD 0
    if earlyStart > 0 then
      if let some k := earlyKeys[earlyStart - 1]? then
        if let some st := kept.lookup k then
          restore ((ours st).getD st) decls
          made := (k, st) :: made
    -- (None of them uses another: all side by side, the state kept after.)
    if earlyStart < early.length then
      checkSideBySide ((early.drop earlyStart).map ([·]))
      made := (earlyKeys[early.length - 1]!, forKeeping (← get)) :: made
    if let some k := earlyKeys.getLast? then key := k
    -- The state after the last group whose key, and so every key before
    -- it, is kept is taken; the groups after it are checked. A state is
    -- kept after a group only now and then, in a unit of many (`keptEvery`):
    -- each kept is the whole state, and the next change to it copies what
    -- it holds, so one after every group grew with the square of their
    -- number, in time and in what is saved.
    let keys := (groups.foldl (fun (acc : List UInt64 × UInt64) g =>
      let k := groupKey acc.2 g
      (k :: acc.1, k)) ([], key)).1.reverse
    let every := keptEvery groups.length
    let start := ((keys.zipIdx.reverse.find? fun (k, _) => (look k).isSome).map (·.2 + 1)).getD 0
    if start > 0 then
      if let some k := keys[start - 1]? then
        if let some st := look k then
          restore st ((groups.drop start).flatten)
          made := (k, st) :: made
    let rest := (groups.zipIdx.drop start).toArray
    -- Each function's type as its signature says, first; then every body
    -- checked from that, side by side, none waiting for another's. Where a
    -- body's type is not what its signature said, the groups are checked
    -- as before, callees first.
    let pre ← get
    let signed ← if !Trace.universesAsked then pure false else
      tryCatchThe Elab.Said (do
          for (g, _) in rest do
            for d in g do checkGroup [d] (signature := true)
          pure true)
        fun _ => do set pre; pure false
    let mut universes := false
    if signed && rest.size > 0 then
      let sigs := (← get).fns
      let ok ← tryCatchThe Elab.Said (do checkSideBySide (rest.toList.map (·.1)); pure true) fun _ => pure false
      let now := (← get).fns
      let same := ok && rest.all fun (g, _) => g.all fun d =>
        match sigs[d.name]?, now[d.name]? with
        | some a, some b => schemeShape a == schemeShape b
        | _, _ => false
      if same then
        universes := true
        if let some (_, last) := rest.back? then
          made := (keys[last]!, forKeeping (← get)) :: made
      else
        if Trace.groupsTraced then
          for (g, _) in rest do
            for d in g do
              match sigs[d.name]?, now[d.name]? with
              | some a, some b =>
                unless schemeShape a == schemeShape b do
                  (dbgTrace s!"signature differs: {d.name}: {schemeShape a} / {schemeShape b}\n  sig {schemeDetail a}\n  body {schemeDetail b}" fun _ => (pure () : M Unit))
              | _, _ => pure ()
        set pre
    let mut i := if universes then rest.size else 0
    while i < rest.size do
      let level := (levels[(rest[i]?.map (·.2)).getD 0]?).getD 0
      let mut j := i
      while j < rest.size && (levels[(rest[j]?.map (·.2)).getD 0]?).getD 0 == level do j := j + 1
      let run := (rest.extract i j).toList
      checkSideBySide (run.map (·.1))
      let last := (run.getLast?.map (·.2)).getD 0
      if run.any (fun (_, k) => (k + 1) % every == 0) || last + 1 == groups.length then
        made := (keys[last]!, forKeeping (← get)) :: made
      i := j
    if let some k := keys.getLast? then key := k
    -- The functions implementations give, each on its own: any function may
    -- call them, but only through a trait, whose types are declared.
    -- (Those of one that leaves a type to be found were checked with the
    -- rest, before what may use it.)
    let earlyNames := early.map (·.name)
    let mut implGroups : Array (List FnDecl) := #[]
    for im in (← get).impls.toList.drop before do
      for d in ← implFnDecls im do
        unless earlyNames.contains d.name do implGroups := implGroups.push [d]
    -- (Taken, checked and kept as the groups are.)
    let implKeys := (implGroups.toList.foldl (fun (acc : List UInt64 × UInt64) g =>
      let k := groupKey acc.2 g
      (k :: acc.1, k)) ([], key)).1.reverse
    let implStart := ((implKeys.zipIdx.reverse.find? fun (k, _) => (look k).isSome).map (·.2 + 1)).getD 0
    if implStart > 0 then
      if let some k := implKeys[implStart - 1]? then
        if let some st := look k then
          restore st []
          made := (k, st) :: made
    -- (None uses another: all side by side.)
    checkSideBySide (implGroups.toList.drop implStart)
    if implStart < implGroups.size then
      if let some k := implKeys.getLast? then made := (k, ← get) :: made
    if let some k := implKeys.getLast? then key := k
    for c in coercing do
      unless (((← get).fnBounds.lookup c).getD 0) == 0 do
        throw s!"`coerce {c}`: a coercion cannot need a trait of a type it is used at"
    checkDups (← get).lateDups
    checkDrops (← get).lateDrops
    checkStays (← get).lateStays
    modify fun s => { s with lateDups := #[], lateDrops := #[], lateStays := #[] }
    pure ((whole, ← get) :: made)

/-- The declared types a type is made of. -/
partial def namedIn : Ty → List String
  | .var _ => []
  | .con name args => name :: args.flatMap namedIn
  | .tuple args => args.flatMap namedIn
  | .fn params ret effs _ _ =>
    params.flatMap namedIn ++ namedIn ret ++ effs.flatMap fun (_, args) => args.flatMap namedIn
  | .ref _ t _ => namedIn t

/-- What the checker tells the elaborator, once every item is checked. -/
def finish : M Elab.Blocks := fun st => Trace.timed "check: finish" fun _ => (show M Elab.Blocks from do
    -- One who calls a `pub` function has to be able to write its type.
    let info := (← get).modules
    for f in info.pubFns do
      if let some scheme := (← get).fns[f]? then
        let t ← zonk (← instantiate scheme)
        for n in namedIn t do
          -- (A type's own function is named through the type: where the
          -- type cannot be written, neither can the function, `pub` or not.)
          if f.startsWith (n ++ "::") then continue
          if let some home := info.privTypes.lookup n then
            if info.homes.lookup f == some home then
              throw s!"`{Syntax.lastSegment f}` is `pub`, but its type, `{showTy t}`, has `{Syntax.lastSegment n}` in it, which is private to its module: one who calls `{Syntax.lastSegment f}` could not write that type (`pub struct` with fields that are not `pub` keeps what is inside private)"
    unless (((← get).fnBounds.lookup "main").getD 0) == 0 do
      throw "`main` needs a trait of a type that nothing decides"
    match (← get).fns["main"]? with
    | none => pure ()
    | some scheme =>
      match ← zonk (← instantiate scheme) with
      | .fn ps r effs _ _ =>
        unless ps.isEmpty do throw "`main` takes no arguments"
        unless effs.isEmpty do
          throw s!"`main` performs effects that nothing handles: {showEffs effs}"
        -- Nothing uses what the program gives.
        modify fun s => { s with pos := "", drops := #[] }
        mustDrop r "the result of `main` is let go when the program ends"
        checkDrops (← get).drops
      | _ => pure ()
    let s ← get
    let mut links : List (Nat × Nat) := []
    -- (The blocks given to run in an environment, by the root of what they
    -- capture: found once, not for each block that was not run.)
    let mut byRoot : Std.HashMap Nat (List Nat) := {}
    for (owner, c) in s.blockCaps do
      if owner != 0 && s.envBlocks.contains owner then
        let root ← findCap c
        let had := byRoot.getD root []
        unless had.contains owner do byRoot := byRoot.insert root (owner :: had)
    for (id, cap) in s.unrun do
      let root ← findCap cap
      let owners := (byRoot.getD root []).filter (· != id)
      if let [owner] := owners then links := (id, owner) :: links
    -- A block taken to be given one particular block, where in the end it
    -- may be given another, lets go of whatever it is given.
    let mut unlinked : Array (Ty × String) := #[]
    for (id, owner, input, why) in s.assumedLinks do
      unless links.contains (id, owner) do unlinked := unlinked.push (input, why)
    -- (What such a block lets go of, nothing destroys.)
    checkDrops unlinked (callables := true)
    -- (Each trait's functions and each function's arity, the first of each
    -- name as a lookup finds it, found once.)
    let traitsBy := Elab.firstOf s.traits
    let arityBy : Std.HashMap String Nat := s.methods.fold (fun m n sig => m.insert n sig.params.length) {}
    let implEs := s.impls.toList.map fun im =>
      let names := traitsBy.getD (Syntax.traitBase im.trait) []
      (⟨im.dictFn, im.context.length + im.extra.length, names.map fun m =>
        (Syntax.implFnName im.trait im.head m,
          if im.trait == Syntax.destroyTrait then 1
          else arityBy.getD m 0)⟩ :
        Elab.ImplE)
    -- How each type is destroyed, for the elaborator to write the function:
    -- its own `Drop` first, if it has one, and then for each constructor
    -- which fields are destroyed, each by how its type is.
    let mut destroys : Array Elab.Destroy := #[]
    for im in s.impls do
      if im.trait == Syntax.destroyTrait then
        let givens : Traits.Givens := im.context
        let place := fun (j : Nat) => (im.context.idxOf? (Syntax.destroyTrait, j)).map Elab.DictE.param
        let arity := im.params.length
        let hook := if s.kimpls.has "Drop" im.head then
            (Traits.solveIx s.kimpls givens 1000 "Drop"
              (.con im.head ((List.range arity).map Traits.STy.var))).map (toDictE s.impls)
          else none
        let mut ctors : List (String × List (Option Elab.DictE)) := []
        let isArray := some im.head == s.arrayType
        if isArray then ctors := [("%each", [place 0])]
        else if im.head.startsWith "(tuple" then
          ctors := [("", (List.range arity).map place)]
        else if let some decl := s.types[im.head]? then
          for c in decl.ctors do
            if let some sig := s.ctors[c]? then
              -- A field's type, as the solver knows types: a parameter of
              -- the type by its place among them.
              let places := (List.range arity).filter fun j => sig.kinds[j]? != some true
              let sty := fieldSTy sig.tvars places
              let mut parts : List (Option Elab.DictE) := []
              for f in sig.fields do
                let plain := (freeTys f).isEmpty && !(← needsDestroying [] f)
                parts := parts ++ [if plain then none
                  else (Traits.solveIx s.kimpls givens 1000 Syntax.destroyTrait (sty f)).map (toDictE s.impls)]
              ctors := ctors ++ [(c, parts)]
        destroys := destroys.push ⟨im.head, im.context.length, hook, isArray, ctors⟩
    let traitInfo : Elab.TraitInfo :=
      { dicts := s.dictTable.toList
        methods := s.methodCalls.toList
        bounded := s.fnBounds
        impls := implEs
        drops := s.dropSites.toList
        destroys := destroys.toList }
    pure { given := .ofList s.given.toList, links := Elab.firstOf links
           coercions := Elab.firstOf s.coercions.toList, traits := traitInfo.index
           fields := Elab.firstOf (s.fieldTable.toList.map fun (id, rest) => (id, rest))
           fieldReads := Elab.firstOf s.fieldReads.toList, packs := Elab.firstOf s.packs.toList
           derefReads := .ofList s.derefReads.toList, sites := s.siteTable, siteTypes := s.siteTypes
           dotChosen := Elab.firstOf s.dotChosen, argsChosen := Elab.firstOf s.argsChosen
           decided := s.decided }).run st

/-- Check a whole program. Gives what the elaborator needs to know about its
blocks: which take an argument they do not name, and for each that is handed a
block which was not run, the identity of that block if it can only be one. The
elaborator then lets those two share what they capture. -/
def checkProgram (items : List Item) (modules : Syntax.ModuleInfo := {}) (drops : Bool := false) :
    Except String Elab.Blocks := do
  let action : M Elab.Blocks := do
    modify fun s => { s with modules }
    let _ ← checkItems items
    finish
  let (blocks, _) ← (action.run { dropMode := drops }).mapError (·.msg)
  pure blocks

/-- What is known once some items are checked: for a program that is checked
after them, against what they declare. -/
def checkFirst (items : List Item) (modules : Syntax.ModuleInfo := {}) (drops : Bool := false) :
    Except String St := do
  let action : M Unit := do
    modify fun s => { s with modules }
    let _ ← checkItems items
  let (_, st) ← (action.run { dropMode := drops }).mapError (·.msg)
  pure st

/-- Check a program whose first items are already checked. -/
def checkAfter (first : St) (items : List Item) (modules : Syntax.ModuleInfo := {}) :
    Except String Elab.Blocks := do
  let action : M Elab.Blocks := do
    modify fun s => { s with modules, ownItems := true }
    let _ ← checkItems items
    finish
  let (blocks, _) ← (action.run first).mapError (·.msg)
  pure blocks


/-- Check a program's units, each a module, in the order given, which has a
module after those it uses (`deps`: for each, the units before it that it
uses): each unit's declarations and groups are checked after the units before
it, and keyed by what they and those were made from (and, with each unit,
what it reads of the program's modules besides its own items), so what an
earlier check kept of a unit is taken from there where neither it nor any
unit before it changed. Units that do not use each other, the next ones
whose units used are all checked, are checked side by side, each on a
thread of its own, and what each added is put together (`mergeStates`);
where it cannot be, or one of them is refused, they are checked one after
another, as all were. -/
def checkUnitsKept (first : St) (units : List (List Item × UInt64)) (modules : Syntax.ModuleInfo)
    (seed : UInt64) (kept : Kept) (own : Bool := true) (library : Nat := 0)
    (deps : List (List Nat) := []) : Except Elab.Said (Elab.Blocks × Kept × Kept) := do
  -- (Each unit's level: one more than the highest of the units it uses.)
  let levelOf := units.length.fold (init := (#[] : Array Nat)) fun i _ acc =>
    acc.push (((deps[i]?).getD []).foldl (fun m d => max m ((acc[d]?).getD 0 + 1)) 0)
  let levels := (List.range ((levelOf.foldl max 0) + 1)).map fun l =>
    (units.zipIdx.filter fun (_, k) => levelOf[k]? == some l)
  -- (Side by side only where each unit says what it uses.)
  let levels := if deps.length == units.length then levels else units.zipIdx.map ([·])
  let action : M (Elab.Blocks × Kept × Kept) := do
    modify fun s => { s with modules, ownItems := own }
    let mut key := seed
    let mut made : Kept := []
    -- (What the first `library` units made: the library's modules, which
    -- every program that begins with them can take.)
    let mut shared : Kept := []
    for level in levels do
      -- Side by side: each from the state before the level, under keys of
      -- their own, its ids from a place of its own.
      if level.length > 1 then
        let start ← get
        let side := mixHash key (hash "side by side")
        -- (After the level, what follows is keyed by what the level's units
        -- are made of, whichever way they were checked.)
        let after := level.foldl (fun h ((u, info), _) => mixHash h (mixHash info (hash u))) key
        -- (The level as an earlier compile put it together, where it is the
        -- same: each unit kept whole is not what this start grew into, so
        -- what it added could not be told.)
        let whole := mixHash side after
        let allLibrary := level.all fun (_, k) => k < library
        if let some st := kept.lookup whole then
          adopt st
          made := (whole, st) :: made
          if allLibrary then shared := (whole, st) :: shared
          key := after
          continue
        let tasks := level.zipIdx.map fun (((u, info), k), j) =>
          (k, j, Task.spawn fun _ => Trace.timed s!"check unit {k} (side by side)" fun _ =>
            (checkItems u (mixHash side info) kept).run (jumpedFor start j))
        let mut together : Option St := none
        let mut mines : List (Nat × Kept) := []
        let mut ok := true
        for (k, j, t) in tasks do
          match t.get with
          | .ok (mine, after) =>
            if !stayedBelow after start j then ok := false
            together := match together with
              | none => some after
              | some acc => mergeStates start acc after
            if together.isNone then ok := false
            mines := mines ++ [(k, mine)]
          | .error _ => ok := false
        if ok then
          if let some st := together then
            set st
            for (k, mine) in mines do
              made := mine ++ made
              if k < library then shared := mine ++ shared
            made := (whole, st) :: made
            if allLibrary then shared := (whole, st) :: shared
            key := after
            continue
      -- One after another.
      let levelStart := key
      for ((u, info), k) in level do
        let before ← get
        let (mine, after) ← match Trace.timed s!"check unit {k}" fun _ =>
            (checkItems u (mixHash key info) kept).run before with
          | .ok r => pure r
          | .error e => throwThe Elab.Said e
        set after
        if let some (k, _) := mine.head? then key := k
        made := mine ++ made
        if k < library then shared := mine ++ shared
      if level.length > 1 then
        key := level.foldl (fun h ((u, info), _) => mixHash h (mixHash info (hash u))) levelStart
        -- (Kept as the level side by side would have been: a later compile
        -- takes it whole, and does not try them side by side again.)
        let whole := mixHash (mixHash levelStart (hash "side by side")) key
        made := (whole, ← get) :: made
        if level.all (fun (_, k) => k < library) then shared := (whole, ← get) :: shared
    pure (← finish, made, shared)
  let (r, _) ← action.run first
  pure r

end Glorious.Check
