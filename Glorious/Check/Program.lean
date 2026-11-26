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

/-- A state as it is kept: without what a group's bounds found, which the
next group's start anew (`settleBounds`). -/
def forKeeping (st : St) : St :=
  { st with solvedFit := {}, leavesFit := {}, leavesAt := {}, tyIds := {}, tyIdCount := 0, tyMemo := {}, dictShared := {}, dictByShape := {}, destroyFit := {},
            body := {}, fnBodies := {} }

/-- A state to keep, without the bodies of the functions: those are the
program's as it is now, which `adopt` keeps. -/
def noBodies (st : St) : St := { st with body := {}, fnBodies := {} }

/-- A group of functions, as what its check is made from. -/
def groupKey (key : UInt64) (group : List FnDecl) : UInt64 :=
  group.foldl (fun h d => mixHash h (hash (d.name, d.params, d.annots, d.ret, d.body, d.bounds))) key

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
  set { st with modules := now.modules, ownItems := now.ownItems, fnBodies := now.fnBodies }

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
        let name := Syntax.implFnName im.trait im.head m
        -- (Its body, where the declaration has none: by its name.)
        let kept := (← get).fnBodies[name]?
        let body := if clauses.roots.isEmpty then kept.getD {} else clauses
        out := out ++ [{ name,
                         params := im.params ++ inner ++ sig.mparams.map (·.1) ++ lifetimes, annots,
                         ret, body, impl := some (im, sig), bounds := uses }]
  pure out

/-- Each `let` of the group that is a place (`St.placedLets`) written `let
mut` for the elaborator, as a variable the checker decided: what is
checked already, not checked again. -/
def placeLets (decls : List FnDecl) (from_ : Nat) : M Unit := do
  let s ← get
  -- (What was written where it was found, `Elab.Decision.receiverHere`, in
  -- the bodies later checks follow.)
  let here := (s.decided.drop from_).filter fun
    | .receiverHere .. | .derefHere .. | .derefAssignHere .. | .compareHere .. | .refPatsHere .. => true
    | _ => false
  unless here.isEmpty do
    modify fun s =>
      { s with runFns := decls.foldl (fun m d =>
          m.insert d.name (here.foldl (fun b dec => Elab.decideBody dec d.name d.annots b) ((m[d.name]?).getD d.body))) s.runFns }
  let s ← get
  let lets := s.placedLets.toList.filter fun p => decls.any (·.name == p.1)
  -- (A name a clause binds: kept in a variable where the clause starts,
  -- `Elab.heldFirst`.)
  let params := (s.placedNames.toList.filter fun (owner, _, id) =>
      decls.any (·.name == owner) && !s.placedLetIds.contains id).map (fun (owner, x, _) => (owner, 0, 0, x))
  let mine := lets ++ params.eraseDups
  if mine.isEmpty then return
  let ds := mine.map fun (owner, l, c, x) => Elab.Decision.letMut owner l c x
  modify fun s =>
    { s with decided := s.decided ++ ds
             runFns := decls.foldl (fun m d =>
               let b := ds.foldl (fun b dec => Elab.decideBody dec d.name d.annots b) ((m[d.name]?).getD d.body)
               m.insert d.name b) s.runFns }

/-- Check a group, deciding where it is found what can be known only once
types are (`Elab.Decision`): the group is checked again with it, from where
it began, and it is kept for the program to be written with. What is said if
a value kept in a variable is then refused is why it could not be left
unused (`first`). -/
partial def checkDeciding (decls : List FnDecl) (fuel : Nat := 64) (first : Option String := none) :
    M Unit := do
  let before ← get
  tryCatchThe Elab.Said (do checkGroup decls; placeLets decls (before.decided.length)) fun e => do
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
      let decls' := decls.map fun dl => { dl with body := Elab.decideBody d dl.name dl.annots dl.body }
      -- (Nothing changed: what was said stands.)
      -- (As written out: a rewrite may make new nodes of what it leaves the same.)
      if (decls'.map fun d => d.body.hashClosure 0 d.body.roots) == (decls.map fun d => d.body.hashClosure 0 d.body.roots) then
        throwThe Elab.Said said
      set before
      modify fun s =>
        { s with decided := s.decided ++ [d]
                 runFns := decls'.foldl (fun m d => m.insert d.name d.body) s.runFns }
      let first := match d with
        | .letMut .. => some (first.getD e.msg)
        | _ => first
      checkDeciding decls' fuel first
    | _, _ => throwThe Elab.Said said

/-- `x`, or its refusal: what it did kept, the state not put
back (which would hold it twice, and copy what it changes). -/
def attempt {α : Type} (x : M α) : M (Except Elab.Said α) := fun s =>
  match x s with
  | .ok a s => .ok (.ok a) s
  | .error e s => .ok (.error e) s

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

/-- The captures of a type, in the order it has them, with those of what a
callable performs. -/
partial def capsOf : Ty → List Nat
  | .ref how t c => capsOf how ++ capsOf t ++ [c]
  | .fn ps r effs _ c => ps.flatMap capsOf ++ capsOf r ++ effs.flatMap (·.2.flatMap capsOf) ++ [c]
  | .con _ args | .tuple args => args.flatMap capsOf
  | .var _ => []

/-- The lifetimes of the references a type is made of, outermost first. -/
partial def refCapsOf : Ty → List Nat
  | .ref _ t c => c :: refCapsOf t
  | .con _ args => args.flatMap refCapsOf
  | .tuple args => args.flatMap refCapsOf
  | _ => []

/-- The `k`-th lifetime of a type, as `schemeShape` writes it: with no digit,
which it numbers anew. -/
def lifeAt (k : Nat) : String := "life" ++ String.ofList (List.replicate (k + 1) '\'')

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
          | some k => [lifeAt k]
          | none => if seen.contains c' then [] else holds fuel (c' :: seen) c'
        -- (A value held whose type is a reference with a lifetime of the
        -- type's own: as that lifetime held, which is what a signature says
        -- of a borrow of what it is given.)
        -- (Of a lifetime the type does not have, what that one holds: a
        -- borrow made in the body, of what the type's lifetimes borrow.)
        | .ty t => match capsOf t with
          -- (A value of a type with no variable and no lifetime holds
          -- nothing of the caller's: an `Int` a callable keeps.)
          | [] => if (freeTys t).isEmpty then [] else [s!"ty {showTy t}"]
          | cs => if cs.all (fun c' => (place c').isSome) then cs.filterMap fun c' => (place c').map (lifeAt ·)
            else cs.flatMap fun c' => match place c' with
              | some k => [lifeAt k]
              | none => if seen.contains c' then [] else holds fuel (c' :: seen) c'
        | .inner _ => if quiet then [] else ["inner"]
        | .brand _ => ["brand"]
        | .once => ["once"]
        | .must => ["must"]
        -- (That it is a borrow, not a value: what it is a borrow of says it.)
        | .loan _ => []
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

/-- Whether what a function's body was found to need of its callers is no
more than its signature says (`schemeShape` of each): the same type; of the
traits it asks, those the signature asks; as many types to use more than
once, to let go and to come back, or fewer; and of what each of its
lifetimes and callables holds, what the signature says or less. So callers
checked with the signature are checked with all the body needs. -/
def schemeWithin (body sig : Scheme) : Bool :=
  let parts := fun (text : String) =>
    match text.splitOn " holds " with
    | [head, held] =>
      let toks : List String := head.splitOn " "
      let counts := (toks.drop (toks.length - 3)).map fun (t : String) => t.length - 1
      let early := toks.take (toks.length - 3)
      match early.findIdx? (fun (t : String) => t.startsWith "b" && (t.drop 1).all (· == '|')) with
      | some i =>
        let ty := " ".intercalate (early.take i)
        let bounds := ((" ".intercalate (early.drop (i + 1))).drop 1 |>.dropEnd 1 |>.toString).splitOn ", "
          |>.filter (· != "")
        let inner := ((held.drop 1).dropEnd 1).toString
        let lists := if inner.isEmpty then [] else
          ((inner.drop 1).dropEnd 1).toString.splitOn "], [" |>.map fun (l : String) => (l.splitOn ", ").filter (· != "")
        some (ty, bounds, counts, lists)
      | none => none
    | _ => none
  -- (What a callable performs, in any order.)
  let rows := fun (t : String) => (t.splitOn "{").mapIdx (fun i (part : String) =>
    if i == 0 then part else match part.splitOn "}" with
      | inner :: rest => "}".intercalate (", ".intercalate ((inner.splitOn ", ").mergeSort (· ≤ ·)) :: rest)
      | [] => part) |> "{".intercalate
  -- (What holds a reference holds what it is to holds, as Rust's implied
  -- bounds have it: `&'a mut Q<'w>` held, `'w` is.)
  let caps := capsOf sig.ty
  let rec implied : Ty → List (Nat × List Nat)
    | .ref how t c => (c, capsOf t) :: implied how ++ implied t
    | .fn ps r _ _ _ => ps.flatMap implied ++ implied r
    | .con _ args | .tuple args => args.flatMap implied
    | .var _ => []
  let within := (implied sig.ty).filterMap fun (c, inner) =>
    (caps.idxOf? c).map fun k => (lifeAt k, inner.filterMap fun c' => (caps.idxOf? c').map lifeAt)
  let close := fun (h : List String) => h ++ h.flatMap fun x => ((within.lookup x).getD [])
  match parts (schemeShape body), parts (schemeShape sig) with
  | some (t, bs, cs, hs), some (t', bs', cs', hs') =>
    -- (The traits asked are the signature's, in its order: a caller gives a
    -- dictionary for each, where the signature says.)
    rows t == rows t' && bs.all bs'.contains && body.bounds.map (·.1) == sig.bounds.map (·.1)
      && (cs.zip cs').all (fun (a, b) => a ≤ b) && hs.length == hs'.length
      -- (A lifetime is any place the signature has it: `'a` twice.)
      && ((hs.zip hs').zipIdx).all fun ((h, h'), i) =>
        let same := caps.zipIdx.filterMap fun (c, j) => if caps[i]? == some c then some (lifeAt j) else none
        h.all (close (lifeAt i :: same ++ h')).contains
  | _, _ => false

/-- A function's type with what calls of a label it is given give left out:
a jump gives nothing back, and whatever is wanted where it is made. -/
def withoutLabelResults (d : FnDecl) (s : Scheme) : Scheme :=
  let labels := d.annots.zipIdx.filterMap fun
    | (some (.name f []), i) => if d.bounds.any (fun b => b.trait == "Label" && b.subject == f) then some i else none
    | _ => none
  if labels.isEmpty then s else
  match s.ty with
  | .fn ps r effs tail cap =>
    { s with ty := .fn (ps.zipIdx.map fun (p, i) => match p with
        | .fn qs _ es t c => if labels.contains i then .fn qs .unit es t c else p
        | p => p) r effs tail cap }
  | _ => s

/-- What a body needs that its signature does not say, as an error: what to
write (`schemeWithin`). -/
def beyondSignature (name : String) (sig body : Scheme) : String :=
  let ty := fun (s : Scheme) => (schemeShape s).splitOn " b" |>.headD ""
  let traits := body.bounds.filterMap fun (tr, _) =>
    if (body.bounds.filter (·.1 == tr)).length > (sig.bounds.filter (·.1 == tr)).length then some tr else none
  let what :=
    if ty body != ty sig then s!"its body is found to have the type `{ty body}`, and its signature says `{ty sig}`"
    else if !traits.isEmpty then
      s!"its body asks {", ".intercalate (traits.eraseDups.map (s!"`{·}`"))} of a type its signature says nothing of: write it after `where`"
    else if body.dups.length > sig.dups.length then
      "its body uses something it is given more than once, which its signature does not say: write `T: Use<[0, *]>` of its type parameter"
    else if body.drops.length > sig.drops.length then
      "its body lets go of something it is given unused, which its signature does not say: write `T: Use<[0, 1]>` of its type parameter"
    else if body.stays.length > sig.stays.length then
      "its body calls a callable it is given while it holds what has to be used: write `F: Returns` of its type parameter"
    else "what it gives back borrows or holds what its signature does not say: write its lifetimes"
  s!"in `{name}`: {what}"

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

/-- What a group added, with what it read of the rest of its unit: each
name it calls, with what that function showed it (`interfaceOf`), and each
body its count of uses followed (`bodyKey`). -/
abbrev KeptGroup := StDelta × Array (String × UInt64)

/-- Groups none of which uses another, checked side by side: a few runs of
them, each on a thread of its own from the state before, its ids from a place
of its own (`jumpedFor`), and what each added put together (`mergeStates`),
as if one had been checked after another. A run that cannot be put with those
before it (both changed one thing that was there: a lifetime a declared type
has, which each binds), or that was refused, is checked again after them: what
is said is then the first refusal in their order, as one after another would
say it. -/
def checkSideBySideWith {α : Type} (groups : List α) (one : α → M (Array (UInt64 × KeptGroup)))
    (jump : Bool := true) : M (Array (UInt64 × KeptGroup)) := do
  if groups.length < 8 then
    let mut made := #[]
    for g in groups do made := made ++ (← one g)
    return made
  let threads := min (groups.length / 4 + 1) sideThreads
  let size := (groups.length + threads - 1) / threads
  let runs := (List.range threads).filterMap fun t =>
    match (groups.drop (t * size)).take size with
    | [] => none
    | run => some run
  let start ← get
  let tasks := runs.zipIdx.map fun (run, j) =>
    (run, j, Task.spawn (prio := .dedicated) fun _ =>
      (run.foldlM (fun acc g => do pure (acc ++ (← one g))) #[] : M (Array (UInt64 × KeptGroup))).runE
        (if jump then jumpedFor start j runGap else start))
  -- (In order: a run that cannot be put with those before it, or was
  -- refused, is checked again after them, as one after another would.)
  let mut made := #[]
  for (run, j, t) in tasks do
    let here ← get
    let got := Trace.timed "side: wait" fun _ => t.get
    let put := match got with
      | .ok (mine, after) =>
        if !jump || stayedBelow after start j runGap then
          (Trace.timed "side: merge" fun _ => mergeStates start here after).map (mine, ·)
        else none
      | .error _ => none
    match put with
    | some (mine, st) =>
      set st
      made := made ++ mine
    | none =>
      let again ← timedM "side: again" (run.foldlM (fun acc g => do pure (acc ++ (← one g))) #[])
      made := made ++ again
  pure made

def checkSideBySide (groups : List (List FnDecl)) : M Unit := do
  let _ ← checkSideBySideWith groups fun g => do checkMaybe g; pure #[]

/-- What each of the program's own groups added, by a key of what it is
checked from (`checkGroupKept`): kept by one compile for the next. -/
abbrev Deltas := Std.HashMap UInt64 (Thunk (Option KeptGroup))

/-- Is there room for the `i`-th group of a unit that began at `pre` to
number from where it does (`jumpedTo`): no more made already? -/
def jumpRoom (s pre : St) (i : Nat) : Bool :=
  let at_ := fun (n : Nat) => n + (i + 1) * runGap
  let room := fun (now was : Nat) => now ≤ at_ was
  room s.tys.size pre.tys.size && room s.rows.size pre.rows.size && room s.caps.size pre.caps.size
    && room s.capEdges.size pre.capEdges.size && room s.loans.size pre.loans.size
    && room s.rigidKeys.size pre.rigidKeys.size && room s.brands pre.brands && room s.dropAsked pre.dropAsked

/-- The state with what is made next numbered from where the `i`-th group
of a unit that began at `pre` numbers from, `runGap` after the one before,
where there is room (`jumpRoom`). -/
def jumpedTo (s pre : St) (i : Nat) : St :=
  let at_ := fun (n : Nat) => n + (i + 1) * runGap
  { s with
    tys := s.tys.jumpTo (at_ pre.tys.size), rows := s.rows.jumpTo (at_ pre.rows.size)
    caps := s.caps.jumpTo (at_ pre.caps.size), capOut := s.capOut.jumpTo (at_ pre.caps.size)
    capEdges := s.capEdges.jumpTo (at_ pre.capEdges.size)
    capEdgeNames := s.capEdgeNames.jumpTo (at_ pre.capEdges.size)
    loans := s.loans.jumpTo (at_ pre.loans.size), rigidKeys := s.rigidKeys.jumpTo (at_ pre.rigidKeys.size)
    brands := at_ pre.brands, dropAsked := at_ pre.dropAsked }

/-- What a function shows the functions that call it: its scheme written
out whole, and what the checker keeps of it by its name for its callers
(the arguments it runs in place or together, whether it must be run, its
type parameters as written, whether it is `unsafe`, its rows). -/
def interfaceOf (c : String) : M UInt64 := do
  let s ← get
  let shown := fun (xs : List (Ty × String)) => xs.map fun (t, w) => (showTy t, w)
  let sch := match (s.fnCalls[c]?).orElse fun _ => s.fns[c]? with
    | some sc => s!"{schemeDetail sc} {shown sc.stays} {shown sc.statics} {sc.sites.map showTy} {sc.ranked} {shown sc.quiets} {sc.assocs.map fun ((a, t, b, u) : String × Ty × String × Ty) => (a, showTy t, b, showTy u)} {sc.incls.map fun ((t, u) : Ty × Ty) => (showTy t, showTy u)} {sc.rvars} {showTyCaps sc.ty}"
    | none => ""
  let rows := (s.rowChecks.filter (·.1 == c)).map fun (_, ps) => ps.map fun ((n, t) : String × Ty) => (n, showTy t)
  pure (hash (sch, s.fnRunsIn.lookup c, s.fnGroups.lookup c, s.envMust.contains c, s.typeParams.lookup c,
    s.unsafeFns.contains c, rows))

/-- What a function's body is, as the count of uses follows it. -/
def bodyKey (f : String) : M UInt64 := do
  let s ← get
  pure (hash ((s.runFns[f]?).orElse fun _ => s.declFns[f]?))

/-- Is what a group read still what it was? `fn ` a name it calls, `body ` a
body it followed; `*` a count that did not finish, never. -/
def readsHold (reads : Array (String × UInt64)) : M Bool := do
  for (what, was) in reads do
    let now ← if what.startsWith "fn " then interfaceOf (what.drop 3).toString
      else if what.startsWith "body " then bodyKey (what.drop 5).toString
      else pure (was + 1)
    unless now == was do return false
  pure true

/-- A group of a unit begun at `pre`, the `i`-th, under `key` (of the
unit's declarations and the group whole): what an earlier compile found it
added (`kept`), put on the state, where what it read of the rest of the
unit is as it was (`readsHold`): what each function it calls shows it
(`interfaceOf`), not how its body is written, and the bodies its count of
uses followed. Else checked. Each group numbers from a place of its own
(`jumpedTo`), so what it added does not depend on what the groups before
it made. Gives what it added, under `key`, with what it read. `callees`:
the unit's functions it calls; `locals`: the unit's functions. -/
def checkGroupKept (kept : Deltas) (pre : St) (key : UInt64) (i : Nat) (g : List FnDecl)
    (callees : List String) (locals : Std.HashSet String) : M (Array (UInt64 × KeptGroup)) := do
  unless jumpRoom (← get) pre i do
    checkMaybe g
    return #[]
  -- (In place: the state is not held twice, so its stores are not copied.)
  modify fun s => jumpedTo s pre i
  if let some (d, reads) := (kept[key]?).bind (·.get) then
    if ← timedM "group: reads hold" (readsHold reads) then
      -- (Taken out of the state, so that it is held once while what the
      -- group added is put on, in place, where it fits.)
      let cur ← modifyGet fun s => (s, {})
      if fitsDelta none cur d then
        match Trace.timed "group: reused" fun _ => applyDelta none cur d with
        | some st' =>
          set st'
          return #[(key, (d, reads))]
        | none => throw "what an earlier compile kept of a group fits and was not put on; this is a compiler defect: build with GLORIOUS_FRESH=1"
      set cur
  let st ← get
  checkMaybe g
  let after ← get
  -- (One that made more than its room: what it added is not kept.)
  unless jumpRoom after pre (i + 1) do return #[]
  let followed := (after.followed.extract st.followed.size after.followed.size).toList.eraseDups
  if followed.contains "*" then return #[]
  let mut reads : Array (String × UInt64) := #[]
  for c in callees do reads := reads.push (s!"fn {c}", ← interfaceOf c)
  for f in followed do
    if locals.contains f then reads := reads.push (s!"body {f}", ← bodyKey f)
  pure ((Trace.timed "group: delta" fun _ => diffStates st after).toArray.map fun d => (key, (d, reads)))

/-- Errors said together: each once, in the order of where they are in the
text (`line:col:` first; one that says no place, first of all), a line
each (`errorLines` writes each as an error). -/
def sortedErrors (errors : List String) : String :=
  let place := fun (e : String) => match (e.splitOn ":").take 2 |>.map String.toNat? with
    | [some l, some c] => (l, c)
    | _ => (0, 0)
  let sorted := errors.eraseDups.mergeSort fun a b =>
    let (la, ca) := place a
    let (lb, cb) := place b
    la < lb || (la == lb && ca ≤ cb)
  "\n".intercalate sorted

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
def checkItems (fitems : List Syntax.Item) (seed : UInt64 := 0) (kept : Kept := []) (deltas : Option Deltas := none) :
    M (Kept × Array (UInt64 × KeptGroup)) := do
  -- The items as they declare, and their functions' bodies by name.
  let items := fitems.map Syntax.Item.declared
  let bodies := fitems.flatMap Syntax.Item.bodies
  let ownBodies := fun (_ : Unit) => (modify fun s =>
    { s with fnBodies := bodies.foldl (fun m (n, b) => m.insert n b) s.fnBodies } : M Unit)
  ownBodies ()
  let bodyOf : Std.HashMap String Flat.Body := bodies.foldl (fun m (n, b) => m.insertIfNew n b) {}
  let written := items.filterMap fun
    | .bounds fn bounds => some (fn, bounds)
    | _ => none
  let decls : List FnDecl := items.filterMap fun
    | .fn name params annots ret _ =>
      some { name, params, annots, ret, body := (bodyOf[name]?).getD {}, bounds := (written.lookup name).getD [] }
    | _ => none
  -- (The machine's operations, `#[intrinsic]`: each has the type its
  -- signature says, which is declared with the rest; it has no body.)
  let intrinsic := items.filterMap fun
    | .fieldNames mark [n] _ => if mark == Syntax.attrMark "intrinsic" then some n else none
    | _ => none
  let (machine, decls) := decls.partition (intrinsic.contains ·.name)
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
    | .alias name b e => some (name, b.fvExpr [] e)
    | .pub _ (.alias name b e) => some (name, b.fvExpr [] e)
    | _ => none)
  let nameSet : Std.HashSet String := names.foldl (·.insert ·) {}
  -- (And the functions a dot call in it may turn out to be of, the types'
  -- own of the name: one is checked before what may call it.)
  let modules := (← get).modules
  -- (What each function mentions, found once for each.)
  let mentioned : Std.HashMap String (List String) := decls.foldl (fun m d =>
    let fvs := d.body.fvClauses d.body.roots
    let alts := if modules.dotAlts.isEmpty then [] else
      (d.body.callIdsClauses d.body.roots).flatMap
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
    let whole := mixHash seed (hash fitems)
    if let some st := kept.lookup whole then
      adopt st
      ownBodies ()
      return ([(whole, st)], #[])
    let before := (← get).impls.size
    let mut made : Kept := []
    let mut groupDeltas : Array (UInt64 × KeptGroup) := #[]
    -- (A function is declared by checking it, with its group: what is
    -- declared first is the rest, so a function added, or a signature
    -- changed, keeps what was found of the declarations and the groups
    -- before it.)
    let fnNames : Std.HashSet String := decls.foldl (fun s d => s.insert d.name) {}
    let declared := items.filter fun
      | .fn n .. => intrinsic.contains n
      | .pub _ (.fn ..) => false
      | .bounds f _ => !fnNames.contains f
      | _ => true
    let mut key := mixHash seed (hash (declared.map Item.declared))
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
    | some st =>
      adopt st
      ownBodies ()
    | none =>
      -- (Of the program's own units, what declaring added, as an earlier
      -- compile found it, with this program's bodies put in: where it
      -- numbered from is part of its key.)
      let here ← get
      let declFrom := mixHash key (hash [here.tys.size, here.rows.size, here.caps.size, here.capEdges.size,
        here.loans.size, here.rigidKeys.size, here.brands, here.dropAsked, here.impls.size])
      let taken := match deltas with
        | some kept => (kept[declFrom]?).bind (·.get) |>.bind fun (d, _) =>
          ((applyDelta none here d).bind ours).map (d, ·)
        | none => none
      match taken with
      | some (d, st) =>
        set st
        ownBodies ()
        groupDeltas := groupDeltas.push (declFrom, (d, #[]))
      | none =>
        timedM "unit: declare" do
          declare items
          computeVariances
          declareTraits items
          checkUseDecls
          for d in machine do checkGroup [d] (signature := true)
        if deltas.isSome then
          if let some d := diffStates here (← get) then groupDeltas := groupDeltas.push (declFrom, (d, #[]))
    made := (key, noBodies (← get)) :: made
    modify fun s =>
      { s with declFns := decls.foldl (fun m d => m.insertIfNew d.name d.body) s.declFns }
    -- (A state kept from before has the bodies that program's later
    -- functions had: this one's are put in their place.)
    let restore := fun (st : St) (later : List FnDecl) => (do
      adopt st
      modify fun s =>
        { s with runFns := later.foldl (fun m d => m.erase d.name) s.runFns
                 declFns := later.foldl (fun m d => m.insert d.name d.body) s.declFns } : M Unit)
    let declBy : Std.HashMap String FnDecl := decls.foldl (fun m d => if m.contains d.name then m else m.insert d.name d) {}
    let groups := Trace.timed "unit: order" fun _ => (components names deps).map fun comp => comp.filterMap fun n => declBy[n]?
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
    -- (Each group's key of what it is checked from, where what each added
    -- is kept (`checkGroupKept`): the declarations, the group whole, and the
    -- groups it calls into, each by its own such key.)
    let declKey := key
    let readKeys : Array UInt64 := groups.zipIdx.foldl (fun (acc : Array UInt64) (g, i) =>
      let callees := (g.foldl (fun l d => (deps d.name).foldl (fun l n =>
        match groupOf[n]? with
        | some j => if j < i then j :: l else l
        | none => l) l) []).eraseDups.mergeSort
      acc.push (callees.foldl (fun h j => mixHash h ((acc[j]?).getD 0)) (groupKey declKey g))) #[]
    -- (Of the groups themselves: the declarations and the group whole; what
    -- each reads of the others is said with what it added, `checkGroupKept`.)
    let ownKeyAt : Array UInt64 := Trace.timed "unit: own keys" fun _ => (sorted.map fun (_, _, g) => groupKey declKey g).toArray
    let calleesAt : Array (List String) := (sorted.map fun (_, i, g) =>
      (g.flatMap fun d => (deps d.name).filter fun n => match groupOf[n]? with
        | some j => j != i
        | none => false).eraseDups).toArray
    let localFns : Std.HashSet String := names.foldl (·.insert ·) {}
    let groups := sorted.map (·.2.2)
    -- The functions of the copies of an implementation for every type
    -- (`impl<T> Requires for T`, one for each type the unit declares) that
    -- name none of the unit's functions, where no coercion is: checked
    -- before the others, so that what was found of them is kept where only
    -- a function's body changed.
    let blanket := fun (im : ImplDecl) => im.methods.any fun
      | .typeAlias n _ _ => (Syntax.blanketParam n).isSome
      | _ => false
    -- (And those the compiler writes that nothing may ask, `Reflect`.)
    let packed := fun (im : ImplDecl) => im.methods.any fun
      | .typeAlias n _ _ => n == Syntax.askedOnlyName
      | _ => false
    let mut copies : Array (String × FnDecl × Bool) := #[]
    for im in ((← get).impls.toList.drop before).filter (fun im => blanket im || packed im) do
      for d in ← implFnDecls im do copies := copies.push (im.dictFn, d, packed im)
    let namesAny := fun (d : FnDecl) =>
      ((d.body.fvClauses d.body.roots).flatMap fun x => x :: aliasOf.getD x []).any nameSet.contains
    let earlyCopies : Array (String × FnDecl) := if coercing.isEmpty then
        (copies.filter (fun (_, d, isPack) => isPack || !namesAny d)).map fun (f, d, _) => (f, d)
      else #[]
    let early := earlyCopies.toList.map (·.2)
    -- (Checked only where something uses them, at the end of this unit or
    -- of a later one: most are of types no bound asks them of. What a kept
    -- state had of this unit's is put back as they are now.)
    let earlySet : Std.HashSet String := early.foldl (fun s d => s.insert d.name) {}
    let refreshCopies : M Unit := modify fun s =>
      { s with pendingCopies := (s.pendingCopies.filter fun (_, d) => !earlySet.contains d.name) ++ earlyCopies }
    refreshCopies
    -- The state after the last group whose key, and so every key before
    -- it, is kept is taken; the groups after it are checked. (One is kept
    -- after the last group alone.)
    let keys := (groups.foldl (fun (acc : List UInt64 × UInt64) g =>
      let k := groupKey acc.2 g
      (k :: acc.1, k)) ([], key)).1.reverse
    let start := if deltas.isSome then 0 else
      ((keys.zipIdx.reverse.find? fun (k, _) => (look k).isSome).map (·.2 + 1)).getD 0
    if start > 0 then
      if let some k := keys[start - 1]? then
        if let some st := look k then
          restore st ((groups.drop start).flatten)
          refreshCopies
          made := (k, st) :: made
    let rest := (groups.zipIdx.drop start).toArray
    -- (What the unit's declarations say of types left to implementations,
    -- `type Kind = OneToMany`, answered where they ask it, before any body.)
    settleAssocsAll
    -- Each function's type as its signature says, first.
    let pre ← get
    -- (Where each group numbers from is part of what it is checked from.)
    let from_ := hash [pre.tys.size, pre.rows.size, pre.caps.size, pre.capEdges.size, pre.loans.size,
      pre.rigidKeys.size, pre.brands, pre.dropAsked]
    -- (What the signatures added is kept too, under a key of them all and
    -- of the declarations, their bodies not in it: put on where it fits;
    -- with the types the bodies were found to have, from which the next
    -- compile's are checked first.)
    let sigKey := mixHash 2 (rest.foldl (fun h (g, _) => g.foldl (fun h d =>
      mixHash h (hash (d.name, d.params, d.annots, d.ret, d.bounds))) h) (mixHash declKey from_))
    let mut sigsKept : Option StDelta := none
    if let some kept := deltas then
      if let some (d, _) := (kept[sigKey]?).bind (·.get) then
        let cur ← get
        if fitsDelta none cur d then
          if let some st' := applyDelta none cur d then
            set st'
            sigsKept := some d
    if sigsKept.isNone then
      for (g, _) in rest do
        for d in g do tryCatchThe Elab.Said (checkGroup [d] (signature := true)) fun _ => pure ()
    -- Then every body checked from those, side by side, none waiting for
    -- another's: each is to need no more of its callers than its signature
    -- says, as Rust's (`schemeWithin`). A group refused where all before it
    -- need no more: one after another, then callees first.
    -- (Each group kept as the signatures are, `checkGroupKept`: what it
    -- read of the others, held or not, says whether it is checked again.)
    let failMark := "%refused "
    -- (Where only what `main` reaches is asked, `St.reachOnly` (`watch`, to
    -- run before the rest is checked): of the unit `main` is in, the bodies
    -- of the groups it reaches. The others' are checked by the compile
    -- after, and nothing of this one is kept as the unit's.)
    let reachOnly := (← get).reachOnly && names.contains "main"
    let reached : Std.HashSet String := if !reachOnly then {} else Id.run do
      let mut seen : Std.HashSet String := {}
      let mut todo := ["main"]
      while !todo.isEmpty do
        match todo with
        | n :: more =>
          todo := more
          unless seen.contains n do
            seen := seen.insert n
            todo := deps n ++ todo
        | [] => pure ()
      pure seen
    let skipped := fun (g : List FnDecl) => reachOnly && !g.any (reached.contains ·.name)
    let fromSt ← get
    let sigFrom := mixHash 1 (hash [fromSt.tys.size, fromSt.rows.size, fromSt.caps.size, fromSt.capEdges.size,
      fromSt.loans.size, fromSt.rigidKeys.size, fromSt.brands, fromSt.dropAsked])
    -- (A group refused leaves what it did, the state not put back, which
    -- would hold it twice: what comes after it is checked again.)
    let one := fun ((g, k) : List FnDecl × Nat) => do
      if skipped g then return #[]
      let got : Except Elab.Said (Array (UInt64 × KeptGroup)) ← attempt (match deltas with
          | some kept => checkGroupKept kept fromSt (mixHash ((ownKeyAt[k]?).getD 0) (mixHash sigFrom (hash k)))
              k g ((calleesAt[k]?).getD []) localFns
          | none => do checkMaybe g; pure #[])
      match got with
      | .ok made => pure made
      | .error e =>
        modify fun s => { s with refusals := s.refusals.push s!"{failMark}{k} {e.msg}" }
        pure #[]
    let mut settled := rest.isEmpty
    let mut together := false
    while !settled do
      set fromSt
      let checked ← if together then rest.toList.foldlM (fun acc x => do pure (acc ++ (← one x))) #[]
        else checkSideBySideWith rest.toList (jump := deltas.isNone) one
      let now ← get
      let refused : Std.HashSet Nat := (now.refusals.extract fromSt.refusals.size now.refusals.size).foldl
        (fun s m => if m.startsWith failMark then
          match ((m.drop failMark.length).takeWhile Char.isDigit).toString.toNat? with
          | some k => s.insert k
          | none => s
          else s) {}
      -- (A constant's type is its value's, which no signature says.)
      let isSettled := fun (g : List FnDecl) => g.all fun d =>
        Syntax.isConstFn d.name || match fromSt.fns[d.name]?, now.bodySchemes[d.name]? with
        | some a, some b => schemeWithin (withoutLabelResults d b) (withoutLabelResults d a)
        | _, _ => false
      let firstRefused := rest.toList.find? fun (_, k) => refused.contains k
      let before := rest.toList.takeWhile fun (_, k) => !refused.contains k
      -- A body that needs more of its callers than its signature says: said,
      -- as Rust's is, with what to write.
      let mut beyond : Array String := #[]
      for (g, _) in before do
        unless skipped g || isSettled g do
          for d in g do
            match fromSt.fns[d.name]?, now.bodySchemes[d.name]? with
            | some a, some b =>
              unless schemeWithin (withoutLabelResults d b) (withoutLabelResults d a) do
                beyond := beyond.push (beyondSignature d.name a b)
            | _, _ => beyond := beyond.push s!"in `{d.name}`: its signature says too little to check its callers with: write it whole"
      unless beyond.isEmpty do throw (sortedErrors beyond.toList)
      settled := true
      if firstRefused.isSome then
        -- A refusal where all before it are settled: from a group checked
        -- before it that is not its callee (a field's type its body
        -- found), so once more one after another; or the program's,
        -- said as callees first say it, from before the signatures.
        if !together then
          together := true
          settled := false
          continue
        -- Each group again, callees first, from before the signatures:
        -- what each refuses is said, as callees first say it (a
        -- function's calls of itself are at the one type it is being
        -- found to have, and see less of what a signature says than its
        -- callers do). One that calls a refused one is not asked: what it
        -- would say follows from that.
        set pre
        let mut errors : Array String := #[]
        let mut failed : Std.HashSet String := {}
        for (g, k) in rest do
          if ((calleesAt[k]?).getD []).any failed.contains then
            for d in g do failed := failed.insert d.name
            continue
          match ← attempt (checkMaybe g) with
          | .ok _ => pure ()
          | .error e =>
            errors := errors.push e.msg
            for d in g do failed := failed.insert d.name
        if errors.isEmpty then
          let said := (now.refusals.find? (·.startsWith failMark)).getD ""
          errors := errors.push (match (said.drop failMark.length).toString.splitOn " " with
            | _ :: rest => " ".intercalate rest
            | [] => said)
        throw (sortedErrors errors.toList)
      if deltas.isSome then
        match sigsKept with
        | some d => groupDeltas := groupDeltas.push (sigKey, (d, #[]))
        | none => if let some d := diffStates pre fromSt then groupDeltas := groupDeltas.push (sigKey, (d, #[]))
      set now
      groupDeltas := groupDeltas ++ checked
      if let some (_, last) := rest.back? then
        unless reachOnly do made := (keys[last]!, forKeeping (← get)) :: made
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
          refreshCopies
          made := (k, st) :: made
    -- (None uses another: all side by side.)
    timedM "unit: impl groups" (checkSideBySide (implGroups.toList.drop implStart))
    if implStart < implGroups.size then
      if let some k := implKeys.getLast? then made := (k, noBodies (← get)) :: made
    if let some k := implKeys.getLast? then key := k
    for c in coercing do
      unless (((← get).fnBounds.lookup c).getD 0) == 0 do
        throw s!"`coerce {c}`: a coercion cannot need a trait of a type it is used at"
    -- The copies of implementations for every type that something now
    -- uses: checked, and then those that they use, until none is left that
    -- is used.
    -- (What the table names, gone through once for each entry made since the
    -- last look, and once for each dictionary however often it is shared.)
    let mut asking := true
    -- (Each copy checked is kept as the groups are, numbered after them.)
    let mut copyAt := groups.length + 1
    let mut used : Std.HashSet String := {}
    let mut seen : Std.HashSet USize := {}
    let mut scanned := 0
    while asking do
      let table := (← get).dictTable
      let mut todo : Array Elab.DictE := #[]
      for k in [scanned:table.size] do
        if let some (_, ds) := table[k]? then todo := todo ++ ds.toArray
      scanned := table.size
      while !todo.isEmpty do
        let d := todo.back!
        todo := todo.pop
        unless seen.contains (addrOf d) do
          seen := seen.insert (addrOf d)
          if let .impl f subs := d then
            used := used.insert f
            todo := todo ++ subs.toArray
      let (ready, rest) := (← get).pendingCopies.partition fun (f, _) => used.contains f
      if ready.isEmpty then asking := false
      else
        modify fun s => { s with pendingCopies := rest }
        match deltas with
        | some kept =>
          -- (A copy's key: the declarations, the copy, the copies checked
          -- with it, and the keys of the unit's groups it names.)
          let batch := hash (ready.toList.map fun (f, d) => (f, groupKey 0 [d]))
          let keyOfCopy := fun (d : FnDecl) (at_ : Nat) =>
            let callees := ((d.body.fvClauses d.body.roots).filterMap fun n => groupOf[n]?).eraseDups.mergeSort
            let read := callees.foldl (fun h j => mixHash h ((readKeys[j]?).getD 0)) (mixHash (groupKey declKey [d]) batch)
            mixHash read (mixHash from_ (hash at_))
          let start := copyAt
          groupDeltas := groupDeltas ++ (← checkSideBySideWith ready.toList.zipIdx (jump := false) fun ((_, d), j) =>
            checkGroupKept kept pre (keyOfCopy d (start + j)) (start + j) [d] [] localFns)
          copyAt := start + ready.size
        | none => checkSideBySide (ready.toList.map fun (_, d) => [d])
    timedM "unit: late" do
      checkDups (← get).lateDups
      checkDrops (← get).lateDrops
      checkStays (← get).lateStays
    modify fun s => { s with lateDups := #[], lateDrops := #[], lateStays := #[] }
    let wholeSt := noBodies (← get)
    pure (if reachOnly then [] else (whole, wholeSt) :: made, groupDeltas)

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
    let implEs := (s.impls.toList.map fun im =>
      let names := traitsBy.getD (Syntax.traitBase im.trait) []
      (⟨im.dictFn, im.context.length + im.extra.length, names.map fun m =>
        (Syntax.implFnName im.trait im.head m,
          if im.trait == Syntax.destroyTrait then 1
          else arityBy.getD m 0)⟩ :
        Elab.ImplE)) ++ [({ dictFn := Syntax.markerDict, conditions := 0, methods := [] } : Elab.ImplE)]
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
        -- (A `[T; N]`: each of its elements.)
        if im.head == "Fixed" then ctors := [("%each", [place 0])]
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
        destroys := destroys.push ⟨im.head, im.context.length, hook, im.head == "Fixed", ctors⟩
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
           scalarLits := s.scalarLits.foldl (fun m (f, e, t) => m.insert (f, e) t) {}
           decided := s.decided }).run st

/-- Check a whole program. Gives what the elaborator needs to know about its
blocks: which take an argument they do not name, and for each that is handed a
block which was not run, the identity of that block if it can only be one. The
elaborator then lets those two share what they capture. -/
def checkProgram (items : List Syntax.Item) (modules : Syntax.ModuleInfo := {}) (drops : Bool := false) :
    Except String Elab.Blocks := do
  let action : M Elab.Blocks := do
    modify fun s => { s with modules }
    let _ ← checkItems items
    finish
  let (blocks, _) ← (action.runE { dropMode := drops }).mapError (·.msg)
  pure blocks

/-- What is known once some items are checked: for a program that is checked
after them, against what they declare. -/
def checkFirst (items : List Syntax.Item) (modules : Syntax.ModuleInfo := {}) (drops : Bool := false) :
    Except String St := do
  let action : M Unit := do
    modify fun s => { s with modules }
    let _ ← checkItems items
  let (_, st) ← (action.runE { dropMode := drops }).mapError (·.msg)
  pure st

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
def checkUnitsKept (first : St) (units : List (List Syntax.Item × UInt64)) (modules : Syntax.ModuleInfo)
    (seed : UInt64) (kept : Kept) (own : Bool := true) (library : Nat := 0)
    (deps : List (List Nat) := []) (groupsKept : Option Deltas := none) :
    Except Elab.Said (Elab.Blocks × Kept × Kept × Array (UInt64 × KeptGroup)) := do
  -- (Each unit's level: one more than the highest of the units it uses.)
  let levelOf := units.length.fold (init := (#[] : Array Nat)) fun i _ acc =>
    acc.push (((deps[i]?).getD []).foldl (fun m d => max m ((acc[d]?).getD 0 + 1)) 0)
  let levels := (List.range ((levelOf.foldl max 0) + 1)).map fun l =>
    (units.zipIdx.filter fun (_, k) => levelOf[k]? == some l)
  -- (Side by side only where each unit says what it uses.)
  let levels := if deps.length == units.length then levels else units.zipIdx.map ([·])
  -- (What each of the program's own units' groups added, kept where asked:
  -- the library's units are kept whole.)
  let deltasOf := fun (k : Nat) => if k ≥ library then groupsKept else none
  let action : M (Elab.Blocks × Kept × Kept × Array (UInt64 × KeptGroup)) := do
    modify fun s => { s with modules, ownItems := own }
    let mut groupsMade : Array (UInt64 × KeptGroup) := #[]
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
            (checkItems u (mixHash side info) kept (deltasOf k)).runE (jumpedFor start j))
        let mut together : Option St := none
        let mut mines : List (Nat × Kept) := []
        let mut deltasMine : Array (UInt64 × KeptGroup) := #[]
        let mut ok := true
        for (k, j, t) in tasks do
          match t.get with
          | .ok ((mine, ds), after) =>
            deltasMine := deltasMine ++ ds
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
            groupsMade := groupsMade ++ deltasMine
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
        let ((mine, ds), after) ← match Trace.timed s!"check unit {k}" fun _ =>
            (checkItems u (mixHash key info) kept (deltasOf k)).runE before with
          | .ok r => pure r
          | .error e => throwThe Elab.Said e
        set after
        groupsMade := groupsMade ++ ds
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
    pure (← finish, made, shared, groupsMade)
  let (r, _) ← action.runE first
  pure r

end Glorious.Check
