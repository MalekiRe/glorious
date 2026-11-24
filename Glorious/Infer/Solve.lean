module

public import Glorious.Infer.Schemes

public section

namespace Glorious.Infer

open Syntax
open Glorious.Typing (Ty FnSig Hint Cert SigEntry DataInst OpInst)

/-- What inferring a group sets aside of the group it is inferred inside,
and puts back when it is done. -/
structure Around where
  curScc : Option Nat
  cur : List (Nat × ISig)
  incls : Array Incl
  places : Array (ITy × Nat × ITy)
  coerces : Array (ITy × ITy × Bool)
  nevers : Array ITy
  onces : Array (ICls × List ITy)
  shows : Array (ITy × List ITy)
  opens : Array (ITy × ITy × List (Nat × Nat))
  calls : Array Call
  hints : Array IHint
  refs : Array (Nat × ISig)
  cancels : Array (ITy × IRow × Nat × Bool)
  pending : Array (ITy × IRow × Nat)

/-- The type of a length written as a type (`B1<B0<Z>>` is five), as
inference has a `[T; N]`'s: `lenBase + n` where the number is written out,
and otherwise what `other` makes of it (a type parameter's unknown). -/
partial def lengthTy (other : TypeExpr → M ITy) (t : TypeExpr) : M ITy := do
  let rec number : TypeExpr → Option Nat
    | .name "Z" [] => some 0
    | .name "B0" [n] => (number n).map (2 * ·)
    | .name "B1" [n] => (number n).map (2 * · + 1)
    | _ => none
  match number t with
  | some n => pure (.data (lenBase + n) [])
  | none => other t

/-- A type a function writes of a parameter, as a type inference starts
from: a declared type, a whole number, a tuple or a reference of such, each
of its type parameters one unknown (`vars`); anything else an unknown. -/
partial def writtenTy (vars : List (String × ITy)) : TypeExpr → M ITy
  | .name x args => do
    if let some t := vars.lookup x then return t
    if x == "Int" then return .int
    if Syntax.isScalar x then return .scalar (Syntax.scalarBits x)
    let s ← get
    if s.arrayType == some x then
      return .data arrayName (← args.mapM (writtenTy vars))
    -- (A `[T; N]`: of the element's type and the length's.)
    if x == "Fixed" then
      if let [t, n] := args then
        return .data fixedName [← writtenTy vars t, ← lengthTy (writtenTy vars) n]
    match s.typeNames.idxOf? x with
    | some id =>
      -- (Of a type with lifetimes, the regions are not said here.)
      if (s.typeLifetimes[id]?.getD []).any (· == true) then return ← freshTy
      if args.any (fun | .name l [] => l.startsWith "'" | _ => false) then return ← freshTy
      pure (.data id (← args.mapM (writtenTy vars)))
    | none => freshTy
  | .tuple args => do pure (.tuple (← args.mapM (writtenTy vars)))
  | .ref _ t _ => do pure (.ref (← freshRg) (← writtenTy vars t))
  | _ => freshTy

/-- What the function says of its parameters, where it says it: each
parameter's type starts as the one written. -/
def declaredParams (f : Nat) (params : List ITy) : M Unit := do
  let some (tparams, annots) := (← get).declared[f]? | return
  unless annots.length == params.length do return
  let vars ← tparams.mapM fun p => do pure (p, ← freshTy)
  for (p, annot) in params.zip annots do
    if let some te := annot then
      -- (A type that says nothing here, a callable's, is not taken.)
      if says te then
        let t ← writtenTy vars te
        -- (Each parameter's type is a variable made for it just now, and
        -- what is written is made of new ones: it is bound, and nothing
        -- can fail. Not `try unify`: that holds the state as it was, for
        -- going back to, and the binding then copies every type's.)
        if let .var i ← find p then
          unless ← occurs i t do bindTy i t
where
  says : TypeExpr → Bool
    | .name _ _ => true
    | .tuple _ => true
    | .ref _ _ _ => true
    | _ => false

/-- The type of a callable made of a function of this signature: a class
and an environment of its own, of what it captured. -/
def closureTy (sig : ISig) : M (ITy × Option ISig) := do
  let cls ← freshCls
  if (← get).strict then modify fun s => { s with onces := s.onces.push (cls, sig.caps) }
  let env ← freshTy
  modify fun s => { s with shows := s.shows.push (env, sig.caps) }
  pure (.func sig.params sig.ret sig.row cls env sig.acc, some sig)

mutual

/-- The key of group `scc`, for what is kept: what its functions are made of,
and what each group it refers to shows those that use it (`faceOf`), so that
a change to a function that leaves its scheme as it was keys none of the
groups that use it anew. Zero where nothing is keyed. -/
partial def groupKeyOf (scc : Nat) : M UInt64 := do
  let s ← get
  if !s.keyed then return 0
  if let some k := s.groupKeys[scc]? then return k
  let ms := s.members.getD scc [scc]
  let mut k := ms.foldl (fun h f => mixHash h ((s.ownKeys[f]?).getD 0)) s.keyBase
  for g in s.outside.getD scc [] do
    k := mixHash k (← faceOf g)
  modify fun s =>
    { s with
      groupKeys := s.groupKeys.insert scc k
      byKey := ms.zipIdx.foldl (fun m (f, i) => m.insert (mixHash k (hash (i, f))) f) s.byKey }
  return k

/-- The key of function `fn`: its group's, and which of the group it is. -/
partial def fnKey (fn : Nat) : M UInt64 := do
  let scc := ((← get).scc[fn]?).getD fn
  let k ← groupKeyOf scc
  if k == 0 then return 0
  let i := (((← get).members.getD scc [scc]).idxOf fn)
  return mixHash k (hash (i, fn))

/-- What group `scc` shows the groups that use it: what an earlier compile
found it to, for its key; or else of the scheme inferred now, where that can
be kept, and its key where not. -/
partial def faceOf (scc : Nat) : M UInt64 := do
  if let some f := (← get).faces[scc]? then return f
  let key ← fnKey scc
  let face ← match (← get).keptFaces[key]? with
    | some f => pure f
    | none => do
      discard <| schemeOf scc
      let made := (← get).frozenMade
      pure ((made.findRev? (·.1 == key)).map (·.2.face) |>.getD key)
  modify fun s => { s with faces := s.faces.insert scc face, facesMade := s.facesMade.push (key, face) }
  return face

/-- The general type of the group of `fn`, inferring the group if this is its first use. -/
partial def schemeOf (scc : Nat) : M Scheme := do
  if let some sch := (← get).schemes[scc]? then return sch
  -- (Kept from an earlier compile, where the group and all it reaches are
  -- the same: taken with new variables, and not inferred.)
  let key ← fnKey scc
  if key != 0 then
    if let some fz := (← get).frozen.get? key then
      let sch ← thaw fz
      modify fun s => { s with schemes := s.schemes.insert scc sch, frozenMade := s.frozenMade.push (key, fz) }
      return sch
  -- The groups it refers to, first: each then has its scheme before this one
  -- begins, and what this one makes is its own, not theirs inside it too.
  for g in (← get).outside.getD scc [] do
    discard (schemeOf g)
  -- (What is put back once the group is done is kept, and not the whole
  -- state: held, every array of it would be copied where the group first
  -- changes it, and again in each group inferred inside this one.)
  let (startTy, startRow, startCls, startRg, startAcc) ← do
    let s ← get
    pure (s.tys.size, s.rows.size, s.clss.size, s.rgs.size, s.accs.size)
  let (allFns, sccs, ncaps) ← do
    let s ← get
    pure (s.fns, s.scc, s.ncaps)
  let back : Around ← do
    let s ← get
    pure ⟨s.curScc, s.cur, s.incls, s.places, s.coerces, s.nevers, s.onces, s.shows,
      s.opens, s.calls, s.hints, s.refs, s.cancels, s.pending⟩
  -- (Of the declarations' variables, what they were: kept only where the
  -- scheme may be kept for a later compile.)
  let prefixes ← do
    let s ← get
    pure (if s.remember && key != 0 then
      some (s.tys.extract 0 s.globalTys, s.rows.extract 0 s.globalRows,
        s.clss.extract 0 s.globalClss, s.accs.extract 0 s.globalAccs, s.closureRanks)
    else none)
  -- (The group's functions, as certifyM found them once.)
  let st0 ← get
  let fns : List Nat := match Std.HashMap.get? st0.members scc with
    | some ms => ms
    | none => (List.range allFns.size).filter fun f => sccs[f]?.getD f == scc
  -- A signature for each function of the group, before any body is looked at.
  let mut cur : List (Nat × ISig) := []
  for f in fns do
    let arity := match allFns[f]? with
      | some ⟨c :: _⟩ => c.pats.length
      | _ => 0
    let sig : ISig :=
      ⟨← freshTys (ncaps[f]?.getD 0), ← freshTys arity, ← freshTy, ← freshRow, ← freshAcc⟩
    declaredParams f sig.params
    cur := cur ++ [(f, sig)]
  modify fun s =>
    { s with
      curScc := some scc, cur := cur, incls := #[], places := #[], coerces := #[], nevers := #[]
      onces := #[], shows := #[], opens := #[], calls := #[], cancels := #[], pending := #[] }
  let mut raw : List Member := []
  for (f, sig) in cur do
    let F := (allFns[f]?).getD ⟨[]⟩
    modify fun s => { s with refs := #[] }
    let mut hints : Array (Array IHint) := #[]
    for c in F.clauses do
      modify fun s => { s with hints := #[] }
      unless c.pats.length == sig.params.length do
        throw s!"the clauses of function {f} take different numbers of arguments"
      let binds ← inferPats c.pats sig.params
      try inferTm sig.acc sig.row sig.ret (sig.params ++ sig.caps ++ binds).toArray c.body
      catch e => throw (if (e.splitOn "(in function ").length > 1 then e else s!"{e} (in function {f})")
      hints := hints.push (← get).hints
    raw := raw ++ [⟨f, sig, hints, (← get).refs⟩]
  -- A callable given up, now that more is known of its type: one whose type
  -- is still not known is taken to be a resumption's, of one argument, but
  -- by a function that destroys callables of every type, or where it is
  -- something the function captured, whose type its maker knows.
  let anyCallable := (← get).anyCallable
  let armFns := (← get).armFns
  let general := cur.any fun (f, _) => anyCallable.contains f
  let mut captured : List (Nat × Option Nat) := []
  let arities := (← get).capArities
  for (f, sig) in cur do
    for (c, j) in sig.caps.zipIdx do
      if let .var v ← find c then captured := (v, arities[(f, j)]?) :: captured
  for (kt, amb, self, inherited) in (← get).cancels do
    match ← find kt with
    | .var v =>
      let leave := modify fun s => { s with pending := s.pending.push (kt, amb, self) }
      if inherited then leave else
      match captured.lookup v with
      -- (Captured: of as many arguments as every closure made says, else
      -- of whatever type its maker gives.)
      | some (some n) => givenUp (.var v) amb self n
      | some none => pure ()
      -- (Else a resumption's, of one argument, in a handler's arm; anywhere
      -- else, what each use gives: the group's users find it.)
      | none =>
        if !general && cur.any (fun (f, _) => armFns.contains f) then givenUp (.var v) amb self
        else leave
    | kt => if !inherited || (← bindsNone kt) then givenUp kt amb self
  modify fun s => { s with cancels := #[] }
  settle
  -- Write out what was learnt, and separate what is general from what is shared.
  let members ← raw.mapM fun m => do
    pure { m with
      sig := ← resolveSig m.sig
      hints := ← m.hints.mapM fun hs => hs.mapM resolveHint
      refs := ← m.refs.mapM fun (g, s) => do pure (g, ← resolveSig s) }
  let incls ← (← get).incls.mapM resolveIncl
  let places ← (← get).places.mapM fun (t, i, r) => do pure (← resolve t, i, ← resolve r)
  let coerces ← (← get).coerces.mapM fun (r, b, w) => do pure (← resolve r, ← resolve b, w)
  let nevers ← (← get).nevers.mapM resolve
  let onces ← (← get).onces.mapM fun (c, tys) => do pure (← findCls c, ← tys.mapM resolve)
  let shows ← (← get).shows.mapM fun (env, caps) => do pure (← resolve env, ← caps.mapM resolve)
  let opens ← (← get).opens.mapM fun (template, opened, chosen) => do
    pure (← resolve template, ← resolve opened, ← chosen.mapM fun (bound, actual) => do
      pure (← findRg bound, ← findRg actual))
  let calls ← (← get).calls.mapM fun c => do
    pure (⟨← resolve c.callee, ← c.given.mapM resolve, ← resolve c.result, ← resolveRow c.row,
      ← findAcc c.acc, ← c.actuals.mapM findRg, ← findAcc c.self⟩ : Call)
  let s ← get
  let mut fixed : Vars := {}
  for g in [0:s.globalTys] do
    fixed := varsOf (← resolve (.var g)) fixed
  for g in [0:s.globalRows] do
    fixed := varsOfRow (← resolveRow ⟨[], some g⟩) fixed
  for g in [0:s.globalClss] do
    if let .var c ← findCls (.var g) then fixed := { fixed with clss := fixed.clss.insert c }
  -- Regions, and what callables touch, that types shared by the program mention.
  let mut shared : Std.HashSet Nat × Std.HashSet Nat := ({}, {})
  for g in [0:s.globalTys] do
    shared ← sharedRegions (.var g) shared
  -- A variable can still be bound if a user can reach it, or if something that
  -- can still change decides it.
  let liveTy (live : Vars) (t : ITy) : Bool :=
    match t with
    | .var v => v < s.globalTys || live.tys.contains v
    | _ => false
  let liveRow (live : Vars) (r : IRow) : Bool :=
    match r.tail with
    | some v => v < s.globalRows || live.rows.contains v
    | none => false
  let liveCls (live : Vars) (c : ICls) : Bool :=
    match c with
    | .var v => v < s.globalClss || live.clss.contains v
    | .lit _ => false
  let mut live := members.foldl (fun acc m => varsOfSig m.sig acc) fixed
  -- A call still to be settled is settled by whoever uses the group.
  for c in calls do
    live := varsOfRow c.row ((c.callee :: c.result :: c.given).foldl (fun acc t => varsOf t acc) live)
  let mut size := 0
  while live.size != size do
    size := live.size
    for c in incls do
      if liveRow live c.sub then live := varsOfRow ⟨c.under, none⟩ (varsOfRow c.sup live)
    for (r, b, _) in coerces do
      if liveTy live r then live := varsOf b live
    for (t, _, r) in places do
      if liveTy live t then live := varsOf r live
    for (c, tys) in onces do
      if tys.any live.touches then
        if let .var v := c then live := { live with clss := live.clss.insert v }
    for (env, caps) in shows do
      if liveTy live env then live := caps.foldl (fun acc c => varsOf c acc) live
    for (template, opened, _) in opens do
      if liveTy live template then live := varsOf opened live
      if liveTy live opened then live := varsOf template live
  -- What a callable of the group touches is worked out once and written
  -- into its own record, in place of what it includes and calls, where
  -- nothing can be added to that any more. A use of the group then copies
  -- the record, and not, as it did, everything the function calls, and what
  -- those call, each time: the copies grew with every level of calls.
  --
  -- Something can still be added to a record that a type names which the
  -- group's users or its unsettled questions can reach: a parameter that is
  -- a callable touches what the one given for it does, which a use decides.
  -- So a record is settled only if it is not such a one and includes none.
  if (← get).regions then
    let mut open_ : Std.HashSet Nat := {}
    -- (The group's own records, kept for those who use it: worked out all
    -- the same where they reach nothing open, as a use copies them and
    -- adds to the copy, not to them.)
    let mut mine : Std.HashSet Nat := {}
    for m in members do
      for ty in m.sig.caps ++ m.sig.params ++ [m.sig.ret] do
        open_ ← namedAccs ty open_
      open_ ← namedAccsRow m.sig.row open_
      mine := mine.insert (← findAcc m.sig.acc)
    for c in incls do
      open_ ← namedAccsRow c.sub open_
      open_ ← namedAccsRow ⟨c.under, none⟩ open_
      open_ ← namedAccsRow c.sup open_
    for (ty, _, r) in places do
      open_ ← namedAccs ty open_
      open_ ← namedAccs r open_
    for (r, b, _) in coerces do
      open_ ← namedAccs r open_
      open_ ← namedAccs b open_
    for ty in nevers do
      open_ ← namedAccs ty open_
    for (_, tys) in onces do
      for ty in tys do
        open_ ← namedAccs ty open_
    for (env, caps) in shows do
      for ty in env :: caps do
        open_ ← namedAccs ty open_
    for (template, opened, _) in opens do
      open_ ← namedAccs template open_
      open_ ← namedAccs opened open_
    for c in calls do
      for ty in c.callee :: c.result :: c.given do
        open_ ← namedAccs ty open_
      open_ ← namedAccsRow c.row open_
      open_ := (open_.insert (← findAcc c.acc)).insert (← findAcc c.self)
    for (kt, _, self) in (← get).pending do
      open_ ← namedAccs kt open_
      open_ := open_.insert (← findAcc self)
    -- (And the same of the groups settled while this one was inferred,
    -- whose records are among this one's.)
    modify fun s => { s with kept := (open_.fold (fun k a => k.insert a) s.kept).insertMany mine }
    let kept := (← get).kept
    let last := (← get).accs.size
    -- A record is settled if nothing it reaches is open: older than the
    -- group, shared, or kept. Every record reachable from the group's is
    -- visited once, and openness goes back along the edges from the open
    -- ones. (Done for each record apart, as it was, a group went again over
    -- the records of every group inferred inside it.)
    let mut roots : Array Nat := #[]
    for a in [startAcc:last] do
      if (← findAcc a) == a && !(← accNode a).final then roots := roots.push a
    let mut seen : Std.HashSet Nat := roots.foldl (fun s a => s.insert a) {}
    let mut stack := roots
    let mut preds : Std.HashMap Nat (List Nat) := {}
    let mut opened : Array Nat := #[]
    while !stack.isEmpty do
      let n := stack.back!
      stack := stack.pop
      let x ← accNode n
      unless x.final do
        if n < startAcc || shared.2.contains n || (kept.contains n && !(mine.contains n && !open_.contains n)) then
          opened := opened.push n
        else
          for next in x.subs.map (·.1) ++ x.insts.map (·.1) do
            let m ← findAcc next
            preds := preds.insert m (n :: preds.getD m [])
            unless seen.contains m do
              seen := seen.insert m
              stack := stack.push m
    let mut isOpen : Std.HashSet Nat := opened.foldl (fun s a => s.insert a) {}
    while !opened.isEmpty do
      let n := opened.back!
      opened := opened.pop
      for p in preds.getD n [] do
        unless isOpen.contains p do
          isOpen := isOpen.insert p
          opened := opened.push p
    let mut settled : Array (Nat × List Nat × List Nat) := #[]
    for a in roots do
      unless isOpen.contains a do settled := settled.push (a, ← accSet a, ← accWrSet a)
    unless settled.isEmpty do
      modify fun s =>
        { s with
          accVer := s.accVer + 1
          accs := settled.foldl (fun accs (a, rs, ws) =>
            accs.modify a fun x => { x with rgns := rs, wrs := ws, subs := [], insts := [], final := true }) s.accs }
  let sch : Scheme :=
    { startTy, startRow, startCls, startRg, startAcc, fixedTys := fixed.tys
      fixedRows := fixed.rows, fixedClss := fixed.clss, fixedRgs := shared.1
      fixedAccs := shared.2, members, incls, places, coerces, nevers, onces, shows, opens, calls
      givenUpOpen := (← get).pending
      exported := incls.filter fun c => liveRow live c.sub
      exportedPlaces := places.filter fun (t, _, _) => liveTy live t
      exportedCoerces := coerces.filter fun (r, _, _) => liveTy live r
      exportedNevers := nevers.filter (liveTy live)
      exportedOnces := onces.filter fun (c, tys) => liveCls live c || tys.any live.touches
      exportedShows := shows.filter fun (env, _) => liveTy live env }
  modify fun s =>
    { s with
      schemes := s.schemes.insert scc sch
      curScc := back.curScc, cur := back.cur, incls := back.incls, places := back.places
      coerces := back.coerces, nevers := back.nevers, onces := back.onces, shows := back.shows
      opens := back.opens, calls := back.calls, hints := back.hints, refs := back.refs
      cancels := back.cancels, pending := back.pending }
  -- (Kept for a later compile where inferring it changed nothing of the
  -- declarations' and decided nothing left waiting by others: then the
  -- scheme, and what of its own it leaves waiting, is all it made.)
  let now ← get
  if let some (tys, rows, clss, accs, ranks) := prefixes then
    let waiting := ranks.size
    if samePrefix now.tys tys now.globalTys && samePrefix now.rows rows now.globalRows
        && samePrefix now.clss clss now.globalClss && samePrefix now.accs accs now.globalAccs
        && samePrefix now.closureRanks ranks waiting then
      if let some fz ← freeze sch (now.closureRanks.extract waiting now.closureRanks.size).toList then
        modify fun s => { s with frozenMade := s.frozenMade.push (key, fz) }
  pure sch

/-- The signature to use for a reference to `fn`: the group's own inside its
group, and otherwise a fresh copy of its general type, whose conditions the
referring function takes on. -/
partial def refSig (fn : Nat) : M ISig := do
  let s ← get
  let scc := s.scc[fn]?.getD fn
  if s.curScc == some scc then
    match s.cur.lookup fn with
    | some sig => pure sig
    | none => throw s!"certificate: function {fn} is missing from its group"
  else
    let sch ← schemeOf scc
    match sch.members.find? (·.fn == fn) with
    | none => throw s!"certificate: function {fn} is missing from its group"
    | some m =>
      startCopy
      let sig ← renSig (copyRen sch) m.sig
      let (incls, places, coerces, nevers, onces, shows, opens, calls) ← copyAsks sch sch.exported
        sch.exportedPlaces sch.exportedCoerces sch.exportedNevers sch.exportedOnces sch.exportedShows
      let open_ ← sch.givenUpOpen.mapM fun (kt, amb, self) => do
        pure (← renTy (copyRen sch) kt, ← renRow (copyRen sch) amb, ← copyAcc sch self, true)
      modify fun s => { s with opens := s.opens ++ opens, calls := s.calls ++ calls
                               cancels := s.cancels ++ open_ }
      modify fun s =>
        { s with
          incls := s.incls ++ incls, places := s.places ++ places
          coerces := s.coerces ++ coerces, nevers := s.nevers ++ nevers
          onces := s.onces ++ onces, shows := s.shows ++ shows, refs := s.refs.push (fn, sig) }
      pure sig

partial def inferRhs (Γ : Array ITy) : Rhs → M (ITy × Option ISig)
  | .atom a => do pure (← widenTy (← atomTy Γ a), none)
  | .prim p args => do
    -- An array is a value of the type kept for arrays, of its elements' type.
    let t ← freshTy
    let array := ITy.data arrayName [t]
    match p, args with
    | .arrGet, [a, i] =>
      unify (← atomTy Γ a) array
      unify (← atomTy Γ i) .int
      pure (t, none)
    | .arrSet, [a, i, v] =>
      unify (← atomTy Γ a) array
      unify (← atomTy Γ i) .int
      unify (← atomTy Γ v) t
      pure (array, none)
    | .arrLen, [a, _] =>
      unify (← atomTy Γ a) array
      pure (.int, none)
    | .arrPush, [a, v] =>
      unify (← atomTy Γ a) array
      unify (← atomTy Γ v) t
      pure (array, none)
    | .arrPop, [a, _] =>
      unify (← atomTy Γ a) array
      pure (.tuple [array, t], none)
    | .cast b into, [a] =>
      if into then do unify (← atomTy Γ a) .int; pure (.scalar b, none)
      else do unify (← atomTy Γ a) (.scalar b); pure (.int, none)
    -- (A `[T; N]`: of its elements' type and its length, a type of its own.)
    | .fixed 0, [a, .int n] =>
      unify (← atomTy Γ a) array
      pure (.data fixedName [t, .data (lenBase + n.toNat) []], none)
    | .fixed op, a :: rest => do
      let fixed := ITy.data fixedName [t, ← freshTy]
      unify (← atomTy Γ a) fixed
      match op, rest with
      | 1, [] => pure (array, none)
      | 2, [i] => do unify (← atomTy Γ i) .int; pure (t, none)
      | 3, [i, v] => do unify (← atomTy Γ i) .int; unify (← atomTy Γ v) t; pure (fixed, none)
      | _, _ => throw "an intrinsic of `[T; N]` is given what it does not take"
    | _, _ =>
      for a in args do
        unify (← atomTy Γ a) .int
      pure (.int, none)
  | .construct tag args => do
    let ts ← args.mapM (atomTy Γ)
    if tag == 0 then pure (.tuple ts, none)
    else if fixedBase ≤ tag then
      let t ← freshTy
      for s in ts do
        unify s t
      pure (.data fixedName [t, .data (lenBase + (tag - fixedBase)) []], none)
    else if arrayBase ≤ tag then
      let t ← freshTy
      for s in ts do
        unify s t
      pure (.data arrayName [t], none)
    else
      let (result, fields) ← instCtor tag
      -- (A number written out is a scalar's where the field is one: a
      -- constant worked out at compile time is written so.)
      let ts ← ((args.zip ts).zip (fields ++ ts.drop fields.length)).mapM fun ((a, t), f) => do
        match a with
        | .int _ => match ← find f with
          | .scalar b => pure (.scalar b)
          | _ => pure t
        | _ => pure t
      unifyList (← ts.mapM widenTy) fields
      pure (result, none)
  | .place pl => do
    let mut t ← atomTy Γ (.var pl.var)
    for i in pl.path do
      t ← field t i
    pure (t, none)
  | .closure fn captures => do
    let ts ← captures.mapM fun a => do widenTy (← atomTy Γ a)
    let sig ← refSig fn
    unifyList ts sig.caps
    -- A callable that takes a reference, to a region nothing it captured
    -- mentions, can take one to any cell: its type binds the region.
    if (← get).regions && (← get).ranked && (← get).curScc != some ((← get).scc[fn]?.getD fn) then
      if (← binderOf sig.acc).isNone then
        -- (What it is given may not be known yet: a parameter read a part at
        -- a time is a tuple only once something says so.)
        if ← sig.params.anyM fun p => do pure (match ← find p with | .var _ => true | _ => false) then
          modify fun s => { s with closureRanks := s.closureRanks.push (sig.params, sig.caps, sig.acc) }
        else rankClosure sig.params sig.caps sig.acc
    closureTy sig
  -- The elaborator gives another function only the environment of a block,
  -- and says how many arguments the block took: none, or the one it did not
  -- name.
  | .rebind a fn => do
    let sig ← refSig fn
    let arity := ((← get).givenUp.lookup fn).getD 0
    unify (← atomTy Γ a)
      (.func (← freshTys arity) (← freshTy) (← freshRow) (← freshCls) (.tuple sig.caps) (← freshAcc))
    closureTy sig

/-- Infer a handler's functions, which with the handled computation touch `Φ`.
Gives its operations, in the order of `ops`, and the signatures its functions
are used at. -/
partial def inferHandler (amb : IRow) (Φ : Nat) (Γ : Array ITy) (ret : Nat)
    (ops : List (Nat × Nat)) (captures : List Atom) (σ ρ : ITy) : M (IOps × List ISig) := do
  let Cs ← captures.mapM (atomTy Γ)
  let retSig ← refSig ret
  unifyList Cs retSig.caps
  unifyList [σ] retSig.params
  unify ρ retSig.ret
  needs retSig.row [] amb
  accSub Φ retSig.acc
  let mut H : IOps := []
  let mut sigs : List ISig := [retSig]
  let mut shared : List (Nat × List ITy) := []
  for (op, arm) in ops do
    let ((targs, payload, result), shared') ← instOp shared op
    shared := shared'
    H := H ++ [(op, targs)]
    let armSig ← refSig arm
    unifyList Cs armSig.caps
    let params := match result with
      | some o => payload ++ [.func [o] ρ amb (.lit true) .never Φ]
      | none => payload
    unifyList params armSig.params
    unify ρ armSig.ret
    needs armSig.row [] amb
    accSub Φ armSig.acc
    sigs := sigs ++ [armSig]
  pure (H, sigs)

/-- Infer a computation that must give a `τ`, may perform what `amb` serves,
and is part of a function that touches `self`. -/
partial def inferTm (self : Nat) (amb : IRow) (τ : ITy) (Γ : Array ITy) : Core.Tm → M Unit
  | .ret a => do unify (← widenTy (← atomTy Γ a)) τ
  | .let_ rhs body => do
    let (σ, sig) ← inferRhs Γ rhs
    hint (match sig with
      | some sig => .clo σ sig
      | none => .ty σ)
    inferTm self amb τ (Γ.push σ) body
  | .call f args body => do
    let r ← applied Γ amb f args
    let b ← freshTy
    coerce r b
    hint (.result r b)
    inferTm self amb τ (Γ.push b) body
  | .tail f args => do
    let r ← applied Γ amb f args
    coerce r τ
  | .handle ret ops captures thunk body => do
    let σ ← freshTy
    let ρ ← freshTy
    let εt ← freshRow
    let Φ ← handled Γ thunk σ εt
    let (H, sigs) ← inferHandler amb Φ Γ ret ops captures σ ρ
    needs εt H amb
    hint (.handler ρ H Φ sigs)
    inferTm self amb τ (Γ.push ρ) body
  | .handleTail ret ops captures thunk => do
    let σ ← freshTy
    let εt ← freshRow
    let Φ ← handled Γ thunk σ εt
    let (H, sigs) ← inferHandler amb Φ Γ ret ops captures σ τ
    needs εt H amb
    hint (.handler τ H Φ sigs)
  | .raise op args => do
    let ((targs, payload, result), _) ← instOp [] op
    unifyList (← args.mapM (atomTy Γ)) payload
    if result.isSome then throw s!"operation {op} is raised, but it can be resumed"
    requireOp amb op targs
  | .perform op args body => do
    let ((targs, payload, result), _) ← instOp [] op
    unifyList (← args.mapM (atomTy Γ)) payload
    match result with
    | some σ =>
      requireOp amb op targs
      inferTm self amb τ (Γ.push σ) body
    | none => throw s!"operation {op} is performed for a result, but it never returns"
  | .label thunk body => do
    let σ ← scope Γ amb thunk
    inferTm self amb τ (Γ.push σ) body
  | .labelTail thunk => do
    let σ ← scope Γ amb thunk
    unify σ τ
  | .guard cleanup thunk body => do
    let σ ← guarded Γ amb cleanup thunk
    inferTm self amb τ (Γ.push σ) body
  | .guardTail cleanup thunk => do
    let σ ← guarded Γ amb cleanup thunk
    unify σ τ
  | .cancel k body => do
    -- (One whose type is not known yet is settled when the body is read.)
    let kt ← atomTy Γ k
    match ← find kt with
    | .var _ => modify fun s => { s with cancels := s.cancels.push (kt, amb, self, false) }
    | kt => givenUp kt amb self
    inferTm self amb τ (Γ.push .unit) body
  | .cell init thunk body => do
    let ρ ← freshTy
    let εt ← freshRow
    celled Γ init thunk ρ εt
    needs εt [] amb
    inferTm self amb τ (Γ.push ρ) body
  | .cellTail init thunk => do
    let εt ← freshRow
    celled Γ init thunk τ εt
    needs εt [] amb
  | .lend uniq r thunk pre post body => do
    let ρt ← freshTy
    let εt ← freshRow
    lent Γ uniq r thunk pre post ρt εt
    needs εt [] amb
    inferTm self amb τ (Γ.push ρt) body
  -- (Cells of memory are the typed lowering's, after inference.)
  | .cellL .. | .cellTailL .. => throw "a cell of memory is not inferred"
  | .mem op args body => do
    let ts ← args.mapM (atomTy Γ)
    let ρ ← freshRg
    let int := fun (t : ITy) => unify t .int
    -- (An address is a `usize`.)
    let addr := fun (t : ITy) => unify t (.scalar (-64))
    let σ ← match op, ts with
      | .alloc, [s, a] => do addr s; addr a; pure (.scalar (-64))
      | .free, [a] => do addr a; pure .unit
      | .readBits, [a, w] => do addr a; int w; pure .int
      | .writeBits, [a, w, v] => do addr a; int w; int v; pure .unit
      | .copy, [a, b, n] => do addr a; addr b; addr n; pure .unit
      | .sizeOf, [_] | .alignOf, [_] | .staticAt, _ => pure (.scalar (-64))
      | .deref, [p, a, _] =>
        match args with
        | [_, _, .int tag] => do
          addr a
          -- (The pointer is of its type; what it points to, of its argument.)
          let (whole, _) ← instCtor tag.toNat
          unify p whole
          match ← find whole with
          | .data _ (t :: _) => pure (.ref ρ t)
          | _ => throw "a pointer of a type with no argument"
        | _ => throw "a pointer without its type's constructor"
      | .load, [t] => do
        accRgn self ρ
        let σ ← freshTy
        unify t (.ref ρ σ)
        pure σ
      | .store, [t, v] => do
        accWr self ρ
        unify t (.ref ρ (← widenTy v))
        pure .unit
      | .swap, [t, v] => do
        accWr self ρ
        let held ← widenTy v
        unify t (.ref ρ held)
        pure held
      | .tag, t :: _ => do
        accRgn self ρ
        unify t (.ref ρ (← freshTy))
        pure .int
      | .focus, [t, _] => do
        accRgn self ρ
        let σ ← freshTy
        unify t (.ref ρ σ)
        match args with
        | [_, .int i] => pure (.ref ρ (← field σ i.toNat))
        | [_, ix] =>
          -- A place found when the program runs: of an array.
          unify (← atomTy Γ ix) .int
          let elem ← freshTy
          unify σ (.data arrayName [elem])
          pure (.ref ρ elem)
        | _ => throw "a memory operation has the wrong number of arguments"
      | .focus, [t, _, _] => do
        -- A field of one of a type's several constructors.
        accRgn self ρ
        match args with
        -- (Into a `[T; N]`, at a place found when the program runs.)
        | [_, ix, .int (-1)] =>
          unify (← atomTy Γ ix) .int
          let elem ← freshTy
          unify t (.ref ρ (.data fixedName [elem, ← freshTy]))
          pure (.ref ρ elem)
        | [_, .int i, .int built] =>
          if built ≤ 0 || arrayBase ≤ built.toNat then
            throw "a reference into a constructor's field names no constructor"
          let (whole, fields) ← instCtor built.toNat
          unify t (.ref ρ whole)
          match fields[i.toNat]? with
          | some σ => pure (.ref ρ σ)
          | none => throw s!"constructor {built} has no field {i}"
        | _ => throw "a memory operation has the wrong number of arguments"
      | _, _ => throw "a memory operation has the wrong number of arguments"
    inferTm self amb τ (Γ.push σ) body
  | .host id args body => do
    let ts ← args.mapM (atomTy Γ)
    -- (Those past the first two are outside what Core's rules are about: a
    -- program with one has types, and no certificate the checker accepts.)
    let int := fun (t : ITy) => unify t .int
    let σ ← match id, ts with
      | 0, [_] => pure ITy.unit
      | 1, [] => pure (ITy.tuple [.int, .int])
      | 2, _ => do ts.forM int; pure .int
      | 5, [_, n] => do int n; pure (.scalar (-64))
      | 6, [_] => pure .int
      | 7, [c] => do int c; freshTy
      | 8, [c, _] => do int c; pure .unit
      | 9, [v] => pure (ITy.tuple [.data arrayName [.int], v])
      | 10, [] => pure (ITy.tuple [.int, .int])
      -- (`transmute`: the value, of another type.)
      | 14, [_] => freshTy
      | _, _ => throw s!"host operation {id} does not exist with {args.length} arguments"
    -- (What one outside Core's rules gives, for the typed lowering.)
    if 2 ≤ id then hint (.ty σ)
    inferTm self amb τ (Γ.push σ) body
where
  /-- A call: the callee's operations must be served where it is called, and
  the caller touches what the callee does. -/
  applied (Γ : Array ITy) (amb : IRow) (f : Atom) (args : List Atom) : M ITy := do
    let σ ← freshTy
    let ε' ← freshRow
    let a ← freshAcc
    let given ← args.mapM fun a => do widenTy (← atomTy Γ a)
    let callee ← find (← atomTy Γ f)
    if (← get).regions && (← get).ranked then
      -- Whether the callable's type binds a region may not be known yet:
      -- the call is settled when it is.
      let actuals := [← freshRg, ← freshRg, ← freshRg]
      hint (.rgns a actuals)
      needs ε' [] amb
      let call : Call := ⟨callee, given, σ, ε', a, actuals, self⟩
      unless ← tryCall call do modify fun s => { s with calls := s.calls.push call }
      return σ
    unify callee (.func given σ ε' (← freshCls) (← freshTy) a)
    needs ε' [] amb
    accSub self a
    pure σ
  /-- A handled computation: what it and its handler touch, which the code
  installing the handler touches too. -/
  handled (Γ : Array ITy) (thunk : Atom) (σ : ITy) (εt : IRow) : M Nat := do
    let a ← freshAcc
    unify (← atomTy Γ thunk) (.func [] σ εt (← freshCls) (← freshTy) a)
    let Φ ← freshAcc
    accSub Φ a
    accSub self Φ
    pure Φ
  scope (Γ : Array ITy) (amb : IRow) (thunk : Atom) : M ITy := do
    let σ ← freshTy
    let εt ← freshRow
    -- Applying the label does not return, unless something uses the label as
    -- a callable with a result.
    let ρ ← freshTy
    modify fun s => { s with nevers := s.nevers.push ρ }
    -- The scope has a region of its own, which the callable it runs binds and
    -- applying the label touches.
    let a ← freshAcc
    let applying ← freshAcc
    let own ← if (← get).regions then some <$> freshAtom else pure none
    if let some r := own then
      modify fun s => { s with accVer := s.accVer + 1, accs := s.accs.set! a { binder := some r } }
      accRgn applying r
    unify (← atomTy Γ thunk)
      (.func [.func [σ] ρ (← freshRow) (.lit false) .never applying] σ εt (← freshCls)
        (← freshTy) a)
    needs εt [] amb
    accSub self a own
    pure σ
  guarded (Γ : Array ITy) (amb : IRow) (cleanup thunk : Atom) : M ITy := do
    let σ ← freshTy
    let εt ← freshRow
    let ac ← freshAcc
    let a ← freshAcc
    -- A cleanup performs no operations.
    unify (← atomTy Γ cleanup) (.func [] (← freshTy) ⟨[], none⟩ (← freshCls) (← freshTy) ac)
    unify (← atomTy Γ thunk) (.func [] σ εt (← freshCls) (← freshTy) a)
    needs εt [] amb
    accSub self ac
    accSub self a
    pure σ
  /-- The scope of a cell: the callable it runs is given a reference to the
  cell, whose region is the callable's own. The code making the scope touches
  what the callable does, but for the cell. -/
  celled (Γ : Array ITy) (init thunk : Atom) (ρ : ITy) (εt : IRow) : M Unit := do
    let cell ← if (← get).regions then freshAtom else freshRg
    let a ← freshAcc
    if (← get).regions then
      modify fun s => { s with accVer := s.accVer + 1, accs := s.accs.set! a { binder := some cell } }
    unify (← atomTy Γ thunk)
      (.func [.ref cell (← atomTy Γ init)] ρ εt (← freshCls) (← freshTy) a)
    accSub self a (some cell)
  /-- The scope of a borrow. Under the rules for borrows the callable it runs
  is given a reference whose region is the callable's own, as for a cell; the
  code making the scope touches what the callable does but for the borrow, and
  what is lent. Otherwise the callable is given the reference lent. -/
  lent (Γ : Array ITy) (uniq : Bool) (r thunk : Atom) (pre post : List Atom) (ρt : ITy)
      (εt : IRow) : M Unit := do
    let σ ← freshTy
    let source ← freshRg
    unify (← atomTy Γ r) (.ref source σ)
    let before ← pre.mapM (atomTy Γ)
    let after ← post.mapM (atomTy Γ)
    let a ← freshAcc
    if (← get).regions && (← get).loans then
      -- The callable binds the borrow's region. It may be a function that is
      -- lent to more than once, itself among the lenders: then the region
      -- is no one borrow's.
      -- (A resumption's type binds none: it is no function.)
      let resumption ← match ← find (← atomTy Γ thunk) with
        | .fn _ _ _ _ _ env _ => do
          match ← find env with
          | .never => pure true
          | _ => pure false
        | _ => pure false
      let loan ← if (← get).ranked && !resumption then do
          let r ← freshRg
          markRank r
          pure r
        else freshAtom
      modify fun s => { s with accVer := s.accVer + 1, accs := s.accs.set! a { binder := some loan } }
      unify (← atomTy Γ thunk)
        (.func (before ++ .ref loan σ :: after) ρt εt (← freshCls) (← freshTy) a)
      accSub self a (some loan)
    else
      unify (← atomTy Γ thunk)
        (.func (before ++ .ref source σ :: after) ρt εt (← freshCls) (← freshTy) a)
      accSub self a
    if uniq then accWr self source else accRgn self source

end

/-- Settle, then decide what nothing decided, and settle again: a label's result
is `never`; a call whose callee is still unknown gives back what the code after
it expects; and a value whose fields are read, but whose type nothing else
determines, has the smallest tuple type with those fields. The last happens for
a callable that is never called. -/
partial def settleAll : M Unit := do
  settle
  let mut decided := false
  for ρ in (← get).nevers do
    if let .var v ← find ρ then
      bindTy v .never
      decided := true
  modify fun s => { s with nevers := #[] }
  if decided then return ← settleAll
  match (← get).coerces[0]? with
  | some (r, b, _) =>
    unify r b
    return ← settleAll
  | none => pure ()
  -- A callable still unknown is taken as it is.
  match (← get).calls[0]? with
  | some c =>
    modify fun s => { s with calls := s.calls.extract 1 s.calls.size }
    plainCall c
    return ← settleAll
  | none => pure ()
  -- What a callable gives, where nothing says: the same at every region.
  match (← get).opens[0]? with
  | some (template, opened, _) =>
    modify fun s => { s with opens := s.opens.extract 1 s.opens.size }
    unify template opened
    return ← settleAll
  | none => pure ()
  match (← get).places[0]? with
  | none => pure ()
  | some (t, _, _) =>
    match ← find t with
    | .var v =>
      let mut width := 0
      for (t', i, _) in (← get).places do
        if let .var v' ← find t' then
          if v' == v then width := max width (i + 1)
      bindTy v (.tuple (← freshTys width))
      settleAll
    | _ => settleAll

end Glorious.Infer
