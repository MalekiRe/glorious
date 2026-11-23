module

public import Glorious.Infer.Base

public section

namespace Glorious.Infer

open Syntax
open Glorious.Typing (Ty FnSig Hint Cert SigEntry DataInst OpInst)

/-! ## General types of groups -/

/-- A type with everything known about it written out. -/
partial def resolve (t : ITy) : M ITy := do
  match ← find t with
  | .var id => pure (.var id)
  | .param i => pure (.param i)
  | .int => pure .int
  | .tuple fs => do pure (.tuple (← fs.mapM resolve))
  | .data n args => do pure (.data n (← args.mapM resolve))
  | .fn ps r ops tail cls env acc => do
    let row ← flattenRow ⟨ops, tail⟩
    let ops ← row.ops.mapM fun (op, targs) => do pure (op, ← targs.mapM resolve)
    pure (.fn (← ps.mapM resolve) (← resolve r) ops row.tail (← findCls cls) (← resolve env)
      (← findAcc acc))
  | .ref ρ t => do pure (.ref (← findRg ρ) (← resolve t))
  | .never => pure .never

def resolveRow (r : IRow) : M IRow := do
  let r ← flattenRow r
  pure ⟨← r.ops.mapM fun (op, targs) => do pure (op, ← targs.mapM resolve), r.tail⟩

def resolveSig (s : ISig) : M ISig := do
  pure ⟨← s.caps.mapM resolve, ← s.params.mapM resolve, ← resolve s.ret, ← resolveRow s.row,
    ← findAcc s.acc⟩

def resolveIncl (c : Incl) : M Incl := do
  pure ⟨← resolveRow c.sub, ← c.under.mapM fun (op, targs) => do pure (op, ← targs.mapM resolve),
    ← resolveRow c.sup⟩

def resolveHint : IHint → M IHint
  | .ty t => do pure (.ty (← resolve t))
  | .clo t sig => do pure (.clo (← resolve t) (← resolveSig sig))
  | .handler ρ H Φ sigs => do
    pure (.handler (← resolve ρ) (← H.mapM fun (op, targs) => do pure (op, ← targs.mapM resolve))
      (← findAcc Φ) (← sigs.mapM resolveSig))
  | .result r b => do pure (.result (← resolve r) (← resolve b))
  | .rgns acc actuals => do pure (.rgns (← findAcc acc) (← actuals.mapM findRg))

/-- The variables of a resolved type: of types, of rows and of classes. -/
structure Vars where
  tys : Std.HashSet Nat := {}
  rows : Std.HashSet Nat := {}
  clss : Std.HashSet Nat := {}

def Vars.size (v : Vars) : Nat := v.tys.size + v.rows.size + v.clss.size

partial def varsOf (t : ITy) (acc : Vars) : Vars :=
  match t with
  | .var id => { acc with tys := acc.tys.insert id }
  | .param _ | .int => acc
  | .tuple fs | .data _ fs => fs.foldl (fun a f => varsOf f a) acc
  | .fn ps r ops tail cls env _ =>
    let acc := ps.foldl (fun a f => varsOf f a) acc
    let acc := varsOf r acc
    let acc := varsOf env acc
    let acc := ops.foldl (fun a e => e.2.foldl (fun a f => varsOf f a) a) acc
    let acc := match tail with
      | some v => { acc with rows := acc.rows.insert v }
      | none => acc
    match cls with
    | .var c => { acc with clss := acc.clss.insert c }
    | .lit _ => acc
  | .ref _ t => varsOf t acc
  | .never => acc

def varsOfRow (r : IRow) (acc : Vars) : Vars :=
  varsOf (.fn [] .int r.ops r.tail (.lit false) .never 0) acc

def varsOfSig (s : ISig) (acc : Vars) : Vars :=
  varsOf (.fn (s.caps ++ s.params) s.ret s.row.ops s.row.tail (.lit false) .never 0) acc

/-- Does a type mention a variable in the set? -/
def Vars.touches (live : Vars) (t : ITy) : Bool :=
  let v := varsOf t {}
  v.tys.toList.any live.tys.contains || v.rows.toList.any live.rows.contains
    || v.clss.toList.any live.clss.contains

/-! ## Renaming the variables of a scheme -/

/-- What to do with each kind of variable a scheme names. -/
structure Ren (m : Type → Type) where
  ty : Nat → m Nat
  row : Nat → m Nat
  cls : Nat → m Nat
  rg : Nat → m Nat
  acc : Nat → m Nat

section Ren
variable {m : Type → Type} [Monad m] (f : Ren m)

def renCls : ICls → m ICls
  | .var id => do pure (.var (← f.cls id))
  | c => pure c

mutual
partial def renTy : ITy → m ITy
  | .var id => do pure (.var (← f.ty id))
  | .tuple fs => do pure (.tuple (← fs.mapM renTy))
  | .data n args => do pure (.data n (← args.mapM renTy))
  | .fn ps r ops tail cls env acc => do
    pure (.fn (← ps.mapM renTy) (← renTy r) (← renOps ops) (← tail.mapM f.row) (← renCls f cls)
      (← renTy env) (← f.acc acc))
  | .ref ρ t => do pure (.ref (← f.rg ρ) (← renTy t))
  | t => pure t
partial def renOps (ops : IOps) : m IOps :=
  ops.mapM fun (op, targs) => do pure (op, ← targs.mapM renTy)
end

def renRow (r : IRow) : m IRow := do pure ⟨← renOps f r.ops, ← r.tail.mapM f.row⟩

def renSig (s : ISig) : m ISig := do
  pure ⟨← s.caps.mapM (renTy f), ← s.params.mapM (renTy f), ← renTy f s.ret, ← renRow f s.row, ← f.acc s.acc⟩

def renHint : IHint → m IHint
  | .ty t => do pure (.ty (← renTy f t))
  | .clo t sig => do pure (.clo (← renTy f t) (← renSig f sig))
  | .handler ρ H Φ sigs => do pure (.handler (← renTy f ρ) (← renOps f H) (← f.acc Φ) (← sigs.mapM (renSig f)))
  | .result r b => do pure (.result (← renTy f r) (← renTy f b))
  | .rgns acc actuals => do pure (.rgns (← f.acc acc) (← actuals.mapM f.rg))

def renIncl (c : Incl) : m Incl := do pure ⟨← renRow f c.sub, ← renOps f c.under, ← renRow f c.sup⟩

def renPlace (p : ITy × Nat × ITy) : m (ITy × Nat × ITy) := do pure (← renTy f p.1, p.2.1, ← renTy f p.2.2)

def renCoerce (p : ITy × ITy × Bool) : m (ITy × ITy × Bool) := do pure (← renTy f p.1, ← renTy f p.2.1, p.2.2)

def renOnce (o : ICls × List ITy) : m (ICls × List ITy) := do pure (← renCls f o.1, ← o.2.mapM (renTy f))

def renShow (o : ITy × List ITy) : m (ITy × List ITy) := do pure (← renTy f o.1, ← o.2.mapM (renTy f))

def renCall (c : Call) : m Call := do
  pure ⟨← renTy f c.callee, ← c.given.mapM (renTy f), ← renTy f c.result, ← renRow f c.row,
    ← f.acc c.acc, ← c.actuals.mapM f.rg, ← f.acc c.self⟩

def renNode (x : IAcc) : m IAcc := do
  pure { x with
    link := none
    rgns := ← x.rgns.mapM f.rg, wrs := ← x.wrs.mapM f.rg
    subs := ← x.subs.mapM fun (b, e) => do pure (← f.acc b, ← e.mapM f.rg)
    binder := ← x.binder.mapM f.rg, more := ← x.more.mapM f.rg
    insts := ← x.insts.mapM fun (sub, chosen) => do
      pure (← f.acc sub, ← chosen.mapM fun (a, b) => do pure (← f.rg a, ← f.rg b)) }

/-- A scheme with its variables renamed (and its own variables from `start`). -/
def renScheme (sch : Scheme) (start : Nat × Nat × Nat × Nat × Nat) : m Scheme := do
  let set := fun (g : Nat → m Nat) (xs : Std.HashSet Nat) => do
    pure ((← xs.toList.mapM g).foldl (fun s x => s.insert x) ({} : Std.HashSet Nat))
  pure { sch with
    startTy := start.1, startRow := start.2.1, startCls := start.2.2.1, startRg := start.2.2.2.1
    startAcc := start.2.2.2.2
    fixedTys := ← set f.ty sch.fixedTys, fixedRows := ← set f.row sch.fixedRows
    fixedClss := ← set f.cls sch.fixedClss, fixedRgs := ← set f.rg sch.fixedRgs
    fixedAccs := ← set f.acc sch.fixedAccs
    members := ← sch.members.mapM fun mb => do
      pure { mb with
        sig := ← renSig f mb.sig
        hints := ← mb.hints.mapM fun hs => hs.mapM (renHint f)
        refs := ← mb.refs.mapM fun (g, s) => do pure (g, ← renSig f s) }
    incls := ← sch.incls.mapM (renIncl f), places := ← sch.places.mapM (renPlace f)
    coerces := ← sch.coerces.mapM (renCoerce f), nevers := ← sch.nevers.mapM (renTy f)
    onces := ← sch.onces.mapM (renOnce f), shows := ← sch.shows.mapM (renShow f)
    opens := ← sch.opens.mapM fun (a, b, ch) => do
      pure (← renTy f a, ← renTy f b, ← ch.mapM fun (x, y) => do pure (← f.rg x, ← f.rg y))
    calls := ← sch.calls.mapM (renCall f)
    givenUpOpen := ← sch.givenUpOpen.mapM fun (t, r, a) => do pure (← renTy f t, ← renRow f r, ← f.acc a)
    exported := ← sch.exported.mapM (renIncl f)
    exportedPlaces := ← sch.exportedPlaces.mapM (renPlace f)
    exportedCoerces := ← sch.exportedCoerces.mapM (renCoerce f)
    exportedNevers := ← sch.exportedNevers.mapM (renTy f)
    exportedOnces := ← sch.exportedOnces.mapM (renOnce f)
    exportedShows := ← sch.exportedShows.mapM (renShow f) }

end Ren

/-- A copy of a region of a scheme: itself if it is a cell or shared with the
rest of the program, and otherwise a new unknown. -/
partial def copyRg (sch : Scheme) (ρ : Nat) : M Nat := do
  let r ← findRg ρ
  if (← isAtom r) || r < sch.startRg || sch.fixedRgs.contains r then pure r
  else
    match (← get).renRg[r]? with
    | some r' => pure r'
    | none =>
      let r' ← freshRg
      modify fun s => { s with renRg := s.renRg.insert r r' }
      if ← isRank r then markRank r'
      if let some ls := (← get).lows[r]? then
        let ls' ← ls.mapM (copyRg sch)
        modify fun s => { s with lows := s.lows.insert r' ls' }
      pure r'

/-- A copy of what a callable of a scheme touches, with everything it includes. -/
partial def copyAcc (sch : Scheme) (a : Nat) : M Nat := do
  let a ← findAcc a
  if a < sch.startAcc || sch.fixedAccs.contains a then pure a
  else
    match (← get).renAcc[a]? with
    | some a' => pure a'
    | none =>
      let a' ← freshAcc
      modify fun s => { s with renAcc := s.renAcc.insert a a' }
      let x ← accNode a
      let rgns ← x.rgns.mapM (copyRg sch)
      let wrs ← x.wrs.mapM (copyRg sch)
      let subs ← x.subs.mapM fun (b, e) => do
        pure (← copyAcc sch b, ← match e with
          | some q => some <$> copyRg sch q
          | none => pure none)
      let binder ← match x.binder with
        | some q => some <$> copyRg sch q
        | none => pure none
      let more ← x.more.mapM (copyRg sch)
      let insts ← x.insts.mapM fun (sub, chosen) => do
        pure (← copyAcc sch sub, ← chosen.mapM fun (bound, actual) => do
          pure (← copyRg sch bound, ← copyRg sch actual))
      modify fun s => { s with accVer := s.accVer + 1, accs := s.accs.set! a' { rgns, wrs, subs, binder, more, insts } }
      pure a'

/-- A copy of a variable of a scheme: itself if it is older than the
scheme or shared with the rest of the program, and otherwise a new one, the
same for each time it is met in one copy. -/
def copyVar (start : Nat) (fixed : Std.HashSet Nat) (renamed : St → Std.HashMap Nat Nat)
    (record : St → Nat → Nat → St) (fresh : M Nat) (id : Nat) : M Nat := do
  if id < start || fixed.contains id then return id
  match (renamed (← get))[id]? with
  | some id' => pure id'
  | none =>
    let id' ← fresh
    modify fun s => record s id id'
    pure id'

/-- How a scheme is copied for a use of it: its general variables renamed. -/
def copyRen (sch : Scheme) : Ren M :=
  { ty := copyVar sch.startTy sch.fixedTys (·.renTy) (fun s a b => { s with renTy := s.renTy.insert a b })
      (do match ← freshTy with | .var v => pure v | _ => pure 0)
    row := copyVar sch.startRow sch.fixedRows (·.renRow) (fun s a b => { s with renRow := s.renRow.insert a b })
      (do pure ((← freshRow).tail.getD 0))
    cls := copyVar sch.startCls sch.fixedClss (·.renCls) (fun s a b => { s with renCls := s.renCls.insert a b })
      (do match ← freshCls with | .var v => pure v | _ => pure 0)
    rg := copyRg sch
    acc := copyAcc sch }

/-- What a group asks besides its functions' types, named for a use
(`copyRen`): the inclusions, places, coercions, nevers, onces and shows
given (the whole group's, or what it exports), and its openings and calls. -/
def copyAsks (sch : Scheme) (incls : Array Incl) (places : Array (ITy × Nat × ITy))
    (coerces : Array (ITy × ITy × Bool)) (nevers : Array ITy) (onces : Array (ICls × List ITy))
    (shows : Array (ITy × List ITy)) :
    M (Array Incl × Array (ITy × Nat × ITy) × Array (ITy × ITy × Bool) × Array ITy × Array (ICls × List ITy)
      × Array (ITy × List ITy) × Array (ITy × ITy × List (Nat × Nat)) × Array Call) := do
  let r := copyRen sch
  pure (← incls.mapM (renIncl r), ← places.mapM (renPlace r),
    ← coerces.mapM (fun (a, b, w) => do pure (← renTy r a, ← renTy r b, w)), ← nevers.mapM (renTy r),
    ← onces.mapM (renOnce r), ← shows.mapM (renShow r),
    ← sch.opens.mapM (fun (template, opened, chosen) => do
      pure (← renTy r template, ← renTy r opened, ← chosen.mapM fun (bound, actual) => do
        pure (← copyRg sch bound, ← copyRg sch actual))),
    ← sch.calls.mapM (renCall r))

def startCopy : M Unit :=
  modify fun s => { s with renTy := {}, renRow := {}, renCls := {}, renRg := {}, renAcc := {} }



/-- Do two arrays agree on their first `n` places? -/
def samePrefix {α : Type} [BEq α] (a b : Array α) (n : Nat) : Bool :=
  (List.range n).all fun i => a[i]? == b[i]?

/-- Where the variables of a scheme kept between compiles are numbered from:
far above any a compile makes. -/
def frozenBase : Nat := 1 <<< 40

/-- What freezing has numbered so far, by kind. -/
structure FreezeSt where
  ty : Std.HashMap Nat Nat := {}
  row : Std.HashMap Nat Nat := {}
  cls : Std.HashMap Nat Nat := {}
  rg : Std.HashMap Nat Nat := {}
  acc : Std.HashMap Nat Nat := {}
  nodes : Array (Nat × IAcc) := #[]
  /-- A variable neither the group's own nor the declarations' was named. -/
  foreign : Bool := false

/-- The number a variable of a scheme has as kept: as it is if it is one
of the declarations', and otherwise from `frozenBase` in the order met. One
that is older than the group and not the declarations' is foreign. -/
def freezeId (globals start id : Nat) (get : FreezeSt → Std.HashMap Nat Nat)
    (put : FreezeSt → Std.HashMap Nat Nat → FreezeSt) : StateT FreezeSt M Nat := do
  if id < globals then return id
  if id < start then
    modify fun z => { z with foreign := true }
    return id
  let z ← StateT.get
  match (get z)[id]? with
  | some k => pure k
  | none =>
    let k := frozenBase + (get z).size
    StateT.set (put z ((get z).insert id k))
    pure k

def freezeRg (sch : Scheme) (id : Nat) : StateT FreezeSt M Nat := do
  let r ← findRg id
  -- (No region is the declarations': one is the group's or foreign.)
  freezeId 0 sch.startRg r (·.rg) fun z m => { z with rg := m }

/-- A record of what a callable touches, as kept, with what it reaches. -/
partial def freezeAcc (sch : Scheme) (id : Nat) : StateT FreezeSt M Nat := do
  let a ← findAcc id
  if a < (← getThe St).globalAccs then return a
  if a < sch.startAcc then
    modify fun z => { z with foreign := true }
    return a
  if let some k := (← StateT.get).acc[a]? then return k
  let k := frozenBase + (← StateT.get).acc.size
  modify fun z => { z with acc := z.acc.insert a k }
  let x ← accNode a
  let node : IAcc := { x with
    link := none
    rgns := ← x.rgns.mapM (freezeRg sch), wrs := ← x.wrs.mapM (freezeRg sch)
    subs := ← x.subs.mapM fun (b, e) => do pure (← freezeAcc sch b, ← e.mapM (freezeRg sch))
    binder := ← x.binder.mapM (freezeRg sch), more := ← x.more.mapM (freezeRg sch)
    insts := ← x.insts.mapM fun (sub, chosen) => do
      pure (← freezeAcc sch sub, ← chosen.mapM fun (p, q) => do pure (← freezeRg sch p, ← freezeRg sch q)) }
  modify fun z => { z with nodes := z.nodes.push (k, node) }
  pure k

/-- A group's scheme as kept for a later compile, if it names no variable
but its own and the declarations'. -/
def freeze (sch : Scheme) (waiting : List (List ITy × List ITy × Nat)) : M (Option Frozen) := do
  let s0 ← get
  let ren : Ren (StateT FreezeSt M) :=
    { ty := fun id => freezeId s0.globalTys sch.startTy id (·.ty) fun z m => { z with ty := m }
      row := fun id => freezeId s0.globalRows sch.startRow id (·.row) fun z m => { z with row := m }
      cls := fun id => freezeId s0.globalClss sch.startCls id (·.cls) fun z m => { z with cls := m }
      rg := freezeRg sch
      acc := freezeAcc sch }
  let ((frozen, waiting), z) ← (do
      let sch ← renScheme ren sch (frozenBase, frozenBase, frozenBase, frozenBase, frozenBase)
      let waiting ← waiting.mapM fun ((ps, cs, a) : List ITy × List ITy × Nat) => do
        pure (← ps.mapM (renTy ren), ← cs.mapM (renTy ren), ← ren.acc a)
      pure (sch, waiting)).run {}
  if z.foreign then return none
  let s ← get
  let mut atoms : List Nat := []
  let mut ranks : List Nat := []
  let mut lows : List (Nat × List Nat) := []
  for (r, k) in z.rg.toList do
    if ← isAtom r then atoms := k :: atoms
    if s.rankBinders.contains r then ranks := k :: ranks
    if let some ls := s.lows[r]? then
      let ls' ← ls.mapM fun l => do
        let l ← findRg l
        pure ((z.rg[l]?).getD l)
      lows := (k, ls') :: lows
  let kept := z.acc.toList.filterMap fun (a, k) => if s.kept.contains a then some k else none
  pure (some ⟨frozen, (z.ty.size, z.row.size, z.cls.size, z.rg.size, z.acc.size), atoms, ranks,
    z.nodes.toList, lows, kept, waiting⟩)

/-- A kept scheme taken into this compile: each of its own variables a new one. -/
def thaw (fz : Frozen) : M Scheme := do
  let s ← get
  let start := (s.tys.size, s.rows.size, s.clss.size, s.rgs.size, s.accs.size)
  let (nTy, nRow, nCls, nRg, nAcc) := fz.counts
  for _ in [0:nTy] do discard freshTy
  for _ in [0:nRow] do discard freshRow
  for _ in [0:nCls] do discard freshCls
  for k in [0:nRg] do
    if fz.atoms.contains (frozenBase + k) then discard freshAtom else discard freshRg
  for _ in [0:nAcc] do discard freshAcc
  let shift := fun (base : Nat) (id : Nat) => if id ≥ frozenBase then base + (id - frozenBase) else id
  let ren : Ren Id :=
    { ty := shift start.1, row := shift start.2.1, cls := shift start.2.2.1
      rg := shift start.2.2.2.1, acc := shift start.2.2.2.2 }
  for (k, node) in fz.nodes do
    let node := Id.run (renNode ren node)
    modify fun s => { s with accVer := s.accVer + 1, accs := s.accs.set! (ren.acc k) node }
  for k in fz.ranks do markRank (ren.rg k)
  for (k, ls) in fz.lows do
    modify fun s => { s with lows := s.lows.insert (ren.rg k) (ls.map ren.rg) }
  modify fun s =>
    { s with
      kept := fz.kept.foldl (fun kp a => kp.insert (ren.acc a)) s.kept
      closureRanks := fz.waiting.foldl (fun w (ps, cs, a) =>
        w.push (ps.map fun t => Id.run (renTy ren t), cs.map fun t => Id.run (renTy ren t), ren.acc a)) s.closureRanks }
  pure (Id.run (renScheme ren fz.scheme start))

/-- Is this type known to hold something that cannot be duplicated? -/
partial def nonDup (seen : List Nat) (t : ITy) : M Bool := do
  match ← find t with
  | .var _ | .param _ | .int => pure false
  | .tuple fs => fs.anyM (nonDup seen)
  | .data name args =>
    if name == arrayName then args.anyM (nonDup seen)
    else if seen.contains name then pure false
    else
      let tags := (← get).types[name]?.getD []
      tags.anyM fun tag => do
        let d ← ctorDecl tag
        d.fields.anyM fun f => nonDup (name :: seen) (subst args f)
  | .fn _ _ _ _ cls _ _ => do
    match ← findCls cls with
    | .lit once => pure once
    | .var _ => pure false
  | .ref _ _ | .never => pure false

/-- Does a type have a reference to this region in it, or a callable that
takes or gives one? -/
partial def mentionsRg (region : Nat) (t : ITy) (depth : Nat := 24) : M Bool := do
  -- (a type can hold itself, through what a callable captured: far enough
  -- down, it is taken to mention the region)
  if depth == 0 then return true
  match ← find t with
  | .ref r u => do
    if (← findRg r) == region || (← leavesOf r).contains region then pure true
    else mentionsRg region u (depth - 1)
  | .tuple fs => fs.anyM (mentionsRg region · (depth - 1))
  | .data _ args => args.anyM (mentionsRg region · (depth - 1))
  | .fn ps r _ _ _ env _ => do
    if ← ps.anyM (mentionsRg region · (depth - 1)) then pure true
    else if ← mentionsRg region r (depth - 1) then pure true
    else mentionsRg region env (depth - 1)
  | _ => pure false

/-- A type with one region for another wherever a reference is of it: what a
callable whose type binds `from_` gives at a call that chooses `to`, or the
other way round. A type not yet known is taken to have no reference in it. -/
partial def reregionAll (pairs : List (Nat × Nat)) (t : ITy) (depth : Nat := 24) : M ITy := do
  if depth == 0 then return t
  match ← find t with
  | .ref r u => do
    let r' ← findRg r
    let mut to := r
    for (from_, other) in pairs do
      if r' == (← findRg from_) then to := other
    pure (.ref to (← reregionAll pairs u (depth - 1)))
  | .tuple fs => do pure (.tuple (← fs.mapM (reregionAll pairs · (depth - 1))))
  | .data n args => do pure (.data n (← args.mapM (reregionAll pairs · (depth - 1))))
  | t => pure t

def reregion (from_ to : Nat) (t : ITy) : M ITy := reregionAll [(from_, to)] t

/-- A call of a callable taken as it is: given what it is given, giving what
it gives. -/
def plainCall (c : Call) : M Unit := do
  unify c.callee (.func c.given c.result c.row (← freshCls) (← freshTy) c.acc)
  accSub c.self c.acc

/-- The regions of the references in some types, through tuples, in order. -/
partial def refRegions (ts : List ITy) : M (List Nat) := do
  let mut out := []
  for t in ts do
    match ← find t with
    | .ref ρ _ => out := out ++ [ρ]
    | .tuple fs => out := out ++ (← refRegions fs)
    | _ => pure ()
  pure out

/-- A ranked region that what `acc` touches binds. -/
def bindRank (acc region : Nat) : M Unit := do
  markRank region
  let a ← findAcc acc
  modify fun s => { s with accVer := s.accVer + 1, accs := s.accs.modify a fun x => { x with binder := some region } }

/-- A callable that takes a reference, to a region nothing it captured
mentions (directly or in a tuple), can take one to any cell: its type binds
the region. -/
def rankClosure (params caps : List ITy) (acc : Nat) : M Unit := do
  if (← binderOf acc).isSome then return
  let mut chosen : Option Nat := none
  for ρ in ← refRegions params do
    let root ← findRg ρ
    if chosen.isNone && !(← isAtom root) && !(← caps.anyM (mentionsRg root)) then
      chosen := some root
  if let some region := chosen then bindRank acc region

/-- Settle a call if enough is known. A callable whose type binds a region
is called at the region this call chooses: what it takes and gives are its
type's with that region. A callable nothing is known of, given a reference,
is taken to be one whose type binds the reference's region, so that it can
be given a reference to any cell: as one a function is passed has to be,
when the cell is the function's own. -/
partial def tryCall (c : Call) : M Bool := do
  let callee ← find c.callee
  match callee with
  | .fn ps r ops tail _ _ acc =>
    match ← bindersOf acc with
    | bound :: others =>
      if ps.length != c.given.length then
        plainCall c
        return true
      let chosen := (bound :: others).zip c.actuals
      for (p, g) in ps.zip c.given do
        unify g (← reregionAll chosen p)
      unifyRow c.row ⟨ops, tail⟩
      unifyAcc c.acc acc
      modify fun s => { s with opens := s.opens.push (r, c.result, chosen) }
      accInst c.self c.acc chosen
      pure true
    | [] =>
      -- A callable whose own parameter is not known yet, given a reference
      -- there: a function that calls itself with a reference to a variable
      -- of its own. Its type binds the region.
      let mut chosen : Option (ITy × ITy × Nat) := none
      -- Whether it is a reference may itself not be known yet.
      let mut unknown := false
      if ps.length == c.given.length then
        for (p, g) in ps.zip c.given do
          match ← find p, ← find g with
          | .var _, .ref ρ _ => if chosen.isNone then chosen := some (p, g, ρ)
          | .var _, .var _ => unknown := true
          -- (what it is given there may yet be a reference to a cell)
          | .ref _ _, .var _ => unknown := true
          | _, _ => pure ()
      match chosen with
      | some (p, g, region) =>
        let bound ← freshRg
        markRank bound
        let a ← findAcc acc
        modify fun s => { s with accVer := s.accVer + 1, accs := s.accs.modify a fun x => { x with binder := some bound } }
        unify p (← reregion region bound g)
        tryCall c
      | none =>
        if unknown then pure false
        else
          -- Or its parameter is known to be a reference, to no cell yet,
          -- and it is given one to a cell: its type binds that region.
          let mut own : Option Nat := none
          if ps.length == c.given.length then
            for (p, g) in ps.zip c.given do
              if let (.ref ρp _, .ref ρ _) := (← find p, ← find g) then
                let rp ← findRg ρp
                if own.isNone && !(← isAtom rp) && (← isAtom (← findRg ρ)) then own := some rp
          match own with
          | some region =>
            bindRank acc region
            tryCall c
          | none =>
            plainCall c
            pure true
  | .var _ =>
    let given ← c.given.mapM find
    -- Not before all it is given is known: another of them may be a
    -- reference too.
    if given.any (fun
        | .var _ => true
        | _ => false) then return false
    -- The regions of the references it is given, each once.
    let mut found : List Nat := []
    for g in given do
      if let .ref ρ _ := g then
        let root ← findRg ρ
        if !found.contains root && found.length < c.actuals.length then found := found ++ [root]
    match found with
    | _ :: _ =>
      -- The regions the type binds are no cells': each stands for whichever
      -- cell a call chooses.
      let bounds ← found.mapM fun _ => freshRg
      for b in bounds do
        markRank b
      let a ← findAcc c.acc
      modify fun s =>
        { s with accVer := s.accVer + 1, accs := s.accs.modify a fun x =>
            { x with binder := bounds.head?, more := bounds.drop 1 } }
      for (actual, region) in c.actuals.zip found do
        unifyRg actual region
      let params ← c.given.mapM (reregionAll (found.zip bounds))
      let template ← freshTy
      unify callee (.func params template c.row (← freshCls) (← freshTy) c.acc)
      let chosen := bounds.zip c.actuals
      modify fun s => { s with opens := s.opens.push (template, c.result, chosen) }
      accInst c.self c.acc chosen
      pure true
    | [] =>
      -- Nothing it is given is a reference, if all it is given is known.
      let known := given.all fun
        | .var _ => false
        | _ => true
      if known then
        plainCall c
        pure true
      else pure false
  | _ =>
    plainCall c
    pure true

/-- Enforce the inclusions and the field reads until nothing more is learnt. -/
partial def settle : M Unit := do
  let before := (← get).gen
  let waitingRanks := (← get).closureRanks
  modify fun s => { s with closureRanks := #[] }
  for (params, caps, acc) in waitingRanks do
    if ← params.anyM fun p => do pure (match ← find p with | .var _ => true | _ => false) then
      modify fun s => { s with closureRanks := s.closureRanks.push (params, caps, acc) }
    else rankClosure params caps acc
  let waitingCalls := (← get).calls
  modify fun s => { s with calls := #[] }
  for c in waitingCalls do
    unless ← tryCall c do modify fun s => { s with calls := s.calls.push c }
  let waitingOpen := (← get).opens
  modify fun s => { s with opens := #[] }
  for (template, opened, chosen) in waitingOpen do
    match ← find template, ← find opened with
    | .var _, .var _ => modify fun s => { s with opens := s.opens.push (template, opened, chosen) }
    | .var _, _ => unify template (← reregionAll (chosen.map fun (b, a) => (a, b)) opened)
    | _, _ => unify opened (← reregionAll chosen template)
  for c in (← get).incls do
    let sub ← flattenRow c.sub
    for (op, targs) in sub.ops do
      match c.under.lookup op with
      | some targs' => unifyList targs targs'
      | none => requireOp c.sup op targs
  let waiting := (← get).places
  modify fun s => { s with places := #[] }
  -- (One field of one subject is one type: a read waiting as another did
  -- is that one, and waits no longer apart. A group copies what those it
  -- uses leave waiting, so without this they grew with every level.)
  let mut seen : Std.HashMap (Nat × Nat) ITy := {}
  for (t, i, r) in waiting do
    match ← fieldNow t i with
    | some f => unify f r
    | none =>
      match ← find t with
      | .var v =>
        match seen[(v, i)]? with
        | some r' => unify r r'
        | none =>
          seen := seen.insert (v, i) r
          modify fun s => { s with places := s.places.push (t, i, r) }
      | _ => modify fun s => { s with places := s.places.push (t, i, r) }
  let pending := (← get).coerces
  modify fun s => { s with coerces := #[] }
  for (r, b, w) in pending do
    coerce r b w
  let waitingOnce := (← get).onces
  modify fun s => { s with onces := #[] }
  for (c, tys) in waitingOnce do
    if ← tys.anyM (nonDup []) then unifyCls c (.lit true)
    else modify fun s => { s with onces := s.onces.push (c, tys) }
  let waitingShow := (← get).shows
  modify fun s => { s with shows := #[] }
  for (env, caps) in waitingShow do
    match ← find env with
    | .var _ => modify fun s => { s with shows := s.shows.push (env, caps) }
    | .tuple stated => unifyList stated caps
    | _ => pure ()
  if (← get).gen != before then settle

/-- The callables' records of what they touch that a type names: those of the
callable types in it. (Not what those include in turn.) -/
partial def namedAccs (t : ITy) (out : Std.HashSet Nat) : M (Std.HashSet Nat) := do
  match ← find t with
  | .var _ | .param _ | .int => pure out
  | .tuple fs | .data _ fs => fs.foldlM (fun o f => namedAccs f o) out
  | .fn ps r ops tail _ env a => do
    let mut out ← ps.foldlM (fun o f => namedAccs f o) out
    out ← namedAccs r out
    out ← namedAccs env out
    let row ← flattenRow ⟨ops, tail⟩
    for (_, targs) in row.ops do
      out ← targs.foldlM (fun o f => namedAccs f o) out
    pure (out.insert (← findAcc a))
  | .ref _ t => namedAccs t out
  | .never => pure out

/-- Those a row's operations name. -/
def namedAccsRow (r : IRow) (out : Std.HashSet Nat) : M (Std.HashSet Nat) := do
  let row ← flattenRow r
  row.ops.foldlM (fun o (_, targs) => targs.foldlM (fun o f => namedAccs f o) o) out

/-- The regions a type mentions and what its callables touch, with whatever
those include: gathered for the types the whole program shares. -/
partial def sharedRegions (t : ITy) (acc : Std.HashSet Nat × Std.HashSet Nat) :
    M (Std.HashSet Nat × Std.HashSet Nat) := do
  match ← find t with
  | .var _ | .param _ | .int => pure acc
  | .tuple fs | .data _ fs => fs.foldlM (fun a f => sharedRegions f a) acc
  | .fn ps r ops tail _ env a => do
    let mut acc ← ps.foldlM (fun a f => sharedRegions f a) acc
    acc ← sharedRegions r acc
    acc ← sharedRegions env acc
    let row ← flattenRow ⟨ops, tail⟩
    for (_, targs) in row.ops do
      acc ← targs.foldlM (fun a f => sharedRegions f a) acc
    touched a acc
  | .ref ρ t => do
    let r ← findRg ρ
    sharedRegions t (acc.1.insert r, acc.2)
  | .never => pure acc
where
  touched (a : Nat) (acc : Std.HashSet Nat × Std.HashSet Nat) :
      M (Std.HashSet Nat × Std.HashSet Nat) := do
    let a ← findAcc a
    if acc.2.contains a then return acc
    let x ← accNode a
    let mut acc := (acc.1, acc.2.insert a)
    for ρ in x.rgns do
      acc := (acc.1.insert (← findRg ρ), acc.2)
    for (b, _) in x.subs do
      acc ← touched b acc
    for (sub, chosen) in x.insts do
      for (_, actual) in chosen do
        acc := (acc.1.insert (← findRg actual), acc.2)
      acc ← touched sub acc
    pure acc


/-- A callable type that binds no region of its own. (Giving up one that
does touches nothing of those: they are chosen at a call. What else it
touches is not told apart here, so one given up where its type is fixed by a
use is left to the destroyer's own typing.) -/
def bindsNone (kt : ITy) : M Bool := do
  match kt with
  | .fn _ _ _ _ _ _ acc => pure (← bindersOf acc).isEmpty
  | _ => pure true

/-- A callable of type `kt` given up where the effects `amb` may be performed
and the regions `self` touched: whatever it takes, a call of it could do what
it says. -/
def givenUp (kt : ITy) (amb : IRow) (self : Nat) (known : Option Nat := none) : M Unit := do
  let ε' ← freshRow
  let a ← freshAcc
  -- A resumption or label takes one argument; a closure, any number.
  let arity := match kt, known with
    | .fn ps .., _ => ps.length
    | _, some n => n
    | _, none => 1
  let ps ← (List.range arity).mapM fun _ => freshTy
  unify kt (.func ps (← freshTy) ε' (← freshCls) (← freshTy) a)
  needs ε' [] amb
  accSub self a

end Glorious.Infer
