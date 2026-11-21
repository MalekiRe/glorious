module

public import Glorious.Check.Expr

public section

namespace Glorious.Check

open Syntax

/-! ## What a check added, and putting it on another state

A check of some groups or units from a state adds to it: entries made in
stores of its own (its ids numbered from a place of its own, `Store.jumpTo`),
entries at the end of arrays and in front of lists, entries in maps. What it
added is its delta (`StDelta`, `diffStates`), and a delta is put on another
state (`applyDelta`): on the state of a check that went on from the same
one, side by side (`mergeStates`), or, of the program's own groups, on the
state of a later compile where nothing the group reads changed (`Check.reuse`).

Where the check changed what it began with (a variable bound, a list
grown at an entry that was there), the delta says what the entry was and
is; put where that entry is still what it was, it is changed, and where both
changed it, only if the two can be put together (`Absorb`): a variable both
bound alike, what a capture variable captures grown by both. Where the other
state is at hand (`p`, side by side) what it changed is told by whether an
entry is the same object; without it (a later compile), only one unchanged
or that can absorb the change takes it. -/

unsafe def samePtrImpl {α : Type} (a b : α) : Bool := ptrAddrUnsafe a == ptrAddrUnsafe b

/-- Are these the same object? (Taken to be not, where that cannot be asked.) -/
@[implemented_by samePtrImpl] def samePtr {α : Type} (_ _ : α) : Bool := false

/-- How an entry two checks both changed is put together: from what it was,
what one made it, and what the other did. -/
class Absorb (α : Type) where
  absorb : α → α → α → Option α

instance (priority := low) {α : Type} : Absorb α := ⟨fun _ _ _ => none⟩
/-- (A variable bound by one, or both bound to what is the same.) -/
instance {β : Type} [BEq β] : Absorb (Option β) := ⟨fun _ x y => match x, y with
  | none, y => some y
  | some a, some b => if a == b then some x else none
  | some _, none => some x⟩
/-- (A type variable both bound to the same type, written alike with nothing
unknown in it.) -/
instance : Absorb (Option Ty) := ⟨fun _ x y => match x, y with
  | none, y => some y
  | some a, some b => let s := showTy a; if s == showTy b && !s.contains '?' then some x else none
  | some _, none => some x⟩
/-- (A row variable both bound to the same effects, with no row after.) -/
instance : Absorb (Option Row) := ⟨fun _ x y => match x, y with
  | none, y => some y
  | some a, some b =>
    if a.tail.isNone && b.tail.isNone && showEffs a.effs == showEffs b.effs && !(showEffs a.effs).contains '?' then some x
    else none
  | some _, none => some x⟩
/-- (What a capture variable captures, grown by both: what each added after
what was there, first's first.) -/
instance : Absorb (Array Nat) := ⟨fun z x y =>
  if x.size ≥ z.size && y.size ≥ z.size && y.extract 0 z.size == z then some (x ++ y.extract z.size y.size)
  else none⟩

/-- (A function's body as a check wrote a decision into it: where it is what
it was, written alike.) -/
instance : Absorb Flat.Body := ⟨fun z x y => if x == z then some y else if x == y then some x else none⟩

/-- What a check did to a store: segments of its own, entries pushed onto a
segment that was there (its start, how many it had, and those), and entries
changed (where, what it was, what it is). -/
structure StoreD (α : Type) where
  segs : Array (Seg α) := #[]
  grown : Array (Nat × Nat × Array α) := #[]
  sets : Array (Nat × α × α) := #[]

/-- What a check did to an array: entries after the first `start`, or all
of it made anew. -/
inductive ArrD (α : Type) where
  | grown (start : Nat) (tail : Array α)
  | whole (all : Array α)

/-- What a check did to a list: entries in front, entries after the first
`start`, or all of it made anew. -/
inductive ListD (α : Type) where
  | front (xs : List α)
  | back (start : Nat) (xs : List α)
  | whole (all : List α)

/-- What a check did to a map: each entry it made or changed, with what was
there. -/
abbrev MapD (κ ν : Type) := Array (κ × Option ν × ν)

/-- What a check did to a map of lists: each list it made or grew. -/
abbrev MapLD (κ ν : Type) := Array (κ × Option (List ν) × ListD ν)

/-- How what a check did to one part of the state is found (`diff`, from
what it began with), and put on another (`apply`; `p`, where it is at hand,
the state it began with too). -/
class Delta (α : Type) (δ : outParam Type) where
  diff : α → α → Option δ
  apply : Option α → α → δ → Option α

/-- An entry of `a` changed to `now` by a check that found it `was`. -/
@[inline] def putEntry {α : Type} [Absorb α] (cur was now : α) : Option α :=
  if samePtr cur was then some now
  else if samePtr cur now then some cur
  else Absorb.absorb was cur now

namespace StoreD

variable {α : Type}

def diff (p b : Store α) : Option (StoreD α) := do
  if samePtr p b then return {}
  let ps := p.segs
  let bs := b.segs
  let mut d : StoreD α := {}
  let mut k := 0
  for sb in bs do
    while k < ps.size && ((ps[k]?.map (·.base)).getD 0) < sb.base do
      -- (One of `p`'s that `b` does not have: only an empty last one, which
      -- a jump took the place of.)
      if ((ps[k]?.map (·.count)).getD 0) != 0 then none
      k := k + 1
    match ps[k]? with
    | some sp =>
      if sp.base == sb.base then
        k := k + 1
        if sb.count < sp.count then none
        for c in [0:sb.pieces.size] do
          let pb := sb.pieces.getD c #[]
          let pp := sp.pieces.getD c #[]
          unless samePtr pb pp do
            for j in [0:min pb.size pp.size] do
              match pb[j]?, pp[j]? with
              | some x, some z => unless samePtr x z do d := { d with sets := d.sets.push (sp.base + 64 * c + j, z, x) }
              | _, _ => pure ()
        if sb.count > sp.count then
          let pushed := ((List.range (sb.count - sp.count)).filterMap fun i => sb.get? (sp.count + i)).toArray
          d := { d with grown := d.grown.push (sp.base, sp.count, pushed) }
      else d := { d with segs := d.segs.push sb }
    | none => d := { d with segs := d.segs.push sb }
  while k < ps.size do
    if ((ps[k]?.map (·.count)).getD 0) != 0 then none
    k := k + 1
  pure d

def apply [Absorb α] (a : Store α) (d : StoreD α) : Option (Store α) := do
  if d.segs.isEmpty && d.grown.isEmpty && d.sets.isEmpty then return a
  let mut segs := a.segs
  for (base, before, pushed) in d.grown do
    match segs.findIdx? (·.base == base) with
    | some i =>
      match segs[i]? with
      | some s =>
        if s.count != before then none
        segs := segs.set! i (pushed.foldl Seg.push s)
      | none => none
    | none => none
  -- (In the order of where they start; one begun with nothing in it gives
  -- way to one of the same start.)
  for s in d.segs do
    match segs.findIdx? (·.base ≥ s.base) with
    | some i =>
      match segs[i]? with
      | some t =>
        if t.base == s.base then
          if t.count != 0 then none
          segs := segs.set! i s
        else segs := segs.insertIdx! i s
      | none => none
    | none => segs := segs.push s
  -- (An empty one before the last is dropped: nothing is numbered in it.)
  let n := segs.size
  let kept := segs.zipIdx.filterMap fun (s, i) => if s.count != 0 || i + 1 == n then some s else none
  let mut st : Store α := match kept.back? with
    | some last => { older := kept.pop, last }
    | none => {}
  for (i, was, now) in d.sets do
    match st.get? i with
    | some cur => st := st.set! i (← putEntry cur was now)
    | none => none
  pure st

end StoreD

instance {α : Type} [Absorb α] : Delta (Store α) (StoreD α) where
  diff := StoreD.diff
  apply _ a d := StoreD.apply a d

/-- Does `b` go on from `p`: its first entries `p`'s? -/
def extendsArr {α : Type} (p b : Array α) : Bool :=
  b.size ≥ p.size && (List.range p.size).all fun i => match b[i]?, p[i]? with
    | some x, some z => samePtr x z
    | _, _ => false

instance {α : Type} : Delta (Array α) (ArrD α) where
  diff p b :=
    if samePtr p b then some (.grown p.size #[])
    else if extendsArr p b then some (.grown p.size (b.extract p.size b.size))
    else some (.whole b)
  apply p a
    | .grown _ tail =>
      if tail.isEmpty then some a else
      match p with
      | some p => if samePtr a p || extendsArr p a then some (a ++ tail) else none
      | none => some (a ++ tail)
    | .whole all =>
      match p with
      | some p => if samePtr a p then some all else none
      | none => some all

/-- Does `b` go on from `p` at its end? -/
def extendsList {α : Type} (p b : List α) : Bool :=
  b.length ≥ p.length && ((b.take p.length).zip p).all fun (x, z) => samePtr x z

instance {α : Type} : Delta (List α) (ListD α) where
  diff p b :=
    if samePtr p b then some (.front [])
    else
      let lp := p.length
      let lb := b.length
      if lb ≥ lp && samePtr (b.drop (lb - lp)) p then some (.front (b.take (lb - lp)))
      else if extendsList p b then some (.back lp (b.drop lp))
      else some (.whole b)
  apply p a
    | .front [] => some a
    | .front xs =>
      match p with
      | some p =>
        let la := a.length
        if samePtr a p || (la ≥ p.length && samePtr (a.drop (la - p.length)) p) then some (xs ++ a)
        -- (One grew at the end, the other in front.)
        else if extendsList p a then some (xs ++ a)
        else none
      | none => some (xs ++ a)
    | .back _ [] => some a
    | .back _ xs =>
      match p with
      | some p => if samePtr a p || extendsList p a then some (a ++ xs) else none
      | none => some (a ++ xs)
    | .whole all =>
      match p with
      | some p => if samePtr a p then some all else none
      | none => some all

/-- The entries of `b` in the buckets it changed of `p`'s, where it has as many
buckets: a bucket not changed is the same object. -/
def changedEntries {κ ν : Type} [BEq κ] [Hashable κ] (p b : Std.HashMap κ ν) : Option (List (κ × ν)) :=
  let pb := p.inner.1.buckets
  let bb := b.inner.1.buckets
  if pb.size != bb.size then none else
  some ((List.range bb.size).foldl (fun acc i =>
    match bb[i]?, pb[i]? with
    | some bl, some pl => if samePtr bl pl then acc else bl.toList.foldl (fun acc e => (e.1, e.2) :: acc) acc
    | _, _ => acc) [])

/-- The entries of `b` that are not `p`'s. -/
def newEntries {κ ν : Type} [BEq κ] [Hashable κ] (p b : Std.HashMap κ ν) : List (κ × ν × Option ν) :=
  let es := match changedEntries p b with
    | some es => es
    | none => b.toList
  es.filterMap fun (k, v) => match p.get? k with
    | some pv => if samePtr pv v then none else some (k, v, some pv)
    | none => some (k, v, none)

instance (priority := low) {κ ν : Type} [BEq κ] [Hashable κ] [Absorb ν] : Delta (Std.HashMap κ ν) (MapD κ ν) where
  diff p b := if samePtr p b then some #[] else some ((newEntries p b).map fun (k, v, was) => (k, was, v)).toArray
  apply p a d := d.foldlM (init := a) fun m (k, was, v) =>
    match was, m.get? k with
    | some pv, some cur => (putEntry cur pv v).map (m.insert k ·)
    -- (Made by both: the same, as both took it from what is the same.)
    | none, some cur => if samePtr cur v then some m else
        match p with
        | some _ => none
        | none => none
    | none, none => some (m.insert k v)
    | some _, none => none

instance {κ ν : Type} [BEq κ] [Hashable κ] : Delta (Std.HashMap κ (List ν)) (MapLD κ ν) where
  diff p b := if samePtr p b then some #[] else
    some ((newEntries p b).filterMap fun (k, v, was) =>
      match was with
      | some pv => (Delta.diff pv v : Option (ListD ν)).map fun d => (k, some pv, d)
      | none => some (k, none, ListD.whole v)).toArray
  apply p a d := d.foldlM (init := a) fun m (k, was, ld) =>
    match was, m.get? k with
    | some pv, some cur => do
      let p' := p.map fun _ => pv
      pure (m.insert k (← Delta.apply p' cur ld))
    -- (Made by both: the two put together, this one's in front.)
    | none, some cur => match ld with
      | .whole v => some (m.insert k (v ++ cur))
      | _ => none
    | none, none => match ld with
      | .whole v => some (m.insert k v)
      | _ => none
    | some _, none => none

instance {κ : Type} [BEq κ] [Hashable κ] : Delta (Std.HashSet κ) (Array κ) where
  diff p b := if samePtr p b then some #[] else
    let es : List κ := match changedEntries p.inner b.inner with
      | some es => es.map fun (k, _) => k
      | none => b.toList
    some (es.filter (!p.contains ·)).toArray
  apply _ a d := some (d.foldl (·.insert ·) a)

instance : Delta Traits.ImplIndex (Array Traits.Impl) where
  diff p b :=
    if samePtr p b then some #[]
    else if extendsArr p.impls b.impls then some (b.impls.extract p.impls.size b.impls.size)
    else none
  apply p a d :=
    if d.isEmpty then some a else
    match p with
    | some p => if samePtr a p || extendsArr p.impls a.impls then some (.ofArray (a.impls ++ d)) else none
    | none => some (.ofArray (a.impls ++ d))

/-- (A part of `StDelta`.) -/
structure StDelta0 where
  tys : StoreD (Option Ty)
  rows : StoreD (Option Row)
  mono : ListD Nat
  monoRows : ListD Nat
  monoCaps : ListD Nat
  caps : StoreD (Option Nat)
  capEdges : StoreD (Nat × Captured)
  capOut : StoreD (Array Nat)
  capEdgeNames : StoreD (Option (String × Nat))
  dups : ArrD (Ty × String)
  lateDups : ArrD (Ty × String)
  drops : ArrD (Ty × String)

def diffPart0 (p b : St) : Option StDelta0 := do
  pure {
    tys := ← Delta.diff p.tys b.tys
    rows := ← Delta.diff p.rows b.rows
    mono := ← Delta.diff p.mono b.mono
    monoRows := ← Delta.diff p.monoRows b.monoRows
    monoCaps := ← Delta.diff p.monoCaps b.monoCaps
    caps := ← Delta.diff p.caps b.caps
    capEdges := ← Delta.diff p.capEdges b.capEdges
    capOut := ← Delta.diff p.capOut b.capOut
    capEdgeNames := ← Delta.diff p.capEdgeNames b.capEdgeNames
    dups := ← Delta.diff p.dups b.dups
    lateDups := ← Delta.diff p.lateDups b.lateDups
    drops := ← Delta.diff p.drops b.drops }

def applyPart0 (p : Option St) (a : St) (d : StDelta0) : Option St := do
  pure { a with
    tys := ← Delta.apply (p.map (·.tys)) a.tys d.tys,
    rows := ← Delta.apply (p.map (·.rows)) a.rows d.rows,
    mono := ← Delta.apply (p.map (·.mono)) a.mono d.mono,
    monoRows := ← Delta.apply (p.map (·.monoRows)) a.monoRows d.monoRows,
    monoCaps := ← Delta.apply (p.map (·.monoCaps)) a.monoCaps d.monoCaps,
    caps := ← Delta.apply (p.map (·.caps)) a.caps d.caps,
    capEdges := ← Delta.apply (p.map (·.capEdges)) a.capEdges d.capEdges,
    capOut := ← Delta.apply (p.map (·.capOut)) a.capOut d.capOut,
    capEdgeNames := ← Delta.apply (p.map (·.capEdgeNames)) a.capEdgeNames d.capEdgeNames,
    dups := ← Delta.apply (p.map (·.dups)) a.dups d.dups,
    lateDups := ← Delta.apply (p.map (·.lateDups)) a.lateDups d.lateDups,
    drops := ← Delta.apply (p.map (·.drops)) a.drops d.drops }

/-- (A part of `StDelta`.) -/
structure StDelta1 where
  lateDrops : ArrD (Ty × String)
  stays : ArrD (Ty × String)
  lateStays : ArrD (Ty × String)
  statics : ArrD (Ty × String)
  pendingCopies : ArrD (String × FnDecl)
  useDecls : MapD String (Bool × Bool)
  movedCells : ListD Nat
  flagged : ListD String
  givenSites : ListD (String × Elab.DropSite × Ty × String)
  givenEdges : Array Nat
  givers : ListD (Nat × Nat)
  givenReads : ArrD (Ty × String)

def diffPart1 (p b : St) : Option StDelta1 := do
  pure {
    lateDrops := ← Delta.diff p.lateDrops b.lateDrops
    stays := ← Delta.diff p.stays b.stays
    lateStays := ← Delta.diff p.lateStays b.lateStays
    statics := ← Delta.diff p.statics b.statics
    pendingCopies := ← Delta.diff p.pendingCopies b.pendingCopies
    useDecls := ← Delta.diff p.useDecls b.useDecls
    movedCells := ← Delta.diff p.movedCells b.movedCells
    flagged := ← Delta.diff p.flagged b.flagged
    givenSites := ← Delta.diff p.givenSites b.givenSites
    givenEdges := ← Delta.diff p.givenEdges b.givenEdges
    givers := ← Delta.diff p.givers b.givers
    givenReads := ← Delta.diff p.givenReads b.givenReads }

def applyPart1 (p : Option St) (a : St) (d : StDelta1) : Option St := do
  pure { a with
    lateDrops := ← Delta.apply (p.map (·.lateDrops)) a.lateDrops d.lateDrops,
    stays := ← Delta.apply (p.map (·.stays)) a.stays d.stays,
    lateStays := ← Delta.apply (p.map (·.lateStays)) a.lateStays d.lateStays,
    statics := ← Delta.apply (p.map (·.statics)) a.statics d.statics,
    pendingCopies := ← Delta.apply (p.map (·.pendingCopies)) a.pendingCopies d.pendingCopies,
    useDecls := ← Delta.apply (p.map (·.useDecls)) a.useDecls d.useDecls,
    movedCells := ← Delta.apply (p.map (·.movedCells)) a.movedCells d.movedCells,
    flagged := ← Delta.apply (p.map (·.flagged)) a.flagged d.flagged,
    givenSites := ← Delta.apply (p.map (·.givenSites)) a.givenSites d.givenSites,
    givenEdges := ← Delta.apply (p.map (·.givenEdges)) a.givenEdges d.givenEdges,
    givers := ← Delta.apply (p.map (·.givers)) a.givers d.givers,
    givenReads := ← Delta.apply (p.map (·.givenReads)) a.givenReads d.givenReads }

/-- (A part of `StDelta`.) -/
structure StDelta2 where
  aparts : ArrD (Ty × String × Option Nat)
  fieldNames : MapLD String String
  dotChosen : ListD (Nat × String × Nat)
  argsChosen : ListD ((Nat × Nat) × Expr)
  decided : ListD Elab.Decision
  traitShape : MapD String (Nat × List String)
  writtenArgs : ListD (String × String × String × List Ty)
  supers : ListD (String × List String)
  ranked : ListD (Nat × List (Nat × String))
  packs : ArrD (Nat × List String)
  envGroups : ArrD (String × List (String × Nat) × Bool × List String × Flat.Body × List Flat.StmtId)
  envAfter : ArrD (String × List (String × Nat) × List (String × Nat) × List String × Flat.Body × List Flat.StmtId)

def diffPart2 (p b : St) : Option StDelta2 := do
  pure {
    aparts := ← Delta.diff p.aparts b.aparts
    fieldNames := ← Delta.diff p.fieldNames b.fieldNames
    dotChosen := ← Delta.diff p.dotChosen b.dotChosen
    argsChosen := ← Delta.diff p.argsChosen b.argsChosen
    decided := ← Delta.diff p.decided b.decided
    traitShape := ← Delta.diff p.traitShape b.traitShape
    writtenArgs := ← Delta.diff p.writtenArgs b.writtenArgs
    supers := ← Delta.diff p.supers b.supers
    ranked := ← Delta.diff p.ranked b.ranked
    packs := ← Delta.diff p.packs b.packs
    envGroups := ← Delta.diff p.envGroups b.envGroups
    envAfter := ← Delta.diff p.envAfter b.envAfter }

def applyPart2 (p : Option St) (a : St) (d : StDelta2) : Option St := do
  pure { a with
    aparts := ← Delta.apply (p.map (·.aparts)) a.aparts d.aparts,
    fieldNames := ← Delta.apply (p.map (·.fieldNames)) a.fieldNames d.fieldNames,
    dotChosen := ← Delta.apply (p.map (·.dotChosen)) a.dotChosen d.dotChosen,
    argsChosen := ← Delta.apply (p.map (·.argsChosen)) a.argsChosen d.argsChosen,
    decided := ← Delta.apply (p.map (·.decided)) a.decided d.decided,
    traitShape := ← Delta.apply (p.map (·.traitShape)) a.traitShape d.traitShape,
    writtenArgs := ← Delta.apply (p.map (·.writtenArgs)) a.writtenArgs d.writtenArgs,
    supers := ← Delta.apply (p.map (·.supers)) a.supers d.supers,
    ranked := ← Delta.apply (p.map (·.ranked)) a.ranked d.ranked,
    packs := ← Delta.apply (p.map (·.packs)) a.packs d.packs,
    envGroups := ← Delta.apply (p.map (·.envGroups)) a.envGroups d.envGroups,
    envAfter := ← Delta.apply (p.map (·.envAfter)) a.envAfter d.envAfter }

/-- (A part of `StDelta`.) -/
structure StDelta3 where
  envLent : ArrD (String × List (String × Nat) × List (String × Nat) × List String × Flat.Body × List Flat.StmtId)
  fnGroups : ListD (String × List (List Nat))
  fnRunsIn : ListD (String × List (Nat × Bool))
  bindLoans : MapD Nat Nat
  envBlocks : Array Nat
  inPlace : Array Nat
  envMust : ListD String
  envHeld : ArrD (String × String × List Nat)
  derefReads : ArrD Nat
  rowChecks : ListD (String × List (String × Ty))
  typeBounds : ListD (String × List (String × Nat))
  typeParams : ListD (String × List (Option Nat))

def diffPart3 (p b : St) : Option StDelta3 := do
  pure {
    envLent := ← Delta.diff p.envLent b.envLent
    fnGroups := ← Delta.diff p.fnGroups b.fnGroups
    fnRunsIn := ← Delta.diff p.fnRunsIn b.fnRunsIn
    bindLoans := ← Delta.diff p.bindLoans b.bindLoans
    envBlocks := ← Delta.diff p.envBlocks b.envBlocks
    inPlace := ← Delta.diff p.inPlace b.inPlace
    envMust := ← Delta.diff p.envMust b.envMust
    envHeld := ← Delta.diff p.envHeld b.envHeld
    derefReads := ← Delta.diff p.derefReads b.derefReads
    rowChecks := ← Delta.diff p.rowChecks b.rowChecks
    typeBounds := ← Delta.diff p.typeBounds b.typeBounds
    typeParams := ← Delta.diff p.typeParams b.typeParams }

def applyPart3 (p : Option St) (a : St) (d : StDelta3) : Option St := do
  pure { a with
    envLent := ← Delta.apply (p.map (·.envLent)) a.envLent d.envLent,
    fnGroups := ← Delta.apply (p.map (·.fnGroups)) a.fnGroups d.fnGroups,
    fnRunsIn := ← Delta.apply (p.map (·.fnRunsIn)) a.fnRunsIn d.fnRunsIn,
    bindLoans := ← Delta.apply (p.map (·.bindLoans)) a.bindLoans d.bindLoans,
    envBlocks := ← Delta.apply (p.map (·.envBlocks)) a.envBlocks d.envBlocks,
    inPlace := ← Delta.apply (p.map (·.inPlace)) a.inPlace d.inPlace,
    envMust := ← Delta.apply (p.map (·.envMust)) a.envMust d.envMust,
    envHeld := ← Delta.apply (p.map (·.envHeld)) a.envHeld d.envHeld,
    derefReads := ← Delta.apply (p.map (·.derefReads)) a.derefReads d.derefReads,
    rowChecks := ← Delta.apply (p.map (·.rowChecks)) a.rowChecks d.rowChecks,
    typeBounds := ← Delta.apply (p.map (·.typeBounds)) a.typeBounds d.typeBounds,
    typeParams := ← Delta.apply (p.map (·.typeParams)) a.typeParams d.typeParams }

/-- (A part of `StDelta`.) -/
structure StDelta4 where
  fieldReads : ArrD (Nat × Nat)
  fieldSites : ArrD (Nat × Bool × Ty × List Nat × List (Option String) × String × String)
  fieldTable : ArrD (Nat × Bool × List Nat × List (Option String × Nat))
  calls : ArrD (Nat × Ty × Bool)
  instRows : ListD Nat
  unrunGiven : ArrD (Nat × Nat × Ty × List (String × Nat) × String × Nat)
  sharedEdges : Array Nat
  assumedLinks : ArrD (Nat × Nat × Ty × String)
  abandoned : ArrD (Nat × Ty × String)
  sure : Array Nat
  lowerChecks : ArrD (String × String × Ty × List String × Flat.Body × List Flat.StmtId)
  refusals : ArrD String

def diffPart4 (p b : St) : Option StDelta4 := do
  pure {
    fieldReads := ← Delta.diff p.fieldReads b.fieldReads
    fieldSites := ← Delta.diff p.fieldSites b.fieldSites
    fieldTable := ← Delta.diff p.fieldTable b.fieldTable
    calls := ← Delta.diff p.calls b.calls
    instRows := ← Delta.diff p.instRows b.instRows
    unrunGiven := ← Delta.diff p.unrunGiven b.unrunGiven
    sharedEdges := ← Delta.diff p.sharedEdges b.sharedEdges
    assumedLinks := ← Delta.diff p.assumedLinks b.assumedLinks
    abandoned := ← Delta.diff p.abandoned b.abandoned
    sure := ← Delta.diff p.sure b.sure
    lowerChecks := ← Delta.diff p.lowerChecks b.lowerChecks
    refusals := ← Delta.diff p.refusals b.refusals }

def applyPart4 (p : Option St) (a : St) (d : StDelta4) : Option St := do
  pure { a with
    fieldReads := ← Delta.apply (p.map (·.fieldReads)) a.fieldReads d.fieldReads,
    fieldSites := ← Delta.apply (p.map (·.fieldSites)) a.fieldSites d.fieldSites,
    fieldTable := ← Delta.apply (p.map (·.fieldTable)) a.fieldTable d.fieldTable,
    calls := ← Delta.apply (p.map (·.calls)) a.calls d.calls,
    instRows := ← Delta.apply (p.map (·.instRows)) a.instRows d.instRows,
    unrunGiven := ← Delta.apply (p.map (·.unrunGiven)) a.unrunGiven d.unrunGiven,
    sharedEdges := ← Delta.apply (p.map (·.sharedEdges)) a.sharedEdges d.sharedEdges,
    assumedLinks := ← Delta.apply (p.map (·.assumedLinks)) a.assumedLinks d.assumedLinks,
    abandoned := ← Delta.apply (p.map (·.abandoned)) a.abandoned d.abandoned,
    sure := ← Delta.apply (p.map (·.sure)) a.sure d.sure,
    lowerChecks := ← Delta.apply (p.map (·.lowerChecks)) a.lowerChecks d.lowerChecks,
    refusals := ← Delta.apply (p.map (·.refusals)) a.refusals d.refusals }

/-- (A part of `StDelta`.) -/
structure StDelta5 where
  runFns : MapD String Flat.Body
  runCtors : Array String
  runAliases : MapD String Expr
  runOps : MapD String Bool
  runExact : Array String
  runNow : Array Nat
  rowIncl : ArrD (Row × Row × String)
  types : MapD String TypeDecl
  ctors : MapD String CtorSig
  ops : ListD (String × OpSig)
  effects : ListD (String × EffectDecl)
  aliases : MapD String Expr

def diffPart5 (p b : St) : Option StDelta5 := do
  pure {
    runFns := ← Delta.diff p.runFns b.runFns
    runCtors := ← Delta.diff p.runCtors b.runCtors
    runAliases := ← Delta.diff p.runAliases b.runAliases
    runOps := ← Delta.diff p.runOps b.runOps
    runExact := ← Delta.diff p.runExact b.runExact
    runNow := ← Delta.diff p.runNow b.runNow
    rowIncl := ← Delta.diff p.rowIncl b.rowIncl
    types := ← Delta.diff p.types b.types
    ctors := ← Delta.diff p.ctors b.ctors
    ops := ← Delta.diff p.ops b.ops
    effects := ← Delta.diff p.effects b.effects
    aliases := ← Delta.diff p.aliases b.aliases }

def applyPart5 (p : Option St) (a : St) (d : StDelta5) : Option St := do
  pure { a with
    runFns := ← Delta.apply (p.map (·.runFns)) a.runFns d.runFns,
    runCtors := ← Delta.apply (p.map (·.runCtors)) a.runCtors d.runCtors,
    runAliases := ← Delta.apply (p.map (·.runAliases)) a.runAliases d.runAliases,
    runOps := ← Delta.apply (p.map (·.runOps)) a.runOps d.runOps,
    runExact := ← Delta.apply (p.map (·.runExact)) a.runExact d.runExact,
    runNow := ← Delta.apply (p.map (·.runNow)) a.runNow d.runNow,
    rowIncl := ← Delta.apply (p.map (·.rowIncl)) a.rowIncl d.rowIncl,
    types := ← Delta.apply (p.map (·.types)) a.types d.types,
    ctors := ← Delta.apply (p.map (·.ctors)) a.ctors d.ctors,
    ops := ← Delta.apply (p.map (·.ops)) a.ops d.ops,
    effects := ← Delta.apply (p.map (·.effects)) a.effects d.effects,
    aliases := ← Delta.apply (p.map (·.aliases)) a.aliases d.aliases }

/-- (A part of `StDelta`.) -/
structure StDelta6 where
  fns : MapD String Scheme
  pending : ArrD Pending
  projections : ArrD (Ty × Nat × Ty × String × Nat)
  namedReads : ArrD (Ty × String × Ty × Nat × String)
  blockCaps : ArrD (Nat × Nat)
  given : ArrD Nat
  unrun : ArrD (Nat × Nat)
  coercing : ListD String
  coercions : ArrD (Elab.Site × String)
  loans : StoreD Loan
  cells : ArrD (Nat × String × Ty)
  bindSites : ListD (Nat × Nat × Nat)

def diffPart6 (p b : St) : Option StDelta6 := do
  pure {
    fns := ← Delta.diff p.fns b.fns
    pending := ← Delta.diff p.pending b.pending
    projections := ← Delta.diff p.projections b.projections
    namedReads := ← Delta.diff p.namedReads b.namedReads
    blockCaps := ← Delta.diff p.blockCaps b.blockCaps
    given := ← Delta.diff p.given b.given
    unrun := ← Delta.diff p.unrun b.unrun
    coercing := ← Delta.diff p.coercing b.coercing
    coercions := ← Delta.diff p.coercions b.coercions
    loans := ← Delta.diff p.loans b.loans
    cells := ← Delta.diff p.cells b.cells
    bindSites := ← Delta.diff p.bindSites b.bindSites }

def applyPart6 (p : Option St) (a : St) (d : StDelta6) : Option St := do
  pure { a with
    fns := ← Delta.apply (p.map (·.fns)) a.fns d.fns,
    pending := ← Delta.apply (p.map (·.pending)) a.pending d.pending,
    projections := ← Delta.apply (p.map (·.projections)) a.projections d.projections,
    namedReads := ← Delta.apply (p.map (·.namedReads)) a.namedReads d.namedReads,
    blockCaps := ← Delta.apply (p.map (·.blockCaps)) a.blockCaps d.blockCaps,
    given := ← Delta.apply (p.map (·.given)) a.given d.given,
    unrun := ← Delta.apply (p.map (·.unrun)) a.unrun d.unrun,
    coercing := ← Delta.apply (p.map (·.coercing)) a.coercing d.coercing,
    coercions := ← Delta.apply (p.map (·.coercions)) a.coercions d.coercions,
    loans := ← Delta.apply (p.map (·.loans)) a.loans d.loans,
    cells := ← Delta.apply (p.map (·.cells)) a.cells d.cells,
    bindSites := ← Delta.apply (p.map (·.bindSites)) a.bindSites d.bindSites }

/-- (A part of `StDelta`.) -/
structure StDelta7 where
  leftBehind : ArrD (Ty × String)
  takenApart : ArrD (Ty × String)
  partReads : ArrD (Nat × String × Ty × Nat × String × String)
  uses : ArrD Use
  heldMoves : ArrD Use
  traits : ListD (String × List String)
  methods : MapD String MethodSig
  kimpls : Array Traits.Impl
  blanketTraits : ListD (String × List String)
  instSites : ArrD (String × Nat × String × String × List Ty)
  siteTable : ListD (String × List (Nat × String × String × Nat × Nat))
  siteTypes : ListD (String × List (Option Syntax.TypeExpr))

def diffPart7 (p b : St) : Option StDelta7 := do
  pure {
    leftBehind := ← Delta.diff p.leftBehind b.leftBehind
    takenApart := ← Delta.diff p.takenApart b.takenApart
    partReads := ← Delta.diff p.partReads b.partReads
    uses := ← Delta.diff p.uses b.uses
    heldMoves := ← Delta.diff p.heldMoves b.heldMoves
    traits := ← Delta.diff p.traits b.traits
    methods := ← Delta.diff p.methods b.methods
    kimpls := ← Delta.diff p.kimpls b.kimpls
    blanketTraits := ← Delta.diff p.blanketTraits b.blanketTraits
    instSites := ← Delta.diff p.instSites b.instSites
    siteTable := ← Delta.diff p.siteTable b.siteTable
    siteTypes := ← Delta.diff p.siteTypes b.siteTypes }

def applyPart7 (p : Option St) (a : St) (d : StDelta7) : Option St := do
  pure { a with
    leftBehind := ← Delta.apply (p.map (·.leftBehind)) a.leftBehind d.leftBehind,
    takenApart := ← Delta.apply (p.map (·.takenApart)) a.takenApart d.takenApart,
    partReads := ← Delta.apply (p.map (·.partReads)) a.partReads d.partReads,
    uses := ← Delta.apply (p.map (·.uses)) a.uses d.uses,
    heldMoves := ← Delta.apply (p.map (·.heldMoves)) a.heldMoves d.heldMoves,
    traits := ← Delta.apply (p.map (·.traits)) a.traits d.traits,
    methods := ← Delta.apply (p.map (·.methods)) a.methods d.methods,
    kimpls := ← Delta.apply (p.map (·.kimpls)) a.kimpls d.kimpls,
    blanketTraits := ← Delta.apply (p.map (·.blanketTraits)) a.blanketTraits d.blanketTraits,
    instSites := ← Delta.apply (p.map (·.instSites)) a.instSites d.instSites,
    siteTable := ← Delta.apply (p.map (·.siteTable)) a.siteTable d.siteTable,
    siteTypes := ← Delta.apply (p.map (·.siteTypes)) a.siteTypes d.siteTypes }

/-- (A part of `StDelta`.) -/
structure StDelta8 where
  bounds : ArrD Bound
  groupUses : ArrD GroupUse
  rigidKeys : StoreD String
  rigidAt : MapD String Nat
  conditionsAt : MapLD String Nat
  dropCands : ArrD (Elab.DropSite × Ty × String)
  unsafeFns : ListD String
  dropSites : ArrD (Elab.DropSite × Nat)
  lateKeeps : ArrD (Elab.DropSite × Ty × List (Ty × Nat) × String)
  quiets : ArrD (Ty × String)
  paramTraits : ListD (String × String × List TypeExpr)
  gatOccs : ArrD (String × List Ty × Nat)

def diffPart8 (p b : St) : Option StDelta8 := do
  pure {
    bounds := ← Delta.diff p.bounds b.bounds
    groupUses := ← Delta.diff p.groupUses b.groupUses
    rigidKeys := ← Delta.diff p.rigidKeys b.rigidKeys
    rigidAt := ← Delta.diff p.rigidAt b.rigidAt
    conditionsAt := ← Delta.diff p.conditionsAt b.conditionsAt
    dropCands := ← Delta.diff p.dropCands b.dropCands
    unsafeFns := ← Delta.diff p.unsafeFns b.unsafeFns
    dropSites := ← Delta.diff p.dropSites b.dropSites
    lateKeeps := ← Delta.diff p.lateKeeps b.lateKeeps
    quiets := ← Delta.diff p.quiets b.quiets
    paramTraits := ← Delta.diff p.paramTraits b.paramTraits
    gatOccs := ← Delta.diff p.gatOccs b.gatOccs }

def applyPart8 (p : Option St) (a : St) (d : StDelta8) : Option St := do
  pure { a with
    bounds := ← Delta.apply (p.map (·.bounds)) a.bounds d.bounds,
    groupUses := ← Delta.apply (p.map (·.groupUses)) a.groupUses d.groupUses,
    rigidKeys := ← Delta.apply (p.map (·.rigidKeys)) a.rigidKeys d.rigidKeys,
    rigidAt := ← Delta.apply (p.map (·.rigidAt)) a.rigidAt d.rigidAt,
    conditionsAt := ← Delta.apply (p.map (·.conditionsAt)) a.conditionsAt d.conditionsAt,
    dropCands := ← Delta.apply (p.map (·.dropCands)) a.dropCands d.dropCands,
    unsafeFns := ← Delta.apply (p.map (·.unsafeFns)) a.unsafeFns d.unsafeFns,
    dropSites := ← Delta.apply (p.map (·.dropSites)) a.dropSites d.dropSites,
    lateKeeps := ← Delta.apply (p.map (·.lateKeeps)) a.lateKeeps d.lateKeeps,
    quiets := ← Delta.apply (p.map (·.quiets)) a.quiets d.quiets,
    paramTraits := ← Delta.apply (p.map (·.paramTraits)) a.paramTraits d.paramTraits,
    gatOccs := ← Delta.apply (p.map (·.gatOccs)) a.gatOccs d.gatOccs }

/-- (A part of `StDelta`.) -/
structure StDelta9 where
  gatHolds : ArrD (Nat × List Nat)
  dictTable : ArrD (Nat × List Elab.DictE)
  methodCalls : ArrD (Nat × Nat)
  fnBounds : ListD (String × Nat)
  impls : ArrD ImplDecl
  fnBodies : MapD String Flat.Body

def diffPart9 (p b : St) : Option StDelta9 := do
  pure {
    gatHolds := ← Delta.diff p.gatHolds b.gatHolds
    dictTable := ← Delta.diff p.dictTable b.dictTable
    methodCalls := ← Delta.diff p.methodCalls b.methodCalls
    fnBounds := ← Delta.diff p.fnBounds b.fnBounds
    impls := ← Delta.diff p.impls b.impls
    fnBodies := ← Delta.diff p.fnBodies b.fnBodies }

def applyPart9 (p : Option St) (a : St) (d : StDelta9) : Option St := do
  pure { a with
    gatHolds := ← Delta.apply (p.map (·.gatHolds)) a.gatHolds d.gatHolds,
    dictTable := ← Delta.apply (p.map (·.dictTable)) a.dictTable d.dictTable,
    methodCalls := ← Delta.apply (p.map (·.methodCalls)) a.methodCalls d.methodCalls,
    fnBounds := ← Delta.apply (p.map (·.fnBounds)) a.fnBounds d.fnBounds,
    impls := ← Delta.apply (p.map (·.impls)) a.impls d.impls,
    fnBodies := ← Delta.apply (p.map (·.fnBodies)) a.fnBodies d.fnBodies }

/-- What a check added to the state it began with (`diffStates`): each part
the checks put together as above, and the rest as the check left it. -/
structure StDelta where
  /-- The rest, as the check left it: what says where the check is. -/
  rest : St
  /-- Where the implementations the check declared start. -/
  implsStart : Nat
  assocUses : ArrD (String × Ty × String × Ty × String × String)
  part0 : StDelta0
  part1 : StDelta1
  part2 : StDelta2
  part3 : StDelta3
  part4 : StDelta4
  part5 : StDelta5
  part6 : StDelta6
  part7 : StDelta7
  part8 : StDelta8
  part9 : StDelta9

/-- What `b` added to `p`, of a check that went on from `p`; none where it
changed what cannot be told apart from what was there. -/
def diffStates (p b : St) : Option StDelta := do
  pure {
    rest := { b with
      tys := {},
      rows := {},
      mono := [],
      monoRows := [],
      monoCaps := [],
      caps := {},
      capEdges := {},
      capOut := {},
      capEdgeNames := {},
      dups := #[],
      lateDups := #[],
      drops := #[],
      lateDrops := #[],
      stays := #[],
      lateStays := #[],
      statics := #[],
      pendingCopies := #[],
      useDecls := {},
      movedCells := [],
      flagged := [],
      givenSites := [],
      givenEdges := {},
      givers := [],
      givenReads := #[],
      aparts := #[],
      fieldNames := {},
      dotChosen := [],
      argsChosen := [],
      decided := [],
      traitShape := {},
      writtenArgs := [],
      supers := [],
      ranked := [],
      packs := #[],
      envGroups := #[],
      envAfter := #[],
      envLent := #[],
      fnGroups := [],
      fnRunsIn := [],
      bindLoans := {},
      envBlocks := {},
      inPlace := {},
      envMust := [],
      envHeld := #[],
      derefReads := #[],
      rowChecks := [],
      typeBounds := [],
      typeParams := [],
      fieldReads := #[],
      fieldSites := #[],
      fieldTable := #[],
      calls := #[],
      instRows := [],
      unrunGiven := #[],
      sharedEdges := {},
      assumedLinks := #[],
      abandoned := #[],
      sure := {},
      lowerChecks := #[],
      refusals := #[],
      runFns := {},
      runCtors := {},
      runAliases := {},
      runOps := {},
      runExact := {},
      runNow := {},
      rowIncl := #[],
      types := {},
      ctors := {},
      ops := [],
      effects := [],
      aliases := {},
      fns := {},
      pending := #[],
      projections := #[],
      namedReads := #[],
      blockCaps := #[],
      given := #[],
      unrun := #[],
      coercing := [],
      coercions := #[],
      loans := {},
      cells := #[],
      bindSites := [],
      leftBehind := #[],
      takenApart := #[],
      partReads := #[],
      uses := #[],
      heldMoves := #[],
      traits := [],
      methods := {},
      kimpls := {},
      blanketTraits := [],
      instSites := #[],
      siteTable := [],
      siteTypes := [],
      bounds := #[],
      groupUses := #[],
      rigidKeys := {},
      rigidAt := {},
      conditionsAt := {},
      dropCands := #[],
      unsafeFns := [],
      dropSites := #[],
      lateKeeps := #[],
      quiets := #[],
      paramTraits := [],
      gatOccs := #[],
      gatHolds := #[],
      dictTable := #[],
      methodCalls := #[],
      fnBounds := [],
      impls := #[],
      fnBodies := {},
      assocUses := #[],
      solvedFit := {}, leavesFit := {}, leavesAt := {}, tyIds := {}, tyIdCount := 0,
      tyMemo := {}, dictShared := {}, modules := {}, body := {}, blockRoots := {}, blockRootsAt := 0 }
    implsStart := p.impls.size
    assocUses := ← Delta.diff p.assocUses b.assocUses
    part0 := ← diffPart0 p b
    part1 := ← diffPart1 p b
    part2 := ← diffPart2 p b
    part3 := ← diffPart3 p b
    part4 := ← diffPart4 p b
    part5 := ← diffPart5 p b
    part6 := ← diffPart6 p b
    part7 := ← diffPart7 p b
    part8 := ← diffPart8 p b
    part9 := ← diffPart9 p b }

/-- `d` put on `a`: the state after checking what made `d` after what made
`a`. `p`, where it is at hand, is the state both went on from. None where
both changed one thing that cannot be put together. -/
def applyDelta (p : Option St) (a : St) (d : StDelta) : Option St := do
  if let some p := p then
    unless samePtr a.modules p.modules do none
    unless samePtr a.dropMode p.dropMode do none
  let b := d.rest
  -- (An implementation's place: what `d` declared comes after what `a` did.)
  let shift := a.impls.size - d.implsStart
  let implsByBase := b.implsByBase.fold (init := a.implsByBase) fun m key is =>
    let mine := (is.filter (· ≥ d.implsStart)).map (· + shift)
    if mine.isEmpty then m else m.insert key ((m.getD key #[]) ++ mine)
  let implsByHead := b.implsByHead.fold (init := a.implsByHead) fun m key is =>
    let mine := (is.filter (· ≥ d.implsStart)).map (· + shift)
    if mine.isEmpty then m else m.insert key ((m.getD key #[]) ++ mine)
  -- (Emptied as each group's are gone through: empty if both left it so.)
  let left := match d.assocUses with
    | .grown _ tail => tail.isEmpty
    | .whole all => all.isEmpty
  let assocUses ← if a.assocUses.isEmpty && left then pure #[] else Delta.apply (p.map (·.assocUses)) a.assocUses d.assocUses
  -- (The parts put together on `a`, then the rest as `d` left it.)
  let mut s := a
  s ← applyPart0 p s d.part0
  s ← applyPart1 p s d.part1
  s ← applyPart2 p s d.part2
  s ← applyPart3 p s d.part3
  s ← applyPart4 p s d.part4
  s ← applyPart5 p s d.part5
  s ← applyPart6 p s d.part6
  s ← applyPart7 p s d.part7
  s ← applyPart8 p s d.part8
  s ← applyPart9 p s d.part9
  pure { b with
    tys := s.tys,
    rows := s.rows,
    mono := s.mono,
    monoRows := s.monoRows,
    monoCaps := s.monoCaps,
    caps := s.caps,
    capEdges := s.capEdges,
    capOut := s.capOut,
    capEdgeNames := s.capEdgeNames,
    dups := s.dups,
    lateDups := s.lateDups,
    drops := s.drops,
    lateDrops := s.lateDrops,
    stays := s.stays,
    lateStays := s.lateStays,
    statics := s.statics,
    pendingCopies := s.pendingCopies,
    useDecls := s.useDecls,
    movedCells := s.movedCells,
    flagged := s.flagged,
    givenSites := s.givenSites,
    givenEdges := s.givenEdges,
    givers := s.givers,
    givenReads := s.givenReads,
    aparts := s.aparts,
    fieldNames := s.fieldNames,
    dotChosen := s.dotChosen,
    argsChosen := s.argsChosen,
    decided := s.decided,
    traitShape := s.traitShape,
    writtenArgs := s.writtenArgs,
    supers := s.supers,
    ranked := s.ranked,
    packs := s.packs,
    envGroups := s.envGroups,
    envAfter := s.envAfter,
    envLent := s.envLent,
    fnGroups := s.fnGroups,
    fnRunsIn := s.fnRunsIn,
    bindLoans := s.bindLoans,
    envBlocks := s.envBlocks,
    inPlace := s.inPlace,
    envMust := s.envMust,
    envHeld := s.envHeld,
    derefReads := s.derefReads,
    rowChecks := s.rowChecks,
    typeBounds := s.typeBounds,
    typeParams := s.typeParams,
    fieldReads := s.fieldReads,
    fieldSites := s.fieldSites,
    fieldTable := s.fieldTable,
    calls := s.calls,
    instRows := s.instRows,
    unrunGiven := s.unrunGiven,
    sharedEdges := s.sharedEdges,
    assumedLinks := s.assumedLinks,
    abandoned := s.abandoned,
    sure := s.sure,
    lowerChecks := s.lowerChecks,
    refusals := s.refusals,
    runFns := s.runFns,
    runCtors := s.runCtors,
    runAliases := s.runAliases,
    runOps := s.runOps,
    runExact := s.runExact,
    runNow := s.runNow,
    rowIncl := s.rowIncl,
    types := s.types,
    ctors := s.ctors,
    ops := s.ops,
    effects := s.effects,
    aliases := s.aliases,
    fns := s.fns,
    pending := s.pending,
    projections := s.projections,
    namedReads := s.namedReads,
    blockCaps := s.blockCaps,
    given := s.given,
    unrun := s.unrun,
    coercing := s.coercing,
    coercions := s.coercions,
    loans := s.loans,
    cells := s.cells,
    bindSites := s.bindSites,
    leftBehind := s.leftBehind,
    takenApart := s.takenApart,
    partReads := s.partReads,
    uses := s.uses,
    heldMoves := s.heldMoves,
    traits := s.traits,
    methods := s.methods,
    kimpls := s.kimpls,
    blanketTraits := s.blanketTraits,
    instSites := s.instSites,
    siteTable := s.siteTable,
    siteTypes := s.siteTypes,
    bounds := s.bounds,
    groupUses := s.groupUses,
    rigidKeys := s.rigidKeys,
    rigidAt := s.rigidAt,
    conditionsAt := s.conditionsAt,
    dropCands := s.dropCands,
    unsafeFns := s.unsafeFns,
    dropSites := s.dropSites,
    lateKeeps := s.lateKeeps,
    quiets := s.quiets,
    paramTraits := s.paramTraits,
    gatOccs := s.gatOccs,
    gatHolds := s.gatHolds,
    dictTable := s.dictTable,
    methodCalls := s.methodCalls,
    fnBounds := s.fnBounds,
    impls := s.impls,
    fnBodies := s.fnBodies,
    assocUses,
    brands := max a.brands b.brands, anyMust := a.anyMust || b.anyMust, modules := a.modules,
    shapes := a.shapes || b.shapes, patterned := a.patterned || b.patterned, dropMode := a.dropMode,
    dropAsked := max a.dropAsked b.dropAsked, implsByBase, implsByHead,
    at_ := (p.map (·.at_)).getD a.at_,
    -- (Found again from the block captures put together.)
    blockRoots := {}, blockRootsAt := 0 }


/-- The state after checking `b`'s units after `a`'s, both having gone on
from `p`, where it can be put together from what each added. -/
def mergeStates (p a b : St) : Option St := do
  applyDelta (some p) a (← diffStates p b)

end Glorious.Check
