module

public import Glorious.Check.Expr

public section

namespace Glorious.Check

open Syntax

/-! ## Two checks that went on from one state, put together

Units that do not use each other are checked side by side, each from the
state after the units before them, its ids numbered from a place of its own
(`Store.jumpTo`). What each added is put together here, as if one had been
checked after the other. What both changed of what was there before, or
anything not made by adding, is not put together (none): the units are then
checked one after another. -/

unsafe def samePtrImpl {α : Type} (a b : α) : Bool := ptrAddrUnsafe a == ptrAddrUnsafe b

/-- Are these the same object? (Taken to be not, where that cannot be asked.) -/
@[implemented_by samePtrImpl] def samePtr {α : Type} (_ _ : α) : Bool := false

/-- Two lists grown from `p`, by adding in front or at the end. -/
def mergeList {α : Type} (p a b : List α) : Option (List α) :=
  if samePtr a p then some b else if samePtr b p then some a else
  let lp := p.length
  let la := a.length
  let lb := b.length
  if la < lp || lb < lp then none
  else if samePtr (a.drop (la - lp)) p && samePtr (b.drop (lb - lp)) p then some (b.take (lb - lp) ++ a)
  else if ((a.take lp).zip p).all (fun (x, y) => samePtr x y) && ((b.take lp).zip p).all (fun (x, y) => samePtr x y) then
    some (a ++ b.drop lp)
  else none

/-- Two arrays grown from `p` at the end. -/
def mergeArr {α : Type} (p a b : Array α) : Option (Array α) :=
  if samePtr a p then some b else if samePtr b p then some a else
  let lp := p.size
  if a.size < lp || b.size < lp then none
  else if (List.range lp).all (fun i => match a[i]?, b[i]?, p[i]? with
      | some x, some y, some z => samePtr x z && samePtr y z
      | _, _, _ => false) then
    some (a ++ b.extract lp b.size)
  else none

/-- Two segments grown from `p`: each piece changed by at most one of them. -/
def mergeSeg {α : Type} (p a b : Seg α) (same : α → α → Bool := fun _ _ => false) : Option (Seg α) := do
  if samePtr a p then return b
  if samePtr b p then return a
  let mut out : Array (Array α) := #[]
  for i in [0:max a.pieces.size b.pieces.size] do
    let pa := a.pieces.getD i #[]
    let pb := b.pieces.getD i #[]
    let pp := p.pieces.getD i #[]
    if samePtr pb pp || pb.isEmpty then out := out.push pa
    else if samePtr pa pp || pa.isEmpty then out := out.push pb
    else
      -- (Each entry changed by at most one of them.)
      let mut piece : Array α := #[]
      for k in [0:max pa.size pb.size] do
        match pa[k]?, pb[k]?, pp[k]? with
        | some x, some y, some z =>
          if samePtr y z then piece := piece.push x
          else if samePtr x z then piece := piece.push y
          -- (Both made it the same: as for a variable both bound alike.)
          else if same x y then piece := piece.push x
          else none
        | some x, none, _ => piece := piece.push x
        | none, some y, _ => piece := piece.push y
        | some _, some _, none => none
        | none, none, _ => pure ()
      out := out.push piece
  pure { base := p.base, pieces := out, count := max a.count b.count }

/-- Two stores grown from `p`: segments by where they start, each changed by
at most one of them, or with pieces changed by at most one; and what each
began of its own. -/
def mergeStore {α : Type} (p a b : Store α) (same : α → α → Bool := fun _ _ => false) : Option (Store α) := do
  if samePtr a p then return b
  if samePtr b p then return a
  let ps := p.segs
  let as := a.segs
  let bs := b.segs
  let mut out : Array (Seg α) := Array.mkEmpty (as.size + bs.size)
  let mut i := 0
  let mut j := 0
  let mut k := 0
  -- (In the order of where they start, all three: each segment of `p` is
  -- in both, but one begun with nothing in it, which one that jumped left
  -- for a segment of its own, as if it were still there.)
  while i < as.size || j < bs.size do
    let ba := (as[i]?.map (·.base)).getD (bs[j]?.map (·.base) |>.getD 0)
    let bb := (bs[j]?.map (·.base)).getD ba
    let base := min (if i < as.size then ba else bb) (if j < bs.size then bb else ba)
    while k < ps.size && ((ps[k]?.map (·.base)).getD 0) < base do k := k + 1
    let sp := (ps[k]?).filter (·.base == base)
    let sa := (as[i]?).filter (·.base == base)
    let sb := (bs[j]?).filter (·.base == base)
    if sa.isSome then i := i + 1
    if sb.isSome then j := j + 1
    let empty := sp.filter (·.count == 0)
    match sp, sa.orElse fun _ => empty, sb.orElse fun _ => empty with
    | some sp, some sa, some sb => out := out.push (← mergeSeg sp sa sb same)
    | none, some sa, none => out := out.push sa
    | none, none, some sb => out := out.push sb
    | _, _, _ => none
  match out.back? with
  | some last => pure { older := out.pop, last }
  | none => pure {}

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

/-- Two maps grown from `p`: an entry changed by at most one of them. -/
def mergeMap {κ ν : Type} [BEq κ] [Hashable κ] (p a b : Std.HashMap κ ν) : Option (Std.HashMap κ ν) :=
  if samePtr a p then some b else if samePtr b p then some a else
  let step := fun (acc : Option (Std.HashMap κ ν)) (key : κ) (val : ν) => acc.bind fun m =>
    match p.get? key, a.get? key with
    | some pv, some av =>
      if samePtr val pv then some m else if samePtr av pv then some (m.insert key val) else none
    | some _, none => none
    | none, some av => if samePtr av val then some m else none
    | none, none => some (m.insert key val)
  match changedEntries p b with
  | some es => es.foldl (fun acc (k, v) => step acc k v) (some a)
  | none => b.fold (init := some a) step

/-- Two sets grown from `p`. -/
def mergeSet {κ : Type} [BEq κ] [Hashable κ] (p a b : Std.HashSet κ) : Option (Std.HashSet κ) :=
  if samePtr a p then some b else if samePtr b p then some a else
  match changedEntries p.inner b.inner with
  | some es => some (es.foldl (fun m (x, _) => m.insert x) a)
  | none => some (b.fold (init := a) fun m x => m.insert x)

/-- How a part of the state grown by two checks from one is put together. -/
class Merge3 (α : Type) where
  merge3 : α → α → α → Option α

instance {α : Type} : Merge3 (List α) := ⟨mergeList⟩
instance {α : Type} : Merge3 (Array α) := ⟨mergeArr⟩
instance (priority := low) {α : Type} : Merge3 (Store α) := ⟨fun p a b => mergeStore p a b⟩
/-- (A type variable both bound to the same type, written alike with nothing
unknown in it.) -/
instance : Merge3 (Store (Option Ty)) := ⟨fun p a b => mergeStore p a b fun
  | some x, some y => let s := showTy x; s == showTy y && !s.contains '?'
  | _, _ => false⟩
instance (priority := low) {κ ν : Type} [BEq κ] [Hashable κ] : Merge3 (Std.HashMap κ ν) := ⟨mergeMap⟩
/-- (A row variable both bound to the same effects, with no row after.) -/
instance : Merge3 (Store (Option Row)) := ⟨fun p a b => mergeStore p a b fun
  | some x, some y => x.tail.isNone && y.tail.isNone && showEffs x.effs == showEffs y.effs && !(showEffs x.effs).contains '?'
  | _, _ => false⟩
/-- (A list under a key, grown by both: the two grown together.) -/
instance {κ ν : Type} [BEq κ] [Hashable κ] : Merge3 (Std.HashMap κ (List ν)) where
  merge3 p a b :=
    if samePtr a p then some b else if samePtr b p then some a else
    let step := fun (acc : Option (Std.HashMap κ (List ν))) (key : κ) (val : List ν) => acc.bind fun m =>
      match p.get? key, a.get? key with
      | some pv, some av =>
        if samePtr val pv then some m else if samePtr av pv then some (m.insert key val)
        else (mergeList pv av val).map (m.insert key ·)
      | some _, none => none
      | none, some av => (mergeList [] av val).map (m.insert key ·)
      | none, none => some (m.insert key val)
    match changedEntries p b with
    | some es => es.foldl (fun acc (k, v) => step acc k v) (some a)
    | none => b.fold (init := some a) step
instance {κ : Type} [BEq κ] [Hashable κ] : Merge3 (Std.HashSet κ) := ⟨mergeSet⟩
/-- Two persistent maps grown from `p`: an entry changed by at most one of them. -/
def mergePMap {κ ν : Type} [BEq κ] [Hashable κ] (p a b : PMap κ ν) : Option (PMap κ ν) :=
  if samePtr a p then some b else if samePtr b p then some a else
  b.fold (init := some a) fun acc key val => acc.bind fun m =>
    match p.get? key, a.get? key with
    | some pv, some av =>
      if samePtr val pv then some m else if samePtr av pv then some (m.insert key val) else none
    | some _, none => none
    | none, some av => if samePtr av val then some m else none
    | none, none => some (m.insert key val)
instance {κ ν : Type} [BEq κ] [Hashable κ] : Merge3 (PMap κ ν) := ⟨mergePMap⟩
instance : Merge3 Traits.ImplIndex where
  merge3 p a b := do
    if samePtr a p then return b
    if samePtr b p then return a
    pure (.ofArray (← mergeArr p.impls a.impls b.impls))

/-- The state after checking `b`'s units after `a`'s, both having gone on
from `p`, where it can be put together from what each added: what both grew
put together (`Merge3`); what says where the check is, `b`'s. -/
def mergeStates (p a b : St) : Option St := do
  unless samePtr a.modules b.modules || samePtr a.modules p.modules || samePtr b.modules p.modules do none
  unless samePtr a.dropMode b.dropMode || samePtr a.dropMode p.dropMode || samePtr b.dropMode p.dropMode do none
  -- (An implementation's place: `b`'s come after `a`'s.)
  let shift := a.impls.size - p.impls.size
  let implsByBase := b.implsByBase.fold (init := a.implsByBase) fun m key is =>
    let mine := (is.filter (· ≥ p.impls.size)).map (· + shift)
    if mine.isEmpty then m else m.insert key ((m.getD key #[]) ++ mine)
  let implsByHead := b.implsByHead.fold (init := a.implsByHead) fun m key is =>
    let mine := (is.filter (· ≥ p.impls.size)).map (· + shift)
    if mine.isEmpty then m else m.insert key ((m.getD key #[]) ++ mine)
  let m3 := fun {α : Type} [Merge3 α] (f : St → α) => Merge3.merge3 (f p) (f a) (f b)
  pure { b with
    tys := ← m3 (·.tys), rows := ← m3 (·.rows), mono := ← m3 (·.mono),
    monoRows := ← m3 (·.monoRows), monoCaps := ← m3 (·.monoCaps), caps := ← m3 (·.caps),
    capEdges := ← m3 (·.capEdges), capOut := ← m3 (·.capOut),
    capEdgeNames := ← m3 (·.capEdgeNames), dups := ← m3 (·.dups), lateDups := ← m3 (·.lateDups),
    drops := ← m3 (·.drops), lateDrops := ← m3 (·.lateDrops), stays := ← m3 (·.stays),
    lateStays := ← m3 (·.lateStays), statics := ← m3 (·.statics), useDecls := ← m3 (·.useDecls),
    movedCells := ← m3 (·.movedCells), flagged := ← m3 (·.flagged),
    givenSites := ← m3 (·.givenSites), givenEdges := ← m3 (·.givenEdges),
    givers := ← m3 (·.givers), givenReads := ← m3 (·.givenReads), aparts := ← m3 (·.aparts),
    fieldNames := ← m3 (·.fieldNames), dotChosen := ← m3 (·.dotChosen),
    argsChosen := ← m3 (·.argsChosen), decided := ← m3 (·.decided),
    traitShape := ← m3 (·.traitShape), assocUses := ← (if a.assocUses.isEmpty && b.assocUses.isEmpty then some #[] else m3 (·.assocUses)),
    writtenArgs := ← m3 (·.writtenArgs), supers := ← m3 (·.supers), ranked := ← m3 (·.ranked),
    packs := ← m3 (·.packs), envGroups := ← m3 (·.envGroups), envAfter := ← m3 (·.envAfter),
    envLent := ← m3 (·.envLent), fnGroups := ← m3 (·.fnGroups), fnRunsIn := ← m3 (·.fnRunsIn), bindLoans := ← m3 (·.bindLoans),
    envBlocks := ← m3 (·.envBlocks), inPlace := ← m3 (·.inPlace), envMust := ← m3 (·.envMust),
    envHeld := ← m3 (·.envHeld), derefReads := ← m3 (·.derefReads),
    rowChecks := ← m3 (·.rowChecks), typeBounds := ← m3 (·.typeBounds),
    typeParams := ← m3 (·.typeParams), fieldReads := ← m3 (·.fieldReads),
    fieldSites := ← m3 (·.fieldSites), fieldTable := ← m3 (·.fieldTable), calls := ← m3 (·.calls),
    instRows := ← m3 (·.instRows), unrunGiven := ← m3 (·.unrunGiven),
    sharedEdges := ← m3 (·.sharedEdges), assumedLinks := ← m3 (·.assumedLinks),
    abandoned := ← m3 (·.abandoned), sure := ← m3 (·.sure), lowerChecks := ← m3 (·.lowerChecks),
    refusals := ← m3 (·.refusals), runFns := ← m3 (·.runFns), runCtors := ← m3 (·.runCtors),
    runAliases := ← m3 (·.runAliases), runOps := ← m3 (·.runOps), runExact := ← m3 (·.runExact),
    runNow := ← m3 (·.runNow), rowIncl := ← m3 (·.rowIncl), types := ← m3 (·.types),
    ctors := ← m3 (·.ctors), ops := ← m3 (·.ops), effects := ← m3 (·.effects),
    aliases := ← m3 (·.aliases), fns := ← m3 (·.fns), pending := ← m3 (·.pending),
    projections := ← m3 (·.projections), namedReads := ← m3 (·.namedReads),
    blockCaps := ← m3 (·.blockCaps), given := ← m3 (·.given), unrun := ← m3 (·.unrun),
    coercing := ← m3 (·.coercing), coercions := ← m3 (·.coercions), loans := ← m3 (·.loans),
    cells := ← m3 (·.cells), bindSites := ← m3 (·.bindSites), leftBehind := ← m3 (·.leftBehind),
    takenApart := ← m3 (·.takenApart), partReads := ← m3 (·.partReads), uses := ← m3 (·.uses),
    heldMoves := ← m3 (·.heldMoves), traits := ← m3 (·.traits), methods := ← m3 (·.methods),
    kimpls := ← m3 (·.kimpls), blanketTraits := ← m3 (·.blanketTraits),
    instSites := ← m3 (·.instSites), siteTable := ← m3 (·.siteTable),
    siteTypes := ← m3 (·.siteTypes), bounds := ← m3 (·.bounds), groupUses := ← m3 (·.groupUses),
    rigidKeys := ← m3 (·.rigidKeys), rigidAt := ← m3 (·.rigidAt),
    conditionsAt := ← m3 (·.conditionsAt), dropCands := ← m3 (·.dropCands),
    unsafeFns := ← m3 (·.unsafeFns), dropSites := ← m3 (·.dropSites),
    lateKeeps := ← m3 (·.lateKeeps), quiets := ← m3 (·.quiets),
    paramTraits := ← m3 (·.paramTraits), gatOccs := ← m3 (·.gatOccs),
    gatHolds := ← m3 (·.gatHolds), dictTable := ← m3 (·.dictTable),
    methodCalls := ← m3 (·.methodCalls), fnBounds := ← m3 (·.fnBounds), impls := ← m3 (·.impls),
    brands := max a.brands b.brands, anyMust := a.anyMust || b.anyMust, modules := a.modules,
    shapes := a.shapes || b.shapes, patterned := a.patterned || b.patterned, dropMode := a.dropMode,
    dropAsked := max a.dropAsked b.dropAsked, implsByBase, implsByHead, at_ := p.at_,
    -- (Found again from the block captures put together.)
    blockRoots := {}, blockRootsAt := 0 }

end Glorious.Check
