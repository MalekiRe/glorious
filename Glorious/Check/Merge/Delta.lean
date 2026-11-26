module

public import Glorious.Check.Types
meta import Lean.Parser.Command

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

A check changes nothing it began with (a signature is not changed by a
body, a capture made before a group is put back when it is done,
`St.capUndo`): where one did, there is no delta, and what it checked is
checked again after the others, or not kept. A list may grow at an entry
that was there (`MapLD`). Where the other state is at hand (`p`, side by
side) what it changed is told by whether an entry is the same object. -/

unsafe def samePtrImpl {α : Type} (a b : α) : Bool := ptrAddrUnsafe a == ptrAddrUnsafe b

/-- Are these the same object? (Taken to be not, where that cannot be asked.) -/
@[implemented_by samePtrImpl] def samePtr {α : Type} (_ _ : α) : Bool := false

/-- What a check did to a store: segments of its own, and entries pushed onto
a segment that was there (its start, how many it had, and those). -/
structure StoreD (α : Type) where
  segs : Array (Seg α) := #[]
  grown : Array (Nat × Nat × Array α) := #[]

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

/-- What a check did to a map: each entry it made. -/
abbrev MapD (κ ν : Type) := Array (κ × ν)

/-- What a check did to a map of lists: each list it made or grew. -/
abbrev MapLD (κ ν : Type) := Array (κ × Option (List ν) × ListD ν)

/-- How what a check did to one part of the state is found (`diff`, from
what it began with), and put on another (`apply`; `p`, where it is at hand,
the state it began with too). -/
class Delta (α : Type) (δ : outParam Type) where
  diff : α → α → Option δ
  apply : Option α → α → δ → Option α
  /-- Would `apply` put it on: read only, so that it can be put on in place
  after, the value held once. -/
  fits : Option α → α → δ → Bool

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
        -- (Most are the same object: nothing changed in them.)
        if samePtr sb sp then continue
        if sb.count < sp.count then none
        -- (One it began with, changed: no delta.)
        for c in [0:sb.pieces.size] do
          let pb := sb.pieces.getD c #[]
          let pp := sp.pieces.getD c #[]
          unless samePtr pb pp do
            for j in [0:min pb.size pp.size] do
              match pb[j]?, pp[j]? with
              | some x, some z => unless samePtr x z do none
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

def apply (a : Store α) (d : StoreD α) : Option (Store α) := do
  if d.segs.isEmpty && d.grown.isEmpty then return a
  -- (Mostly segments of its own, after all of `a`'s: put after them, the
  -- rest of `a` let be.)
  -- (What it pushed onto `a`'s last segment, begun with as many: pushed.)
  let onLast := d.grown.foldl (init := some a) fun st (base, before, pushed) => st.bind fun st =>
    if base == st.last.base && st.last.count == before then some { st with last := pushed.foldl Seg.push st.last }
    else none
  let after := d.segs.foldl (init := onLast) fun st s => st.bind fun st =>
    if s.base == st.last.base && st.last.count == 0 then some { st with last := s }
    else if s.base ≥ st.last.base + st.last.count && s.base > st.last.base then
      some (if st.last.count == 0 then { st with last := s } else { older := st.older.push st.last, last := s })
    else none
  if let some st := after then return st
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
  pure (match kept.back? with
    | some last => { older := kept.pop, last }
    | none => {})

end StoreD

/-- Would `apply` put `d` on `a`: where only its last segment grows and new
ones come after, by where each starts and how many it has; else tried. -/
def StoreD.fits {α : Type} (a : Store α) (d : StoreD α) : Bool := Id.run do
  if d.segs.isEmpty && d.grown.isEmpty then return true
  let mut base := a.last.base
  let mut count := a.last.count
  let mut quick := true
  for (b, before, pushed) in d.grown do
    if b == base && count == before then count := count + pushed.size
    else quick := false
  if quick then
    for s in d.segs do
      if s.base == base && count == 0 then
        base := s.base
        count := s.count
      else if s.base ≥ base + count && s.base > base then
        base := s.base
        count := s.count
      else quick := false
    if quick then return true
  return (StoreD.apply a d).isSome

instance {α : Type} : Delta (Store α) (StoreD α) where
  diff := StoreD.diff
  apply _ a d := StoreD.apply a d
  fits _ a d := StoreD.fits a d

/-- Does `b` go on from `p`: its first entries `p`'s? -/
def extendsArr {α : Type} (p b : Array α) : Bool := Id.run do
  if b.size < p.size then return false
  for i in [0:p.size] do
    match b[i]?, p[i]? with
    | some x, some z => unless samePtr x z do return false
    | _, _ => return false
  pure true

/-- The entries `b` has in front of `p`, where `b` is `p` with entries put
in front: found by going down `b` until what is left is `p`. -/
def frontOf {α : Type} (p b : List α) : Option (List α) :=
  let rec go (acc : List α) (l : List α) : Option (List α) :=
    if samePtr l p then some acc.reverse else
    match l with
    | [] => none
    | x :: more => go (x :: acc) more
  go [] b

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
  fits p a
    | .grown _ tail => tail.isEmpty || match p with
      | some p => samePtr a p || extendsArr p a
      | none => true
    | .whole _ => match p with
      | some p => samePtr a p
      | none => true

/-- Does `b` go on from `p` at its end? -/
def extendsList {α : Type} (p b : List α) : Bool :=
  b.length ≥ p.length && ((b.take p.length).zip p).all fun (x, z) => samePtr x z

instance {α : Type} : Delta (List α) (ListD α) where
  diff p b :=
    if samePtr p b then some (.front [])
    else match frontOf p b with
      | some xs => some (.front xs)
      | none =>
        let lp := p.length
        if extendsList p b then some (.back lp (b.drop lp))
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
  fits p a
    | .front [] => true
    | .front _ => match p with
      | some p =>
        let la := a.length
        samePtr a p || (la ≥ p.length && samePtr (a.drop (la - p.length)) p) || extendsList p a
      | none => true
    | .back _ [] => true
    | .back _ _ => match p with
      | some p => samePtr a p || extendsList p a
      | none => true
    | .whole _ => match p with
      | some p => samePtr a p
      | none => true

/-- The entries of `b` in the buckets it changed of `p`'s, where it has as many
buckets: a bucket not changed is the same object. -/
def changedEntries {κ ν : Type} [BEq κ] [Hashable κ] (p b : Std.HashMap κ ν) : Option (List (κ × ν)) :=
  let pb := p.inner.1.buckets
  let bb := b.inner.1.buckets
  if pb.size != bb.size then none else Id.run do
    let mut acc : List (κ × ν) := []
    for i in [0:bb.size] do
      match bb[i]?, pb[i]? with
      | some bl, some pl => unless samePtr bl pl do acc := bl.toList.foldl (fun acc e => (e.1, e.2) :: acc) acc
      | _, _ => pure ()
    pure (some acc)

/-- The entries of `b` that are not `p`'s, with what `p` had there. -/
def newEntries {κ ν : Type} [BEq κ] [Hashable κ] (p b : Std.HashMap κ ν) : List (κ × ν × Option ν) :=
  let es := match changedEntries p b with
    | some es => es
    | none => b.toList
  es.filterMap fun (k, v) => match p.get? k with
    | some pv => if samePtr pv v then none else some (k, v, some pv)
    | none => some (k, v, none)

instance (priority := low) {κ ν : Type} [BEq κ] [Hashable κ] : Delta (Std.HashMap κ ν) (MapD κ ν) where
  -- (One it began with, changed: no delta.)
  diff p b := if samePtr p b then some #[] else
    (newEntries p b).toArray.mapM fun (k, v, was) => if was.isSome then none else some (k, v)
  -- (Made by both: the same, as both took it from what is the same.)
  apply _ a d := d.foldlM (init := a) fun m (k, v) =>
    match m.get? k with
    | some cur => if samePtr cur v then some m else none
    | none => some (m.insert k v)
  fits _ a d := d.all fun (k, v) =>
    match a.get? k with
    | some cur => samePtr cur v
    | none => true

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
  fits p a d := d.all fun (k, was, ld) =>
    match was, a.get? k with
    | some pv, some cur => Delta.fits (p.map fun _ => pv) cur ld
    | none, some _ => match ld with
      | .whole _ => true
      | _ => false
    | none, none => match ld with
      | .whole _ => true
      | _ => false
    | some _, none => false

instance {κ : Type} [BEq κ] [Hashable κ] : Delta (Std.HashSet κ) (Array κ) where
  diff p b := if samePtr p b then some #[] else
    let es : List κ := match changedEntries p.inner b.inner with
      | some es => es.map fun (k, _) => k
      | none => b.toList
    some (es.filter (!p.contains ·)).toArray
  apply _ a d := some (d.foldl (·.insert ·) a)
  fits _ _ _ := true

instance : Delta (Traits.ImplIndex Syntax.TraitKey) (Array (Traits.Impl Syntax.TraitKey)) where
  diff p b :=
    if samePtr p b then some #[]
    else if extendsArr p.impls b.impls then some (b.impls.extract p.impls.size b.impls.size)
    else none
  apply p a d :=
    if d.isEmpty then some a else
    match p with
    | some p => if samePtr a p || extendsArr p.impls a.impls then some (.ofArray (a.impls ++ d)) else none
    | none => some (.ofArray (a.impls ++ d))
  fits p a d := d.isEmpty || match p with
    | some p => samePtr a p || extendsArr p.impls a.impls
    | none => true

/-- Of a map to implementations by their places, the places from `start` on. -/
def ownImpls {κ : Type} [BEq κ] [Hashable κ] (start : Nat) (m : Std.HashMap κ (Array Nat)) : Std.HashMap κ (Array Nat) :=
  m.fold (init := {}) fun acc k is =>
    let mine := is.filter (· ≥ start)
    if mine.isEmpty then acc else acc.insert k mine

/-- `delta_part StDeltaN diffPartN applyPartN fitsPartN clearPartN restorePartN
[field : D, ..]`: a part of `StDelta`, those fields of `St` each its delta `D`
(`Delta`); what a check added to each (`diffPartN`), it put on another state
(`applyPartN`: each field taken out of the state first, so that it is held
once while the delta is put on it, in place, not copied), whether that would
go (`fitsPartN`, read only), the state with them empty (`clearPartN`) and with
them another's (`restorePartN`). -/
syntax "delta_part " ident ident ident ident ident ident " [" sepBy1(ident " : " term, ", ") "]" : command

open Lean in
macro_rules
  | `(delta_part $S $diff $apply $fits $clear $restore [ $[$fs : $ts],* ]) => do
    -- (The names bound here are written as the fields are reached through
    -- them, `p.tys`: unhygienic, both.)
    let (pI, bI, aI, dI, sI) := (mkIdent `p, mkIdent `b, mkIdent `a, mkIdent `d, mkIdent `s)
    let proj := fun (x : Name) (f : TSyntax `ident) => mkIdent (x ++ f.getId)
    let mk := mkIdent (S.getId ++ `mk)
    let diffs ← fs.mapM fun f => `((← Delta.diff $(proj `p f) $(proj `b f)))
    let set := fun (acc : TSyntax `term) (f : TSyntax `ident) (v : TSyntax `term) => `({ $acc with $f:ident := $v })
    let cleared ← fs.foldlM (fun acc f => do set acc f (← `({}))) aI
    let put ← fs.foldlM (fun acc f => do
      set acc f (← `(← Delta.apply (Option.map (fun $sI => $(proj `s f)) $pI) $f $(proj `d f)))) aI
    let back ← fs.foldlM (fun acc f => set acc f (proj `s f)) bI
    let fitsEach ← fs.mapM fun f => `(Delta.fits (Option.map (fun $sI => $(proj `s f)) $pI) $(proj `a f) $(proj `d f))
    let fitsAll ← fitsEach[1:].foldlM (fun acc x => `($acc && $x)) fitsEach[0]!
    let tuple := fun (xs : Array (TSyntax `term)) => (do
      let mut acc := xs.back!
      for x in xs.pop.reverse do acc ← `(($x, $acc))
      pure acc : MacroM (TSyntax `term))
    let taken ← tuple (fs.map fun f => ⟨f.raw⟩)
    let projs ← tuple (fs.map fun f => ⟨(proj `a f).raw⟩)
    let fields ← (fs.zip ts).mapM fun (f, t) => `(Lean.Parser.Command.structExplicitBinder| ($f:ident : $t))
    `(structure $S where
        $[$fields]*
      def $diff ($pI $bI : St) : Option $S := do
        pure ($mk $diffs*)
      def $apply ($pI : Option St) ($aI : St) ($dI : $S) : Option St := do
        let $taken:term := $projs
        let $aI := $cleared
        pure $put
      def $fits ($pI : Option St) ($aI : St) ($dI : $S) : Bool := $fitsAll
      def $clear ($aI : St) : St := $cleared
      def $restore ($bI $sI : St) : St := $back)

end Glorious.Check
