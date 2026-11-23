module

public import Glorious.Check.Expr
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

/-- (Written alike, all it holds: its variables, captures and reasons too.) -/
partial def tyEq : Ty → Ty → Bool
  | .var a, .var b => a == b
  | .con n as, .con m bs => n == m && listEq as bs
  | .tuple as, .tuple bs => listEq as bs
  | .fn ps r es t c, .fn qs s fs u d =>
    listEq ps qs && tyEq r s && t == u && c == d && es.length == fs.length
      && (es.zip fs).all fun ((n, as), (m, bs)) => n == m && listEq as bs
  | .ref h t c, .ref h' t' c' => tyEq h h' && tyEq t t' && c == c'
  | _, _ => false
where
  listEq (as bs : List Ty) : Bool := as.length == bs.length && (as.zip bs).all fun (a, b) => tyEq a b

def capturedEq : Captured → Captured → Bool
  | .brand a, .brand b => a == b
  | .ty a, .ty b => tyEq a b
  | .once, .once => true
  | .must, .must => true
  | .loan a, .loan b => a == b
  | .touch a w, .touch b v => a == b && w == v
  | .inner a, .inner b => a == b
  | _, _ => false

def schemeEq (a b : Scheme) : Bool :=
  let tys := fun (xs ys : List Ty) => tyEq.listEq xs ys
  let why := fun (xs ys : List (Ty × String)) => xs.length == ys.length && (xs.zip ys).all fun ((t, w), (u, v)) => w == v && tyEq t u
  a.tvars == b.tvars && a.rvars == b.rvars && a.cvars == b.cvars && tyEq a.ty b.ty
    && a.edges.length == b.edges.length && (a.edges.zip b.edges).all (fun ((n, c), (m, d)) => n == m && capturedEq c d)
    && why a.dups b.dups && why a.drops b.drops && why a.stays b.stays && why a.statics b.statics && why a.quiets b.quiets
    && tys a.sites b.sites && a.ranked == b.ranked
    && a.bounds.length == b.bounds.length && (a.bounds.zip b.bounds).all (fun ((n, t), (m, u)) => n == m && tyEq t u)
    && a.assocs.length == b.assocs.length
    && (a.assocs.zip b.assocs).all (fun ((n, t, k, u), (m, t', k', u')) => n == m && k == k' && tyEq t t' && tyEq u u')
    && a.incls.length == b.incls.length && (a.incls.zip b.incls).all (fun ((t, u), (t', u')) => tyEq t t' && tyEq u u')

instance : BEq Scheme := ⟨schemeEq⟩

/-- (A function's type as its signature gives it, made again by this compile:
the same as the one the kept check began with, if it is equal to it.) -/
instance : Absorb Scheme := ⟨fun z x y => if x == z then some y else if x == y then some x else none⟩

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
  /-- Would `apply` put it on: read only, so that it can be put on in place
  after, the value held once. -/
  fits : Option α → α → δ → Bool

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
        -- (Most are the same object: nothing changed in them.)
        if samePtr sb sp then continue
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
  -- (Mostly segments of its own, after all of `a`'s: put after them, the
  -- rest of `a` let be.)
  -- (What it pushed onto `a`'s last segment, begun with as many: pushed.)
  let onLast := d.grown.foldl (init := some a) fun st (base, before, pushed) => st.bind fun st =>
    if base == st.last.base && st.last.count == before then some { st with last := pushed.foldl Seg.push st.last }
    else none
  if d.sets.isEmpty then
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
  let mut st : Store α := match kept.back? with
    | some last => { older := kept.pop, last }
    | none => {}
  for (i, was, now) in d.sets do
    match st.get? i with
    | some cur => st := st.set! i (← putEntry cur was now)
    | none => none
  pure st

end StoreD

/-- Would `apply` put `d` on `a`: where only its last segment grows and new
ones come after, by where each starts and how many it has; else tried. -/
def StoreD.fits {α : Type} [Absorb α] (a : Store α) (d : StoreD α) : Bool := Id.run do
  if d.segs.isEmpty && d.grown.isEmpty && d.sets.isEmpty then return true
  if d.sets.isEmpty then
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

instance {α : Type} [Absorb α] : Delta (Store α) (StoreD α) where
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
        | some _ | none => none
    | none, none => some (m.insert k v)
    | some _, none => none
  fits _ a d := d.all fun (k, was, v) =>
    match was, a.get? k with
    | some pv, some cur => (putEntry cur pv v).isSome
    | none, some cur => samePtr cur v
    | none, none => true
    | some _, none => false

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

delta_part StDelta0 diffPart0 applyPart0 fitsPart0 clearPart0 restorePart0 [
  tys : StoreD (Option Ty),
  rows : StoreD (Option Row),
  mono : ListD Nat,
  monoRows : ListD Nat,
  monoCaps : ListD Nat,
  caps : StoreD (Option Nat),
  capEdges : StoreD (Nat × Captured),
  capOut : StoreD (Array Nat),
  capEdgeNames : StoreD (Option (String × Nat)),
  dups : ArrD (Ty × String),
  lateDups : ArrD (Ty × String),
  drops : ArrD (Ty × String)]

delta_part StDelta1 diffPart1 applyPart1 fitsPart1 clearPart1 restorePart1 [
  lateDrops : ArrD (Ty × String),
  stays : ArrD (Ty × String),
  lateStays : ArrD (Ty × String),
  statics : ArrD (Ty × String),
  pendingCopies : ArrD (String × FnDecl),
  useDecls : MapD String (Bool × Bool),
  movedCells : ListD Nat,
  flagged : ListD String,
  givenSites : ListD (String × Elab.DropSite × Ty × String),
  givenEdges : Array Nat,
  givers : ListD (Nat × Nat),
  givenReads : ArrD (Ty × String)]

delta_part StDelta2 diffPart2 applyPart2 fitsPart2 clearPart2 restorePart2 [
  aparts : ArrD (Ty × String × Option Nat),
  fieldNames : MapLD String String,
  dotChosen : ListD (Nat × String × Nat),
  scalarLits : ListD (String × Nat × String),
  argsChosen : ListD ((Nat × Nat) × Expr),
  decided : ListD Elab.Decision,
  traitShape : MapD String (Nat × List String),
  writtenArgs : ListD (String × String × String × List Ty),
  supers : ListD (String × List String),
  ranked : ListD (Nat × List (Nat × String)),
  packs : ArrD (Nat × List String),
  envGroups : ArrD (String × List (String × Nat) × Bool × List String × Flat.Body × List Flat.StmtId),
  envAfter : ArrD (String × List (String × Nat) × List (String × Nat) × List String × Flat.Body × List Flat.StmtId)]

delta_part StDelta3 diffPart3 applyPart3 fitsPart3 clearPart3 restorePart3 [
  envLent : ArrD (String × List (String × Nat) × List (String × Nat) × List String × Flat.Body × List Flat.StmtId),
  fnGroups : ListD (String × List (List Nat)),
  fnRunsIn : ListD (String × List (Nat × Bool)),
  bindLoans : MapD Nat Nat,
  envBlocks : Array Nat,
  inPlace : Array Nat,
  envMust : ListD String,
  envHeld : ArrD (String × String × List Nat),
  derefReads : ArrD Nat,
  rowChecks : ListD (String × List (String × Ty)),
  typeBounds : ListD (String × List (String × Nat)),
  typeParams : ListD (String × List (Option Nat))]

delta_part StDelta4 diffPart4 applyPart4 fitsPart4 clearPart4 restorePart4 [
  fieldReads : ArrD (Nat × Nat),
  fieldSites : ArrD (Nat × Bool × Ty × List Nat × List (Option String) × String × String),
  fieldTable : ArrD (Nat × Bool × List Nat × List (Option String × Nat)),
  calls : ArrD (Nat × Ty × Bool),
  instRows : ListD Nat,
  unrunGiven : ArrD (Nat × Nat × Ty × List (String × Nat) × String × Nat),
  sharedEdges : Array Nat,
  assumedLinks : ArrD (Nat × Nat × Ty × String),
  abandoned : ArrD (Nat × Ty × String),
  sure : Array Nat,
  lowerChecks : ArrD (String × String × Ty × List String × Flat.Body × List Flat.StmtId),
  refusals : ArrD String]

delta_part StDelta5 diffPart5 applyPart5 fitsPart5 clearPart5 restorePart5 [
  runFns : MapD String Flat.Body,
  runCtors : Array String,
  runAliases : MapD String Expr,
  runOps : MapD String Bool,
  runExact : Array String,
  runNow : Array Nat,
  rowIncl : ArrD (Row × Row × String),
  types : MapD String TypeDecl,
  ctors : MapD String CtorSig,
  ops : ListD (String × OpSig),
  effects : ListD (String × EffectDecl),
  aliases : MapD String Expr]

delta_part StDelta6 diffPart6 applyPart6 fitsPart6 clearPart6 restorePart6 [
  fns : MapD String Scheme,
  pending : ArrD Pending,
  projections : ArrD (Ty × Nat × Ty × String × Nat),
  namedReads : ArrD (Ty × String × Ty × Nat × String),
  blockCaps : ArrD (Nat × Nat),
  given : ArrD Nat,
  unrun : ArrD (Nat × Nat),
  coercing : ListD String,
  coercions : ArrD (Elab.Site × String),
  loans : StoreD Loan,
  cells : ArrD (Nat × String × Ty),
  bindSites : ListD (Nat × Nat × Nat)]

delta_part StDelta7 diffPart7 applyPart7 fitsPart7 clearPart7 restorePart7 [
  leftBehind : ArrD (Ty × String),
  takenApart : ArrD (Ty × String),
  partReads : ArrD (Nat × String × Ty × Nat × String × String),
  uses : ArrD Use,
  heldMoves : ArrD Use,
  traits : ListD (String × List String),
  methods : MapD String MethodSig,
  kimpls : Array Traits.Impl,
  blanketTraits : ListD (String × List String),
  instSites : ArrD (String × Nat × String × String × List Ty),
  siteTable : ListD (String × List (Nat × String × String × Nat × Nat)),
  siteTypes : ListD (String × List (Option Syntax.TypeExpr))]

delta_part StDelta8 diffPart8 applyPart8 fitsPart8 clearPart8 restorePart8 [
  bounds : ArrD Bound,
  groupUses : ArrD GroupUse,
  rigidKeys : StoreD String,
  rigidAt : MapD String Nat,
  conditionsAt : MapLD String Nat,
  dropCands : ArrD (Elab.DropSite × Ty × String),
  unsafeFns : ListD String,
  dropSites : ArrD (Elab.DropSite × Nat),
  lateKeeps : ArrD (Elab.DropSite × Ty × List (Ty × Nat) × String),
  quiets : ArrD (Ty × String),
  paramTraits : ListD (String × String × List TypeExpr),
  gatOccs : ArrD (String × List Ty × Nat)]

delta_part StDelta9 diffPart9 applyPart9 fitsPart9 clearPart9 restorePart9 [
  gatHolds : ArrD (Nat × List Nat),
  dictTable : ArrD (Nat × List Elab.DictE),
  methodCalls : ArrD (Nat × Nat),
  fnBounds : ListD (String × Nat),
  impls : ArrD ImplDecl,
  fnBodies : MapD String Flat.Body,
  followed : ArrD String]

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
    rest := clearPart9 <| clearPart8 <| clearPart7 <| clearPart6 <| clearPart5 <| clearPart4 <| clearPart3 <| clearPart2 <| clearPart1 <| clearPart0 <| { b with
      assocUses := #[],
      solvedFit := {}, leavesFit := {}, leavesAt := {}, tyIds := {}, tyIdCount := 0,
      tyMemo := {}, dictShared := {}, dictByShape := {}, destroyFit := {}, modules := {}, body := {}, blockRoots := {}, blockRootsAt := 0,
      -- (Of where implementations are, only those it declared.)
      implsByBase := ownImpls p.impls.size b.implsByBase, implsByHead := ownImpls p.impls.size b.implsByHead }
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

/-- Would `applyDelta` put `d` on `a`: read only. -/
def fitsDelta (p : Option St) (a : St) (d : StDelta) : Bool :=
  let sameBase := match p with
    | some p => samePtr a.modules p.modules && samePtr a.dropMode p.dropMode
    | none => true
  let left := match d.assocUses with
    | .grown _ tail | .whole tail => tail.isEmpty
  sameBase && (a.assocUses.isEmpty && left || Delta.fits (p.map (·.assocUses)) a.assocUses d.assocUses)
    && fitsPart0 p a d.part0 && fitsPart1 p a d.part1 && fitsPart2 p a d.part2 && fitsPart3 p a d.part3
    && fitsPart4 p a d.part4 && fitsPart5 p a d.part5 && fitsPart6 p a d.part6 && fitsPart7 p a d.part7
    && fitsPart8 p a d.part8 && fitsPart9 p a d.part9

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
    | .grown _ tail | .whole tail => tail.isEmpty
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
  pure { restorePart9 (restorePart8 (restorePart7 (restorePart6 (restorePart5 (restorePart4 (restorePart3 (restorePart2 (restorePart1 (restorePart0 b s) s) s) s) s) s) s) s) s) s with
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
