module

public import Glorious.Check.Merge.Part0
public import Glorious.Check.Merge.Part1
public import Glorious.Check.Merge.Part2
public import Glorious.Check.Merge.Part3
public import Glorious.Check.Merge.Part4
public import Glorious.Check.Merge.Part5
public import Glorious.Check.Merge.Part6
public import Glorious.Check.Merge.Part7
public import Glorious.Check.Merge.Part8
public import Glorious.Check.Merge.Part9

public section

namespace Glorious.Check

open Syntax

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
