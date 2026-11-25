module

public import Glorious.Check.Merge.Delta

public section

namespace Glorious.Check

open Syntax

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

end Glorious.Check
