module

public import Glorious.Check.Merge.Delta

public section

namespace Glorious.Check

open Syntax

delta_part StDelta1 diffPart1 applyPart1 fitsPart1 clearPart1 restorePart1 [
  lateDrops : ArrD (Ty × String),
  lateReceivers : ArrD (Nat × Ty × Ty),
  stays : ArrD (Ty × String),
  lateStays : ArrD (Ty × String),
  statics : ArrD (Ty × String),
  pendingCopies : ArrD (String × FnDecl),
  useDecls : MapD String (Bool × Bool),
  movedCells : ListD Nat,
  placedVals : ListD Nat,
  placedLets : ArrD (String × Nat × Nat × String),
  placedLetIds : ListD Nat,
  placedNames : ArrD (String × String × Nat),
  flagged : ListD (String × String),
  givenSites : ListD (String × Elab.DropSite × Ty × String),
  givenEdges : Array Nat,
  givers : ListD (Nat × Nat),
  givenReads : ArrD (Ty × String)]

end Glorious.Check
