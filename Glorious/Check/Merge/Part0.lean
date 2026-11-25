module

public import Glorious.Check.Merge.Delta

public section

namespace Glorious.Check

open Syntax

delta_part StDelta0 diffPart0 applyPart0 fitsPart0 clearPart0 restorePart0 [
  tys : StoreD (Option Ty),
  rows : StoreD (Option Row),
  monoCaps : ListD Nat,
  caps : StoreD (Option Nat),
  capEdges : StoreD (Nat × Captured),
  capOut : StoreD (Array Nat),
  capEdgeNames : StoreD (Option (String × Nat)),
  dups : ArrD (Ty × String),
  lateDups : ArrD (Ty × String),
  drops : ArrD (Ty × String)]

end Glorious.Check
