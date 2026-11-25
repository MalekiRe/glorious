module

public import Glorious.Check.Merge.Delta

public section

namespace Glorious.Check

open Syntax

delta_part StDelta6 diffPart6 applyPart6 fitsPart6 clearPart6 restorePart6 [
  fns : MapD String Scheme,
  bodySchemes : MapD String Scheme,
  fnCalls : MapD String Scheme,
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

end Glorious.Check
