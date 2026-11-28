module

public import Glorious.Check.Merge.Delta

public section

namespace Glorious.Check

open Syntax

delta_part StDelta9 diffPart9 applyPart9 fitsPart9 clearPart9 restorePart9 [
  gatHolds : ArrD (Nat × List Nat),
  dictTable : ArrD (Nat × List Elab.DictE),
  dictTypes : MapLD USize (String × Syntax.TypeExpr),
  projAt : MapD Nat (Nat × String),
  methodCalls : ArrD (Nat × Nat),
  fnBounds : ListD (String × Nat),
  impls : ArrD ImplDecl,
  fnBodies : MapD String Flat.Body,
  followed : ArrD String,
  declFailed : ArrD (List String × String)]

end Glorious.Check
