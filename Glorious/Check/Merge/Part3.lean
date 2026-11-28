module

public import Glorious.Check.Merge.Delta

public section

namespace Glorious.Check

open Syntax

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
  typeParams : ListD (String × List (Option Nat)),
  typeParamNames : ListD (String × List String)]

end Glorious.Check
