module

public import Glorious.Check.Merge.Delta

public section

namespace Glorious.Check

open Syntax

delta_part StDelta2 diffPart2 applyPart2 fitsPart2 clearPart2 restorePart2 [
  aparts : ArrD (Ty × String × Option Nat),
  fieldNames : MapLD String String,
  scalarLits : ListD (String × Nat × String),
  adjust : ListD Elab.Adjust,
  traitShape : MapD String (Nat × List String),
  selfDefaults : MapLD String Nat,
  writtenArgs : ListD (String × String × String × List Ty),
  supers : ListD (String × List String),
  ranked : ListD (Nat × List (Nat × String)),
  packs : ArrD (Nat × List String),
  envGroups : ArrD (String × List (String × Nat) × Bool × List String × Flat.Body × List Flat.StmtId),
  envAfter : ArrD (String × List (String × Nat) × List (String × Nat) × List String × Flat.Body × List Flat.StmtId)]

end Glorious.Check
