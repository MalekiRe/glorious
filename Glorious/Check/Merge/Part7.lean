module

public import Glorious.Check.Merge.Delta

public section

namespace Glorious.Check

open Syntax

delta_part StDelta7 diffPart7 applyPart7 fitsPart7 clearPart7 restorePart7 [
  leftBehind : ArrD (Ty × String),
  takenApart : ArrD (Ty × String),
  partReads : ArrD (Nat × String × Ty × Nat × String × String),
  uses : ArrD Use,
  heldMoves : ArrD Use,
  traits : ListD (String × List String),
  methods : MapD String MethodSig,
  kimpls : Array (Traits.Impl Syntax.TraitKey),
  blanketTraits : ListD (String × List String),
  instSites : ArrD (String × Nat × String × String × List Ty),
  siteTable : ListD (String × List (Nat × String × String × Nat × Nat)),
  siteTypes : ListD (String × List (Option Syntax.TypeExpr))]

end Glorious.Check
