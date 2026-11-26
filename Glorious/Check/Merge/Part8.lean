module

public import Glorious.Check.Merge.Delta

public section

namespace Glorious.Check

open Syntax

delta_part StDelta8 diffPart8 applyPart8 fitsPart8 clearPart8 restorePart8 [
  bounds : ArrD Bound,
  groupUses : ArrD GroupUse,
  rigidKeys : StoreD Rigid,
  rigidAt : MapD Rigid Nat,
  conditionsAt : MapLD (Syntax.TraitKey × Syntax.TypeExpr) Nat,
  dropCands : ArrD (Elab.DropSite × Ty × String),
  unsafeFns : ListD String,
  dropSites : ArrD (Elab.DropSite × Nat),
  lateKeeps : ArrD (Elab.DropSite × Ty × List (Ty × Nat) × String),
  quiets : ArrD (Ty × String),
  paramTraits : ListD (String × String × List TypeExpr),
  gatOccs : ArrD (String × List Ty × Nat)]

end Glorious.Check
