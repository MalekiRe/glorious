module

public import Glorious.Check.Merge.Delta

public section

namespace Glorious.Check

open Syntax

delta_part StDelta5 diffPart5 applyPart5 fitsPart5 clearPart5 restorePart5 [
  runFns : MapD String Flat.Body,
  declFns : MapD String Flat.Body,
  decidedFns : MapD String Flat.Body,
  runCtors : Array String,
  runAliases : MapD String Expr,
  runOps : MapD String Bool,
  runExact : Array String,
  runNow : Array Nat,
  rowIncl : ArrD (Row × Row × String),
  types : MapD String TypeDecl,
  ctors : MapD String CtorSig,
  ops : ListD (String × OpSig),
  effects : ListD (String × EffectDecl),
  aliases : MapD String Expr]

end Glorious.Check
