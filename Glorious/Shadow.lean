module

public import Glorious.Typing.Checker
public import Glorious.Elab
public import Glorious.Infer

/-!
# The elaborator's types beside the certificate's

Step 2 of the redesign (docs/redesign.md): the elaborator is to write the
certificate `Infer` finds. While it does not yet, what it knows is set
beside what `Infer` found (`GLORIOUS_TRACE=types`): for each `let` of each
function at each signature, the type the checker found of what the local
holds (`Elab.Output.fnTys`) and the type `Infer` gave it, compared by their
shapes (regions and data types' identities aside).
-/

@[expose] public section

namespace Glorious.Shadow

open Typing

/-- A type's shape: what it is made of, without regions, effects, and which
declared type a data type is. -/
partial def coreShape : Ty → String
  | .int => "Int"
  | .scalar _ => "scalar"
  | .tuple fs => s!"({",".intercalate (fs.map coreShape)})"
  | .data _ args => s!"data<{",".intercalate (args.map coreShape)}>"
  | .fn _ ps r _ _ _ _ => s!"fn({",".intercalate (ps.map coreShape)})->{coreShape r}"
  | .ref _ t => s!"&{coreShape t}"
  | .never => "!"

/-- The same of a type as written. `_` (not known) is `none`. -/
partial def writtenShape : Syntax.TypeExpr → Option String
  | .name "Int" [] => some "Int"
  | .name n args =>
    if Syntax.isScalar n then some "scalar"
    else do pure s!"data<{",".intercalate (← args.mapM writtenShape)}>"
  | .tuple fs => do pure s!"({",".intercalate (← fs.mapM writtenShape)})"
  | .fn ps r => do pure s!"fn({",".intercalate (← ps.mapM writtenShape)})->{← writtenShape r}"
  | .performs r _ => writtenShape r
  | .ref _ t _ => do pure s!"&{← writtenShape t}"
  | .never => some "!"
  | .hole => none

/-- Each `let` of a computation, by its local's place, with the type its hint
gives (the hints taken in order, a call's regions and a handler's aside). -/
partial def letTypes (depth : Nat) (hs : List Hint) : Core.Tm → List (Nat × Ty)
  | .let_ _ body =>
    match hs.findIdx? (·.bind?.isSome) with
    | some i =>
      let here := (hs[i]?.bind (·.bind?)).map (·.1)
      (here.toList.map (depth, ·)) ++ letTypes (depth + 1) (hs.drop (i + 1)) body
    | none => []
  | .call _ _ body | .handle _ _ _ _ body | .perform _ _ body | .label _ body | .guard _ _ body
  | .cancel _ body | .cell _ _ body | .cellL _ _ _ body | .lend _ _ _ _ _ body | .mem _ _ body
  | .host _ _ body => letTypes (depth + 1) hs body
  | _ => []

/-- How many the elaborator's types are of the certificate's: those it has
one for, and those whose shapes are the same; a few that differ, to see. -/
structure Count where
  lets : Nat := 0
  typed : Nat := 0
  same : Nat := 0
  differ : List String := []

/-- Set the elaborator's types beside the certificate's. -/
def compare (out : Elab.Output) (cert : Cert) : Count := Id.run do
  let mut c : Count := {}
  for e in cert.sigs do
    let some F := out.program.fns[e.fn]? | continue
    let some tys := out.fnTys[e.fn]? | do
      for (cl, hs) in F.clauses.zip e.hints do
        c := { c with lets := c.lets + (letTypes 0 hs cl.body).length }
      continue
    for ((cl, hs), mine) in (F.clauses.zip e.hints).zip tys do
      let d0 := cl.pats.length + e.sig.caps.length + (cl.pats.map Infer.patBinds).sum
      for (level, t) in letTypes d0 hs cl.body do
        c := { c with lets := c.lets + 1 }
        match (mine.find? (·.1 == level)).bind (writtenShape ·.2) with
        | some w =>
          c := { c with typed := c.typed + 1 }
          if w == coreShape t then c := { c with same := c.same + 1 }
          else if c.differ.length < 12 then
            c := { c with differ := c.differ ++ [s!"{(out.fnNames[e.fn]?).getD ""} local {level}: checker {w}, Core {coreShape t}"] }
        | none => pure ()
  pure c

end Glorious.Shadow
