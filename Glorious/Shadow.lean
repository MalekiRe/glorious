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

/-- The same of a type as written, each type parameter as `env` has it.
`_` (not known), or a parameter `env` has not, is `none`. -/
partial def writtenShape (env : List (String × String) := []) : Syntax.TypeExpr → Option String
  | .name "Int" [] => some "Int"
  | .name n [] => match env.lookup n with
    | some s => some s
    | none => if Syntax.isScalar n then some "scalar" else some "data<>"
  | .name n args =>
    if Syntax.isScalar n then some "scalar"
    else do pure s!"data<{",".intercalate (← args.mapM (writtenShape env))}>"
  | .tuple fs => do pure s!"({",".intercalate (← fs.mapM (writtenShape env))})"
  | .fn ps r => do pure s!"fn({",".intercalate (← ps.mapM (writtenShape env))})->{← writtenShape env r}"
  | .performs r _ => writtenShape env r
  | .ref _ t _ => do pure s!"&{← writtenShape env t}"
  | .never => some "!"
  | .hole => none

/-- What each type parameter of `params` is, where a type written of them
meets a Core type: `Vec<T>` and `data<scalar>`, `T` is `scalar`. -/
partial def bindParams (params : List String) (w : Syntax.TypeExpr) (t : Ty)
    (env : List (String × String)) : List (String × String) :=
  match w, t with
  | .name p [], t => if params.contains p && (env.lookup p).isNone then (p, coreShape t) :: env else env
  | .name _ args, .data _ targs => (args.zip targs).foldl (fun env (a, b) => bindParams params a b env) env
  | .tuple ws, .tuple ts => (ws.zip ts).foldl (fun env (a, b) => bindParams params a b env) env
  | .fn ws r, .fn _ ts s _ _ _ _ => bindParams params r s ((ws.zip ts).foldl (fun env (a, b) => bindParams params a b env) env)
  | .performs r _, t => bindParams params r t env
  | .ref _ a _, .ref _ b => bindParams params a b env
  | _, _ => env

/-- The type parameters and the types written of the parameters of each
function a program writes, by its name. -/
partial def written (items : List Syntax.Item) : Std.HashMap String (List String × List (Option Syntax.TypeExpr)) :=
  items.foldl (init := {}) fun m item => match item with
    | .fn name ps annots ret _ => m.insert name (ps, annots ++ [ret])
    | .pub _ i => (written [i]).fold (·.insert) m
    | .module _ (some body) => (written body).fold (·.insert) m
    | _ => m

/-- What a `let` binds, as a word: to count those without a type. -/
def rhsKind : Rhs → String
  | .atom _ => "atom"
  | .prim _ _ => "prim"
  | .construct _ _ => "construct"
  | .place _ => "place"
  | .closure f _ => s!"closure {f}"
  | .rebind _ _ => "rebind"

/-- Each `let` of a computation, by its local's place, with the type its hint
gives (the hints taken in order, a call's regions and a handler's aside),
and what it binds. -/
partial def letTypes (depth : Nat) (hs : List Hint) : Core.Tm → List (Nat × Ty × String)
  | .let_ rhs body =>
    match hs.findIdx? (·.bind?.isSome) with
    | some i =>
      let here := (hs[i]?.bind (·.bind?)).map (·.1)
      (here.toList.map (depth, ·, rhsKind rhs)) ++ letTypes (depth + 1) (hs.drop (i + 1)) body
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
  /-- Those without a type, by what they bind. -/
  untyped : Std.HashMap String Nat := {}

/-- Set the elaborator's types beside the certificate's: each function at
each signature, its type parameters what that signature makes them
(`bindParams`, from the types written of its parameters). -/
def compare (items : List Syntax.Item) (out : Elab.Output) (cert : Cert) : Count := Id.run do
  let mut c : Count := {}
  let sigsOf := written items
  for e in cert.sigs do
    -- (Of a function the program writes, its parameters' types as this
    -- signature has them: the last of the signature's, after any
    -- dictionaries it is given first.)
    let env : List (String × String) := match out.program.names[e.fn]?.bind (sigsOf[·]?) with
      | some (ps, annots) =>
        let ps := Syntax.genericParams ps
        let (annots, ret) := (annots.dropLast, annots.getLast?.getD none)
        let given := e.sig.params.drop (e.sig.params.length - annots.length)
        ((annots ++ [ret]).zip (given ++ [e.sig.ret])).foldl (fun env (a, t) => match a with
          | some w => bindParams ps w t env
          | none => env) []
      | none => []
    let some F := out.program.fns[e.fn]? | continue
    let some tys := out.fnTys[e.fn]? | do
      for (cl, hs) in F.clauses.zip e.hints do
        c := { c with lets := c.lets + (letTypes 0 hs cl.body).length }
      continue
    for ((cl, hs), mine) in (F.clauses.zip e.hints).zip tys do
      let d0 := cl.pats.length + e.sig.caps.length + (cl.pats.map Infer.patBinds).sum
      for (level, t, kind) in letTypes d0 hs cl.body do
        c := { c with lets := c.lets + 1 }
        if (mine.find? (·.1 == level)).isNone then
          let kind := match kind.splitOn " " with
            | ["closure", f] => s!"closure of {((f.toNat?.bind (out.fnNames[·]?)).getD "").take 40}"
            | k :: _ => k
            | [] => kind
          c := { c with untyped := c.untyped.insert kind (c.untyped.getD kind 0 + 1) }
        match (mine.find? (·.1 == level)).bind (writtenShape env ·.2) with
        | some w =>
          c := { c with typed := c.typed + 1 }
          if w == coreShape t then c := { c with same := c.same + 1 }
          else if c.differ.length < 12 then
            c := { c with differ := c.differ ++ [s!"{(out.fnNames[e.fn]?).getD ""} local {level}: checker {w}, Core {coreShape t}"] }
        | none => pure ()
  pure c

end Glorious.Shadow
