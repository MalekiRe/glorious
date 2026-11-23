module

public import Glorious.Elab.Base

/-!
# Instances of an effect as effects of their own

`effect Store<C> { take() -> [C] }` is a family: `Store<Int>` and `Store<Str>`
are two effects, each handled by the nearest handler of exactly that one. Core
knows an operation by a number, so before a program is elaborated each
instance it uses is made an effect of its own, with operations of its own:
`take@<Int>`, `take@<Str>`.

A function that performs `Store<C>` for a `C` of its caller's choosing is
written out once for each choice: the checker says, for every call in a
function, which types say which instance (`Blocks.sites`), in terms a caller
of the function fills in in turn. So the copies are found from the functions
that need no caller to say: `main` first.

Nothing is done to a program in which no family has two instances.
-/

public section

namespace Glorious.Elab

open Glorious.Syntax

def instName (x key : String) : String := s!"{x}@<{key}>"

/-- What a function's text is rewritten by: its places, the types of this
copy of it, the families with several instances, the functions that are
copied, which effect each operation is of, and the function's own name with
this copy's. -/
structure Copy where
  table : List (Nat × String × String × Nat × Nat)
  types : List TypeExpr
  several : List String
  copied : List String
  opOf : List (String × String)
  self : String × String

def Copy.key (c : Copy) (off len : Nat) : String :=
  ", ".intercalate (((c.types.drop off).take len).map TypeExpr.spell)

/-- The name called at the call numbered `id`, as this copy has it. -/
def Copy.callee (c : Copy) (id : Nat) (x : String) : String :=
  let here := c.table.filter fun (i, _, _, _, _) => i == id && id != 0
  match here.find? fun (_, kind, e, _, _) => kind == "op" && c.opOf.lookup x == some e && c.several.contains e with
  | some (_, _, _, off, len) => instName x (c.key off len)
  | none =>
    match here.find? fun (_, kind, f, _, _) => kind == "call" && f == x && c.copied.contains x with
    | some (_, _, _, off, len) => instName x (c.key off len)
    | none => if x == c.self.1 then c.self.2 else x

/-- A function's body for one copy: each call with the instance's callee,
each handler's arms of an effect it handles an instance of named so. -/
def copyRewrite (c : Copy) : Flat.FRewrite where
  onExpr go b e :=
    let named := fun (id : Nat) (f : Flat.ExprId) (args : Array Flat.ExprId) (tail : Bool) =>
      match b.expr f with
      | .name q x => some (do
        let f' ← Flat.pushExpr (.name q (c.callee id x))
        let args' ← args.mapM go.ex
        Flat.pushExpr (if tail then .tailCall id f' args' else .call id f' args'))
      | _ => none
    match b.expr e with
    | .call id f args => named id f args false
    | .tailCall id f args => named id f args true
    | .handle subject arms =>
      let id := match b.expr subject with
        | .call id _ _ => id
        | _ => 0
      -- The effects this handler handles an instance of, with which.
      let handled := c.table.filterMap fun (i, kind, e, off, len) =>
        if i == id && id != 0 && kind == "handle" && c.several.contains e then some (e, c.key off len) else none
      some (do
        let subject' ← go.ex subject
        let arms' ← arms.mapM fun arm => do
          let ⟨pats, body⟩ := (← get).clause arm
          match pats with
          | [.ctor x q ps] =>
            let pats' := match (c.opOf.lookup x).bind fun e => handled.lookup e with
              | some key => [Pattern.ctor (instName x key) q ps]
              | none => pats
            let body' ← body.mapM go.st
            Flat.pushClause ⟨pats', body'⟩
          | _ => go.clause arm
        Flat.pushExpr (.handle subject' arms'))
    | _ => none

/-- How each item is written for the instances of effects: worked out once
for the whole program (`instancesOf`), each item then on its own. -/
structure Instances where
  /-- The functions a function is written as, by name: itself, or a copy for
  each instance it is called at, or none (one that is copied and nothing
  calls). -/
  names : String → List String
  /-- A function written as those. -/
  fn : Syntax.Item → List Syntax.Item
  /-- Any other item: an effect with several instances, one for each. -/
  other : Syntax.Item → List Syntax.Item

/-- Each instance of an effect a program uses made an effect of its own, and
each function that is about an instance of its caller's choosing written out
for each choice. `written` has the effects with the types they declare. -/
partial def instancesOf (b : Blocks) (written : List Item) : Except String Instances := do
  let same : Instances := { names := fun f => [f], fn := fun i => [i], other := fun i => [i] }
  let rec bare : Item → Item
    | .pub _ i => bare i
    | i => i
  let typesOf := fun (f : String) => (b.siteTypes.lookup f).getD []
  let tableOf := fun (f : String) => (b.sites.lookup f).getD []
  -- A function is copied if some type of its places waits for a caller.
  let copied := b.sites.filterMap fun (f, _) => if (typesOf f).any Option.isNone then some f else none
  -- From the functions that wait for nobody, every copy that is called.
  let roots : List (String × String × List TypeExpr) := b.sites.filterMap fun (f, _) =>
    if copied.contains f then none else some (f, f, (typesOf f).filterMap id)
  let rec reach (fuel : Nat) (todo done : List (String × String × List TypeExpr)) :
      Except String (List (String × String × List TypeExpr)) :=
    match fuel, todo with
    | _, [] => pure done
    | 0, _ => throw "a function that performs an effect of its caller's choosing is used at ever more types: it calls itself at a type that holds the one it was called at"
    | fuel + 1, (f, name, types) :: rest =>
      if done.any (·.2.1 == name) then reach fuel rest done
      else
        let more := (tableOf f).filterMap fun (_, kind, g, off, len) =>
          if kind == "call" && copied.contains g then
            let slice := (types.drop off).take len
            some (g, instName g (", ".intercalate (slice.map TypeExpr.spell)), slice)
          else none
        reach fuel (more ++ rest) ((f, name, types) :: done)
  let all ← reach 100000 roots []
  -- The instances of each family, by how their types are written.
  let mut found : List (String × List (String × List TypeExpr)) := []
  for (f, _, types) in all do
    for (_, kind, e, off, len) in tableOf f do
      if kind == "op" || kind == "handle" then
        let slice := (types.drop off).take len
        let key := ", ".intercalate (slice.map TypeExpr.spell)
        let known := (found.lookup e).getD []
        unless known.any (·.1 == key) do
          found := (e, known ++ [(key, slice)]) :: found.filter (·.1 != e)
  let several := found.filterMap fun (e, known) => if known.length > 1 then some e else none
  if several.isEmpty then return same
  let effects := written.filterMap fun i =>
    match bare i with
    | .effect name ps ops => some (name, ps, ops)
    | _ => none
  let opOf := effects.flatMap fun (name, _, ops) => ops.map fun o => (o.name, name)
  let copyOf := fun (f name : String) (types : List TypeExpr) (item : Syntax.Item) =>
    let c : Copy := ⟨tableOf f, types, several, copied, opOf, (f, name)⟩
    match item with
    | .fn _ ps annots ret body => Syntax.Item.fn name ps annots ret ((copyRewrite c).body body)
    | other => other
  let rec bareF : Syntax.Item → Syntax.Item
    | .pub _ i => bareF i
    | i => i
  let mineOf := fun (name : String) => all.filter (·.1 == name)
  pure
    { names := fun name =>
        match mineOf name with
        -- (No place of its own: as it is, unless it is one that is copied
        -- and nothing calls.)
        | [] => if copied.contains name then [] else [name]
        | mine => mine.map (·.2.1)
      fn := fun item =>
        match item with
        | .fn name ps annots ret body =>
          match mineOf name with
          | [] => if copied.contains name then [] else [item]
          | mine => mine.map fun (f, copy, types) => copyOf f copy types (.fn name ps annots ret body)
        | _ => [item]
      other := fun item =>
        match bareF item with
        | (.effect name ps ops) =>
          if several.contains name then
            -- One effect for each instance, with the family's types written in.
            let typed := (effects.find? (·.1 == name)).map fun (_, ps, ops) => (ps, ops)
            let (ps, ops) := typed.getD (ps, ops)
            let places := ps.filter (!·.startsWith "'")
            ((found.lookup name).getD []).map fun (key, types) =>
              let σ := places.zip types
              (.effect (instName name key) (ps.filter (·.startsWith "'")) (ops.map fun o =>
                { o with name := instName o.name key, payload := o.payload.map (substTypeExpr σ)
                         result := o.result.map (substTypeExpr σ) }))
          else [item]
        | _ => [item] }

end Glorious.Elab
