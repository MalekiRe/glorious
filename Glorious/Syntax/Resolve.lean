import Glorious.Syntax.Ast

/-!
# What is settled before a program is checked

A type alias is another way to write a type, not a type: every use is replaced
by what it stands for, and the checker never sees one.
-/

namespace Glorious.Syntax

/-- A type with each of the named parameters replaced. -/
partial def substTypeExpr (m : List (String × TypeExpr)) : TypeExpr → TypeExpr
  | .name x args =>
    match m.lookup x, args with
    | some t, [] => t
    | _, _ => .name x (args.map (substTypeExpr m))
  | .tuple args => .tuple (args.map (substTypeExpr m))
  | .fn ps r => .fn (ps.map (substTypeExpr m)) (substTypeExpr m r)
  | .performs r effects =>
    .performs (substTypeExpr m r) (effects.map fun (e, args) => (e, args.map (substTypeExpr m)))
  | .ref uniq t life =>
    -- A lifetime parameter is replaced by the lifetime it is given.
    let life := match life.bind fun l => m.lookup l with
      | some (TypeExpr.name l []) => some l
      | _ => life
    .ref uniq (substTypeExpr m t) life
  | t => t

/-- A type with every alias in it written out. `seen` are the aliases being
written out already: one that stands for itself has no meaning. -/
partial def expandTypeExpr (aliases : List (String × List String × TypeExpr))
    (seen : List String) : TypeExpr → Except String TypeExpr
  | .name x args => do
    let args ← args.mapM (expandTypeExpr aliases seen)
    match aliases.lookup x with
    | none => pure (.name x args)
    | some (params, body) =>
      if seen.contains x then throw s!"type alias `{x}` stands for itself"
      let params := genericParams params
      unless params.length == args.length do
        throw s!"type alias `{x}` takes {params.length} arguments, but is given {args.length}"
      expandTypeExpr aliases (x :: seen) (substTypeExpr (params.zip args) body)
  | .tuple args => .tuple <$> args.mapM (expandTypeExpr aliases seen)
  | .fn ps r => do
    pure (.fn (← ps.mapM (expandTypeExpr aliases seen)) (← expandTypeExpr aliases seen r))
  | .performs r effects => do
    let effects ← effects.mapM fun (e, args) => do
      pure (e, ← args.mapM (expandTypeExpr aliases seen))
    pure (.performs (← expandTypeExpr aliases seen r) effects)
  | .ref uniq t life => do pure (.ref uniq (← expandTypeExpr aliases seen t) life)
  | t => pure t

/-- A program without its type aliases: each use is what the alias stands for. -/
partial def expandAliases (items : List Item) : Except String (List Item) := do
  let aliases := items.filterMap fun
    | .typeAlias name params body => some (name, params, body)
    | .pub (.typeAlias name params body) => some (name, params, body)
    | _ => none
  for (name, _, _) in aliases do
    if (aliases.filter (·.1 == name)).length > 1 then
      throw s!"type alias `{name}` is declared twice"
  -- A type the program declares is that type, whatever an alias of the same
  -- name would have stood for.
  let declared := items.filterMap fun
    | .enum name _ _ => some name
    | .struct name _ _ => some name
    | .pub (.enum name _ _) => some name
    | .pub (.struct name _ _) => some name
    | _ => none
  let aliases := aliases.filter fun (name, _, _) => !declared.contains name
  if aliases.isEmpty then return items
  let ty := expandTypeExpr aliases []
  let rec item : Item → Except String Item
    | .enum name ps ctors => do
      pure (.enum name ps (← ctors.mapM fun (c, fields) => do pure (c, ← fields.mapM ty)))
    | .struct name ps fields => do pure (.struct name ps (← fields.mapM ty))
    | .effect name ps ops => do
      let ops ← ops.mapM fun op => do
        pure { op with payload := ← op.payload.mapM ty, result := ← op.result.mapM ty }
      pure (.effect name ps ops)
    | .fn name ps annots ret clauses => do
      pure (.fn name ps (← annots.mapM fun a => a.mapM ty) (← ret.mapM ty) clauses)
    | .trait name methods => do
      pure (.trait name (← methods.mapM fun (m, ps, r) => do
        pure (m, ← ps.mapM ty, ← r.mapM ty)))
    | .impl ps tr head args context methods => do
      pure (.impl ps tr head args context (← methods.mapM item))
    | .pub i => .pub <$> item i
    | i => pure i
  let rest := items.filter fun
    | .typeAlias _ _ _ => false
    | .pub (.typeAlias _ _ _) => false
    | _ => true
  rest.mapM item

/-- A program with `pub` taken off its items: for where visibility is not asked. -/
partial def stripPub (items : List Item) : List Item :=
  items.map fun
    | .pub item => (stripPub [item]).headD item
    | item => item

end Glorious.Syntax
