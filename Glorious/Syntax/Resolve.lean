import Glorious.Syntax.Ast

/-!
# What is settled before a program is checked

A type alias is another way to write a type, not a type: every use is replaced
by what it stands for, and the checker never sees one. This is done once the
names of the program are resolved, so an alias is found like any other name.
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
    let mut args ← args.mapM (expandTypeExpr aliases seen)
    -- A declared type written with fewer arguments than it has parameters:
    -- the rest are what its declaration says they are where not written.
    repeat
      match aliases.lookup (defaultKey x args.length) with
      | some (params, body) =>
        let given := (genericParams params).zip args
        args := args ++ [← expandTypeExpr aliases seen (substTypeExpr given body)]
      | none => break
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

mutual

/-- An expression with each type written in it, `let x: Type = ..`, changed. -/
partial def mapTypesExpr (f : TypeExpr → Except String TypeExpr) : Expr → Except String Expr
  | .call id (.name none mark) [value, ty] => do
    if mark == ascribeMark || mark == instMark then
      pure (.call id (.name none mark) [← mapTypesExpr f value, (← f (TypeExpr.ofExpr ty)).asExpr])
    else pure (.call id (.name none mark) [← mapTypesExpr f value, ← mapTypesExpr f ty])
  | .call id g args => do pure (.call id (← mapTypesExpr f g) (← args.mapM (mapTypesExpr f)))
  | .tailCall id g args => do pure (.tailCall id (← mapTypesExpr f g) (← args.mapM (mapTypesExpr f)))
  | .tuple args => .tuple <$> args.mapM (mapTypesExpr f)
  | .proj e i => do pure (.proj (← mapTypesExpr f e) i)
  | .fieldOf id e name => do pure (.fieldOf id (← mapTypesExpr f e) name)
  | .deref e => .deref <$> mapTypesExpr f e
  | .reborrow u e => .reborrow u <$> mapTypesExpr f e
  | .closure id clauses => .closure id <$> clauses.mapM (mapTypesClause f)
  | .handle subject arms => do
    pure (.handle (← mapTypesExpr f subject) (← arms.mapM (mapTypesClause f)))
  | .labelScope l body => .labelScope l <$> body.mapM (mapTypesStmt f)
  | e => pure e

partial def mapTypesClause (f : TypeExpr → Except String TypeExpr) : Clause → Except String Clause
  | .mk pats body => .mk pats <$> body.mapM (mapTypesStmt f)

partial def mapTypesStmt (f : TypeExpr → Except String TypeExpr) : Stmt → Except String Stmt
  | .let_ pat value => .let_ pat <$> mapTypesExpr f value
  | .letMut x value => .letMut x <$> mapTypesExpr f value
  | .expr e => .expr <$> mapTypesExpr f e
  | .defer e => .defer <$> mapTypesExpr f e
  | .assign target value => do pure (.assign (← mapTypesExpr f target) (← mapTypesExpr f value))
  | .located line col s => .located line col <$> mapTypesStmt f s

end

/-- A program without its type aliases: each use is what the alias stands for. -/
partial def expandAliases (items : List Item) : Except String (List Item) := do
  let aliases := items.filterMap fun
    | .typeAlias name params body => some (name, params, body)
    | _ => none
  for (name, _, _) in aliases do
    if (aliases.filter (·.1 == name)).length > 1 then
      throw s!"type alias `{name}` is declared twice"
  -- A type the program declares is that type, whatever an alias of the same
  -- name would have stood for.
  let declared := items.filterMap fun
    | .enum name _ _ => some name
    | .struct name _ _ => some name
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
      pure (.fn name ps (← annots.mapM fun a => a.mapM ty) (← ret.mapM ty)
        (← clauses.mapM (mapTypesClause ty)))
    | .trait name methods => do
      pure (.trait name (← methods.mapM fun (m, ps, r) => do
        pure (m, ← ps.mapM ty, ← r.mapM ty)))
    | .impl ps tr head args context methods => do
      let methods ← methods.mapM fun
        | .typeAlias name aps body => do pure (.typeAlias name aps (← ty body))
        | m => item m
      pure (.impl ps tr head args context methods)
    | i => pure i
  let rest := items.filter fun
    | .typeAlias _ _ _ => false
    | _ => true
  rest.mapM item

mutual

/-- An expression with every identity in it moved on by `k`: a copy of a
function is then told apart from the function and from every other copy. -/
partial def shiftExpr (k : Nat) : Expr → Expr
  | .call id g args => .call (id + k) (shiftExpr k g) (args.map (shiftExpr k))
  | .tailCall id g args => .tailCall (id + k) (shiftExpr k g) (args.map (shiftExpr k))
  | .tuple args => .tuple (args.map (shiftExpr k))
  | .proj e i => .proj (shiftExpr k e) i
  | .fieldOf id e name => .fieldOf (id + k) (shiftExpr k e) name
  | .refField id uniq name path star => .refField (id + k) uniq name path star
  | .deref e => .deref (shiftExpr k e)
  | .reborrow u e => .reborrow u (shiftExpr k e)
  | .closure id clauses => .closure (id + k) (clauses.map (shiftClause k))
  | .handle subject arms => .handle (shiftExpr k subject) (arms.map (shiftClause k))
  | .labelScope l body => .labelScope l (body.map (shiftStmt k))
  | e => e

partial def shiftClause (k : Nat) : Clause → Clause
  | .mk pats body => .mk pats (body.map (shiftStmt k))

partial def shiftStmt (k : Nat) : Stmt → Stmt
  | .let_ pat value => .let_ pat (shiftExpr k value)
  | .letMut x value => .letMut x (shiftExpr k value)
  | .expr e => .expr (shiftExpr k e)
  | .defer e => .defer (shiftExpr k e)
  | .assign target value => .assign (shiftExpr k target) (shiftExpr k value)
  | .located line col s => .located line col (shiftStmt k s)

end

/-- Each implementation with the functions its trait gives a body that it
does not write itself; and, where it gives its trait arguments, `impl
From<Int> for u8`, as an implementation of the trait at those: `From<Int>` is
the name of what it implements from here on. -/
def fillDefaults (items : List Item) : List Item :=
  let defaults := items.filterMap fun
    | .traitInfo name _ fns _ _ => some (name, fns)
    | _ => none
  items.zipIdx.map fun
    | (.impl ps tr head args context methods, index) =>
      let written := methods.filterMap fun
        | .fn m _ _ _ _ => some m
        | _ => none
      let missing := ((defaults.lookup tr).getD []).filter fun
        | .fn m _ _ _ _ => !written.contains m
        | _ => false
      let given := (List.range methods.length).filterMap fun i =>
        methods.findSome? fun
          | .typeAlias name _ body => if name == traitArgName i then some body.spell else none
          | _ => none
      -- A default is written against `Self`; in the implementation its types
      -- are the trait's at the implementing type, as for a function the
      -- implementation writes itself without saying them.
      -- Each implementation has its own copy: the calls in it are met by
      -- this implementation's types, and are known by their identities.
      let missing := missing.map fun
        | .fn m fps annots _ clauses =>
          Item.fn m fps (annots.map fun _ => none) none
            (clauses.map (shiftClause (10000000000 * (index + 1))))
        | item => item
      .impl ps (traitAt tr given) head args context (methods ++ missing)
    | (item, _) => item

end Glorious.Syntax
