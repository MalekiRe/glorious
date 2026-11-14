module

public import Glorious.Syntax.Ast

/-!
# What is settled before a program is checked

A type alias is another way to write a type, not a type: every use is replaced
by what it stands for, and the checker never sees one. This is done once the
names of the program are resolved, so an alias is found like any other name.
-/

public section

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
  -- An argument of an implementation's type that is not one of its type
  -- parameters is a type: `impl T for Option<Int>`. It is fixed, as an
  -- argument another name of the type fixes is.
  let concrete := fun (ps : List String) (tr head : String) (args : List String)
      (context : List (String × String)) (methods : List Item) => do
    let mut newArgs : Array String := #[]
    let mut fresh : Array String := #[]
    let mut fixed : Array Item := #[]
    for (a, j) in args.zipIdx do
      if ps.contains a || head.startsWith "(tuple" then newArgs := newArgs.push a
      else
        let name := s!"%fixed{j}"
        newArgs := newArgs.push name
        fresh := fresh.push name
        fixed := fixed.push (.typeAlias (fixedArgName j) [] (← ty (.name a [])))
    pure (Item.impl (ps ++ fresh.toList) tr head newArgs.toList context (methods ++ fixed.toList))
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
      -- An implementation for another name of a type, `impl T for
      -- Option<A>`, is one for the type the name stands for, with the
      -- arguments the name fixes said beside it.
      match aliases.find? (·.1 == head) with
      | some (_, aps, .name target targs) =>
        let given := aps.zip args
        let mut newArgs : Array String := #[]
        let mut fresh : Array String := #[]
        let mut fixed : Array Item := #[]
        for (targ, j) in targs.zipIdx do
          let named := match targ with
            | .name p [] => given.lookup p
            | _ => none
          match named with
          | some a => newArgs := newArgs.push a
          | none =>
            let name := s!"%fixed{j}"
            newArgs := newArgs.push name
            fresh := fresh.push name
            fixed := fixed.push (.typeAlias (fixedArgName j) [] (← ty targ))
        concrete (ps ++ fresh.toList) tr target newArgs.toList context (methods ++ fixed.toList)
      | _ => concrete ps tr head args context methods
    -- A name given a value with its type written, `let Just: fn(Int) ->
    -- Option<Int> = Ok;`.
    | .alias name value => do pure (.alias name (← mapTypesExpr ty value))
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

/-- The functions written to take a reference first, each with whether it is
`&mut`: a function by its first parameter's type, a trait's function by the
first type it lists. -/
partial def takesReference : List Item → List (String × Bool)
  | [] => []
  | .pub _ item :: rest => takesReference (item :: rest)
  | .module _ (some body) :: rest => takesReference body ++ takesReference rest
  | .fn name _ (some (.ref uniq _ _) :: _) _ _ :: rest => (name, uniq) :: takesReference rest
  | .trait _ methods :: rest =>
    methods.filterMap (fun (m, ps, _) => match ps with
      | .ref uniq _ _ :: _ => some (m, uniq)
      | _ => none) ++ takesReference rest
  | _ :: rest => takesReference rest

mutual

/-- `value.f(a)` where `f` takes a reference first and `value` is a variable,
or a field of one: the variable is borrowed for the call. `known` are the
names in scope that are known to hold a value and not a reference: `1` a
mutable variable, `2` a name bound to what is plainly a value (see
`valueLike`), or a parameter written with a type that is no reference's.
Anything else is given as it is: a reference already, or a value `f` takes
whole. -/
partial def receiverExpr (taken : List (String × Bool)) (known : List (String × Nat)) : Expr → Expr
  | .call id f args =>
    let f := receiverExpr taken known f
    let args := args.map (receiverExpr taken known)
    match f, args with
    | .name q name, .call _ (.name none mark) [receiver] :: rest =>
      if mark == receiverMark then
        -- The name a path of fields starts at, and the path.
        let rec place : Expr → Option (String × List String × Nat)
          | .name none x => if (known.lookup x).any (· != 0) then some (x, [], 0) else none
          | .fieldOf fid e field => (place e).map fun (x, path, _) => (x, path ++ [field], fid)
          | .proj e n => (place e).map fun (x, path, fid) => (x, path ++ [toString n], fid)
          | _ => none
        let given := match taken.lookup name, place receiver with
          | some uniq, some (x, [], _) => Expr.ref uniq x
          | some uniq, some (x, path, fid) => if fid == 0 then receiver else .refField fid uniq x path false
          | _, _ => receiver
        .call id (.name q name) (given :: rest)
      else .call id f args
    | _, _ => .call id f args
  | .tailCall id f args => .tailCall id (receiverExpr taken known f) (args.map (receiverExpr taken known))
  | .tuple args => .tuple (args.map (receiverExpr taken known))
  | .proj e n => .proj (receiverExpr taken known e) n
  | .closure id clauses => .closure id (clauses.map (receiverClause taken known []))
  | .handle subject arms => .handle (receiverExpr taken known subject) (arms.map (receiverClause taken known []))
  | .labelScope l body => .labelScope l (receiverStmts taken known body)
  | .deref e => .deref (receiverExpr taken known e)
  | .reborrow uniq e => .reborrow uniq (receiverExpr taken known e)
  | .fieldOf id e name => .fieldOf id (receiverExpr taken known e) name
  | e => e

/-- (`values`: the parameters written with types that are no reference's.) -/
partial def receiverClause (taken : List (String × Bool)) (known : List (String × Nat))
    (values : List String) : Clause → Clause
  | .mk pats body =>
    let named := (pats.flatMap patternNames).map fun x => (x, if values.contains x then 2 else 0)
    .mk pats (receiverStmts taken (named ++ known) body)

partial def receiverStmts (taken : List (String × Bool)) (known : List (String × Nat)) :
    List Stmt → List Stmt
  | [] => []
  | s :: rest =>
    let rec here : Stmt → Stmt × List (String × Nat)
      | .let_ pat value =>
        let kind := match pat with
          | .var _ => if valueLike value then 2 else 0
          | _ => 0
        (.let_ pat (receiverExpr taken known value), (patternNames pat).map (·, kind) ++ known)
      | .letMut x value => (.letMut x (receiverExpr taken known value), (x, 1) :: known)
      | .expr e => (.expr (receiverExpr taken known e), known)
      | .defer e => (.defer (receiverExpr taken known e), known)
      | .assign target value =>
        (.assign (receiverExpr taken known target) (receiverExpr taken known value), known)
      | .located line col s => let (s, known) := here s; (.located line col s, known)
    let (s, known) := here s
    s :: receiverStmts taken known rest

end

/-- Every dotted call of a program with what it is called on borrowed where
the function takes a reference: see `receiverExpr`. A name that is then
borrowed and was not a variable is kept where a reference can point, as one
borrowed with `&` in the text is (`promoteItems`). -/
partial def borrowReceivers (items : List Item) : List Item :=
  let taken := takesReference items
  let rec go : Item → Item
    | .pub parent item => .pub parent (go item)
    | .module name (some body) => .module name (some (body.map go))
    | .fn name ps annots ret clauses =>
      .fn name ps annots ret (clauses.map fun c =>
        let values := match c with
          | .mk pats _ => (pats.zip annots).filterMap fun
            | (.var _, some (.ref _ _ _)) => none
            | (.var x, some _) => some x
            | _ => none
        receiverClause taken [] values c)
    | .impl ps tr head args context methods => .impl ps tr head args context (methods.map go)
    | .traitInfo name supers defaults params assocs => .traitInfo name supers (defaults.map go) params assocs
    | .alias name value => .alias name (receiverExpr taken [] value)
    | item => item
  promoteItems (items.map go)

/-- Each implementation with the functions its trait gives a body that it
does not write itself; and, where it gives its trait arguments, `impl
From<Int> for u8`, as an implementation of the trait at those: `From<Int>` is
the name of what it implements from here on. -/
def fillDefaults (items : List Item) : List Item :=
  -- (First, with every declaration to hand: what dotted calls borrow.)
  let items := borrowReceivers items
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
      -- (`Self::f(..)` in it is this implementation's `f`, as it is in a
      -- function the implementation writes.)
      let self := selfTypeOf head (args.map (TypeExpr.name · []))
      let missing := missing.map fun
        | .fn m fps annots _ clauses =>
          Item.fn m fps (annots.map fun _ => none) none
            (clauses.map fun c =>
              shiftClause (10000000000 * (index + 1)) (selfClause head (some (tr, (TypeExpr.tuple [self]).asExpr)) c))
        | item => item
      -- Two implementations of a trait for one type, written with the
      -- same arguments (`impl<T, R> Get<T> for (Column<T>, R)` and
      -- `impl<T, H, R> Get<T> for (Column<H>, R)`): each is known by a
      -- name of its own, the later ones numbered.
      let same := fun (other : Item) => match other with
        | .impl _ tr' head' _ _ methods' =>
          tr' == tr && head' == head && (List.range methods'.length).filterMap (fun i =>
            methods'.findSome? fun
              | .typeAlias name _ body => if name == traitArgName i then some body.spell else none
              | _ => none) == given
        | _ => false
      let before := ((items.take index).filter same).length
      let tr := if before == 0 then tr else s!"{tr}#{before}"
      .impl ps (traitAt tr given) head args context (methods ++ missing)
    | (item, _) => item

end Glorious.Syntax
