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

/-- The type with these lifetimes left out of its references. -/
partial def elideLifetimes (lifes : List String) : TypeExpr → TypeExpr
  | .ref uniq t life => .ref uniq (elideLifetimes lifes t) (if life.any lifes.contains then none else life)
  | .name x args => .name x (args.map (elideLifetimes lifes))
  | .tuple args => .tuple (args.map (elideLifetimes lifes))
  | .fn ps r => .fn (ps.map (elideLifetimes lifes)) (elideLifetimes lifes r)
  | .performs r effects => .performs (elideLifetimes lifes r) (effects.map fun (e, args) => (e, args.map (elideLifetimes lifes)))
  | t => t

/-- A type with every alias in it written out. `seen` are the aliases being
written out already: one that stands for itself has no meaning. -/
partial def expandTypeExpr (aliases : List (String × List String × TypeExpr))
    (seen : List String) : TypeExpr → Except String TypeExpr
  | .name x args => do
    let mut args ← args.mapM (expandTypeExpr aliases seen)
    -- A declared type written with fewer arguments than it has parameters:
    -- the rest are what its declaration says they are where not written.
    -- (Of a use that writes no lifetime, by the place among the types,
    -- which are what the default is given.)
    let written := args.any fun | .name l [] => l.startsWith "'" | _ => false
    let byTypes := !written && (List.range 16).any fun k => (aliases.lookup (defaultKey x k ++ "~")).isSome
    repeat
      match aliases.lookup (defaultKey x args.length ++ (if byTypes then "~" else "")) with
      | some (params, body) =>
        let params := genericParams params
        let params := if byTypes then params.filter (!·.startsWith "'") else params
        let given := params.zip args
        args := args ++ [← expandTypeExpr aliases seen (substTypeExpr given body)]
      | none => break
    match aliases.lookup x with
    | none => pure (.name x args)
    | some (params, body) =>
      if seen.contains x then throw s!"type alias `{x}` stands for itself"
      let params := genericParams params
      -- (Its lifetimes not written, `Res<T>` of `type Res<'a, T> = &'a T`:
      -- each is left out where the alias is used, as in a written `&T`.)
      let lifes := params.filter (·.startsWith "'")
      let (params, body) := if !lifes.isEmpty && args.length + lifes.length == params.length
        then (params.filter (!·.startsWith "'"), elideLifetimes lifes body) else (params, body)
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
  | e => e.traverse (mapTypesExpr f) fun _ b => b.mapM (mapTypesStmt f)

partial def mapTypesClause (f : TypeExpr → Except String TypeExpr) : Clause → Except String Clause
  | .mk pats body => .mk pats <$> body.mapM (mapTypesStmt f)

partial def mapTypesStmt (f : TypeExpr → Except String TypeExpr) (s : Stmt) : Except String Stmt :=
  s.traverse (mapTypesExpr f)

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


/-- How `givesReference`'s functions are kept among `takesReference`'s. -/
def givesKey (name : String) : String := "%gives:" ++ name

/-- The functions written to give a reference: a dot call on what one gives
is given it as it is, not borrowed again. -/
partial def givesReference : List Item → List String
  | [] => []
  | .pub _ item :: rest => givesReference (item :: rest)
  | .module _ (some body) :: rest => givesReference body ++ givesReference rest
  | .fn name _ _ (some r) _ :: rest =>
    let gives := match r with
      | .ref .. => true
      | .performs (.ref ..) _ => true
      | _ => false
    if gives then name :: givesReference rest else givesReference rest
  | .impl _ _ _ _ _ methods :: rest => givesReference methods ++ givesReference rest
  | _ :: rest => givesReference rest

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
          | .name none x => if (known.lookup x).any (fun k => k != 0 && k != 3) then some (x, [], 0) else none
          | .fieldOf fid e field => (place e).map fun (x, path, _) => (x, path ++ [field], fid)
          | .proj e n => (place e).map fun (x, path, fid) => (x, path ++ [toString n], fid)
          | _ => none
        -- (A field of what a `&mut` parameter points to, `p.items`.)
        let rec throughRef : Expr → Option (String × List String × Nat)
          | .fieldOf fid (.name none x) field =>
            if known.lookup x == some 3 then some (x, [field], fid) else none
          | .fieldOf fid e field => (throughRef e).map fun (x, path, _) => (x, path ++ [field], fid)
          | _ => none
        -- (`v[i].f()` where `f` takes a reference: the element, borrowed
        -- where it is.)
        let rec element (uniq : Bool) (fuel : Nat) : Expr → Option Expr
          | .call cid (.name _ "index") [a, i] =>
            let base := match fuel, place a, throughRef a with
              | _, some (x, [], _), _ => some (Expr.ref uniq x)
              | _, some (x, path, fid), _ => if fid == 0 then none else some (.refField fid uniq x path false)
              | _, none, some (x, path, fid) => some (.refField fid uniq x path true)
              | fuel + 1, none, none =>
                match a with
                | .name none x => if known.lookup x == some 3 then some (.name none x) else none
                | _ => element uniq fuel a
              | 0, _, _ => none
            base.map fun b =>
              if uniq then .call cid (.name none "place_at") [i, b] else .call cid (.name none "element_at") [b, i]
          | _ => none
        let given := match taken.lookup name, place receiver, throughRef receiver with
          | some uniq, some (x, [], _), _ => Expr.ref uniq x
          | some uniq, some (x, path, fid), _ => if fid == 0 then receiver else .refField fid uniq x path false
          | some uniq, none, some (x, path, fid) => .refField fid uniq x path true
          | some uniq, none, none =>
            match element uniq 8 receiver with
            | some e => e
            | none =>
              -- (A value made where it is called on, `half(4).is_ok()`:
              -- given a name first, and borrowed.)
              match receiver with
              -- (Not what a function written to give a reference gives.)
              | .call _ (.name _ g) _ =>
                if (taken.lookup (givesKey g)).isSome then receiver
                else .call id (.name none (if uniq then borrowMutMark else borrowMark)) [receiver]
              | .call .. => .call id (.name none (if uniq then borrowMutMark else borrowMark)) [receiver]
              -- (A constructor without fields or a constant, `D.greet()`.)
              | .name none x =>
                if (lastSegment x).front.isUpper then
                  .call id (.name none (if uniq then borrowMutMark else borrowMark)) [receiver]
                else receiver
              | _ => receiver
          | _, _, _ => receiver
        .call id (.name q name) (given :: rest)
      else .call id f args
    | _, _ => .call id f args
  | e => Id.run (e.traverse (pure <| receiverExpr taken known ·) fun pats body =>
      pure (match receiverClause taken known [] (.mk pats body) with | .mk _ body => body))

/-- (`values`: the parameters written with types that are no reference's.) -/
partial def receiverClause (taken : List (String × Bool)) (known : List (String × Nat))
    (values : List String) : Clause → Clause
  | .mk pats body =>
    let named := (pats.flatMap patternNames).map fun x =>
      (x, if values.contains x then 2 else if known.lookup x == some 3 then 3 else 0)
    .mk pats (receiverStmts taken (named ++ known) body)

partial def receiverStmts (taken : List (String × Bool)) (known : List (String × Nat)) :
    List Stmt → List Stmt
  | [] => []
  | s :: rest =>
    let rec here : Stmt → Stmt × List (String × Nat)
      | .let_ pat value =>
        -- (`let s = &v[i]`: an element borrowed, a reference.)
        let elementRef := match value with
          | .call _ (.name _ f) _ => f == "element_at" || f == "place_at"
          | .ref _ _ => true
          | .refField .. => true
          | _ => false
        let kind := match pat with
          | .var _ => if elementRef then 3 else if valueLike value then 2 else 0
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
  let taken := takesReference items ++ (givesReference items).map (givesKey ·, false)
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
        -- (Those written with a reference's type: a field of what one points
        -- to is borrowed through it.)
        let refs : List String := match c with
          | .mk pats _ => (pats.zip annots).filterMap fun
            | (Pattern.var x, some (TypeExpr.ref _ _ _)) => some x
            | _ => none
        nameBorrowsClause (receiverClause taken (refs.map (·, 3)) values c))
    | .impl ps tr head args context methods => .impl ps tr head args context (methods.map go)
    | .traitInfo name supers defaults params assocs => .traitInfo name supers (defaults.map go) params assocs
    | .alias name value => .alias name (receiverExpr taken [] value)
    | item => item
  promoteItems (items.map go)

/-- Each implementation for every type, `impl<T: Show> Print for T`, written
out as one for each type made with a name, each tuple and callable of a few
parts, and each reference, that has an implementation of every trait it asks
of `T` (or every such type, if it asks none): `impl<A> Print for Option<A>
where Option<A>: Show`. Not for a type that has an implementation of the
trait for all its arguments: that one is the type's. A type with one for some
of its arguments (`impl Print for Option<Int>`) has both, and the one that
asks more of the type is the one for those (as for any two). In each copy
`T` is the type it is for, and its calls are told apart from the other
copies'. The copies come after everything else. -/
def expandBlankets (items : List Item) : List Item := Id.run do
  let blankets := items.filterMap fun
    | .impl ps tr head [t] ctx ms => if head == blanketHead then some (ps, tr, t, ctx, ms) else none
    | _ => none
  if blankets.isEmpty then return items
  let rest := items.filter fun
    | .impl _ _ head _ _ _ => head != blanketHead
    | _ => true
  let declared : List (String × List String) := rest.filterMap fun
    | .struct n ps _ | .pub _ (.struct n ps _) | .enum n ps _ | .pub _ (.enum n ps _) => some (n, ps)
    | _ => none
  let params := fun (n : Nat) => (List.range n).map (s!"T{·}")
  let heads : List (String × List String) :=
    [("Int", [])] ++ scalars.map (fun (n, _) => (n, [])) ++ declared
      ++ (List.range 9).map (fun n => (s!"(tuple{n})", params n))
      ++ (List.range 7).map (fun n => (s!"(fn{n})", params (n + 1)))
      ++ [("(&)", ["T"]), ("(&mut)", ["T"])]
  -- (Which trait each implementation is of, for which head, and whether for
  -- all of the head's arguments.)
  -- (The arguments an implementation gives its trait, as written.)
  let givenArgs := fun (ms : List Item) => (List.range ms.length).filterMap fun i =>
    ms.findSome? fun
      | .typeAlias name _ body => if name == traitArgName i then some body.spell else none
      | _ => none
  -- (Which trait each implementation is of, at which arguments, for which
  -- head.)
  let implOf : Item → Option (String × String × List String) := fun
    | .impl _ tr head _ _ ms => some (traitBase tr, head, givenArgs ms)
    | _ => none
  let mut known : List (String × String × List String) := rest.filterMap implOf
  -- (Those another implementation for every type gave, by which: two of
  -- them for one trait both written out for a type are two implementations
  -- of it for that type, which the checker refuses.)
  let mut byBlanket : List (Nat × String × String × List String) := []
  -- (`impl !Print for Secret {}`: not written out for that type.)
  let last := fun (s : String) => (s.splitOn "::").getLast!
  let denied := rest.filterMap fun
    | .fieldNames mark [tr, head] _ => if mark == attrMark "negative_impl" then some (last tr, last head) else none
    | _ => none
  -- (What a function generic in `T` may take a trait of `T` to be met by:
  -- see `Check.St.blanketTraits`.)
  let mut out : Array Item := (blankets.map fun (_, tr, t, ctx, _) =>
    Item.fieldNames (attrMark "blanket_impl")
      (traitBase tr :: ctx.filterMap fun (p, c) => if p == t then some (traitBase c) else none) []).toArray
  let mut copies := 0
  -- (A copy may give what another asks: as many rounds as there are.)
  for _ in List.range (blankets.length + 1) do
    let mut more := false
    for ((ps, tr, t, ctx, ms), b) in blankets.zipIdx do
      let asked := ctx.filterMap fun (p, c) => if p == t then some (traitBase c) else none
      for (h, hps) in heads do
        let fresh := hps.zipIdx.map fun (p, j) => if p.startsWith "'" then s!"'%b{j}" else s!"%b{j}"
        let self := selfTypeOf h (fresh.map (TypeExpr.name · []))
        let mine := givenArgs (ms.map fun
          | .typeAlias n takes body => .typeAlias n takes (substTypeExpr [(t, self)] body)
          | item => item)
        if byBlanket.any (fun (b', tr', h', a) => b' == b && tr' == traitBase tr && h' == h && a == mine) then continue
        let mineToo := byBlanket.any fun (b', tr', h', a) => b' != b && tr' == traitBase tr && h' == h && a == mine
        if !mineToo && known.any (fun (tr', h', a) => tr' == traitBase tr && h' == h && a == mine) then continue
        if denied.contains (last (traitBase tr), last h) then continue
        unless asked.all (fun c => known.any fun (c', h', _) => c' == c && h' == h) do continue
        let ctx' := ctx.zipIdx.map fun ((p, c), k) => if p == t then (s!"%subject{k}", c) else (p, c)
        let subjects := (ctx.zipIdx.filter fun ((p, _), _) => p == t).map fun (_, k) =>
          Item.typeAlias (ctxSubjectName k) [] self
        copies := copies + 1
        let shift := 100000000000000 * copies
        let ms' := ms.map fun
          | .typeAlias n takes body => .typeAlias n takes (substTypeExpr [(t, self)] body)
          | .fn m fps annots ret clauses =>
            .fn m fps (annots.map (·.map (substTypeExpr [(t, self)]))) (ret.map (substTypeExpr [(t, self)]))
              (clauses.map (shiftClause shift))
          | item => item
        out := out.push (.impl (fresh ++ ps.filter (· != t)) tr h fresh ctx'
          (ms' ++ subjects ++ [.typeAlias (blanketName t) [] self]))
        known := known ++ [(traitBase tr, h, mine)]
        byBlanket := byBlanket ++ [(b, traitBase tr, h, mine)]
        more := true
    unless more do break
  pure (rest ++ out.toList)

/-- A type with `Self::Name` in it written `<Self as Trait<..>>::Name`, of
the implementation's own trait and type. -/
partial def selfAssocs (self : TypeExpr) (tr : String) (targs : List TypeExpr) : TypeExpr → TypeExpr
  | .name x args =>
    match x.splitOn "::" with
    | ["Self", name] => if args.isEmpty then .name assocOfMark [self, .name tr targs, .name name []]
      else .name x (args.map (selfAssocs self tr targs))
    | _ => .name x (args.map (selfAssocs self tr targs))
  | .tuple ts => .tuple (ts.map (selfAssocs self tr targs))
  | .fn ps r => .fn (ps.map (selfAssocs self tr targs)) (selfAssocs self tr targs r)
  | .performs r effs => .performs (selfAssocs self tr targs r) (effs.map fun (e, as) => (e, as.map (selfAssocs self tr targs)))
  | .ref u t l => .ref u (selfAssocs self tr targs t) l
  | t => t

/-- Each implementation with the functions its trait gives a body that it
does not write itself; and, where it gives its trait arguments, `impl
From<Int> for u8`, as an implementation of the trait at those: `From<Int>` is
the name of what it implements from here on. -/
def fillDefaults (items : List Item) : List Item :=
  -- (Implementations for every type written out for each.)
  let items := expandBlankets items
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
      let said := methods.filterMap fun
        | .typeAlias n _ _ => some n
        | _ => none
      let missing := ((defaults.lookup tr).getD []).filter fun
        | .fn m _ _ _ _ => !written.contains m
        | .typeAlias n _ _ => !said.contains n
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
        -- (A type's default is written against `Self` too.)
        | .typeAlias n takes body => .typeAlias n takes (TypeExpr.withSelf self body)
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
      -- (`Self::Components` in its functions: what this implementation's
      -- trait leaves, at this type.)
      let targs := (List.range methods.length).filterMap fun i =>
        methods.findSome? fun
          | .typeAlias name _ body => if name == traitArgName i then some body else none
          | _ => none
      let ofSelf := selfAssocs self tr targs
      let all := (methods ++ missing).map fun
        | .fn m fps annots ret clauses =>
          Item.fn m fps (annots.map (·.map ofSelf)) (ret.map ofSelf)
            (clauses.map fun c => match mapTypesClause (fun t => pure (ofSelf t)) c with
              | .ok c => c
              | .error _ => c)
        | item => item
      let tr := if before == 0 then tr else s!"{tr}#{before}"
      .impl ps (traitAt tr given) head args context all
    | (item, _) => item

end Glorious.Syntax
