module

public import Glorious.Syntax.Ast
public import Glorious.Syntax.FlatOps
public import Glorious.Trace
public import Std.Data.HashMap
public import Std.Data.HashSet

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
  | t => t.mapParts (elideLifetimes lifes)

/-- The type a default's alias (`defaultKey`) is of, with whether it is of a
place among the types (`~`). -/
def defaultOf? (alias : String) : Option (String × Bool) :=
  let segs := alias.splitOn "::"
  let last := segs.getLast!
  if last.startsWith "%default:" then
    let parts := (last.drop "%default:".length).toString.splitOn ":"
    some ("::".intercalate (segs.dropLast ++ [":".intercalate parts.dropLast]), alias.endsWith "~")
  else none

mutual

/-- A type with every alias in it written out. `seen` are the aliases being
written out already: one that stands for itself has no meaning. `defaulted`:
the types with defaults, each with whether one is of a place among the
types. -/
partial def expandTypeExpr (aliases : Std.HashMap String (List String × TypeExpr))
    (defaulted : Std.HashMap String Bool) (seen : List String) : TypeExpr → Except String TypeExpr
  | .name x args => do
    let mut args ← args.mapM (expandTypeExpr aliases defaulted seen)
    -- A declared type whose last parameter is `..T`: what is written from
    -- there on is one tuple.
    if let some (_, .name k []) := aliases[variadicKey x]? then
      if let some k := k.toNat? then args := args.take k ++ [.tuple (args.drop k)]
    let some byTypes := defaulted[x]? | expandNamed aliases defaulted seen x args
    -- A declared type written with fewer arguments than it has parameters:
    -- the rest are what its declaration says they are where not written.
    -- (Of a use that writes no lifetime, by the place among the types,
    -- which are what the default is given.)
    let written := args.any fun | .name l [] => l.startsWith "'" | _ => false
    let byTypes := !written && byTypes
    repeat
      match aliases[defaultKey x args.length ++ (if byTypes then "~" else "")]? with
      | some (params, body) =>
        let params := genericParams params
        let params := if byTypes then params.filter (!·.startsWith "'") else params
        let given := params.zip args
        args := args ++ [← expandTypeExpr aliases defaulted seen (substTypeExpr given body)]
      | none => break
    expandNamed aliases defaulted seen x args
  | .tuple args => .tuple <$> args.mapM (expandTypeExpr aliases defaulted seen)
  | .fn ps r => do
    pure (.fn (← ps.mapM (expandTypeExpr aliases defaulted seen)) (← expandTypeExpr aliases defaulted seen r))
  | .performs r effects => do
    let effects ← effects.mapM fun (e, args) => do
      pure (e, ← args.mapM (expandTypeExpr aliases defaulted seen))
    pure (.performs (← expandTypeExpr aliases defaulted seen r) effects)
  | .ref uniq t life => do pure (.ref uniq (← expandTypeExpr aliases defaulted seen t) life)
  | t => pure t

/-- A named type, its arguments written out, with the alias it is written out. -/
partial def expandNamed (aliases : Std.HashMap String (List String × TypeExpr))
    (defaulted : Std.HashMap String Bool) (seen : List String) (x : String) (args : List TypeExpr) :
    Except String TypeExpr := do
    match aliases[x]? with
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
      expandTypeExpr aliases defaulted (x :: seen) (substTypeExpr (params.zip args) body)

end


/-- The size and alignment of a type that mentions no type parameter, where
its structure says them without asking anything (`staticLayout`): `none`
where it does not (a type parameter, or one not declared). -/
partial def staticLayout (fields : Std.HashMap String (List String × List (List TypeExpr)))
    (seen : List String) : TypeExpr → Option (Nat × Nat)
  | .name x args =>
    if x == rankedMark then some (16, 8)
    else if x == "Int" then some (8, 8)
    else if let some w := scalars.lookup x then
      let b := match w with
        | some bits => bits.natAbs / 8
        | none => if x == "f32" || x == "char" then 4 else 8
      some (b, b)
    else if seen.contains x then some (8, 8)
    else match fields[x]? with
      | some (ps, cs) =>
        if ps.length != args.length then none else
        let m := ps.zip args
        let tagged := cs.length > 1
        let variant := fun (fs : List TypeExpr) => fs.foldlM (init := (if tagged then (1, 1) else (0, 1))) fun (s, a) f => do
          let (fs', fa) ← staticLayout fields (x :: seen) (substTypeExpr m f)
          let fa := max fa 1
          let start := (s + fa - 1) / fa * fa
          pure (start + fs', max a fa)
        let vs := cs.mapM variant
        vs.map fun vs =>
          let (s, a) := vs.foldl (fun (s, a) (s', a') => (max s s', max a a')) (if tagged then (1, 1) else (0, 1))
          ((s + a - 1) / a * a, a)
      | none => none
  | .tuple args =>
    args.foldlM (init := ((0 : Nat), (1 : Nat))) (fun (s, a) f => do
      let (fs, fa) ← staticLayout fields seen f
      let fa := max fa 1
      let start := (s + fa - 1) / fa * fa
      pure (start + fs, max a fa)) |>.map fun (s, a) => ((s + a - 1) / a * a, a)
  | .ref .. => some (8, 8)
  | .fn .. | .performs .. => some (16, 8)
  | _ => none

/-- Is a field's type said, not a bare field name whose type is left to be
found: of a type there is, or a type parameter. -/
partial def typedField (known : Std.HashSet String) (ps : List String) : TypeExpr → Bool
  | .name x args => x.startsWith "%" || ((known.contains x || ps.contains x || x.contains ':' || (x.toList.headD 'a').isUpper) && args.all (typedField known ps))
  | .tuple args => args.all (typedField known ps)
  | _ => true

/-- A type with `Self::Name` in it written `<Self as Trait<..>>::Name`, of
the implementation's own trait and type. -/
partial def selfAssocs (self : TypeExpr) (tr : String) (targs : List TypeExpr) : TypeExpr → TypeExpr
  | .name x [] =>
    match x.splitOn "::" with
    | ["Self", name] => .name assocOfMark [self, .name tr targs, .name name []]
    | _ => .name x []
  | t => t.mapParts (selfAssocs self tr targs)

namespace Flat


/-- What the front end's passes made of items before (`kept`), and what
they make now (`made`, where `keep`): each pass's result for one item, under
a key of the pass, what it reads of the program besides the item, and the
item. A compile that changed one function's body makes that one anew. -/
structure FrontMemo where
  kept : Std.HashMap UInt64 (List Item) := {}
  made : Array (UInt64 × List Item) := #[]
  keep : Bool := false

/-- A hash of a map's entries, whatever their order. -/
def unorderedHash {κ ν : Type} [BEq κ] [Hashable κ] [Hashable ν] (m : Std.HashMap κ ν) : UInt64 :=
  m.fold (init := 7) fun h k v => h + hash (k, v)

/-- What `make` gives, or what was made under `key` before. -/
def FrontMemo.take (m : FrontMemo) (key : UInt64) (make : Unit → List Item) : List Item × FrontMemo :=
  let v := match m.kept[key]? with
    | some v => v
    | none => make ()
  (v, if m.keep then { m with made := m.made.push (key, v) } else m)

/-- A program without its type aliases: each use is what the alias stands for. -/
partial def expandAliases (items : List Item) (memo : FrontMemo := {}) : Except String (List Item × FrontMemo) := do
  let aliases := items.filterMap fun
    | (.typeAlias name params body) => some (name, params, body)
    | _ => none
  let mut seen : Std.HashSet String := {}
  for (name, _, _) in aliases do
    if seen.contains name then throw s!"type alias `{name}` is declared twice"
    seen := seen.insert name
  -- A type the program declares is that type, whatever an alias of the same
  -- name would have stood for.
  let declared : Std.HashSet String := .ofList (items.filterMap fun
    | (.enum name _ _) => some name
    | (.struct name _ _) => some name
    | _ => none)
  let aliases := aliases.filter fun (name, _, _) => !declared.contains name
  if aliases.isEmpty then return (items, memo)
  let byName : Std.HashMap String (List String × TypeExpr) :=
    aliases.foldl (fun m (name, ps, body) => if m.contains name then m else m.insert name (ps, body)) {}
  let defaulted : Std.HashMap String Bool := aliases.foldl (fun m (name, _, _) =>
    match defaultOf? name with
    | some (x, byTypes) => m.insert x (byTypes || m.getD x false)
    | none => m) {}
  let ty := expandTypeExpr byName defaulted []
  -- An argument of an implementation's type that is not one of its type
  -- parameters is a type: `impl T for Option<Int>`. It is fixed, as an
  -- argument another name of the type fixes is.
  let concrete := fun (whole : ImplOf Item) => do
    let mut newArgs : Array String := #[]
    let mut fresh : Array String := #[]
    let mut fixed := whole.fixed
    for (a, j) in whole.args.zipIdx do
      if whole.params.contains a || whole.head.startsWith "(tuple" then newArgs := newArgs.push a
      else
        let name := s!"%fixed{j}"
        newArgs := newArgs.push name
        fresh := fresh.push name
        fixed := fixed ++ [(j, ← ty (.name a []))]
    pure (Item.impl { whole with params := whole.params ++ fresh.toList, args := newArgs.toList, fixed })
  let rec item : Item → Except String Item
    -- (What is said of a type parameter: `F: Fn<(Int,), Output = Bool>`.)
    | .bounds f bs => do
      pure (.bounds f (← bs.mapM fun b => do
        pure { b with args := ← b.args.mapM ty, assoc := ← b.assoc.mapM fun (n, t) => do pure (n, ← ty t) }))
    | (.enum name ps ctors) => do
      pure ((.enum name ps (← ctors.mapM fun (c, fields) => do pure (c, ← fields.mapM ty))))
    | (.struct name ps fields) => do pure ((.struct name ps (← fields.mapM ty)))
    | (.effect name ps ops) => do
      let ops ← ops.mapM fun op => do
        pure { op with payload := ← op.payload.mapM ty, result := ← op.result.mapM ty }
      pure ((.effect name ps ops))
    | .fn name ps annots ret b => do
      pure (.fn name ps (← annots.mapM fun a => a.mapM ty) (← ret.mapM ty) (← mapTypes ty b))
    | (.trait name methods) => do
      pure ((.trait name (← methods.mapM fun md => do
        pure { md with params := ← md.params.mapM ty, ret := ← md.ret.mapM ty })))
    | .impl whole@{ params := ps, trait := tr, head := head, args := args, context := context, methods := methods, .. } => do
      let tr := TraitKey.at tr.base tr.nth (← tr.written.mapM ty)
      let context ← context.mapM (·.mapTypesM ty)
      let methods ← methods.mapM fun
        | (.typeAlias name aps body) => do pure ((.typeAlias name aps (← ty body)))
        | m => item m
      let fixed ← whole.fixed.mapM fun (j, t) => do pure (j, ← ty t)
      -- For a type whose last parameter is `..T`: the arguments written from
      -- there on are one tuple, an argument the implementation fixes.
      let (ps, args, fixed) := match byName[variadicKey head]? with
        | some (_, .name kk []) =>
          match kk.toNat? with
          | some k =>
            let parts := (args.drop k).zipIdx.map fun (a, i) =>
              if ps.contains a then TypeExpr.name a [] else (fixed.lookup (k + i)).getD (.name a [])
            let rest := fixed.filter fun (j, _) => j < k
            let name := s!"%fixed{k}"
            (ps.filter (fun p => !((List.range args.length).drop k |>.any (s!"%fixed{·}" == p))) ++ [name],
              args.take k ++ [name], rest ++ [(k, .tuple parts)])
          | none => (ps, args, fixed)
        | _ => (ps, args, fixed)
      let whole := { whole with params := ps, trait := tr, args, context, methods, fixed }
      -- An implementation for another name of a type, `impl T for
      -- Option<A>`, is one for the type the name stands for, with the
      -- arguments the name fixes said beside it.
      match byName[head]? with
      | some (aps, .name target targs) =>
        let given := aps.zip args
        let mut newArgs : Array String := #[]
        let mut fresh : Array String := #[]
        let mut fixed := whole.fixed
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
            fixed := fixed ++ [(j, ← ty targ)]
        concrete { whole with params := ps ++ fresh.toList, head := target, args := newArgs.toList, fixed }
      | _ => concrete whole
    -- A name given a value with its type written, `let Just: fn(Int) ->
    -- Option<Int> = Ok;`.
    | .alias name b value => do
      let (b, value) ← mapTypesOf ty b value
      pure (.alias name b value)
    | i => pure i
  let rest := items.filter fun
    | (.typeAlias _ _ _) => false
    | _ => true
  -- (Each item made from it, the aliases and the types declared.)
  let ctx := mixHash (hash "aliases") (mixHash (hash aliases) (unorderedHash (declared.fold (init := ({} : Std.HashMap String Unit)) fun m n => m.insert n ())))
  let mut out : Array Item := #[]
  let mut memo := memo
  for i in rest do
    let key := mixHash ctx (hash i)
    match memo.kept[key]? with
    | some v =>
      out := out ++ v.toArray
      if memo.keep then memo := { memo with made := memo.made.push (key, v) }
    | none =>
      let v ← item i
      out := out.push v
      if memo.keep then memo := { memo with made := memo.made.push (key, [v]) }
  pure (out.toList, memo)

/-- The heads a type can have without being declared, with type parameters
for their parts: `Int` and the scalars, then `declared`, then tuples,
callables and references. -/
def builtinHeads (declared : List (String × List String) := []) : List (String × List String) :=
  let params := fun (n : Nat) => (List.range n).map (s!"T{·}")
  [("Int", [])] ++ scalars.map (fun (n, _) => (n, [])) ++ declared
    ++ (List.range 9).map (fun n => (s!"(tuple{n})", params n))
    ++ (List.range 7).map (fun n => (s!"(fn{n})", params (n + 1)))
    ++ [("(&)", ["T"]), ("(&mut)", ["T"])]

/-- `NilRepresented` (the prelude's) for each type that is nothing (one
constructor, each field a type parameter, asked it too, or of a type that is
nothing itself, and no `drop` to run): each declared type's right after its
declaration, and the tuples' right after the trait's. In place, so that the
prelude's are the same, item for item, in a program as where the prelude is
checked alone. (What a type takes in memory is its layout, from its type:
`Lower.Layout`.) -/
def writeNils (items : List Item) (memo : FrontMemo := {}) : List Item × FrontMemo := Id.run do
  let rec flatAll : List Item → List Item
    | [] => []
    | .module _ (some body) :: rest => flatAll body ++ flatAll rest
    | .pub _ inner :: rest => flatAll [inner] ++ flatAll rest
    | item :: rest => item :: flatAll rest
  let all := flatAll items
  unless all.any (fun | (.trait n _) => n == nilTrait | _ => false) do return (items, memo)
  let fieldsOf : Std.HashMap String (List String × List (List TypeExpr)) := all.foldl (init := {}) fun m item =>
    match item with
    | (.struct n ps fs) => m.insert n (ps, [fs])
    | (.enum n ps cs) => m.insert n (ps, cs.map (·.2))
    | _ => m
  let count := 0
  -- (The types a field may be of: those declared, and those with none.)
  let known : Std.HashSet String := Std.HashSet.ofList (fieldsOf.toList.map (·.1) ++ ["Int"] ++ scalars.map (·.1))
  let dropped := all.filterMap fun
    | .impl { trait := tr, head := h, .. } => if lastSegment tr.base == "Drop" then some h else none
    | _ => none
  -- (The implementation for one head; none for a type with a field whose
  -- type is left to be found.)
  let implFor := fun (head : String) (ps : List String) =>
    let fresh := ps.zipIdx.map fun (p, j) => if p.startsWith "'" then s!"'%l{j}" else s!"%l{j}"
    let untyped := match fieldsOf[head]? with
      | some (ps, cs) => cs.any (·.any (!typedField known ps ·))
      | none => false
    if untyped then [] else
    match (if head.startsWith "(tuple" then some (ps, [ps.map (TypeExpr.name · [])]) else fieldsOf[head]?) with
    | some (hps, [fs]) =>
      let isParam := fun (f : TypeExpr) => match f with
        | .name x [] => hps.contains x
        | _ => false
      let nothing := fun (f : TypeExpr) => isParam f || (staticLayout fieldsOf [head] f).any (·.1 == 0)
      if !dropped.contains head && fs.all nothing then
        let m := hps.zip fresh
        let asked := (fs.filterMap fun f => match f with
          | .name x [] => m.lookup x
          | _ => none).eraseDups
        [Item.impl { params := fresh, trait := (.of nilTrait), head := head, args := fresh, context := (asked.map (Cond.of · nilTrait)), methods := [] }]
      else []
    | _ => []
  -- (After what is written out beside a declaration, `fieldNames`.)
  let rec beside : List Item → List Item × List Item
    | ((.fieldNames m ns ps)) :: rest =>
      if m.startsWith "%" then ([], (.fieldNames m ns ps) :: rest) else
      let (mine, after) := beside rest
      ((.fieldNames m ns ps) :: mine, after)
    | rest => ([], rest)
  -- (Each type's made from the type and what the types declared are.)
  let ctx := mixHash (hash "nils") (hash (unorderedHash fieldsOf, dropped))
  let implKept := fun (memo : FrontMemo) (h : String) (ps : List String) =>
    memo.take (mixHash ctx (hash (h, ps))) fun _ => implFor h ps
  -- (`fuel`: one for each item.)
  let rec go (fuel : Nat) (memo : FrontMemo) : List Item → (List Item × FrontMemo)
    | [] => ([], memo)
    | item :: rest =>
      match fuel with
      | 0 => (item :: rest, memo)
      | fuel + 1 =>
        let declared : Option (String × List String) := match item with
          | (.struct n ps _) | (.enum n ps _) | .pub _ ((.struct n ps _))
          | .pub _ ((.enum n ps _)) => some (n, ps)
          | _ => none
        match declared with
        | some (n, ps) =>
          let (names, rest) := beside rest
          let (mine, memo) := implKept memo n ps
          let (more, memo) := go fuel memo rest
          (item :: names ++ mine ++ more, memo)
        | none =>
          let (mine, memo) : List Item × FrontMemo := match item with
            | (.trait n _) =>
              if n == nilTrait then
                let (out, memo) := (builtinHeads.filter (·.1.startsWith "(tuple")).foldl (fun (acc : List Item × FrontMemo) (h, ps) =>
                  let (made, m) := implKept acc.2 h ps
                  (acc.1 ++ made, m)) ([], memo)
                (item :: out, memo)
              else ([item], memo)
            | .module name (some body) =>
              let (body, memo) := go fuel memo body
              ([.module name (some body)], memo)
            | other => ([other], memo)
          let (more, memo) := go fuel memo rest
          (mine ++ more, memo)
  let _ := count
  let (out, memo) := go (2 * (flatAll items).length + 2) memo items
  (out, memo)

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
    | .impl whole@{ params := ps, trait := tr, head := head, args := [t], context := ctx, methods := ms, .. } => if head == blanketHead then some (ps, tr, t, ctx, ms, whole) else none
    | _ => none
  if blankets.isEmpty then return items
  let rest := items.filter fun
    | .impl { head := head, .. } => head != blanketHead
    | _ => true
  let declared : List (String × List String) := rest.filterMap fun
    | (.struct n ps _) | .pub _ ((.struct n ps _)) | (.enum n ps _)
    | .pub _ ((.enum n ps _)) => some (n, ps)
    | _ => none
  let heads := builtinHeads declared
  -- (The arguments an implementation gives its trait, as written.)
  -- (Which trait each implementation is of, at which arguments, for which
  -- head.)
  let implOf : Item → Option (String × String × List String) := fun
    | .impl { trait := tr, head := head, .. } => some (tr.base, head, tr.written.map (·.spell))
    | _ => none
  let mut known : Std.HashSet (String × String × List String) := .ofList (rest.filterMap implOf)
  -- (Which traits each head has some implementation of.)
  let mut has : Std.HashSet (String × String) := .ofList ((rest.filterMap implOf).map fun (tr, h, _) => (tr, h))
  -- (Those another implementation for every type gave, by which.)
  let mut byBlanket : Std.HashMap (String × String × List String) (List Nat) := {}
  -- (`impl !Print for Secret {}`: not written out for that type.)
  let last := fun (s : String) => (s.splitOn "::").getLast!
  let denied := rest.filterMap fun
    | (.fieldNames mark [tr, head] _) => if mark == attrMark "negative_impl" then some (last tr, last head) else none
    | _ => none
  -- (What a function generic in `T` may take a trait of `T` to be met by.)
  let mut out : Array Item := (blankets.map fun (_, tr, t, ctx, _, _) =>
    (.fieldNames (attrMark "blanket_impl")
      (tr.base :: ctx.filterMap fun (c : Cond) => if c.subject == t then some c.trait.base else none) [])).toArray
  let mut copies := 0
  -- (How many traits of its type each asks: tried first.)
  let askedOf := fun (b : Nat) => match blankets[b]? with
    | some (_, _, t, ctx, _, _) => (ctx.filter fun (c : Cond) => c.subject == t).length
    | none => 0
  let order := (List.range blankets.length).mergeSort fun a b => askedOf a ≥ askedOf b
  let blankets := order.filterMap fun b => blankets[b]?
  -- (A copy may give what another asks: as many rounds as there are.)
  for _ in List.range (blankets.length + 1) do
    let mut more := false
    for ((ps, tr, t, ctx, ms, whole), b) in blankets.zipIdx do
      let asked := ctx.filterMap fun (c : Cond) => if c.subject == t then some c.trait.base else none
      let bodies := tr.written
      for (h, hps) in heads do
        let fresh := hps.zipIdx.map fun (p, j) => if p.startsWith "'" then s!"'%b{j}" else s!"%b{j}"
        let self := selfTypeOf h (fresh.map (TypeExpr.name · []))
        let mine := bodies.map fun body => (substTypeExpr [(t, self)] body).spell
        let givers := byBlanket.getD (tr.base, h, mine) []
        if givers.contains b then continue
        -- (One that asks more already gave it this type: that one is its.)
        let asksOf := fun (g : Nat) => match blankets[g]? with
          | some (_, _, t', ctx', _, _) => (ctx'.filter fun (c : Cond) => c.subject == t').length
          | none => 0
        if givers.any (fun g => asksOf g > asked.length) then continue
        let mineToo := givers.any (· != b)
        if !mineToo && known.contains (tr.base, h, mine) then continue
        if denied.contains (last (tr.base), last h) then continue
        -- (A tuple of one or more has the one for its first and the rest.)
        if h.startsWith "(tuple" && h != "(tuple0)" && has.contains (tr.base, consHead) then continue
        if h.startsWith "(fn" && has.contains (tr.base, "%Fn") then continue
        unless asked.all (fun c => has.contains (c, h)) do continue
        let ctx' := ctx.zipIdx.map fun (c, k) =>
          let c := c.mapTypes (substTypeExpr [(t, self)])
          if c.subject == t then { c with subject := s!"%subject{k}", subjectTy := some self } else c
        copies := copies + 1
        let shift := 100000000000000 * copies
        -- (`self_name()` in it: this type's name.)
        let named : FRewrite := { onExpr := fun _ b e => match b.expr e with
          | .call _ f #[] =>
            -- (Written as the resolver has written texts by now: the
            -- prelude's constructors by their own names.)
            if b.bare? f == some selfNameFn then some (flatExpr (textValue ((last h).toList.map Char.toNat)))
            else none
          | _ => none }
        let ms' := ms.map fun
          | (.typeAlias n takes body) => (.typeAlias n takes (substTypeExpr [(t, self)] body))
          | .fn m fps annots ret b =>
            .fn m fps (annots.map (·.map (substTypeExpr [(t, self)]))) (ret.map (substTypeExpr [(t, self)]))
              (named.body ((shiftRewrite shift).body b))
          | item => item
        out := out.push (.impl { whole with params := (fresh ++ ps.filter (· != t)), trait := (tr.mapWritten (substTypeExpr [(t, self)])), head := h, args := fresh, context := ctx', methods := ms', blanket := some t })
        known := known.insert (tr.base, h, mine)
        has := has.insert (tr.base, h)
        byBlanket := byBlanket.insert (tr.base, h, mine) (givers ++ [b])
        more := true
    unless more do break
  pure (rest ++ out.toList)

/-- A trait's type parameters that a use does not write, written out as the
trait says (`trait Add<R = Self>`): of a function's bounds, `T: Add` is
`T: Add<T>`; of an implementation, `impl Add for Int` is for `Add<Int>`;
of what an implementation asks, the same of its subject. `Self` is the type
the trait is of there. -/
def traitArgDefaults (items : List Item) : List Item := Id.run do
  let defaults : Std.HashMap String (List (Nat × List String × TypeExpr)) := items.foldl (init := {}) fun m item =>
    match item with
    | .traitInfo name _ fns _ _ =>
      let ds := fns.filterMap fun
        | .typeAlias n earlier ty =>
          if n.startsWith "%traitDefault" then ((n.drop "%traitDefault".length).toString.toNat?).map (·, earlier, ty) else none
        | _ => none
      if ds.isEmpty then m else m.insert name (ds.mergeSort fun a b => a.1 ≤ b.1)
    | _ => m
  if defaults.isEmpty then return items
  let fill := fun (tr : String) (self : TypeExpr) (args : List TypeExpr) =>
    match defaults[tr]? with
    | none => args
    | some ds => ds.foldl (fun args (i, earlier, ty) =>
        if args.length == i then args ++ [substTypeExpr (("Self", self) :: earlier.zip args) ty] else args) args
  let selfOf := fun (head : String) (args : List String) =>
    if head.startsWith "(tuple" then TypeExpr.tuple (args.map (.name · []))
    else TypeExpr.name head (args.map (.name · []))
  let rec go : Item → Item
    | .bounds f bs => .bounds f (bs.map fun b => { b with args := fill b.trait (.name b.subject []) b.args })
    | .pub parent i => .pub parent (go i)
    | .module name (some inner) => .module name (some (inner.map go))
    | .impl whole@{ trait := tr, head := head, args := args, context := context, .. } =>
      let filled := fill tr.base (selfOf head args) tr.written
      -- (What it asks of its type parameters, `where T: Add`, the same.)
      let context := context.map fun (c : Cond) =>
        { c with trait := .at c.trait.base c.trait.nth (fill c.trait.base (.name c.subject []) c.trait.written) }
      .impl { whole with trait := (.at tr.base tr.nth filled), context }
    | item => item
  pure (items.map go)

/-- Each implementation with the functions its trait gives a body that it
does not write itself; and, where it gives its trait arguments, `impl
From<Int> for u8`, as an implementation of the trait at those: `From<Int>` is
the name of what it implements from here on. -/
def fillDefaults (items : List Item) (memo : FrontMemo := {}) : List Item × FrontMemo :=
  let items := traitArgDefaults items
  -- (Implementations for every type written out for each.)
  let (items, memo) := Trace.timed "fill: nils" fun _ => writeNils items memo
  let items := Trace.timed "fill: blankets" fun _ => expandBlankets items
  let defaults := items.filterMap fun
    | .traitInfo name _ fns _ _ => some (name, fns)
    | _ => none
  -- (How many implementations of each trait for each type, at the same
  -- arguments, came before: the later ones are numbered.)
  -- (A trait's defaults by a key of them: each implementation's is made
  -- from its item, where it is and which of its trait at its arguments it
  -- is, and its trait's defaults.)
  let defaultKeys : Std.HashMap String UInt64 := defaults.foldl (fun m (n, fns) => m.insertIfNew n (hash fns)) {}
  let (_, out, memo) := Trace.timed "fill: defaults" fun _ => items.zipIdx.foldl (init := (({} : Std.HashMap (String × String × List String) Nat), #[], memo))
    fun (seen, out, memo) (item, index) => match item with
    | .impl whole@{ trait := tr, head := head, args := args, methods := methods, .. } =>
      let targs := tr.written
      let given := targs.map (·.spell)
      let before := seen.getD (tr.base, head, given) 0
      let key := mixHash (hash "defaults") (hash (defaultKeys.getD tr.base 0, index, before, item))
      let (made, memo) := memo.take key fun _ =>
        let written := methods.filterMap fun
          | .fn m _ _ _ _ => some m
          | _ => none
        let said := methods.filterMap fun
          | (.typeAlias n _ _) => some n
          | _ => none
        let missing := ((defaults.lookup tr.base).getD []).filter fun
          | .fn m _ _ _ _ => !written.contains m
          | (.typeAlias n _ _) => !said.contains n
          | _ => false
        let self := selfTypeOf head (args.map (TypeExpr.name · []))
        -- (A function its trait gives a body: a call of the trait's, checked
        -- once for every implementation, generic in `Self`, at this type.)
        let decls := ((items.findSome? fun | .trait n ms => if n == tr.base then some ms else none | _ => none).getD [])
        let missing := missing.zipIdx.map fun (item, k) => match item with
          | .fn m fps annots _ b =>
            match decls.find? (fun (md : MethodDecl) => md.name == m) with
            | some md =>
              let ps := (List.range md.params.length).map fun i => s!"%arg{i}"
              let cid := 10000000000 * (index + 1) + 7000 + k
              let call := Expr.call cid (.name none s!"%default:{tr.base}::{m}") (ps.map (Expr.name none))
              let at_ := Expr.call 0 (.mark .inst) [call, .type (.tuple (self :: targs))]
              Item.fn m fps (annots.map fun _ => none) none (Flat.ofClauses [.mk (ps.map Pattern.var) [.expr at_]])
            | none => Item.fn m fps annots none b
          -- (A type's default is written against `Self` too.)
          | (.typeAlias n takes body) => (.typeAlias n takes (TypeExpr.withSelf self body))
          | item => item
        -- (`Self::Components` in its functions: what this implementation's
        -- trait leaves, at this type.)
        let ofSelf := selfAssocs self tr.base targs
        let all := (methods ++ missing).map fun
          | .fn m fps annots ret b =>
            Item.fn m fps (annots.map (·.map ofSelf)) (ret.map ofSelf)
              (match mapTypes (fun t => pure (ofSelf t)) b with
                | .ok b => b
                | .error _ => b)
          | item => item
        [.impl { whole with trait := (TraitKey.at tr.base before targs), methods := all }]
      (seen.insert (tr.base, head, given) (before + 1), out ++ made.toArray, memo)
    -- (Each of a trait's defaults a function of its own, after the trait:
    -- generic in `Self`, with the trait's bound and what its signature
    -- asks of types made of `Self`; checked once, as Rust checks a default,
    -- and copied for each type as any generic function is.)
    | item@(.traitInfo tr _ fns params _) =>
      let decls := ((items.findSome? fun | .trait n ms => if n == tr then some ms else none | _ => none).getD [])
      let generic := fns.filterMap fun
        | .fn m _ _ _ b => do
          let md ← decls.find? (·.name == m)
          let name := s!"%default:{tr}::{m}"
          -- (`Self::Components`: what the trait leaves, of `Self`.)
          let ofSelf := selfAssocs (.name "Self" []) tr (params.map (TypeExpr.name · []))
          let b := (selfRewrite "Self" (some (tr, Expr.type (.tuple [.name "Self" []])))).body b
          let b := match mapTypes (fun t => pure (ofSelf t)) b with
            | .ok b => b
            | .error _ => b
          let annots := md.params.map ofSelf
          let ret := md.ret.map ofSelf
          -- (And what its signature asks of types made of `Self`: of `X` in
          -- `<X as Registers<S>>::Out`, `X: Registers<S>`, as Rust's
          -- signatures imply.)
          let rec projections (fuel : Nat) (t : TypeExpr) : List (TypeExpr × String × List TypeExpr) :=
            match fuel, t with
            | 0, _ => []
            | fuel + 1, .name n [subj, .name tr' targs, _] =>
              (if n == assocOfMark then [(subj, tr', targs)] else []) ++ projections fuel subj ++ targs.flatMap (projections fuel)
            | fuel + 1, t => t.parts.flatMap (projections fuel)
          let implied := ((annots ++ ret.toList).flatMap (projections 32)).filter fun (subj, tr', _) =>
            !(subj == .name "Self" [] && tr' == tr)
          let implied := implied.eraseDups.zipIdx.map fun ((subj, tr', targs), k) =>
            ({ subject := s!"%where{k}", subjectTy := some subj, trait := tr', args := targs } : Bound)
          some [Item.fn name ("Self" :: params ++ md.generics) (annots.map some) ret b,
            .bounds name ({ subject := "Self", trait := tr, args := params.map (TypeExpr.name · []) } :: implied)]
        | _ => none
      (seen, (out.push item) ++ generic.flatten.toArray, memo)
    | item => (seen, out.push item, memo)
  (out.toList, memo)

end Flat

end Glorious.Syntax
