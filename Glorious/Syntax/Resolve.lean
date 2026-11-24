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


/-- The arguments an implementation gives its trait, as written
(`traitArgName`), in order. -/
def givenTraitArgs (ms : List Item) : List TypeExpr :=
  let named := ms.filterMap fun
    | .typeAlias name _ body => some (name, body)
    | _ => none
  (List.range named.length).filterMap fun i => named.lookup (traitArgName i)

/-- The names a type mentions, not through a reference, a callable or an
array (each of which holds the other where it is). -/
partial def heldNames : TypeExpr → List String
  | .name x args => if (x.splitOn "::").getLast! == "Array" then [x] else x :: args.flatMap heldNames
  | .tuple args => args.flatMap heldNames
  | .performs r _ => heldNames r
  | _ => []

/-- Does a value of a type hold, not through anything that points, a value of
the type named `head`: its layout would be as large as itself. -/
partial def holdsItself (fields : Std.HashMap String (List String × List (List TypeExpr)))
    (head : String) (seen : List String) (t : TypeExpr) : Bool :=
  (heldNames t).any fun n =>
    n == head || (!seen.contains n && match fields[n]? with
      | some (_, ctors) => ctors.any (·.any (holdsItself fields head (n :: seen)))
      | none => false)

/-- The size and alignment of a type that mentions no type parameter, where
its structure says them without asking anything (`staticLayout`): `none`
where it does not (a type parameter, or one not declared). -/
partial def staticLayout (fields : Std.HashMap String (List String × List (List TypeExpr)))
    (seen : List String) : TypeExpr → Option (Nat × Nat)
  | .name x args =>
    let last := (x.splitOn "::").getLast!
    if x == rankedMark then some (16, 8)
    else if x == "Int" then some (8, 8)
    else if let some w := scalars.lookup x then
      let b := match w with
        | some bits => bits.natAbs / 8
        | none => if x == "f32" || x == "char" then 4 else 8
      some (b, b)
    else if last == "Array" then some (24, 8)
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

/-- `self_size()` and `self_align()` in the copy for `head` of `impl<T>
Layout for T`: the type's size and alignment, from its structure (the
specification's layout, 4.4: fields in their order, each at its alignment;
an enum a tag where it has more than one constructor, then the widest of
its constructors' fields; a field of the type itself, through nothing that
points, a pointer). -/
def layoutOf (fields : Std.HashMap String (List String × List (List TypeExpr)))
    (head : String) (fresh : List String) (base : Nat) : Expr × Expr := Id.run do
  let int := fun (n : Int) => Expr.int n
  let pair := fun (s a : Expr) => Expr.tuple [s, a]
  let mut id := base
  let call := fun (id : Nat) (f : String) (args : List Expr) => Expr.call id (.name none f) args
  let constant := fun (s a : Int) =>
    (call 0 "layout_size" [pair (int s) (int a)], call 0 "layout_align" [pair (int s) (int a)])
  let last := (head.splitOn "::").getLast!
  if head == "Int" then return constant 8 8
  if let some w := scalars.lookup head then
    let bytes : Int := match w with
      | some bits => bits.natAbs / 8
      | none => if head == "f32" || head == "char" then 4 else 8
    return constant bytes bytes
  if head.startsWith "(fn" then return constant 16 8
  if head == "(&)" || head == "(&mut)" then return constant 8 8
  if last == "Array" then return constant 24 8
  let ctors : List (List TypeExpr) ← if head.startsWith "(tuple" then
      pure [fresh.map (TypeExpr.name · [])]
    else match fields[head]? with
      | some (ps, cs) =>
        let m := ps.zip (fresh.map (TypeExpr.name · []))
        pure (cs.map (·.map (substTypeExpr m)))
      | none => pure []
  -- (A field's size and alignment, as a pair.)
  let mut variants : List Expr := []
  let tag := if ctors.length > 1 then pair (int 1) (int 1) else pair (int 0) (int 1)
  for fs in ctors do
    let mut acc := tag
    for f in fs do
      if holdsItself fields head [] f then
        acc := call 0 "layout_add" [acc, int 8, int 8]
      else if (match f with | .fn .. | .performs .. => true | .name x _ => x == rankedMark | _ => false) then
        acc := call 0 "layout_add" [acc, int 16, int 8]
      else if (match f with | .ref .. => true | _ => false) then
        acc := call 0 "layout_add" [acc, int 8, int 8]
      else if let some (s, a) := (if fresh.any (fun p => (heldNames f).contains p) then none else staticLayout fields [head] f) then
        acc := call 0 "layout_add" [acc, int s, int (max a 1)]
      else
        let s := Expr.call 0 (.name none instMark) [call id "size_of" [], (TypeExpr.tuple [f]).asExpr]
        let a := Expr.call 0 (.name none instMark) [call (id + 1) "align_of" [], (TypeExpr.tuple [f]).asExpr]
        id := id + 2
        acc := call 0 "layout_add" [acc, s, a]
    variants := variants ++ [acc]
  let whole := match variants with
    | [] => tag
    | v :: vs => vs.foldl (fun x y => call 0 "layout_widest" [x, y]) v
  (call 0 "layout_size" [whole], call 0 "layout_align" [whole])

/-- `repr_store` and `repr_load` in the copy for `head` of `Repr`: each
field written at its offset, and read back from there, in the order of
`layoutOf` (a tag first, a byte, where there is more than one constructor).
`ctors` are the constructors' names (none for a tuple) and fields. -/
def reprOf (ctors : List (Option String × List TypeExpr)) (base : Nat) : Item × Item := Id.run do
  let name := fun (x : String) => Expr.name none x
  let call := fun (id : Nat) (f : String) (args : List Expr) => Expr.call id (name f) args
  let mut id := base
  let tagged := ctors.length > 1
  let mut stores : List Clause := []
  let mut loads : List Clause := []
  for ((ctor, fs), k) in ctors.zipIdx do
    let vars := (List.range fs.length).map fun i => s!"%v{i}"
    let pat := match ctor with
      | some c => Pattern.ctor c none (vars.map .var)
      | none => Pattern.tuple (vars.map .var)
    -- (Each field's offset, after the tag and the fields before it.)
    let mut offsets : List Stmt := []
    let mut layout := Expr.tuple [.int (if tagged then 1 else 0), .int 1]
    for (f, i) in fs.zipIdx do
      let ty := (TypeExpr.tuple [f]).asExpr
      let size := Expr.call 0 (name instMark) [call id "size_of" [], ty]
      let align := Expr.call 0 (name instMark) [call (id + 1) "align_of" [], ty]
      let align' := Expr.call 0 (name instMark) [call (id + 2) "align_of" [], ty]
      id := id + 3
      offsets := offsets ++ [.let_ (.var s!"%o{i}") (call 0 "layout_start" [layout, align])]
      layout := call 0 "layout_add" [layout, size, align']
    let addr := fun (i : Nat) => call 0 "repr_at" [name "%at", name s!"%o{i}"]
    let tag : List Stmt := if tagged then [.expr (call 0 "ptr_write" [name "%at", .int 8, .int k])] else []
    let mut writes : List Stmt := []
    let mut reads : List Stmt := []
    for i in List.range fs.length do
      writes := writes ++ [.expr (call id "repr_store" [addr i, name s!"%v{i}"])]
      reads := reads ++ [.let_ (.var s!"%v{i}") (call (id + 1) "repr_load" [addr i])]
      id := id + 2
    let made := match ctor with
      | some c => if fs.isEmpty then name c else call 0 c (vars.map name)
      | none => .tuple (vars.map name)
    stores := stores ++ [.mk [.var "%at", pat] (tag ++ offsets ++ writes ++ [.expr (.tuple [])])]
    loads := loads ++ [.mk (if tagged then [.int k] else []) ((if tagged then [.expr (name unsafeMark)] else []) ++ offsets ++ reads ++ [.expr made])]
  let load : List Clause := if tagged then
      [.mk [.var "%at"] [.expr (call (id + 1) "match" [call 0 "ptr_read" [name "%at", .int (-8)],
        .closure id (loads ++ [.mk [.wild] [.expr (call (id + 2) "repr_bad" [name "%at"])]])])]]
    else loads.map fun ⟨_, body⟩ => .mk [.var "%at"] body
  (Item.fnOf "repr_store" [] [] none (stores.map fun ⟨pats, body⟩ => .mk pats (.expr (name unsafeMark) :: body)),
   Item.fnOf "repr_load" [] [] none (load.map fun ⟨pats, body⟩ => .mk pats (.expr (name unsafeMark) :: body)))

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

/-- The name a path of fields starts at, and the path, where the name is
known to hold a value (`receiverExpr`'s `known`). -/
partial def placeOf (b : Body) (known : List (String × Nat)) (e : ExprId) : Nat → Option (String × List String × Nat)
  | 0 => none
  | fuel + 1 =>
    match b.expr e with
    | .name none x => if (known.lookup x).any (fun k => k != 0 && k != 3) then some (x, [], 0) else none
    | .fieldOf fid e field => (placeOf b known e fuel).map fun (x, path, _) => (x, path ++ [field], fid)
    | .proj e n => (placeOf b known e fuel).map fun (x, path, fid) => (x, path ++ [toString n], fid)
    | _ => none

/-- A field of what a reference a name holds points to, `p.items`. -/
partial def throughRefOf (b : Body) (known : List (String × Nat)) (e : ExprId) : Nat → Option (String × List String × Nat)
  | 0 => none
  | fuel + 1 =>
    match b.expr e with
    | .fieldOf fid inner field =>
      match b.bare? inner with
      | some x => if known.lookup x == some 3 then some (x, [field], fid) else none
      | none => (throughRefOf b known inner fuel).map fun (x, path, _) => (x, path ++ [field], fid)
    | _ => none

/-- `a[i]` of a place that is not copied for it: what reads the element
where it is, `*element_at(&a, i)`; none where `a` is not such a place. -/
def elementRead (b : Body) (known : List (String × Nat)) (id : Nat) (a i : ExprId) : Build (Option ExprId) := do
  -- (`a[i][j]`: the element of the element, where it is.)
  let isElement : ExprId → Bool := fun e => match b.expr e with
    | .call _ g _ => (b.name? g).map (·.2) == some "element_at"
    | _ => false
  if let .deref inner := b.expr a then
    if isElement inner then
      return some (← pushExpr (.deref (← pushExpr (.call id (← pushExpr (.name none "element_at")) #[inner, i]))))
  -- (`a[i].f[j]`: the element of a field of the element, through the
  -- element's reference, held for it.)
  let rec fieldsOfElement (e : ExprId) (fuel : Nat) : Option (ExprId × List String × Nat) :=
    match fuel, b.expr e with
    | fuel + 1, .fieldOf fid inner field =>
      match b.expr inner with
      | .deref r => if isElement r then some (r, [field], fid) else none
      | _ => (fieldsOfElement inner fuel).map fun (r, path, _) => (r, path ++ [field], fid)
    | _, _ => none
  if let some (r, path, fid) := fieldsOfElement a 64 then
    if fid != 0 then
      let held := s!"%element{id}"
      let first ← pushStmt (.let_ (.var held) r)
      let base ← pushExpr (.refField fid false held path true)
      let read ← pushExpr (.deref (← pushExpr (.call id (← pushExpr (.name none "element_at")) #[base, i])))
      return some (← pushExpr (.labelScope "%block" #[first, ← pushStmt (.expr read)]))
  let base ← match placeOf b known a 64, throughRefOf b known a 64 with
    | some (x, [], _), _ => if known.lookup x == some 1 then some <$> pushExpr (.ref false x) else pure none
    | some (x, path, fid), _ =>
      if fid == 0 || known.lookup x != some 1 then pure none
      else some <$> pushExpr (.refField fid false x path false)
    | none, some (x, path, fid) => some <$> pushExpr (.refField fid false x path true)
    | none, none => pure none
  match base with
  | some r => some <$> pushExpr (.deref (← pushExpr (.call id (← pushExpr (.name none "element_at")) #[r, i])))
  | none => pure none

mutual

/-- `value.f(a)` where `f` takes a reference first and `value` is a variable,
or a field of one: the variable is borrowed for the call. `known` are the
names in scope that are known to hold a value and not a reference: `1` a
mutable variable, `2` a name bound to what is plainly a value (see
`valueLike`), or a parameter written with a type that is no reference's.
Anything else is given as it is: a reference already, or a value `f` takes
whole. -/

partial def receiverExpr (taken : Std.HashMap String Bool) (known : List (String × Nat)) (e : ExprId) : Build ExprId := do
  let b ← get
  match b.expr e with
  | .call id f args =>
    let f ← receiverExpr taken known f
    let args ← args.mapM (receiverExpr taken known)
    let b ← get
    let plain := fun (_ : Unit) => pushExpr (.call id f args)
    match b.expr f, args.toList with
    -- `a[i]` of a mutable variable, or of a field of a value or of what a
    -- reference points to: the element read where it is, nothing copied.
    | .name none "index", [a, i] =>
      match ← elementRead b known id a i with
      | some e => pure e
      | none => plain ()
    | .name q name, recv :: rest =>
      match b.expr recv with
      | .call _ rm #[receiver] =>
        if b.bare? rm != some receiverMark then return ← plain () else
        -- The name a path of fields starts at, and the path.
        let rec place (e : ExprId) (fuel : Nat) : Option (String × List String × Nat) :=
          match fuel with
          | 0 => none
          | fuel + 1 =>
          match b.expr e with
          | .name none x => if (known.lookup x).any (fun k => k != 0 && k != 3) then some (x, [], 0) else none
          | .fieldOf fid e field => (place e fuel).map fun (x, path, _) => (x, path ++ [field], fid)
          | .proj e n => (place e fuel).map fun (x, path, fid) => (x, path ++ [toString n], fid)
          | _ => none
        -- (A field of what a `&mut` parameter points to, `p.items`.)
        let rec throughRef (e : ExprId) (fuel : Nat) : Option (String × List String × Nat) :=
          match fuel with
          | 0 => none
          | fuel + 1 =>
          match b.expr e with
          | .fieldOf fid inner field =>
            match b.bare? inner with
            | some x => if known.lookup x == some 3 then some (x, [field], fid) else none
            | none => (throughRef inner fuel).map fun (x, path, _) => (x, path ++ [field], fid)
          | _ => none
        -- (`v[i].f()` where `f` takes a reference: the element, borrowed
        -- where it is.)
        let rec element (uniq : Bool) (fuel : Nat) (e : ExprId) : Build (Option ExprId) := do
          match b.expr e with
          -- (One `elementRead` made: the element's reference, for writing
          -- through it where that is asked.)
          | .deref inner =>
            match b.expr inner with
            | .call cid g #[r, i] =>
              if (b.name? g).map (·.2) != some "element_at" then return none
              if !uniq then return some inner
              let r' ← match b.expr r with
                | .ref _ x => pushExpr (.ref true x)
                | .refField fid _ x path star => pushExpr (.refField fid true x path star)
                | _ => return none
              some <$> pushExpr (.call cid (← pushExpr (.name none "place_at")) #[i, r'])
            | _ => pure none
          | .call cid g #[a, i] =>
            if (b.name? g).map (·.2) != some "index" then return none
            let base ← match fuel, place a 64, throughRef a 64 with
              | _, some (x, [], _), _ => some <$> pushExpr (.ref uniq x)
              | _, some (x, path, fid), _ => if fid == 0 then pure none else some <$> pushExpr (.refField fid uniq x path false)
              | _, none, some (x, path, fid) => some <$> pushExpr (.refField fid uniq x path true)
              | fuel + 1, none, none =>
                match b.bare? a with
                | some x => if known.lookup x == some 3 then pure (some a) else pure none
                | none => element uniq fuel a
              | 0, _, _ => pure none
            match base with
            | some bs =>
              if uniq then some <$> pushExpr (.call cid (← pushExpr (.name none "place_at")) #[i, bs])
              else some <$> pushExpr (.call cid (← pushExpr (.name none "element_at")) #[bs, i])
            | none => pure none
          | _ => pure none
        let borrowed := fun (uniq : Bool) => (do
          pushExpr (.call id (← pushExpr (.name none (if uniq then borrowMutMark else borrowMark))) #[receiver]) : Build ExprId)
        let given ← match taken[name]?, place receiver 64, throughRef receiver 64 with
          | some uniq, some (x, [], _), _ => pushExpr (.ref uniq x)
          | some uniq, some (x, path, fid), _ => if fid == 0 then pure receiver else pushExpr (.refField fid uniq x path false)
          | some uniq, none, some (x, path, fid) => pushExpr (.refField fid uniq x path true)
          | some uniq, none, none =>
            match ← element uniq 8 receiver with
            | some e => pure e
            | none =>
              -- (A value made where it is called on, `half(4).is_ok()`:
              -- given a name first, and borrowed.)
              match b.expr receiver with
              -- (Not what a function written to give a reference gives.)
              | .call _ g _ =>
                match b.expr g with
                | .name _ gn => if taken.contains (givesKey gn) then pure receiver else borrowed uniq
                | _ => borrowed uniq
              -- (A constructor without fields or a constant, `D.greet()`.)
              | .name none x =>
                if (lastSegment x).front.isUpper then borrowed uniq else pure receiver
              | _ => pure receiver
          | _, _, _ => pure receiver
        pushExpr (.call id (← pushExpr (.name q name)) (#[given] ++ rest.toArray))
      | _ => plain ()
    | _, _ => plain ()
  | n => do
    let n' ← n.mapIds (receiverExpr taken known) (receiverClause taken known [])
      fun body => do pure (← receiverStmts taken known body.toList).toArray
    if n' == n then pure e else pushExpr n'

/-- (`values`: the parameters written with types that are no reference's.) -/
partial def receiverClause (taken : Std.HashMap String Bool) (known : List (String × Nat))
    (values : List String) (c : ClauseId) : Build ClauseId := do
  let ⟨pats, body⟩ := (← get).clause c
  let named := (pats.flatMap patternNames).map fun x =>
    (x, if values.contains x then 2 else if known.lookup x == some 3 then 3 else 0)
  pushClause ⟨pats, (← receiverStmts taken (named ++ known) body.toList).toArray⟩

partial def receiverStmts (taken : Std.HashMap String Bool) (known : List (String × Nat)) :
    List StmtId → Build (List StmtId)
  | [] => pure []
  | s :: rest => do
    let rec here (s : StmtId) (fuel : Nat) : Build (StmtId × List (String × Nat)) := do
      let b ← get
      match fuel, b.stmt s with
      | 0, _ => pure (s, known)
      | _, .let_ pat value =>
        -- (`let s = &v[i]`: an element borrowed, a reference.)
        let elementRef : Bool := match b.expr value with
          | .call _ f _ => match (b.name? f).map (·.2) with
            | some g => g == "element_at" || g == "place_at"
            | none => false
          | .ref _ _ => true
          | .refField .. => true
          | _ => false
        let kind := match pat with
          | .var _ => if elementRef then 3 else if b.valueLike value then 2 else 0
          | _ => 0
        pure (← pushStmt (.let_ pat (← receiverExpr taken known value)), (patternNames pat).map (·, kind) ++ known)
      | _, .letMut x value => pure (← pushStmt (.letMut x (← receiverExpr taken known value)), (x, 1) :: known)
      | _, .expr e => pure (← pushStmt (.expr (← receiverExpr taken known e)), known)
      | _, .defer e => pure (← pushStmt (.defer (← receiverExpr taken known e)), known)
      | _, .assign target value =>
        -- (`a[i] = v` is written where it is: what is below it is looked at.)
        let t ← match b.expr target with
          | .call id f #[a, i] =>
            if (b.name? f).map (·.2) == some "index" then do
              pushExpr (.call id f #[← receiverExpr taken known a, ← receiverExpr taken known i])
            else receiverExpr taken known target
          | _ => receiverExpr taken known target
        let v ← receiverExpr taken known value
        pure (← pushStmt (.assign t v), known)
      | fuel + 1, .located line col inner =>
        let (inner, known) ← here inner fuel
        pure (← pushStmt (.located line col inner), known)
    let (s, known) ← here s 64
    pure (s :: (← receiverStmts taken known rest))

end

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

/-- An item's functions made so (`promoteFnClause`), as it is read, before
its names are resolved: not a trait's defaults, made so where they are
written out (`borrowReceivers`). -/
partial def promoteItem : Item → Item
  | .fn name ps annots ret b =>
    let (roots, b) := (b.roots.mapM (promoteFnClause annots)).run b
    .fn name ps annots ret { b with roots }
  | .pub parent item => .pub parent (promoteItem item)
  | .module name (some inner) => .module name (some (inner.map promoteItem))
  | .impl ps tr head args context methods => .impl ps tr head args context (methods.map promoteItem)
  | item => item

/-- Every item made so (`promoteItem`), each as an earlier compile made it
where it is the same. -/
def promoteItems (items : List Item) (memo : FrontMemo := {}) : List Item × FrontMemo :=
  let (out, memo) := items.foldl (fun ((acc : Array Item), m) item =>
    let (made, m) := m.take (hash ("promote", item)) fun _ => [promoteItem item]
    (acc ++ made.toArray, m)) (#[], memo)
  (out.toList, memo)

/-- Does a body call, on what it is called on, a function that takes
a reference (`taken`), so that `receiverExpr` may borrow it? -/
def Body.borrowsReceiver (b : Body) (taken : Std.HashMap String Bool) (body : Array StmtId) : Bool :=
  body.any fun s => b.anyStmt (fun n => match n with
    | .call _ f args =>
      match b.name? f, args[0]?.map b.expr with
      | some (_, name), some (.call _ m _) => b.bare? m == some receiverMark && taken.contains name
      | _, _ => false
    | _ => false) s

/-- Every dotted call of a program with what it is called on borrowed where
the function takes a reference: see `receiverExpr`. A name that is then
borrowed and was not a variable is kept where a reference can point, as one
borrowed with `&` in the text is (`promoteFnClause`): in each function's
clause where a borrow may be made, the rest as the text's were made so
(`promoteItems`). -/
partial def borrowReceivers (items : List Item) (memo : FrontMemo := {}) : List Item × FrontMemo :=
  let decls := items.map Item.declared
  let taken : Std.HashMap String Bool :=
    (takesReference decls ++ (givesReference decls).map (givesKey ·, false)).foldl (fun m (k, v) => m.insertIfNew k v) {}
  -- (`promote`: not of a trait's defaults, which are made so where they are
  -- written out.)
  let rec go (promote : Bool) : Item → Item
    | .pub parent item => .pub parent (go promote item)
    | .module name (some body) => .module name (some (body.map (go promote)))
    | .fn name ps annots ret b =>
      let (roots, b) := (b.roots.mapM fun c => (do
        let b ← get
        let ⟨pats, body⟩ := b.clause c
        -- (Those written with a reference's type: a field of what one points
        -- to is borrowed through it.)
        let (values, refs) := paramsOf pats annots
        let borrows := b.borrowsReceiver taken body
        let c' ← nameBorrowsClause (← receiverClause taken (refs.map (·, 3)) values c)
        if promote && borrows then promoteFnClause annots c' else pure c' : Build ClauseId)).run b
      .fn name ps annots ret { b with roots }
    | .impl ps tr head args context methods => .impl ps tr head args context (methods.map (go promote))
    | .traitInfo name supers defaults params assocs => .traitInfo name supers (defaults.map (go false)) params assocs
    | .alias name b value =>
      let (value, b) := (receiverExpr taken [] value).run b
      .alias name b value
    | item => item
  -- (Each item made from it and what dotted calls borrow.)
  let ctx := mixHash (hash "receivers") (unorderedHash taken)
  let (out, memo) := items.foldl (init := (#[], memo)) fun (out, memo) item =>
    let (v, memo) := memo.take (mixHash ctx (hash item)) fun _ => [go true item]
    (out ++ v.toArray, memo)
  (out.toList, memo)

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
        fixed := fixed.push ((.typeAlias (fixedArgName j) [] (← ty (.name a []))))
    pure (Item.impl (ps ++ fresh.toList) tr head newArgs.toList context (methods ++ fixed.toList))
  let rec item : Item → Except String Item
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
      pure ((.trait name (← methods.mapM fun (m, ps, r) => do
        pure (m, ← ps.mapM ty, ← r.mapM ty))))
    | .impl ps tr head args context methods => do
      let methods ← methods.mapM fun
        | (.typeAlias name aps body) => do pure ((.typeAlias name aps (← ty body)))
        | m => item m
      -- For a type whose last parameter is `..T`: the arguments written from
      -- there on are one tuple, an argument the implementation fixes.
      let (ps, args, methods) := match byName[variadicKey head]? with
        | some (_, .name kk []) =>
          match kk.toNat? with
          | some k =>
            let fixedOf := fun (j : Nat) => methods.findSome? fun
              | (.typeAlias n [] body) => if n == fixedArgName j then some body else none
              | _ => none
            let parts := (args.drop k).zipIdx.map fun (a, i) =>
              if ps.contains a then TypeExpr.name a [] else (fixedOf (k + i)).getD (.name a [])
            let rest := methods.filter fun
              | (.typeAlias n [] _) => !((List.range args.length).drop k |>.any (fixedArgName · == n))
              | _ => true
            let name := s!"%fixed{k}"
            (ps.filter (fun p => !((List.range args.length).drop k |>.any (s!"%fixed{·}" == p))) ++ [name],
              args.take k ++ [name], rest ++ [(.typeAlias (fixedArgName k) [] (.tuple parts))])
          | none => (ps, args, methods)
        | _ => (ps, args, methods)
      -- An implementation for another name of a type, `impl T for
      -- Option<A>`, is one for the type the name stands for, with the
      -- arguments the name fixes said beside it.
      match byName[head]? with
      | some (aps, .name target targs) =>
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
            fixed := fixed.push ((.typeAlias (fixedArgName j) [] (← ty targ)))
        concrete (ps ++ fresh.toList) tr target newArgs.toList context (methods ++ fixed.toList)
      | _ => concrete ps tr head args context methods
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

/-- Is a type plain data: what a value of it is, bytes and nothing else, so
far? `Int`, the scalars, a type parameter, and tuples and declared types of
such, none holding itself. -/
partial def plainType (fields : Std.HashMap String (List String × List (List TypeExpr)))
    (seen : List String) : TypeExpr → Bool
  | .name x args =>
    x == "Int" || (scalars.lookup x).isSome || x.startsWith "%l"
      || !seen.contains x && ((fields[x]?).any fun (_, cs) => cs.all (·.all (plainType fields (x :: seen))))
        && args.all (plainType fields seen)
  | .tuple args => args.all (plainType fields seen)
  | _ => false

/-- `Layout` (the prelude's) for each type: each declared type's right after
its declaration, and those of the types with no declaration (`Int`, each
scalar, tuples, callables, references) right after the trait's; each from the
type's structure (`layoutOf`), asking `Layout` of each of its type
parameters. In place, so that the prelude's are the same, item for item, in
a program as where the prelude is checked alone. -/
def writeLayouts (items : List Item) (memo : FrontMemo := {}) : List Item × FrontMemo := Id.run do
  let rec flatAll : List Item → List Item
    | [] => []
    | .module _ (some body) :: rest => flatAll body ++ flatAll rest
    | .pub _ inner :: rest => flatAll [inner] ++ flatAll rest
    | item :: rest => item :: flatAll rest
  let all := flatAll items
  unless all.any (fun | (.trait n _) => n == layoutTrait | _ => false) do return (items, memo)
  let hasNil := all.any (fun | (.trait n _) => n == nilTrait | _ => false)
  let hasRepr := all.any (fun | (.trait n _) => n == reprTrait | _ => false)
  -- (A type whose `Layout` is written out by hand has that one: `[T; N]`'s.)
  let ownLayout : Std.HashSet String := all.foldl (init := {}) fun s item =>
    match item with
    | .impl _ tr h _ _ _ => if tr == layoutTrait then s.insert h else s
    | _ => s
  -- (Each declared type's constructors, by name, with their fields.)
  let ctorsOf : Std.HashMap String (List String × List (Option String × List TypeExpr)) := all.foldl (init := {}) fun m item =>
    match item with
    | (.struct n ps fs) => m.insert n (ps, [(some n, fs)])
    | (.enum n ps cs) => m.insert n (ps, cs.map fun (c, fs) => (some c, fs))
    | _ => m
  let fieldsOf : Std.HashMap String (List String × List (List TypeExpr)) := all.foldl (init := {}) fun m item =>
    match item with
    | (.struct n ps fs) => m.insert n (ps, [fs])
    | (.enum n ps cs) => m.insert n (ps, cs.map (·.2))
    | _ => m
  let count := 0
  -- (The trait's functions, by the names the program has for them.)
  let (sizeName, alignName) := match all.findSome? (fun | (.trait n ms) => if n == layoutTrait then some ms else none | _ => none) with
    | some [(s, _, _), (a, _, _)] => (s, a)
    | _ => ("SIZE", "ALIGN")
  -- (The types a field may be of: those declared, and those with none.)
  let known : Std.HashSet String := Std.HashSet.ofList (fieldsOf.toList.map (·.1) ++ ["Int"] ++ scalars.map (·.1))
  let typed := fun (ps : List String) (t : TypeExpr) => typedField known ps t
  -- (The implementation for one head, its calls numbered apart; none for a
  -- type with a field whose type is left to be found.)
  let implFor := fun (count : Nat) (head : String) (ps : List String) =>
    let fresh := ps.zipIdx.map fun (p, j) => if p.startsWith "'" then s!"'%l{j}" else s!"%l{j}"
    let (sizeE, alignE) := layoutOf fieldsOf head fresh (9000000000000000 + 1000 * count)
    let int := TypeExpr.name "Int" []
    let untyped := match fieldsOf[head]? with
      | some (ps, cs) => cs.any (·.any (!typed ps ·))
      | none => false
    if untyped then [] else
    -- (`NilRepresented`, of one with no payload: one constructor, each field a
    -- type parameter, asked it too, or of a type that is nothing itself; and
    -- no `drop` to run.)
    let nils : List Item := match (if head.startsWith "(tuple" then some (ps, [ps.map (TypeExpr.name · [])]) else fieldsOf[head]?) with
      | some (hps, [fs]) =>
        let isParam := fun (f : TypeExpr) => match f with
          | .name x [] => hps.contains x
          | _ => false
        let nothing := fun (f : TypeExpr) => isParam f || (staticLayout fieldsOf [head] f).any (·.1 == 0)
        let dropped := all.any fun
          | .impl _ tr h _ _ _ => (tr.splitOn "::").getLast! == "Drop" && h == head
          | _ => false
        if hasNil && !dropped && fs.all nothing then
          let m := hps.zip fresh
          let asked := (fs.filterMap fun f => match f with
            | .name x [] => m.lookup x
            | _ => none).eraseDups
          [Item.impl fresh nilTrait head fresh (asked.map (·, nilTrait)) []]
        else []
      | _ => []
    -- (`Repr`, of a declared type or a tuple, its fields written where
    -- `Layout` puts them.)
    let ctors : Option (List (Option String × List TypeExpr)) :=
      if !hasRepr then none
      else if head.startsWith "(tuple" then some [(none, fresh.map (TypeExpr.name · []))]
      else (ctorsOf[head]?).map fun (ps, cs) =>
        let m := ps.zip (fresh.map (TypeExpr.name · []))
        cs.map fun (c, fs) => (c, fs.map (substTypeExpr m))
    let reprs : List Item := match ctors.filter (·.all fun (_, fs) => fs.all (plainType fieldsOf [head])) with
      | some cs =>
        let (store, load) := reprOf cs (8000000000000000 + 100000 * count)
        [Item.impl fresh reprTrait head fresh ((fresh.filter (!·.startsWith "'")).flatMap fun p => [(p, reprTrait), (p, layoutTrait)])
          [store, load, .typeAlias askedOnlyName [] (.tuple [])]]
      | none => []
    if ownLayout.contains head then nils ++ reprs else
    (nils ++ reprs ++ [Item.impl fresh layoutTrait head fresh ((fresh.filter (!·.startsWith "'")).map (·, layoutTrait))
      -- (Checked only where something asks it: `askedOnlyName`.)
      [Item.fnOf sizeName [] [] (some int) [.mk [] [.expr sizeE]], Item.fnOf alignName [] [] (some int) [.mk [] [.expr alignE]],
       .typeAlias askedOnlyName [] (.tuple [])]])
  -- (After what is written out beside a declaration, `fieldNames`.)
  let rec beside : List Item → List Item × List Item
    | ((.fieldNames m ns ps)) :: rest =>
      if m.startsWith "%" then ([], (.fieldNames m ns ps) :: rest) else
      let (mine, after) := beside rest
      ((.fieldNames m ns ps) :: mine, after)
    | rest => ([], rest)
  -- (Each type's made from where it is among them, the type, and what the
  -- types declared are.)
  let dropped := all.filterMap fun
    | .impl _ tr h _ _ _ => if (tr.splitOn "::").getLast! == "Drop" then some h else none
    | _ => none
  let ctx := mixHash (hash "layouts") (hash (unorderedHash fieldsOf, hasNil, sizeName, alignName, dropped))
  let implKept := fun (memo : FrontMemo) (count : Nat) (h : String) (ps : List String) =>
    memo.take (mixHash ctx (hash (count, h, ps))) fun _ => implFor count h ps
  -- (`fuel`: one for each item.)
  let rec go (fuel count : Nat) (memo : FrontMemo) : List Item → (List Item × Nat × FrontMemo)
    | [] => ([], count, memo)
    | item :: rest =>
      match fuel with
      | 0 => (item :: rest, count, memo)
      | fuel + 1 =>
        let declared : Option (String × List String) := match item with
          | (.struct n ps _) | (.enum n ps _) | .pub _ ((.struct n ps _))
          | .pub _ ((.enum n ps _)) => some (n, ps)
          | _ => none
        match declared with
        | some (n, ps) =>
          let (names, rest) := beside rest
          let (mine, memo) := implKept memo count n ps
          let (more, count', memo) := go fuel (count + 1) memo rest
          (item :: names ++ mine ++ more, count', memo)
        | none =>
          let (mine, count, memo) : List Item × Nat × FrontMemo := match item with
            | (.trait n _) =>
              if n == layoutTrait then
                let (out, c, memo) := (builtinHeads).foldl (fun (acc : List Item × Nat × FrontMemo) (h, ps) =>
                  let (made, m) := implKept acc.2.2 acc.2.1 h ps
                  (acc.1 ++ made, acc.2.1 + 1, m)) ([], count, memo)
                (item :: out, c, memo)
              else ([item], count, memo)
            | .module name (some body) =>
              let (body, c, memo) := go fuel count memo body
              ([.module name (some body)], c, memo)
            | other => ([other], count, memo)
          let (more, count, memo) := go fuel count memo rest
          (mine ++ more, count, memo)
  let (out, _, memo) := go (2 * (flatAll items).length + 2) count memo items
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
    | .impl ps tr head [t] ctx ms => if head == blanketHead then some (ps, tr, t, ctx, ms) else none
    | _ => none
  if blankets.isEmpty then return items
  let rest := items.filter fun
    | .impl _ _ head _ _ _ => head != blanketHead
    | _ => true
  let declared : List (String × List String) := rest.filterMap fun
    | (.struct n ps _) | .pub _ ((.struct n ps _)) | (.enum n ps _)
    | .pub _ ((.enum n ps _)) => some (n, ps)
    | _ => none
  let heads := builtinHeads declared
  -- (The arguments an implementation gives its trait, as written.)
  let givenArgs := fun (ms : List Item) => (givenTraitArgs (ms.map Item.declared)).map (·.spell)
  -- (Which trait each implementation is of, at which arguments, for which
  -- head.)
  let implOf : Item → Option (String × String × List String) := fun
    | .impl _ tr head _ _ ms => some (traitBase tr, head, givenArgs ms)
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
  let mut out : Array Item := (blankets.map fun (_, tr, t, ctx, _) =>
    (.fieldNames (attrMark "blanket_impl")
      (traitBase tr :: ctx.filterMap fun (p, c) => if p == t then some (traitBase c) else none) [])).toArray
  let mut copies := 0
  -- (How many traits of its type each asks: tried first.)
  let askedOf := fun (b : Nat) => match blankets[b]? with
    | some (_, _, t, ctx, _) => (ctx.filter fun (pc : String × String) => pc.1 == t).length
    | none => 0
  let order := (List.range blankets.length).mergeSort fun a b => askedOf a ≥ askedOf b
  let blankets := order.filterMap fun b => blankets[b]?
  -- (A copy may give what another asks: as many rounds as there are.)
  for _ in List.range (blankets.length + 1) do
    let mut more := false
    for ((ps, tr, t, ctx, ms), b) in blankets.zipIdx do
      let asked := ctx.filterMap fun (p, c) => if p == t then some (traitBase c) else none
      let bodies := givenTraitArgs (ms.map Item.declared)
      for (h, hps) in heads do
        let fresh := hps.zipIdx.map fun (p, j) => if p.startsWith "'" then s!"'%b{j}" else s!"%b{j}"
        let self := selfTypeOf h (fresh.map (TypeExpr.name · []))
        let mine := bodies.map fun body => (substTypeExpr [(t, self)] body).spell
        let givers := byBlanket.getD (traitBase tr, h, mine) []
        if givers.contains b then continue
        -- (One that asks more already gave it this type: that one is its.)
        let asksOf := fun (g : Nat) => match blankets[g]? with
          | some (_, _, t', ctx', _) => (ctx'.filter fun (pc : String × String) => pc.1 == t').length
          | none => 0
        if givers.any (fun g => asksOf g > asked.length) then continue
        let mineToo := givers.any (· != b)
        if !mineToo && known.contains (traitBase tr, h, mine) then continue
        if denied.contains (last (traitBase tr), last h) then continue
        -- (A tuple of one or more has the one for its first and the rest.)
        if h.startsWith "(tuple" && h != "(tuple0)" && has.contains (traitBase tr, consHead) then continue
        if h.startsWith "(fn" && has.contains (traitBase tr, "%Fn") then continue
        unless asked.all (fun c => has.contains (c, h)) do continue
        let ctx' := ctx.zipIdx.map fun ((p, c), k) => if p == t then (s!"%subject{k}", c) else (p, c)
        let subjects := (ctx.zipIdx.filter fun ((p, _), _) => p == t).map fun (_, k) =>
          (.typeAlias (ctxSubjectName k) [] self)
        copies := copies + 1
        let shift := 100000000000000 * copies
        -- (`self_name()` in it: this type's name.)
        let named : FRewrite := { onExpr := fun _ b e => match b.expr e with
          | .call _ f #[] =>
            -- (Written as the resolver has written texts by now: the
            -- prelude's constructors by their own names.)
            if b.bare? f == some selfNameFn then some (flatExpr ((last h).toList.foldr (fun c rest =>
              .call 0 (.name none "StrChar") [scalarValue "char_of" (c.toNat : Int), rest]) (.name none "StrEnd")))
            else none
          | _ => none }
        let ms' := ms.map fun
          | (.typeAlias n takes body) => (.typeAlias n takes (substTypeExpr [(t, self)] body))
          | .fn m fps annots ret b =>
            .fn m fps (annots.map (·.map (substTypeExpr [(t, self)]))) (ret.map (substTypeExpr [(t, self)]))
              (named.body ((shiftRewrite shift).body b))
          | item => item
        out := out.push (.impl (fresh ++ ps.filter (· != t)) tr h fresh ctx'
          (ms' ++ subjects ++ [(.typeAlias (blanketName t) [] self)]))
        known := known.insert (traitBase tr, h, mine)
        has := has.insert (traitBase tr, h)
        byBlanket := byBlanket.insert (traitBase tr, h, mine) (givers ++ [b])
        more := true
    unless more do break
  pure (rest ++ out.toList)

/-- Each implementation with the functions its trait gives a body that it
does not write itself; and, where it gives its trait arguments, `impl
From<Int> for u8`, as an implementation of the trait at those: `From<Int>` is
the name of what it implements from here on. -/
def fillDefaults (items : List Item) (memo : FrontMemo := {}) : List Item × FrontMemo :=
  -- (Implementations for every type written out for each.)
  let (items, memo) := Trace.timed "fill: layouts" fun _ => writeLayouts items memo
  let items := Trace.timed "fill: blankets" fun _ => expandBlankets items
  -- (First, with every declaration to hand: what dotted calls borrow.)
  let (items, memo) := Trace.timed "fill: borrow receivers" fun _ => borrowReceivers items memo
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
    | .impl ps tr head args context methods =>
      let targs := givenTraitArgs (methods.map Item.declared)
      let given := targs.map (·.spell)
      let before := seen.getD (tr, head, given) 0
      let key := mixHash (hash "defaults") (hash (defaultKeys.getD tr 0, index, before, item))
      let (made, memo) := memo.take key fun _ =>
        let written := methods.filterMap fun
          | .fn m _ _ _ _ => some m
          | _ => none
        let said := methods.filterMap fun
          | (.typeAlias n _ _) => some n
          | _ => none
        let missing := ((defaults.lookup tr).getD []).filter fun
          | .fn m _ _ _ _ => !written.contains m
          | (.typeAlias n _ _) => !said.contains n
          | _ => false
        -- A default is written against `Self`; in the implementation its types
        -- are the trait's at the implementing type. Each implementation has its
        -- own copy: the calls in it are met by this implementation's types, and
        -- are known by their identities. (`Self::f(..)` in it is this
        -- implementation's `f`.)
        let self := selfTypeOf head (args.map (TypeExpr.name · []))
        let missing := missing.map fun
          | .fn m fps annots _ b =>
            Item.fn m fps (annots.map fun _ => none) none
              ((shiftRewrite (10000000000 * (index + 1))).body
                ((selfRewrite head (some (tr, (TypeExpr.tuple [self]).asExpr))).body b))
          -- (A type's default is written against `Self` too.)
          | (.typeAlias n takes body) => (.typeAlias n takes (TypeExpr.withSelf self body))
          | item => item
        -- (`Self::Components` in its functions: what this implementation's
        -- trait leaves, at this type.)
        let ofSelf := selfAssocs self tr targs
        let all := (methods ++ missing).map fun
          | .fn m fps annots ret b =>
            Item.fn m fps (annots.map (·.map ofSelf)) (ret.map ofSelf)
              (match mapTypes (fun t => pure (ofSelf t)) b with
                | .ok b => b
                | .error _ => b)
          | item => item
        let named := if before == 0 then tr else s!"{tr}#{before}"
        [.impl ps (traitAt named given) head args context all]
      (seen.insert (tr, head, given) (before + 1), out ++ made.toArray, memo)
    | item => (seen, out.push item, memo)
  (out.toList, memo)

end Flat

end Glorious.Syntax
