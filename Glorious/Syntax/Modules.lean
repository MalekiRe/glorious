import Glorious.Syntax.Ast

/-!
# Modules

A module is a unit: a file, or `mod name { .. }`. What it declares is its
own unless it says `pub`, and that is the whole of privacy: a module written
inside another sees no more of it than a stranger does. A module uses another
by naming what it declares, `a::b::name` or `use a::b::name;`, and which
modules use which must have no cycle. So a module can be understood knowing
only the public face of the ones it uses, and those first.

This pass is what gives every name its meaning before the program is checked.
It finds what each name of each module refers to, refuses what is private or
circular, and writes the program out as one list of items in which every
declaration has a name of its own: `name` in the module `a::b` is `a::b::name`,
and a name of the first module or of the prelude is itself. The checker, the
elaborator and Core see no modules.

It also writes out what was written with field names, now that it knows which
declaration a name is: `Point { y: 2, x: 1 }` becomes `Point(1, 2)`.

Not done here, and not done: a module is not compiled alone. Every module of
a program becomes part of one Core program.
-/

namespace Glorious.Syntax.Modules

/-- Who can name a declaration: its module, that and the module it is written
in, or anyone. -/
inductive Vis where
  | priv
  | parent
  | pub
  deriving BEq, Inhabited

/-- What a name is the name of. -/
inductive Kind where
  | fn
  | ctor
  | op
  | const
  | method
  | type
  | effect
  | trait
  | module
  deriving BEq, Inhabited

/-- Names of values, of types, of effects, of traits and of modules are told
apart by where they are written. -/
inductive Space where
  | value
  | type
  | effect
  | trait
  | module
  deriving BEq, Inhabited

def Kind.space : Kind → Space
  | .type => .type
  | .effect => .effect
  | .trait => .trait
  | .module => .module
  | _ => .value

/-- A declaration: the module it is in, its name in the whole program, and
who can name it. For a module, `home` is the module itself. -/
structure Entry where
  home : List String
  global : String
  vis : Vis
  kind : Kind
  deriving Inhabited

/-- A name a module can write. `shown` is who can name it as a name of this
module: a declaration as it says, a name brought in by `use` nobody else,
unless by `pub use`. Of two meanings the one with the lower `rank` is meant:
what the module declares or names in a `use`, then what a `use ..::*` brings,
then the prelude. -/
structure Bound where
  name : String
  entry : Entry
  shown : Vis
  rank : Nat
  deriving Inhabited

structure Module where
  path : List String
  items : List Item
  own : List Bound

/-- The path the prelude has as a module. Nothing can write it. -/
def preludePath : List String := ["%prelude"]

/-- How a module is written in a message. -/
def showPath (p : List String) : String :=
  if p.isEmpty then "the first module" else if p == preludePath then "the prelude"
  else s!"module `{"::".intercalate p}`"

/-- A module as one string. -/
def key (p : List String) : String := "::".intercalate p

/-- The name a declaration has in the whole program. -/
def mangle (home : List String) (name : String) : String :=
  if home.isEmpty || home == preludePath then name
  else if home.head? == preludePath.head? then s!"prelude::{key (home.drop 1)}::{name}"
  else s!"{key home}::{name}"

def visible (v : Vis) (home viewer : List String) : Bool :=
  viewer == home || v == .pub || (v == .parent && viewer == home.dropLast && !home.isEmpty)

structure St where
  units : List Module := []
  /-- What each module can write, once its `use`s are settled. -/
  scopes : List (List String × List Bound) := []
  /-- The modules whose `use`s are being settled. -/
  busy : List (List String) := []
  /-- Which module names something of which. -/
  edges : List (List String × List String) := []
  /-- For each constructor with fields: its module, the names of its fields if
  it has names, and which fields are `pub`. -/
  fields : List (String × List String × List String × List Bool) := []
  homes : List (String × String) := []
  /-- The modules that are not `pub`: each can be named by the module it is
  written in, and by what is written in it. -/
  hidden : List (List String) := []
  /-- The coercions, each with the module that declares it. -/
  coerced : List (List String × String) := []
  /-- How many names this pass has made up. -/
  fresh : Nat := 0

abbrev R := StateT St (Except String)

/-- What a module declares. `taken` are the names the first module has: it
may declare a name the prelude has, and the prelude's is then `prelude::name`
in the whole program. -/
def declared (path : List String) (items : List Item) (taken : List String := []) :
    List Bound × List (String × List String × List String × List Bool) := Id.run do
  let mangle := fun (path : List String) (name : String) =>
    if path == preludePath && taken.contains name then s!"prelude::{name}" else mangle path name
  let mut out : Array Bound := #[]
  let mut fields : Array (String × List String × List String × List Bool) := #[]
  -- What the prelude declares is for every module; a module written inside
  -- the prelude is a module like any other.
  let everyone := path == preludePath
  for item in items do
    let (vis, item) := match item with
      | .pub parent i => (if parent then Vis.parent else Vis.pub, i)
      | i => (if everyone then Vis.pub else Vis.priv, i)
    let add := fun (out : Array Bound) (name : String) (kind : Kind) =>
      out.push ⟨name, ⟨path, mangle path name, vis, kind⟩, vis, 0⟩
    match item with
    | .fn name _ _ _ _ => out := add out name .fn
    | .enum name _ ctors =>
      out := add out name .type
      for (c, _) in ctors do out := add out c .ctor
    | .struct name _ _ =>
      out := add out name .type
      out := add out name .ctor
    | .effect name _ ops =>
      out := add out name .effect
      for op in ops do out := add out op.name .op
    | .alias name _ => out := add out name .const
    | .trait name methods =>
      out := add out name .trait
      for (m, _, _) in methods do out := add out m .method
    | .typeAlias name _ _ => out := add out name .type
    | .fieldNames ctor names pubs => fields := fields.push (mangle path ctor, path, names, pubs)
    | _ => pure ()
  (out.toList, fields.toList)

/-- The meaning of a name among those a module can write. -/
def lookupIn (scope : List Bound) (space : Space) (name : String) : Option Entry :=
  let found := scope.filter fun b => b.name == name && b.entry.kind.space == space
  let best := found.foldl (fun (acc : Option Bound) b =>
    match acc with
    | some a => if b.rank < a.rank then some b else some a
    | none => some b) none
  best.map (·.entry)

def unitOf (p : List String) : R (Option Module) := do
  pure ((← get).units.find? (·.path == p))

def noteEdge (viewer target : List String) : R Unit := do
  if viewer == target || target.head? == preludePath.head? || viewer.head? == preludePath.head? then return
  unless (← get).edges.any (· == (viewer, target)) do
    modify fun s => { s with edges := (viewer, target) :: s.edges }

/-- A name used from `viewer` means this declaration. -/
def noteUse (viewer : List String) (e : Entry) : R Unit := noteEdge viewer e.home

mutual

/-- Everything a module can write: what it declares, the modules written in
it, what its `use`s bring, and the prelude. -/
partial def scopeOf (p : List String) : R (List Bound) := do
  if let some s := (← get).scopes.lookup p then return s
  if (← get).busy.contains p then
    let chain := " -> ".intercalate (((← get).busy.reverse ++ [p]).map fun q =>
      if q.isEmpty then "the first module" else "::".intercalate q)
    throw s!"modules use each other in a circle ({chain}); which module uses which must have no cycle"
  let some unit ← unitOf p | throw s!"there is no {showPath p}"
  modify fun s => { s with busy := p :: s.busy }
  let mut out := unit.own
  -- The modules written in this one can be named here.
  for u in (← get).units do
    if u.path.dropLast == p && !u.path.isEmpty && u.path != preludePath then
      out := out ++ [⟨u.path.getLast!, ⟨u.path, "", .pub, .module⟩, .pub, 0⟩]
  for item in unit.items do
    let (shown, item) := match item with
      | .pub parent i => (if parent then Vis.parent else Vis.pub, i)
      | i => (Vis.priv, i)
    if let .import path rename glob := item then
      let found ← imported p out path glob
      for b in found do
        let name := if glob then b.name else rename.getD b.name
        out := out ++ [{ b with name, shown, rank := if glob then 1 else 0 }]
  if p != preludePath then
    if let some prelude ← unitOf preludePath then
      out := out ++ prelude.own.map fun b => { b with shown := .priv, rank := 2 }
  modify fun s => { s with busy := s.busy.filter (· != p), scopes := (p, out) :: s.scopes }
  pure out

/-- A module that is not `pub` is named by the module it is written in and by
what is written in it, and by no other. -/
partial def enter (viewer target : List String) : R Unit := do
  if (← get).hidden.contains target then
    unless viewer == target.dropLast || target.isPrefixOf viewer do
      throw s!"{showPath viewer} cannot name {showPath target}, which is private to {showPath target.dropLast}: only a `pub mod` can be named from outside the module it is written in"

/-- The module a path names, if its first name is a module: `crate`, `self`
and `super`, a module that can be written here, or one of the first module's. -/
partial def moduleAt (viewer : List String) (scope : List Bound) (segs : List String) :
    R (Option (List String)) := do
  let some head := segs.head? | return none
  let start ← match head with
    -- What the compiler itself writes of the prelude, whatever is in scope.
    | "%prelude" => pure (some preludePath)
    | "crate" => pure (some [])
    | "self" => pure (some viewer)
    | "super" =>
      if viewer.isEmpty then throw "`super`: the first module is written in no other"
      pure (some viewer.dropLast)
    | _ =>
      match lookupIn scope .module head with
      | some e => pure (some e.home)
      | none =>
        if (← unitOf [head]).isSome then
          enter viewer [head]
          pure (some [head])
        else pure none
  let some start := start | return none
  let mut cur := start
  for seg in segs.drop 1 do
    if (← unitOf (cur ++ [seg])).isSome then
      enter viewer (cur ++ [seg])
      cur := cur ++ [seg]
    else
      -- A module another module names again with `pub use`.
      let bounds ← if cur == viewer then pure scope else scopeOf cur
      match bounds.find? fun b =>
          b.name == seg && b.entry.kind == .module && b.rank ≤ 1 && visible b.shown cur viewer with
      | some b => cur := b.entry.home
      | none => return none
  pure (some cur)

/-- What a name of the module `q` means to `viewer`, in each space it has a
meaning. An error if it has one that `viewer` may not name and none it may. -/
partial def exported (viewer q : List String) (name : String) : R (List Bound) := do
  let bounds ← scopeOf q
  let named := bounds.filter fun b => b.name == name && b.rank ≤ 1
  let seen := named.filter fun b => visible b.shown q viewer
  if seen.isEmpty && !named.isEmpty then
    throw s!"`{name}` is private to {showPath q}: only what is `pub` can be named from outside"
  pure seen

/-- What a `use` brings into the module `p`, whose names so far are `scope`. -/
partial def imported (p : List String) (scope : List Bound) (path : List String) (glob : Bool) :
    R (List Bound) := do
  let written := "::".intercalate path
  if glob then
    let some q ← moduleAt p scope path | throw s!"`use {written}::*`: there is no module `{written}`"
    if q == p then throw s!"`use {written}::*`: a module does not use itself"
    noteEdge p q
    let bounds ← scopeOf q
    let seen := bounds.filter fun b => b.rank ≤ 1 && visible b.shown q p
    for b in seen do noteUse p b.entry
    return seen
  -- The whole path may be a module.
  let asModule ← moduleAt p scope path
  let name := path.getLast!
  let before := path.dropLast
  let mut found : List Bound := []
  if let some m := asModule then
    if m != p then
      noteEdge p m
      found := [⟨name, ⟨m, "", .pub, .module⟩, .priv, 0⟩]
  if !before.isEmpty then
    if let some q ← moduleAt p scope before then
      if q == p then throw s!"`use {written}`: a module does not use itself"
      noteEdge p q
      let seen ← exported p q name
      for b in seen do noteUse p b.entry
      found := found ++ seen.filter fun b => b.entry.kind != .module || asModule.isNone
  if found.isEmpty then
    if before.isEmpty then throw s!"`use {written}`: there is no module `{written}`"
    match ← moduleAt p scope before with
    | some q => throw s!"`use {written}`: {showPath q} has no `{name}`"
    | none => throw s!"`use {written}`: there is no module `{"::".intercalate before}`"
  pure found

end

/-- Where names are being resolved: the module, and what it can write. -/
structure Ctx where
  here : List String
  scope : List Bound
  /-- The type parameters of the function being read. -/
  generics : List String := []

/-- A constructor some of whose fields are private cannot be built or taken
apart outside its module. -/
def checkSealed (ctx : Ctx) (written : String) (e : Entry) : R Unit := do
  if e.kind != .ctor || e.home == ctx.here then return
  match (← get).fields.lookup e.global with
  | some (_, _, pubs) =>
    if pubs.any (!·) then
      throw s!"`{written}` has private fields: only {showPath e.home} can build one or take one apart"
  | none => pure ()

/-- What a value's name means: the name it is written with from here on, its
qualifier if it keeps one, and the declaration if it is one. A qualifier is a
module, or a type, effect or trait, itself perhaps in a module. -/
def resolveValue (ctx : Ctx) (bound : List String) (qual : Option String) (name : String) :
    R (Option String × String × Option Entry) := do
  match qual with
  | none =>
    if bound.contains name then return (none, name, none)
    match lookupIn ctx.scope .value name with
    | some e =>
      noteUse ctx.here e
      checkSealed ctx name e
      pure (none, e.global, some e)
    | none => pure (none, name, none)
  | some q =>
    let segs := q.splitOn "::"
    if let some m ← moduleAt ctx.here ctx.scope segs then
      noteEdge ctx.here m
      let found ← if m == ctx.here then
          pure (ctx.scope.filter fun b => b.name == name && b.rank == 0)
        else exported ctx.here m name
      match found.find? fun b => b.entry.kind.space == .value with
      | some b =>
        noteUse ctx.here b.entry
        checkSealed ctx name b.entry
        return (none, b.entry.global, some b.entry)
      | none => throw s!"{showPath m} has no `{name}`"
    -- `Type::Constructor`, `Effect::operation`, `Trait::function`.
    let last := segs.getLast!
    let before := segs.dropLast
    let owner ← if before.isEmpty then
        pure ((ctx.scope.filter fun b => b.name == last &&
          (b.entry.kind == .type || b.entry.kind == .effect || b.entry.kind == .trait)).head?.map (·.entry))
      else
        match ← moduleAt ctx.here ctx.scope before with
        | some m =>
          noteEdge ctx.here m
          let found ← if m == ctx.here then
              pure (ctx.scope.filter fun b => b.name == last && b.rank == 0)
            else exported ctx.here m last
          match found.find? fun b =>
              b.entry.kind == .type || b.entry.kind == .effect || b.entry.kind == .trait with
          | some b => pure (some b.entry)
          | none => throw s!"{showPath m} has no `{last}`"
        | none => throw s!"`{q}::{name}`: there is no module `{"::".intercalate before}`"
    match owner with
    | none => pure (some q, name, none)
    | some o =>
      noteUse ctx.here o
      let member := ((← unitOf o.home).bind fun u =>
        u.own.find? fun b => b.name == name && b.entry.kind.space == .value).map (·.entry)
      match member with
      | some m =>
        checkSealed ctx name m
        pure (some o.global, m.global, some m)
      | none => pure (some o.global, name, none)

/-- What a name written where a type, an effect or a trait is expected means. -/
def resolveNamed (ctx : Ctx) (space : Space) (generics : List String) (written : String) :
    R (String × Option Entry) := do
  let segs := written.splitOn "::"
  if segs.length == 1 then
    if generics.contains written then return (written, none)
    match lookupIn ctx.scope space written with
    | some e =>
      noteUse ctx.here e
      pure (e.global, some e)
    | none => pure (written, none)
  else
    let last := segs.getLast!
    let before := segs.dropLast
    -- `T::Item`, of a type parameter: a type one of its traits leaves to an
    -- implementation. The checker finds which.
    if let [p] := before then
      if generics.contains p then return (written, none)
    let some m ← moduleAt ctx.here ctx.scope before
      | throw s!"`{written}`: there is no module `{"::".intercalate before}`"
    noteEdge ctx.here m
    let found ← if m == ctx.here then
        pure (ctx.scope.filter fun b => b.name == last && b.rank == 0)
      else exported ctx.here m last
    match found.find? fun b => b.entry.kind.space == space with
    | some b =>
      noteUse ctx.here b.entry
      pure (b.entry.global, some b.entry)
    | none => throw s!"{showPath m} has no `{last}`"

partial def resolveType (ctx : Ctx) (generics : List String) : TypeExpr → R TypeExpr
  | .name x args => do
    pure (.name (← resolveNamed ctx .type generics x).1 (← args.mapM (resolveType ctx generics)))
  | .tuple args => .tuple <$> args.mapM (resolveType ctx generics)
  | .fn ps r => do
    pure (.fn (← ps.mapM (resolveType ctx generics)) (← resolveType ctx generics r))
  | .performs r effects => do
    let effects ← effects.mapM fun (e, args) => do
      pure ((← resolveNamed ctx .effect [] e).1, ← args.mapM (resolveType ctx generics))
    pure (.performs (← resolveType ctx generics r) effects)
  | .ref uniq t life => do pure (.ref uniq (← resolveType ctx generics t) life)
  | t => pure t

/-- The fields written by name, in the order the declaration has them. -/
def orderFields {α : Type} (written : String) (names : List String)
    (gave : List (String × α)) (rest : Option α) : Except String (List α) := do
  for (field, _) in gave do
    unless names.contains field do throw s!"`{written}` has no field `{field}`"
    if (gave.filter (·.1 == field)).length > 1 then throw s!"field `{field}` is written twice"
  names.mapM fun field =>
    match gave.lookup field, rest with
    | some v, _ => pure v
    | none, some v => pure v
    | none, none => throw s!"field `{field}` of `{written}` is missing"

/-- The names of the fields of the constructor a resolved name is, if it was
declared with names. -/
def fieldNamesOf (written : String) (e : Option Entry) : R (List String) := do
  let fields := (← get).fields
  let names := (e.bind fun e => fields.lookup e.global).map (·.2.1)
  match names with
  | some names => if names.isEmpty then throw s!"the fields of `{written}` have no names" else pure names
  | none => throw s!"`{written}` is not a constructor whose fields have names"

/-- A number no other use of this gets: for a name, or for the identity of a
borrow, well above any the parser gives. -/
def freshId : R Nat := do
  let n := (← get).fresh
  modify fun s => { s with fresh := n + 1 }
  pure n

/-- Is this pattern one that binds by reference, and for writing? -/
def byRef? : Pattern → Option (Bool × Pattern)
  | .ctor name none [p] =>
    if name == byRefMark true then some (true, p)
    else if name == byRefMark false then some (false, p)
    else none
  | _ => none

/-- The constructor a constant is another name of, if it is one: `let Some =
Ok;`. -/
partial def aliased (fuel : Nat) (e : Entry) : R (Option String) := do
  if e.kind == .ctor then return some e.global
  if e.kind != .const || fuel == 0 then return none
  let some unit ← unitOf e.home | return none
  let scope ← scopeOf e.home
  let value := unit.items.findSome? fun item =>
    let item := match item with
      | .pub _ i => i
      | i => i
    match item with
    | .alias name (.name none target) =>
      if mangle e.home name == e.global || s!"prelude::{name}" == e.global then some target else none
    | _ => none
  match value.bind fun target => lookupIn scope .value target with
  | some next => aliased (fuel - 1) next
  | none => pure none

/-- A pattern as the test of a value's shape that it is, its names left out;
and for each name, the way to the part it names: through tuples by number,
through constructors by constructor and number. -/
partial def shapeOf (ctx : Ctx) (way : List String) : Pattern → R (Pattern × List (String × List String))
  | .wild => pure (.wild, [])
  | .int n => pure (.int n, [])
  | .var x => do
    -- A constructor or a constant is a test; a new name names this part.
    match lookupIn ctx.scope .value x with
    | some e => if e.kind == .ctor || e.kind == .const then pure (.var x, []) else pure (.wild, [(x, way)])
    | none => pure (.wild, [(x, way)])
  | .tuple args => do
    let mut pats : Array Pattern := #[]
    let mut names : List (String × List String) := []
    for (p, i) in args.zip (List.range args.length) do
      let (p, ns) ← shapeOf ctx (way ++ [toString i]) p
      pats := pats.push p
      names := names ++ ns
    pure (.tuple pats.toList, names)
  | .ctor name qual args => do
    if (byRef? (.ctor name qual args)).isSome then
      throw "a pattern that binds by reference is written once, around the whole pattern"
    let (_, global, entry) ← resolveValue ctx [] qual name
    -- Fields given by name are put in the declared order first.
    let args ← match args with
      | .var mark :: gave =>
        if mark == recordMark then
          let names ← fieldNamesOf name entry
          let rest := gave.any fun
            | .var r => r == restMark
            | _ => false
          let gave := gave.filterMap fun
            | .ctor mark none [p] => (fieldOfMark mark).map fun field => (field, p)
            | _ => none
          match orderFields name names gave (if rest then some Pattern.wild else none) with
          | .ok ps => pure ps
          | .error e => throw e
        else pure args
      | _ => pure args
    -- A name declared for a constructor, `let Some = Ok;`, is that one.
    let global ← match entry with
      | some e =>
        if e.kind == .ctor then pure global
        else
          let found ← aliased 8 e
          match found with
          | some g => pure g
          | none => throw s!"`{name}` is not a constructor: a pattern that binds by reference is made of constructors, tuples and names"
      | none => throw s!"`{name}` is not a constructor: a pattern that binds by reference is made of constructors, tuples and names"
    let mut pats : Array Pattern := #[]
    let mut names : List (String × List String) := []
    for (p, i) in args.zip (List.range args.length) do
      let (p, ns) ← shapeOf ctx (way ++ [ctorStep global i]) p
      pats := pats.push p
      names := names ++ ns
    pure (.ctor name qual pats.toList, names)

/-- The clauses of a callable in which a parameter binds by reference,
`&mut Circle(r) => ..`: the callable takes the reference, looks at what it
points to to choose a clause, and in the clause each name of the pattern is a
borrow of the part it names, through the reference. So a part of one of a
type's several constructors can be borrowed, once the value is known to be
made by that one. Clauses without such a parameter are as they are. -/
def byReference (ctx : Ctx) (clauses : List Clause) : R (List Clause) := do
  let arity := match clauses.head? with
    | some (.mk pats _) => pats.length
    | none => 0
  let places := (List.range arity).filter fun i => clauses.any fun
    | .mk pats _ => ((pats[i]?).bind byRef?).isSome
  if places.isEmpty then return clauses
  let k ← freshId
  let outer := (List.range arity).map fun i => s!"%given{k}_{i}"
  let mut inner : Array Clause := #[]
  for clause in clauses do
    let .mk pats body := clause
    unless pats.length == arity do
      throw "the clauses of a callable take different numbers of arguments"
    let mut tests : Array Pattern := #[]
    let mut binds : Array Stmt := #[]
    for (p, i) in pats.zip (List.range arity) do
      if places.contains i then
        match byRef? p with
        | some (uniq, p) =>
          let (test, names) ← shapeOf ctx [] p
          tests := tests.push test
          for (x, way) in names do
            let id := 900000000 + (← freshId)
            if way.isEmpty then
              -- The whole of what is pointed to: the reference itself, lent.
              binds := binds.push (.let_ (.var x) (.reborrow uniq (.name none s!"%given{k}_{i}")))
            else
              binds := binds.push (.let_ (.var x) (.refField id uniq s!"%given{k}_{i}" way true))
        | none =>
          -- A clause that takes the reference as it is, or lets it go.
          match p with
          | .wild => tests := tests.push .wild
          | .var x =>
            match lookupIn ctx.scope .value x with
            | some _ => throw "where one clause binds a parameter by reference, `&mut Pattern`, every clause does, or takes the reference whole"
            | none =>
              tests := tests.push .wild
              binds := binds.push (.let_ (.var x) (.name none s!"%given{k}_{i}"))
          | _ =>
            throw "where one clause binds a parameter by reference, `&mut Pattern`, every clause does, or takes the reference whole"
      else tests := tests.push p
    inner := inner.push (.mk tests.toList (binds.toList ++ body))
  let args := (outer.zip (List.range arity)).map fun (x, i) =>
    if places.contains i then Expr.deref (.name none x) else .name none x
  pure [.mk (outer.map Pattern.var) [.expr (.call 0 (.closure 0 inner.toList) args)]]

/-- A pattern with its names resolved, and the names it binds. -/
partial def resolvePattern (ctx : Ctx) : Pattern → R (Pattern × List String)
  | .wild => pure (.wild, [])
  | .int n => pure (.int n, [])
  | .var x => do
    -- A constructor or a constant, if the name is one; else a new name.
    match lookupIn ctx.scope .value x with
    | some e =>
      if e.kind == .ctor || e.kind == .const then
        noteUse ctx.here e
        checkSealed ctx x e
        pure (.var e.global, [])
      else pure (.var x, [x])
    | none => pure (.var x, [x])
  | .tuple args => do
    let args ← args.mapM (resolvePattern ctx)
    pure (.tuple (args.map (·.1)), args.flatMap (·.2))
  | .ctor name qual args => do
    if (byRef? (.ctor name qual args)).isSome then
      throw "a pattern that binds by reference, `&mut Pattern`, is written as a parameter of a clause"
    let (qual', name', entry) ← resolveValue ctx [] qual name
    match args with
    | .var mark :: gave =>
      if mark == recordMark then
        let names ← fieldNamesOf name entry
        let rest := gave.any fun
          | .var r => r == restMark
          | _ => false
        let gave := gave.filterMap fun
          | .ctor mark none [p] => (fieldOfMark mark).map fun field => (field, p)
          | _ => none
        let ordered ← match orderFields name names gave (if rest then some Pattern.wild else none) with
          | .ok ps => pure ps
          | .error e => throw (e ++ (if rest then "" else " (`..` lets the rest go)"))
        let args ← ordered.mapM (resolvePattern ctx)
        return (.ctor name' qual' (args.map (·.1)), args.flatMap (·.2))
    | _ => pure ()
    let args ← args.mapM (resolvePattern ctx)
    pure (.ctor name' qual' (args.map (·.1)), args.flatMap (·.2))

mutual

partial def resolveExpr (ctx : Ctx) (bound : List String) : Expr → R Expr
  | .int n => pure (.int n)
  | .label l => pure (.label l)
  | .name qual name => do
    let (qual, name, _) ← resolveValue ctx bound qual name
    pure (.name qual name)
  | .call id f args => do
    match f, args with
    | .name none mark, [value, ty] =>
      if mark == ascribeMark then
        -- `let x: Type = value`: the type's names are resolved as types.
        let ty ← resolveType ctx ctx.generics (TypeExpr.ofExpr ty)
        return .call id f [← resolveExpr ctx bound value, ty.asExpr]
    | _, _ => pure ()
    match f, args with
    | .name none mark, [subject, .closure _ [.mk [pat] _]] =>
      if mark == isMark then
        -- `subject is Pattern`: a pattern callable applied to the subject,
        -- which gives what the pattern's new names stand for, or fails.
        let subject ← resolveExpr ctx bound subject
        let (pat, names) ← resolvePattern ctx pat
        let result := fun (ctor : String) (payload : Expr) => do
          let (qual, name, _) ← resolveValue ctx [] (some "%prelude::Result") ctor
          pure (Expr.call 0 (.name qual name) [payload])
        let found := if names.isEmpty then Expr.tuple []
          else .call 0 (.name none (packName names)) (names.map fun x => .name none x)
        return .call id (.closure 0
          [.mk [pat] [.expr (← result "Ok" found)], .mk [.wild] [.expr (← result "Err" (.tuple []))]])
          [subject]
    | _, _ => pure ()
    match f, args with
    | .name qual name, .name none mark :: gave =>
      if mark == recordMark then
        -- `Point { y: 2, x: 1 }`: computed as written, kept as declared.
        let (qual', name', entry) ← resolveValue ctx bound qual name
        let names ← fieldNamesOf name entry
        let gave ← gave.filterMapM fun
          | .call _ (.name none mark) [v] => do
            match fieldOfMark mark with
            | some field => pure (some (field, ← resolveExpr ctx bound v))
            | none => pure none
          | _ => pure none
        let _ ← match orderFields name names (gave.map fun (f, _) => (f, ())) none with
          | .ok r => pure r
          | .error e => throw e
        if gave.map (·.1) == names then
          return .call id (.name qual' name') (gave.map (·.2))
        let temps := gave.map fun (field, _) => s!"%{field}"
        return .call id (.closure 0 [.mk (temps.map Pattern.var)
          [.expr (.call (id + 1) (.name qual' name') (names.map fun field => .name none s!"%{field}"))]])
          (gave.map (·.2))
    | _, _ => pure ()
    pure (.call id (← resolveExpr ctx bound f) (← args.mapM (resolveExpr ctx bound)))
  | .tailCall id f args => do
    pure (.tailCall id (← resolveExpr ctx bound f) (← args.mapM (resolveExpr ctx bound)))
  | .tuple args => .tuple <$> args.mapM (resolveExpr ctx bound)
  | .proj e i => do pure (.proj (← resolveExpr ctx bound e) i)
  | .fieldOf id e name => do pure (.fieldOf id (← resolveExpr ctx bound e) name)
  | .deref e => .deref <$> resolveExpr ctx bound e
  | .reborrow uniq e => .reborrow uniq <$> resolveExpr ctx bound e
  | .closure id clauses => do
    pure (.closure id (← (← byReference ctx clauses).mapM (resolveClause ctx bound)))
  | .handle subject arms => do
    pure (.handle (← resolveExpr ctx bound subject) (← arms.mapM (resolveClause ctx bound)))
  | .labelScope l body => .labelScope l <$> resolveStmts ctx bound body
  | e => pure e

partial def resolveClause (ctx : Ctx) (bound : List String) : Clause → R Clause
  | .mk pats body => do
    let pats ← pats.mapM (resolvePattern ctx)
    pure (.mk (pats.map (·.1)) (← resolveStmts ctx (pats.flatMap (·.2) ++ bound) body))

/-- A statement with its names resolved, and the names it binds for the rest. -/
partial def resolveStmt (ctx : Ctx) (bound : List String) : Stmt → R (Stmt × List String)
  | .let_ pat value => do
    if (byRef? pat).isSome then
      throw "`let &mut Pattern = ..` is written as several statements: this is a compiler defect"

    let value ← resolveExpr ctx bound value
    let (pat, names) ← resolvePattern ctx pat
    pure (.let_ pat value, names)
  | .letMut x value => do pure (.letMut x (← resolveExpr ctx bound value), [x])
  | .expr e => do pure (.expr (← resolveExpr ctx bound e), [])
  | .defer e => do pure (.defer (← resolveExpr ctx bound e), [])
  | .assign target value => do
    pure (.assign (← resolveExpr ctx bound target) (← resolveExpr ctx bound value), [])
  | .located line col s => do
    match (resolveStmt ctx bound s).run (← get) with
    | .ok ((s, names), st) =>
      set st
      pure (.located line col s, names)
    | .error e => throw (positioned line col e)

partial def resolveStmts (ctx : Ctx) (bound : List String) : List Stmt → R (List Stmt)
  | [] => pure []
  | s :: rest => do
    -- `let &mut (a, b) = r;`: the reference is given a name, and each name
    -- of the pattern is a borrow of its part through it. The pattern has to
    -- be one that cannot fail.
    let rec peel : Stmt → Option ((Stmt → Stmt) × Bool × Pattern × Expr)
      | .located line col s => (peel s).map fun (wrap, u, p, v) => (fun x => .located line col (wrap x), u, p, v)
      | .let_ pat value => (byRef? pat).map fun (uniq, p) => (id, uniq, p, value)
      | _ => none
    if let some (wrap, uniq, pat, value) := peel s then
      let k ← freshId
      let holder := s!"%given{k}_0"
      let (_, names) ← shapeOf ctx [] pat
      let mut lets : List Stmt := [wrap (.let_ (.var holder) value)]
      for (x, way) in names do
        let id := 900000000 + (← freshId)
        lets := lets ++ [wrap (.let_ (.var x)
          (if way.isEmpty then .reborrow uniq (.name none holder) else .refField id uniq holder way true))]
      return ← resolveStmts ctx bound (lets ++ rest)
    let (s, names) ← resolveStmt ctx bound s
    pure (s :: (← resolveStmts ctx (names ++ bound) rest))

end

/-- The name in the whole program of what this module declares as `name`. -/
def ownName (ctx : Ctx) (space : Space) (name : String) : String :=
  match ctx.scope.find? fun b =>
      b.name == name && b.entry.home == ctx.here && b.entry.kind.space == space && b.rank == 0 with
  | some b => b.entry.global
  | none => mangle ctx.here name

/-- A function with its names resolved, under the name it has in the program. -/
def resolveFn (ctx : Ctx) (global : String) (generics : List String) :
    Item → R Item
  | .fn name ps annots ret clauses => do
    let generics := genericParams ps ++ generics
    let ctx := { ctx with generics }
    let annots ← annots.mapM fun a => a.mapM (resolveType ctx generics)
    let ret ← ret.mapM (resolveType ctx generics)
    let run := (do (← byReference ctx clauses).mapM (resolveClause ctx [])).run (← get)
    match run with
    | .ok (clauses, st) =>
      set st
      modify fun s => { s with homes := (global, key ctx.here) :: s.homes }
      pure (.fn global ps annots ret clauses)
    | .error e => throw (inFunction name e)
  | item => pure item

/-- An item with its names resolved: none for what only this pass reads. -/
partial def resolveItem (ctx : Ctx) : Item → R (List Item)
  | .pub _ item => resolveItem ctx item
  | .module _ _ => pure []
  | .import _ _ _ => pure []
  | .fn name ps annots ret clauses => do
    pure [← resolveFn ctx (ownName ctx .value name) [] (.fn name ps annots ret clauses)]
  | .enum name ps ctors => do
    let generics := genericParams ps
    let ctors ← ctors.mapM fun (c, fields) => do
      pure (ownName ctx .value c, ← fields.mapM (resolveType ctx generics))
    pure [.enum (ownName ctx .type name) ps ctors]
  | .struct name ps fields => do
    pure [.struct (ownName ctx .type name) ps (← fields.mapM (resolveType ctx (genericParams ps)))]
  | .effect name ps ops => do
    let generics := genericParams ps
    let ops ← ops.mapM fun op => do
      pure { op with
        name := ownName ctx .value op.name
        payload := ← op.payload.mapM (resolveType ctx generics)
        result := ← op.result.mapM (resolveType ctx generics) }
    pure [.effect (ownName ctx .effect name) ps ops]
  | .alias name value => do pure [.alias (ownName ctx .value name) (← resolveExpr ctx [] value)]
  | .coerce name => do
    let global := (← resolveValue ctx [] none name).2.1
    modify fun s => { s with coerced := s.coerced ++ [(ctx.here, global)] }
    pure [.coerce global]
  | .trait name methods => do
    -- Its own type parameters and the types an implementation says are
    -- names of its functions' types, as `Self` is.
    let extra := match (← unitOf ctx.here).bind fun u => u.items.findSome? fun item =>
        let item := match item with
          | .pub _ i => i
          | i => i
        match item with
        | .traitInfo n _ _ params assocs => if n == name then some (genericParams params ++ assocs) else none
        | _ => none with
      | some names => names
      | none => []
    let methods ← methods.mapM fun (m, ps, r) => do
      pure (ownName ctx .value m, ← ps.mapM (resolveType ctx ("Self" :: extra)),
        ← r.mapM (resolveType ctx ("Self" :: extra)))
    pure [.trait (ownName ctx .trait name) methods]
  | .traitInfo name supers defaults params assocs => do
    let supers ← supers.mapM fun s => (·.1) <$> resolveNamed ctx .trait [] s
    let generics := "Self" :: genericParams params ++ assocs
    let defaults ← defaults.mapM fun
      | .fn m ps annots ret clauses =>
        resolveFn ctx (ownName ctx .value m) generics (.fn m ps annots ret clauses)
      | item => pure item
    pure [.traitInfo (ownName ctx .trait name) supers defaults params assocs]
  | .impl ps tr head args context methods => do
    let (tr', trEntry) ← resolveNamed ctx .trait [] tr
    let (head', headEntry) ← resolveNamed ctx .type [] head
    -- An implementation is written beside the trait or beside the type, so
    -- that there is one place to look for it and no two can disagree.
    let foreign := fun (e : Option Entry) => match e with
      | some e => e.home != ctx.here
      | none => true
    if foreign trEntry && foreign headEntry && (trEntry.isSome || headEntry.isSome) then
      let homes := (trEntry.toList ++ headEntry.toList).filter (·.home != preludePath)
      unless homes.isEmpty do
        throw s!"`impl {tr} for {head}` is written in {showPath ctx.here}: an implementation is written in the module of its trait or of its type"
    let context ← context.mapM fun (p, bound) => do
      pure (p, (← resolveNamed ctx .trait [] bound).1)
    let generics := "Self" :: genericParams ps
    let methods ← methods.mapM fun
      | .fn m mps annots ret clauses => do
        -- A function of the trait has the name the trait gave it.
        let units := (← get).units
        let member : Option Bound := match trEntry with
          | some t => (units.find? fun (u : Module) => u.path == t.home).bind fun u =>
              u.own.find? fun (b : Bound) => b.name == m && b.entry.kind == Kind.method
          | none => none
        let m' := (member.map (·.entry.global)).getD m
        let item ← resolveFn ctx m' generics (.fn m mps annots ret clauses)
        modify fun s => { s with homes := (implFnName tr' head' m', key ctx.here) :: s.homes }
        pure item
      -- A type the implementation says: an argument of its trait, or a type
      -- the trait leaves to it.
      | .typeAlias name aps body => do
        pure (.typeAlias name aps (← resolveType ctx (genericParams ps) body))
      | item => pure item
    pure [.impl ps tr' head' args context methods]
  | .use head lower upper => do
    let (head', entry) ← resolveNamed ctx .type [] head
    if let some e := entry then
      -- Else a module could say of another's type that it need not be used.
      unless e.home == ctx.here do
        throw s!"`impl Use for {head}` is written in {showPath ctx.here}: how often a type is used is said in its module, {showPath e.home}"
    pure [.use head' lower upper]
  | .bounds fn bounds => do
    -- The types written of a function's type parameters, read as the
    -- function's own types are.
    let generics := match (← unitOf ctx.here).bind fun u => u.items.findSome? fun
        | .fn name ps _ _ _ => if name == fn then some ps else none
        | .pub _ (.fn name ps _ _ _) => if name == fn then some ps else none
        | _ => none with
      | some ps => genericParams ps
      | none => []
    let bounds ← bounds.mapM fun b => do
      let sealed_ := ["Fn", "RunsIn", "Environment", "Use", "Label"].contains b.trait || b.trait.startsWith "'"
      let trait ← if sealed_ then pure b.trait else (·.1) <$> resolveNamed ctx .trait [] b.trait
      let args ← b.args.mapM (resolveType ctx generics)
      let assoc ← b.assoc.mapM fun (name, t) => do pure (name, ← resolveType ctx generics t)
      pure { b with trait, args, assoc }
    pure [.bounds (ownName ctx .value fn) bounds]
  | .fieldNames ctor names pubs => pure [.fieldNames (ownName ctx .value ctor) names pubs]
  | .typeAlias name ps body => do
    pure [.typeAlias (ownName ctx .type name) ps (← resolveType ctx (genericParams ps) body)]
  | item => pure [item]

/-- The modules of a program, each with its items: `root` is the first, and a
module written inside another is taken out of it. -/
partial def gather (path : List String) (items : List Item) : Except String (List (List String × List Item)) := do
  let mut out : List (List String × List Item) := [(path, items)]
  for item in items do
    let inner := match item with
      | .pub _ i => i
      | i => i
    match inner with
    | .module name (some body) =>
      if name == "crate" || name == "self" || name == "super" then
        throw s!"a module cannot be named `{name}`"
      let more ← gather (path ++ [name]) body
      for (p, _) in more do
        if out.any (·.1 == p) then throw s!"module `{"::".intercalate p}` is written twice"
      out := out ++ more
    | .module name none =>
      throw s!"module `{"::".intercalate (path ++ [name])}` has no file"
    | _ => pure ()
  pure out

/-- A cycle among the modules, if which names which has one. -/
partial def findCycle (edges : List (List String × List String)) : Option (List (List String)) :=
  let rec go (trail : List (List String)) (at_ : List String) (fuel : Nat) : Option (List (List String)) :=
    if fuel == 0 then none
    else if trail.contains at_ then some (at_ :: (trail.takeWhile (· != at_)).reverse ++ [at_])
    else (edges.filter (·.1 == at_)).findSome? fun (_, next) => go (at_ :: trail) next (fuel - 1)
  (edges.map (·.1)).findSome? fun start => go [] start (edges.length + 2)

/-- What the checker is told of the modules of a program. -/
structure Resolved where
  items : List Item
  info : ModuleInfo

/-- A program of modules as one list of items, each name meaning one thing:
see above. `prelude` is a module every other can name without `use`. -/
def resolve (prelude root : List Item) : Except String Resolved := do
  let mods ← gather [] root
  -- The library's modules come straight after the prelude's, whatever the
  -- program is: what is checked first is then the same for every program.
  let library := fun (m : List String × List Item) => m.1.head? == some "std"
  let mods := (← gather preludePath prelude) ++ mods.filter library ++ mods.filter (!library ·)
  let mut units : List Module := []
  let mut fields : List (String × List String × List String × List Bool) := []
  let taken := (declared [] root).1.map (·.name)
  for (path, items) in mods do
    let (own, fs) := declared path items taken
    units := units ++ [⟨path, items, own⟩]
    fields := fields ++ fs
  let hidden := mods.flatMap fun (path, items) =>
    items.filterMap fun
      | .module name _ => some (path ++ [name])
      | _ => none
  let run : R (List Item × List (String × List String)) := do
    let mut out : Array Item := #[]
    for u in units do
      let ctx : Ctx := ⟨u.path, ← scopeOf u.path, []⟩
      for item in u.items do
        out := out ++ (← resolveItem ctx item).toArray
    -- Where each coercion applies: in the module that declares it, and in
    -- one that brings its function in with `use`.
    let coerced := (← get).coerced
    let mut applies : List (String × List String) := []
    for u in units do
      let scope ← scopeOf u.path
      let here := coerced.filterMap fun (home, g) =>
        if home == u.path || home == preludePath
            || scope.any (fun b => b.rank ≤ 1 && b.entry.global == g && b.entry.kind == .fn)
        then some g else none
      applies := applies ++ [(key u.path, here)]
    pure (out.toList, applies)
  let ((items, coercions), st) ← match run.run { units, fields, hidden } with
    | .ok r => pure r
    | .error e => throw e
  if let some cycle := findCycle st.edges then
    let chain := " -> ".intercalate (cycle.map fun q =>
      if q.isEmpty then "the first module" else "::".intercalate q)
    throw s!"modules use each other in a circle ({chain}); which module uses which must have no cycle"
  let fieldVis := fields.map fun (ctor, home, _, pubs) => (ctor, key home, pubs)
  -- The constructors of the prelude's text, by the names they have here.
  let preludeOwn := ((units.find? (·.path == preludePath)).map (·.own)).getD []
  let ctor := fun (name : String) =>
    (preludeOwn.find? fun b => b.name == name && b.entry.kind == Kind.ctor).map (·.entry.global)
  let text := match ctor "StrEnd", ctor "StrChar" with
    | some e, some c => some (e, c)
    | _, _ => none
  let preludeNames := (declared preludePath prelude).1.map (·.name)
  let mine := units.filter (·.path != preludePath)
  let pubFns := mine.flatMap fun u => u.own.filterMap fun b =>
    if b.entry.kind == .fn && !(b.entry.vis matches .priv) then some b.entry.global else none
  let privTypes := mine.flatMap fun u => u.own.filterMap fun b =>
    if b.entry.kind == .type && (b.entry.vis matches .priv) then some (b.entry.global, key u.path) else none
  pure ⟨items, ⟨st.homes, fieldVis, text, preludeNames.any taken.contains, pubFns, privTypes, coercions⟩⟩

end Glorious.Syntax.Modules
