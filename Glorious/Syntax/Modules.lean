module

public import Std.Data.HashMap
public import Std.Data.HashSet
public import Glorious.Syntax.Ast
public import Glorious.Syntax.ByRef
public import Glorious.Syntax.FlatOps

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

public section

namespace Glorious.Syntax.Modules

/-- Who can name a declaration: its module, that and the module it is written
in, or anyone. -/
inductive Vis where
  | priv
  | parent
  | pub
  deriving BEq

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
  deriving BEq

/-- Names of values, of types, of effects, of traits and of modules are told
apart by where they are written. -/
inductive Space where
  | value
  | type
  | effect
  | trait
  | module
  deriving BEq

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

structure Module where
  path : List String
  items : List Item
  own : List Bound

/-- The path the prelude has as a module. Nothing can write it. -/
def preludePath : List String := ["%prelude"]

/-- What the specification's default prelude has from the library (§3):
each name, with its module. Every module of a program that has the
library can name them, after what it declares and brings and after the
prelude (`scopeOf`). -/
def libraryPrelude : List (String × String) :=
  [("identity", "value"), ("Either", "value"),
   ("Left", "value"), ("Right", "value"), ("Rejected", "value"), ("Ordering", "cmp"),
   ("Less", "cmp"), ("Equal", "cmp"), ("Greater", "cmp"), ("Range", "iterator"),
   ("Fail", "value"), ("fail", "value"), ("Report", "value"), ("report", "value"),
   ("catch_fail", "value")]

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
  /-- The names of the library's prelude, as every module of the program
  has them: found once. -/
  libraryBounds : Option (List Bound) := none
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
  /-- How many callables the resolver has written out so far, each known by
  a number of its own. -/
  made : Nat := 0
  /-- `#![no_implicit_prelude]` or `#![no_std]`: the program's modules have
  the prelude's names only where they `use` them. -/
  bare : Bool := false
  /-- How many names this pass has made up. -/
  fresh : Nat := 0
  /-- Dot calls with a function in scope and types' own of the same name. -/
  dotAlts : List (Nat × List String) := []
  /-- Types' own functions, `Type::f`, by `f`: each with its module and the
  type's name, in the order of the modules; the types each module declares;
  and the fields written with names, by name, each with its module and
  whether it is `pub`. -/
  typeFns : Std.HashMap String (Array (List String × Bound × String)) := {}
  typesOf : Std.HashMap (List String) (Std.HashSet String) := {}
  fieldsNamed : Std.HashMap String (Array (List String × Bool)) := {}

abbrev R := StateT St (Except String)

/-- A constructor of an `enum` whose name another constructor of its module
has too is named with its type, `TaskError::Cancelled`, here and wherever it
is written: the items of a module with those renamed so. A `struct` keeps
its own name. -/
def qualifyShared (items : List Item) : List Item := Id.run do
  let plain := fun (item : Item) => match item with
    | .pub _ i => i
    | i => i
  let names := items.flatMap fun item => match plain item with
    | .enum _ _ ctors => ctors.map (·.1)
    | .struct name _ _ => [name]
    | _ => []
  let shared := names.filter fun c => (names.filter (· == c)).length > 1
  if shared.isEmpty then return items
  let mut out : Array Item := #[]
  -- (The names of a constructor's fields follow the type that declares it.)
  let mut last : Option (String × List String) := none
  for item in items do
    let again := fun (i : Item) => match item with
      | .pub parent _ => Item.pub parent i
      | _ => i
    match plain item with
    | .enum name ps ctors =>
      last := some (name, ctors.map (·.1))
      out := out.push (again (.enum name ps (ctors.map fun (c, fields) =>
        (if shared.contains c then s!"{name}::{c}" else c, fields))))
    | .struct name _ _ =>
      last := some (name, [])
      out := out.push item
    | .fieldNames ctor names pubs =>
      match last with
      | some (name, ctors) =>
        if shared.contains ctor && ctors.contains ctor then
          out := out.push (again (.fieldNames s!"{name}::{ctor}" names pubs))
        else out := out.push item
      | none => out := out.push item
    | _ => out := out.push item
  out.toList

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
  -- (A function two of its traits have, `fmt` of `Display` and of `Debug`:
  -- each trait's its own, known by the trait's name and its.)
  let methodNames := items.flatMap fun item =>
    match (match item with | .pub _ i => i | i => i) with
    | .trait _ methods => methods.map (·.1)
    | _ => []
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
    | .alias name _ _ => out := add out name .const
    | .trait name methods =>
      out := add out name .trait
      for (m, _, _) in methods do
        if (methodNames.filter (· == m)).length > 1 then
          out := out.push ⟨m, ⟨path, mangle path (sharedMethodName name m), vis, .method⟩, vis, 0⟩
        else out := add out m .method
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

/-- Two different meanings a name has here at once: what the module declares
or names in a `use` twice over, or what two `use ..::*` both bring and nothing
nearer does. -/
def clash (scope : List Bound) (space : Space) (name : String) : Option (Entry × Entry) :=
  let found := scope.filter fun b => b.name == name && b.entry.kind.space == space
  match found.map (·.rank) with
  | [] => none
  | r :: rs =>
    let best := rs.foldl min r
    if best > 1 then none
    else
      match found.filter (·.rank == best) with
      | a :: more => (more.find? fun b => b.entry.global != a.entry.global).map fun b => (a.entry, b.entry)
      | [] => none

def unitOf (p : List String) : R (Option Module) := do
  pure ((← get).units.find? (·.path == p))

/-- The operations of an effect, as its module has them. -/
def opsOf (e : Entry) : R (List Bound) := do
  let some unit ← unitOf e.home | return []
  let some named := unit.own.find? fun b => b.entry.global == e.global && b.entry.kind == .effect
    | return []
  let ops := unit.items.findSome? fun item =>
    let item := match item with
      | .pub _ i => i
      | i => i
    match item with
    | .effect n _ ops => if n == named.name then some (ops.map (·.name)) else none
    | _ => none
  pure (unit.own.filter fun b => b.entry.kind == .op && (ops.getD []).contains b.name)

def noteEdge (viewer target : List String) : R Unit := do
  if viewer == target || target.head? == preludePath.head? || viewer.head? == preludePath.head? then return
  unless (← get).edges.any (· == (viewer, target)) do
    modify fun s => { s with edges := (viewer, target) :: s.edges }

/-- A name used from `viewer` means this declaration. -/
def noteUse (viewer : List String) (e : Entry) : R Unit := noteEdge viewer e.home

/-- The names a pattern says are new with `let name`. -/
partial def forcedNames : Pattern → List String
  | .marked .letBind [.var x] => [x]
  | .ctor _ _ args | .marked _ args => args.flatMap forcedNames
  | .tuple args => args.flatMap forcedNames
  | _ => []

/-- A pattern with each `let name` written as the name it is told by. -/
partial def unforce : Pattern → Pattern
  | .marked .letBind [.var x] => .var (x ++ letSuffix)
  | .marked m args => .marked m (args.map unforce)
  | .ctor c q args => .ctor c q (args.map unforce)
  | .tuple args => .tuple (args.map unforce)
  | p => p

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
        -- An effect brings its operations with it, under their own names
        -- whatever the effect is called here.
        if !glob && b.entry.kind == .effect then
          for o in ← opsOf b.entry do
            unless out.any (fun x => x.name == o.name && x.entry.global == o.entry.global && x.rank == 0) do
              out := out ++ [{ o with shown, rank := 0 }]
  if p != preludePath && !((← get).bare && p.head? != some "std" && p.head? != preludePath.head?) then
    if let some prelude ← unitOf preludePath then
      out := out ++ prelude.own.map fun b => { b with shown := .priv, rank := 2 }
  -- The library's prelude, after all of that, in a module of the program
  -- that has the library: each name from its module, where that is read.
  let library := ["std", "core", "alloc"].any (p.head? == some ·) || p.head? == preludePath.head?
  if !library && !(← get).bare then
    let lib ← match (← get).libraryBounds with
      | some bs => pure bs
      | none => do
        let mut bs : Array Bound := #[]
        for (name, m) in libraryPrelude do
          if (← unitOf ["std", m]).isSome then
            for b in ← exported [] ["std", m] name do
              bs := bs.push { b with shown := .priv, rank := 3 }
        modify fun s => { s with libraryBounds := some bs.toList }
        pure bs.toList
    out := out ++ lib
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
partial def moduleAt (viewer : List String) (named : String → List Bound) (segs : List String) :
    R (Option (List String)) := do
  let some head := segs.head? | return none
  let start ← match head with
    -- What the compiler itself writes of the prelude, whatever is in scope.
    | "%prelude" => pure (some preludePath)
    -- The prelude by name, where the program has no module of that name.
    | "prelude" =>
      if (← unitOf ["prelude"]).isSome || (lookupIn (named "prelude") .module "prelude").isSome then
        match lookupIn (named head) .module head with
        | some e => pure (some e.home)
        | none =>
          enter viewer [head]
          pure (some [head])
      else pure (some preludePath)
    | "crate" => pure (some [])
    | "self" => pure (some viewer)
    | "super" =>
      if viewer.isEmpty then throw "`super`: the first module is written in no other"
      pure (some viewer.dropLast)
    | _ =>
      match lookupIn (named head) .module head with
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
      let bounds ← if cur == viewer then pure (named seg) else scopeOf cur
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
    let some q ← moduleAt p (fun _ => scope) path | throw s!"`use {written}::*`: there is no module `{written}`"
    if q == p then throw s!"`use {written}::*`: a module does not use itself"
    noteEdge p q
    let bounds ← scopeOf q
    let seen := bounds.filter fun b => b.rank ≤ 1 && visible b.shown q p
    for b in seen do noteUse p b.entry
    return seen
  -- The whole path may be a module.
  let asModule ← moduleAt p (fun _ => scope) path
  let name := path.getLast!
  let before := path.dropLast
  let mut found : List Bound := []
  if let some m := asModule then
    if m != p then
      noteEdge p m
      found := [⟨name, ⟨m, "", .pub, .module⟩, .priv, 0⟩]
  if !before.isEmpty then
    if let some q ← moduleAt p (fun _ => scope) before then
      if q == p then throw s!"`use {written}`: a module does not use itself"
      noteEdge p q
      let seen ← exported p q name
      for b in seen do noteUse p b.entry
      found := found ++ seen.filter fun b => b.entry.kind != .module || asModule.isNone
  -- `use a::Effect::operation`: one operation of an effect.
  if found.isEmpty && !before.isEmpty then
    let effect := before.getLast!
    let home ← if before.length == 1 then pure (some p) else moduleAt p (fun _ => scope) before.dropLast
    if let some q := home then
      let named ← if q == p then pure (scope.filter fun b => b.name == effect && b.rank ≤ 1)
        else exported p q effect
      if let some eb := named.find? fun b => b.entry.kind == .effect then
        match (← opsOf eb.entry).find? fun o => o.name == name with
        | some o =>
          noteUse p o.entry
          return [o]
        | none => throw s!"`use {written}`: the effect `{effect}` has no operation `{name}`"
  if found.isEmpty then
    if before.isEmpty then throw s!"`use {written}`: there is no module `{written}`"
    match ← moduleAt p (fun _ => scope) before with
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
  /-- What is in `scope` by name, each name's in the order they are there:
  a name is looked for among its own. -/
  named : Std.HashMap String (List Bound) := {}
  /-- The constructors written with their type, `Type::Name`, by `Name`. -/
  ctorsByLast : Std.HashMap String (List Bound) := {}

/-- What a module can write under a name. -/
def Ctx.of (ctx : Ctx) (name : String) : List Bound := ctx.named.getD name []

/-- What is in a scope, by name. -/
def byName (scope : List Bound) : Std.HashMap String (List Bound) :=
  scope.foldr (fun b m => m.insert b.name (b :: m.getD b.name [])) {}

/-- The constructors of a scope written with their type, by their own name. -/
def ctorsByLastName (scope : List Bound) : Std.HashMap String (List Bound) :=
  scope.foldr (fun b m =>
    match b.name.splitOn "::" with
    | [_, last] => if b.entry.kind == .ctor then m.insert last (b :: m.getD last []) else m
    | _ => m) {}

/-- A constructor some of whose fields are private cannot be built or taken
apart outside its module. -/
def checkSealed (ctx : Ctx) (written : String) (e : Entry) : R Unit := do
  if e.kind != .ctor || e.home == ctx.here then return
  match (← get).fields.lookup e.global with
  | some (_, _, pubs) =>
    if pubs.any (!·) then
      throw s!"`{written}` has private fields: only {showPath e.home} can build one or take one apart"
  | none => pure ()

/-- What module `m` has named `name`, as seen from where `ctx` is. -/
def namedInModule (ctx : Ctx) (m : List String) (name : String) : R (List Bound) := do
  noteEdge ctx.here m
  if m == ctx.here then pure ((ctx.of name).filter fun b => b.name == name && b.rank == 0)
  else exported ctx.here m name

/-- A name the prelude has, where the prelude is not brought in: said so. -/
def preludeNotIn (ctx : Ctx) (space : Space) (name : String) : R Unit := do
  if (← get).bare && ctx.here.head? != preludePath.head? && ctx.here.head? != some "std" then
    if let some prelude ← unitOf preludePath then
      if prelude.own.any fun b => b.name == name && b.entry.kind.space == space then
        throw s!"unknown name `{name}`: the prelude is not brought in here (`use prelude::{name};`)"

/-- What a value's name means: the name it is written with from here on, its
qualifier if it keeps one, and the declaration if it is one. A qualifier is a
module, or a type, effect or trait, itself perhaps in a module. -/
def resolveValue (ctx : Ctx) (bound : List String) (qual : Option String) (name : String) :
    R (Option String × String × Option Entry) := do
  match qual with
  | none =>
    if bound.contains name then return (none, name, none)
    if let some (a, b) := clash (ctx.of name) .value name then
      -- (A function of two traits: which trait's is said with the trait.)
      if a.kind == .method && b.kind == .method then
        let traitOf := fun (e : Entry) => ((e.global.splitOn "::").dropLast.getLast?).getD e.global
        throw s!"`{name}` is a function of more than one trait here, `{traitOf a}` and `{traitOf b}`: say which, `{traitOf a}::{name}(..)` or `<T as {traitOf b}>::{name}(..)`, or call it on a value, `x.{name}(..)`"
      throw s!"`{name}` is two things here, `{a.global}` and `{b.global}`: say which with its module"
    match lookupIn (ctx.of name) .value name with
    | some e =>
      noteUse ctx.here e
      checkSealed ctx name e
      pure (none, e.global, some e)
    | none =>
      -- A constructor that shares its name with another of its module is
      -- written with its type.
      let shared := ctx.ctorsByLast.getD name []
      unless shared.isEmpty do
        let ways := " or ".intercalate (shared.map fun b => s!"`{b.name}`")
        throw s!"`{name}` is a constructor of more than one type here: write {ways}"
      -- Without the prelude brought in, its names are not there to write.
      preludeNotIn ctx .value name
      pure (none, name, none)
  | some q =>
    let segs := q.splitOn "::"
    if let some m ← moduleAt ctx.here ctx.of segs then
      match (← namedInModule ctx m name).find? fun b => b.entry.kind.space == .value with
      | some b =>
        noteUse ctx.here b.entry
        checkSealed ctx name b.entry
        return (none, b.entry.global, some b.entry)
      | none => throw s!"{showPath m} has no `{name}`"
    -- `Type::Constructor`, `Effect::operation`, `Trait::function`.
    let last := segs.getLast!
    let before := segs.dropLast
    let owner ← if before.isEmpty then
        pure (((ctx.of last).filter fun b => b.name == last &&
          (b.entry.kind == .type || b.entry.kind == .effect || b.entry.kind == .trait)).head?.map (·.entry))
      else
        match ← moduleAt ctx.here ctx.of before with
        | some m =>
          match (← namedInModule ctx m last).find? fun b =>
              b.entry.kind == .type || b.entry.kind == .effect || b.entry.kind == .trait with
          | some b => pure (some b.entry)
          | none => throw s!"{showPath m} has no `{last}`"
        | none => throw s!"`{q}::{name}`: there is no module `{"::".intercalate before}`"
    match owner with
    | none => pure (some q, name, none)
    | some o =>
      noteUse ctx.here o
      -- A function of the type's own, `impl Type { fn name .. }`: it is one
      -- of the type's module, named after both, and as private as it is
      -- written.
      let inherent := (← unitOf o.home).bind fun u =>
        u.own.find? fun b => b.name == s!"{last}::{name}" && b.entry.kind.space == .value
      if let some b := inherent then
        unless o.home == ctx.here || visible b.shown o.home ctx.here do
          throw s!"`{last}::{name}` is private to {showPath o.home}: only what is `pub` can be named from outside"
        noteUse ctx.here b.entry
        return (none, b.entry.global, some b.entry)
      -- (Of a trait, its own: where another trait of its module has a
      -- function of the name, the one named after this trait.)
      let member := ((← unitOf o.home).bind fun u =>
        let named := u.own.filter fun b => b.name == name && b.entry.kind.space == .value
        (named.find? fun b => o.kind == .trait && b.entry.global.endsWith (sharedMethodName last name)) <|> named.head?).map (·.entry)
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
    if let some (a, b) := clash (ctx.of written) space written then
      throw s!"`{written}` is two things here, `{a.global}` and `{b.global}`: say which with its module"
    match lookupIn (ctx.of written) space written with
    | some e =>
      noteUse ctx.here e
      pure (e.global, some e)
    | none =>
      preludeNotIn ctx space written
      pure (written, none)
  else
    let last := segs.getLast!
    let before := segs.dropLast
    -- `T::Item`, of a type parameter: a type one of its traits leaves to an
    -- implementation. The checker finds which.
    if let [p] := before then
      if generics.contains p then return (written, none)
    let some m ← moduleAt ctx.here ctx.of before
      | throw s!"`{written}`: there is no module `{"::".intercalate before}`"
    match (← namedInModule ctx m last).find? fun b => b.entry.kind.space == space with
    | some b =>
      noteUse ctx.here b.entry
      pure (b.entry.global, some b.entry)
    | none => throw s!"{showPath m} has no `{last}`"

partial def resolveType (ctx : Ctx) (generics : List String) : TypeExpr → R TypeExpr
  | .name x args => do
    -- (`[T]` is a slice's elements, a type only behind a reference.)
    if x == sliceMark then
      throw "`[T]` alone is no type: a slice is `&[T]` (or `&mut [T]`), an array of so many `[T; N]`, and a list that grows a `Vec<T>`"
    -- `<T as Trait>::Name`: the trait is a trait, and the name is the trait's.
    if x == assocOfMark then
      match args with
      | [self, .name tr targs, name] =>
        return .name x [← resolveType ctx generics self,
          .name (← resolveNamed ctx .trait [] tr).1 (← targs.mapM (resolveType ctx generics)), name]
      | _ => throw "`<Type as Trait>::Name` names a trait and what it leaves to an implementation"
    pure (.name (← resolveNamed ctx .type generics x).1 (← args.mapM (resolveType ctx generics)))
  | .tuple args => .tuple <$> args.mapM (resolveType ctx generics)
  | .fn ps r => do
    pure (.fn (← ps.mapM (resolveType ctx generics)) (← resolveType ctx generics r))
  | .performs r effects => do
    let effects ← effects.mapM fun (e, args) => do
      pure ((← resolveNamed ctx .effect [] e).1, ← args.mapM (resolveType ctx generics))
    pure (.performs (← resolveType ctx generics r) effects)
  -- `&'a str`: text borrowed, the prelude's `StrRef<'a>` (what `str` is
  -- otherwise, where a program names its own, is that).
  | .ref false (.name "str" []) life => do
    if (lookupIn (ctx.of "str") .type "str").isSome then
      return .ref false (← resolveType ctx generics (.name "str" [])) life
    pure (.name (← resolveNamed ctx .type generics "StrRef").1 (life.toList.map (.name · [])))
  -- `&'a [T]` and `&'a mut [T]`: elements borrowed, a slice, the prelude's
  -- `SliceRef<'a, T>` and `SliceMut<'a, T>`: an address and a length.
  | .ref uniq (.name x [t]) life => do
    if x != sliceMark then return .ref uniq (← resolveType ctx generics (.name x [t])) life
    let name := if uniq then "SliceMut" else "SliceRef"
    pure (.name (← resolveNamed ctx .type generics name).1
      (life.toList.map (.name · []) ++ [← resolveType ctx generics t]))
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
    | .alias name b v =>
      -- (A name given with a type stands for the same constructor.)
      match aliasValue (Flat.treeExpr b v) with
      | .name none target =>
        if mangle e.home name == e.global || s!"prelude::{name}" == e.global then some target else none
      | _ => none
    | _ => none
  match value.bind fun target => lookupIn scope .value target with
  | some next => aliased (fuel - 1) next
  | none => pure none

/-- The patterns of a constructor's fields with `..` written out: a `_` for
each field it stands for. -/
def restWritten (written : String) (e : Option Entry) (args : List Pattern) : R (List Pattern) := do
  let isRest := fun (p : Pattern) => match p with
    | .marked .rest [] => true
    | _ => false
  unless args.any isRest do return args
  if (args.filter isRest).length > 1 then throw s!"`{written}(..)`: `..` is written once"
  -- (A name given to a constructor, `let Some = Ok;`, is that constructor.)
  let ctor ← match e with
    | some e => aliased 8 e
    | none => pure none
  let fields := (← get).fields
  match (ctor.bind fun c => fields.lookup c).map (·.2.2.length) with
  | some n =>
    let given := args.length - 1
    if given > n then throw s!"`{written}` has {n} fields, and more than that are written"
    pure (args.flatMap fun p => if isRest p then List.replicate (n - given) Pattern.wild else [p])
  | none => throw s!"`..` stands for the rest of a constructor's fields, and `{written}` is not a constructor of a declared type"

mutual

/-- A pattern with each `&P` that is inside it, and not the whole of it,
replaced by a new name: the pattern, and each name with the pattern it
stands for. -/
partial def liftRefs (top : Bool) : Pattern → R (Pattern × List (String × Pattern))
  | .tuple ps => do
    let (ps, refs) ← liftRefsAll ps
    pure (.tuple ps, refs)
  | .marked (.byRef uniq) args => do
    if top then return (.marked (.byRef uniq) args, [])
    let x := s!"%ref{← freshId}"
    return (.var x, [(x, .marked (.byRef uniq) args)])
  | .ctor name qual args => do
    let (args, refs) ← liftRefsAll args
    pure (.ctor name qual args, refs)
  | p => pure (p, [])

partial def liftRefsAll (ps : List Pattern) : R (List Pattern × List (String × Pattern)) := do
  let mut out : Array Pattern := #[]
  let mut refs : List (String × Pattern) := []
  for p in ps do
    let (p, more) ← liftRefs false p
    out := out.push p
    refs := refs ++ more
  pure (out.toList, refs)

end

/-- A pattern with each `&P` in it written `P`: what the clauses ask, for
seeing that they take every case. -/
partial def throughRefs : Pattern → Pattern
  | .tuple ps => .tuple (ps.map throughRefs)
  | .marked (.byRef _) [p] => throughRefs p
  | .ctor name qual args => .ctor name qual (args.map throughRefs)
  | p => p

/-- A pattern as it is apart from the names it binds: two clauses whose
patterns are the same so differ only in what they ask of the references
inside. -/
partial def patternShape : Pattern → String
  | .wild => "_"
  | .int n => toString n
  | .var x => if x.startsWith "%ref" then "&" else s!"({x})"
  | .tuple ps => "(" ++ ",".intercalate (ps.map patternShape) ++ ")"
  | .ctor name qual args =>
    s!"{qual.getD ""}::{name}(" ++ ",".intercalate (args.map patternShape) ++ ")"
  | .marked m args => s!"{m.shown}(" ++ ",".intercalate (args.map patternShape) ++ ")"

/-- A constructor's patterns given by its fields' names, `C { a, b: p, .. }`,
in the declared order; none where they are not given so. (`hint`: said
after a field left out.) -/
def orderedFieldPats (name : String) (entry : Option Entry) (args : List Pattern) (hint : String := "") :
    R (Option (List Pattern)) := do
  let .marked .record [] :: gave := args | return none
  let names ← fieldNamesOf name entry
  let rest := gave.any fun
    | .marked .rest [] => true
    | _ => false
  let gave := gave.filterMap fun
    | .marked (.field field) [p] => some (field, p)
    | _ => none
  match orderFields name names gave (if rest then some Pattern.wild else none) with
  | .ok ps => pure (some ps)
  | .error e => throw (e ++ (if rest then "" else hint))

/-- What the resolver knows of the names in a pattern it writes out by
reference, before they are resolved. -/
def refNamesOf (ctx : Ctx) : RefNames R where
  kind x := pure <| match lookupIn (ctx.of x) .value x with
    | some e => if e.kind == .ctor then 1 else if e.kind == .const then 2 else 0
    | none => 0
  ctor name qual args := do
    let (_, global, entry) ← resolveValue ctx [] qual name
    -- Fields given by name are put in the declared order first.
    let args ← match ← orderedFieldPats name entry args with
      | some ps => pure ps
      | none => restWritten name entry args
    -- A name declared for a constructor, `let Some = Ok;`, is that one.
    let global ← match entry with
      | some e =>
        if e.kind == .ctor then pure global
        else
          match ← aliased 8 e with
          | some g => pure g
          | none => throw s!"`{name}` is not a constructor: a pattern that binds by reference is made of constructors, tuples and names"
      | none => throw s!"`{name}` is not a constructor: a pattern that binds by reference is made of constructors, tuples and names"
    pure (global, args)
  ctorTest name qual := do
    let (_, _, entry) ← resolveValue ctx [] qual name
    pure (if (entry.map (·.kind == .ctor)).getD false then some (.name qual name) else none)
  fresh := freshId

/-- A pattern with its names resolved, and the names it binds. -/
partial def resolvePattern (ctx : Ctx) : Pattern → R (Pattern × List String)
  | .wild => pure (.wild, [])
  | .int n => pure (.int n, [])
  | .var x => do
    -- A constructor or a constant, if the name is one; else a new name.
    match lookupIn (ctx.of x) .value x with
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
    -- An array of so many elements: its parts are patterns like any.
    if (fixedPatLen name).isSome then
      let args ← args.mapM (resolvePattern ctx)
      return (.ctor name none (args.map (·.1)), args.flatMap (·.2))
    let (qual', name', entry) ← resolveValue ctx [] qual name
    let args ← match ← orderedFieldPats name entry args " (`..` lets the rest go)" with
      | some ps => pure ps
      | none => restWritten name entry args
    let args ← args.mapM (resolvePattern ctx)
    pure (.ctor name' qual' (args.map (·.1)), args.flatMap (·.2))
  | .marked (.byRef _) _ =>
    throw "a pattern that binds by reference, `&mut Pattern`, is written as a parameter of a clause"
  | .marked m _ => throw s!"`{m.shown}` in a pattern where it cannot be; this is a compiler defect"


/-! ### Names resolved in a flat body -/

open Flat in
/-- Resolving names in a flat body: what is written is read from it, and
what it means is written to it anew. -/
abbrev RF := StateT Flat.Body R

open Flat in
def fpush (n : FExpr) : RF ExprId := modifyGet fun b => b.add n
open Flat in
def fpushS (n : FStmt) : RF StmtId := modifyGet fun b => (b.stmts.size, { b with stmts := b.stmts.push n })
open Flat in
def fpushC (n : FClause) : RF ClauseId := modifyGet fun b => (b.clauses.size, { b with clauses := b.clauses.push n })
open Flat in
def fbuild {α : Type} (act : Build α) : RF α := modifyGet fun b => act.run b
open Flat in
def fpushTree (e : Expr) : RF ExprId := fbuild (flatExpr e)

/-- What the resolver knows of names, in a flat body. -/
def refNamesOfF (ctx : Ctx) : RefNames RF :=
  let rn := refNamesOf ctx
  { kind := fun x => liftM (rn.kind x)
    ctor := fun name qual args => liftM (rn.ctor name qual args)
    ctorTest := fun name qual => liftM (rn.ctorTest name qual)
    fresh := liftM rn.fresh }

open Flat in
/-- Clauses in which a pattern for a value has `&P` inside it, `Some(&Leaf(n))
=> ..`, where the value holds a reference: the reference is bound first, and
what it points to is then asked of it by clauses of its own. Where none of
those is for what it points to, the clauses that follow are tried, with the
value the callable was given: so that value is one that can be looked at
again. Clauses without such a pattern are as they are. -/
partial def nestedRefsF (clauses : Array ClauseId) (within : Bool := false) : RF (Array ClauseId) := do
  let b ← get
  let arity := (clauses[0]?.map fun c => (b.clause c).pats.length).getD 0
  -- The clauses up to the first with a reference inside a pattern.
  let mut before : Array ClauseId := #[]
  let mut rest := clauses.toList
  let mut first : Option (List Pattern × List (String × Pattern) × Array StmtId) := none
  while first.isNone && !rest.isEmpty do
    match rest with
    | c :: more =>
      let ⟨pats, body⟩ := b.clause c
      let mut skeleton : Array Pattern := #[]
      let mut refs : List (String × Pattern) := []
      for p in pats do
        let (p, found) ← liftM (liftRefs true p)
        skeleton := skeleton.push p
        refs := refs ++ found
      rest := more
      if refs.isEmpty then before := before.push c
      else first := some (skeleton.toList, refs, body)
    | [] => pure ()
  let some (skeleton, refs, body) := first | return clauses
  -- The clauses after it that ask the same of the value, and differ only
  -- in what they ask of the references.
  let shape := skeleton.map patternShape
  let mut group : Array (List (String × Pattern) × Array StmtId) := #[(refs, body)]
  let mut going := true
  while going do
    match rest with
    | c :: more =>
      let ⟨pats, body⟩ := b.clause c
      let mut theirs : Array Pattern := #[]
      let mut found : List (String × Pattern) := []
      for p in pats do
        let (p, f) ← liftM (liftRefs true p)
        theirs := theirs.push p
        found := found ++ f
      if !found.isEmpty && theirs.toList.map patternShape == shape && found.length == refs.length then
        group := group.push (found, body)
        rest := more
      else going := false
    | [] => going := false
  -- What is tried where none of them is for what the references point to:
  -- the clauses that follow, given the value again.
  let k ← liftM freshId
  let given := (List.range arity).map fun i => s!"%again{k}_{i}"
  let later := s!"%later{k}"
  let after ← nestedRefsF rest.toArray true
  let never := fun (_ : Unit) => (do fpush (.tailCall 0 (← fpush (.name none "%never")) #[]) : RF ExprId)
  -- (The clauses that follow are tried only for what is left: that all of
  -- them together take every case is asked once, of all as written.)
  let after ← if after.isEmpty then pure after
    else pure (after.push (← fpushC ⟨given.map fun _ => Pattern.wild, #[← fpushS (.expr (← never ()))]⟩))
  let names := refs.map (·.1)
  -- (Where nothing follows, what is left is nothing: the clauses as written
  -- are asked whether they take every case, not these.)
  let left := fun (_ : Unit) => (do
    if after.isEmpty then never ()
    else fpush (.call 0 (← fpush (.name none later)) (← given.toArray.mapM fun x => fpush (.name none x))) : RF ExprId)
  let mut inner : Array ClauseId := #[]
  for (found, body) in group do
    inner := inner.push (← fpushC ⟨found.map (·.2), body⟩)
  inner := inner.push (← fpushC ⟨names.map fun _ => Pattern.wild, #[← fpushS (.expr (← left ()))]⟩)
  let innerCall ← fpush (.call 0 (← fpush (.closure 0 inner)) (← names.toArray.mapM fun x => fpush (.name none x)))
  let chosen ← fpushC ⟨skeleton, #[← fpushS (.expr innerCall)]⟩
  let outer := before ++ #[chosen, ← fpushC ⟨given.map fun _ => Pattern.wild, #[← fpushS (.expr (← left ()))]⟩]
  -- Whether the clauses as written take every case: asked of what the
  -- callable is given, each pattern reaching through the references in it.
  let asked ← if within then pure [] else do
    let rows ← clauses.mapM fun c => fpushC ⟨(b.clause c).pats.map fun p =>
        match byRef? p with
        | some _ => Pattern.wild
        | none => throughRefs p, #[]⟩
    let args ← given.toArray.mapM fun x => fpush (.name none x)
    let call ← fpush (.call 0 (← fpush (.mark .shapes)) (args.push (← fpush (.closure 0 rows))))
    pure [← fpushS (.expr call)]
  -- (Asked after the clauses are gone through: what the value is, and so
  -- where it holds references, is known from them by then.)
  let run ← fpush (.call 0 (← fpush (.closure 0 outer)) (← given.toArray.mapM fun x => fpush (.name none x)))
  let result := s!"%result{k}"
  let lets ← if after.isEmpty then pure [] else pure [← fpushS (.let_ (.var later) (← fpush (.closure 0 after)))]
  let tail ← if asked.isEmpty then pure [← fpushS (.expr run)]
    else pure ([← fpushS (.let_ (.var result) run)] ++ asked ++ [← fpushS (.expr (← fpush (.name none result)))])
  pure #[← fpushC ⟨given.map Pattern.var, (lets ++ tail).toArray⟩]

open Flat in
mutual

partial def resolveExprF (ctx : Ctx) (bound : List String) (e : ExprId) : RF ExprId := do
  let b ← get
  match b.expr e with
  | .int n => fpush (.int n)
  | .label l => fpush (.label l)
  | .name qual name => do
    let (qual', name', entry) ← liftM (resolveValue ctx bound qual name)
    -- What indexing and the like are written with is the prelude's function
    -- even where the program has a name of its own that is the same.
    let qual' := if qual == some "%prelude" && bound.contains name' then some "%prelude" else qual'
    -- An operation, or a trait's function, named where it is not called: a
    -- callable that performs it, or calls it, with what it is given (10.8).
    if let some en := entry then
      if en.kind == .op || en.kind == .method then
        let written := (← liftM (unitOf en.home)).bind fun u =>
          (u.own.find? fun bd => bd.entry.global == en.global && bd.entry.kind == en.kind).map (u, ·.name)
        let arity := written.bind fun (u, own) =>
          u.items.findSome? fun item =>
            let item := match item with
              | .pub _ i => i
              | i => i
            match item with
            | .effect _ _ ops => (ops.find? (·.name == own)).map (·.payload.length)
            | .trait _ methods => (methods.find? (·.1 == own)).map (·.2.1.length)
            | _ => none
        if let some n := arity then
          let made := (← getThe St).made
          modifyThe St fun s => { s with made := made + 1 }
          let params := (List.range n).map fun i => s!"%arg{i}"
          return ← fpushTree (.closure 0 [.mk (params.map Pattern.var)
            [.expr (.call (7000000000000 + made) (.name qual' name') (params.map (Expr.name none)))]])
    fpush (.name qual' name')
  | .call id f args => do
    -- `value.f(a)`: `f(value, a)`, where `f` is a function or a trait's
    -- function that can be named here.
    if let .fieldOf _ receiver name := b.expr f then
      -- Types' own functions of the name, that can be named here.
      let own := fun (anywhere : Bool) => (do
        let st ← getThe St
        let found := (st.typeFns.getD name #[]).toList.filter fun (path, bd, ty) =>
          bd.entry.kind.space == .value
            && (path == ctx.here || visible bd.shown path ctx.here)
            && (if anywhere then (st.typesOf.getD path {}).contains ty
              else (ctx.of ty).any fun named => named.name == ty && named.entry.kind == .type
                && named.entry.home == path)
        pure (found.map (·.2.1)) : RF (List Bound))
      unless bound.contains name do
        -- (A function of more than one trait, `x.fmt(f)` of `Display`'s
        -- and `Debug`'s: the first, with the others for the checker to
        -- take where the value's type has their trait and not its.)
        let traits := ((ctx.of name).filter fun b => b.name == name && b.entry.kind == .method).map (·.entry)
        let traits := traits.foldl (fun acc e => if acc.any (·.global == e.global) then acc else acc ++ [e]) []
        if let first :: others@(_ :: _) := traits then
          let alts := others.map (·.global) ++ (← own true).map (·.entry.global)
          unless id == 0 do
            modifyThe St fun s => { s with dotAlts := (id, alts) :: s.dotAlts }
          liftM (noteUse ctx.here first)
          let mark ← fpush (.call 0 (← fpush (.mark .receiver)) #[receiver])
          let call ← fpush (.call id (← fpush (.name none first.global)) (#[mark] ++ args))
          return ← resolveExprF ctx bound call
        if let some en := lookupIn (ctx.of name) .value name then
          if en.kind == .fn || en.kind == .method then
            let alts := (← own true).map (·.entry.global)
            -- (None: still a dot call, which the checker is told.)
            unless id == 0 do
              modifyThe St fun s => { s with dotAlts := (id, alts) :: s.dotAlts }
            -- (Marked: whether it is borrowed for the call is decided once
            -- every function's declaration has been seen.)
            let mark ← fpush (.call 0 (← fpush (.mark .receiver)) #[receiver])
            let call ← fpush (.call id (← fpush (.name none name)) (#[mark] ++ args))
            return ← resolveExprF ctx bound call
        -- A function of a type's own: found by its name alone, where one
        -- type that can be named here has it and no declared type has a
        -- field of that name.
        let fieldNamed := ((← getThe St).fieldsNamed.getD name #[]).any fun (path, p) => p || path == ctx.here
        unless fieldNamed do
          let found ← own true
          -- (One: no other, but a dot call, which the checker is told.)
          if id != 0 then
            modifyThe St fun s => { s with dotAlts := (id, if found.length > 1 then found.map (·.entry.global) else []) :: s.dotAlts }
          if let bd :: _ := found then
            liftM (noteUse ctx.here bd.entry)
            let receiver ← resolveExprF ctx bound receiver
            let args ← args.mapM (resolveExprF ctx bound)
            let mark ← fpush (.call 0 (← fpush (.mark .receiver)) #[receiver])
            return ← fpush (.call id (← fpush (.name none bd.entry.global)) (#[mark] ++ args))
    if let (some .path, #[a]) := (b.mark? f, args) then
      if let .name (some q) name := b.expr a then
        -- `Owner::NAME`: a trait's function of that name called with
        -- nothing, at the type `Owner`, if that is what `NAME` is here;
        -- or else whatever `Owner::NAME` names.
        let (_, _, entry) ← liftM (resolveValue ctx bound (some q) name)
        let method := (lookupIn (ctx.of name) .value name).any (·.kind == .method)
        if method && (entry.isNone || entry.any (·.kind == .method)) then
          if q == "Self" then
            return ← resolveExprF ctx bound (← fpush (.call id (← fpush (.name (some q) name)) #[]))
          let inner ← fpush (.call id (← fpush (.name none name)) #[])
          let ty ← fpush (.type (TypeExpr.tuple [.name q []]))
          return ← resolveExprF ctx bound (← fpush (.call 0 (← fpush (.mark .inst)) #[inner, ty]))
        return ← resolveExprF ctx bound (← fpush (.name (some q) name))
    if let (some mark, #[value, ty]) := (b.mark? f, args) then
      if mark == .ascribe || mark == .inst then
        -- `let x: Type = value`: the type's names are resolved as types.
        let ty ← liftM (resolveType ctx ctx.generics (b.typeAt ty))
        let value ← resolveExprF ctx bound value
        return ← fpush (.call id (← fpush (.mark mark)) #[value, ← fpush (.type ty)])
    if let (some .is_, #[subject, cl]) := (b.mark? f, args) then
      if let .closure _ #[c] := b.expr cl then
        let ⟨pats, _⟩ := b.clause c
        if let [pat] := pats then
          -- `subject is Pattern`: a pattern callable applied to the subject,
          -- which gives what the pattern's new names stand for, or fails.
          let subject ← resolveExprF ctx bound subject
          let (pat, names) ← liftM (resolvePattern ctx pat)
          let result := fun (ctor : String) (payload : Expr) => (do
            let (qual, name, _) ← resolveValue ctx [] (some "%prelude::Result") ctor
            pure (Expr.call 0 (.name qual name) [payload]) : R Expr)
          let found := if names.isEmpty then Expr.tuple []
            else .call 0 (.name none (packName names)) (names.map fun x => .name none x)
          let ok ← liftM (result "Ok" found)
          let err ← liftM (result "Err" (.tuple []))
          let callable ← fpushTree (.closure 0 [.mk [pat] [.expr ok], .mk [.wild] [.expr err]])
          return ← fpush (.call id callable #[subject])
    if let .name qual name := b.expr f then
      if let some first := args[0]? then
        if b.mark? first == some .record then
          -- `Point { y: 2, x: 1 }`: computed as written, kept as declared.
          let (qual', name', entry) ← liftM (resolveValue ctx bound qual name)
          let names ← liftM (fieldNamesOf name entry)
          let mut gave : Array (String × ExprId) := #[]
          for g in args.extract 1 args.size do
            match b.expr g with
            | .call _ m #[v] =>
              match b.mark? m with
              | some (.field field) => gave := gave.push (field, ← resolveExprF ctx bound v)
              | _ => pure ()
            | _ => pure ()
          let _ ← match orderFields name names (gave.toList.map fun (f, _) => (f, ())) none with
            | .ok r => pure r
            | .error err => throw err
          if gave.toList.map (·.1) == names then
            return ← fpush (.call id (← fpush (.name qual' name')) (gave.map (·.2)))
          let temps := gave.toList.map fun (field, _) => s!"%{field}"
          let built ← fpushTree (.call (id + 1) (.name qual' name') (names.map fun field => .name none s!"%{field}"))
          let cl ← fpushC ⟨temps.map Pattern.var, #[← fpushS (.expr built)]⟩
          return ← fpush (.call id (← fpush (.closure 0 #[cl])) (gave.map (·.2)))
    -- What is called is named as it is.
    let called ← match b.expr f with
      | .name q x => do
        let (q', x', _) ← liftM (resolveValue ctx bound q x)
        -- (The prelude's function, whatever is named the same here.)
        fpush (.name (if q == some "%prelude" && bound.contains x' then some "%prelude" else q') x')
      | _ => resolveExprF ctx bound f
    fpush (.call id called (← args.mapM (resolveExprF ctx bound)))
  | .tailCall id f args => do
    let called ← match b.expr f with
      | .name q x => do
        let (q, x, _) ← liftM (resolveValue ctx bound q x)
        fpush (.name q x)
      | _ => resolveExprF ctx bound f
    fpush (.tailCall id called (← args.mapM (resolveExprF ctx bound)))
  | .tuple args => do fpush (.tuple (← args.mapM (resolveExprF ctx bound)))
  | .proj x i => do fpush (.proj (← resolveExprF ctx bound x) i)
  | .fieldOf id x name => do fpush (.fieldOf id (← resolveExprF ctx bound x) name)
  | .deref x => do fpush (.deref (← resolveExprF ctx bound x))
  | .reborrow uniq x => do fpush (.reborrow uniq (← resolveExprF ctx bound x))
  | .closure id clauses => do
    let clauses ← Flat.byReference (refNamesOfF ctx) (← nestedRefsF clauses)
    fpush (.closure id (← clauses.mapM (resolveClauseF ctx bound)))
  | .handle subject arms => do
    fpush (.handle (← resolveExprF ctx bound subject) (← arms.mapM (resolveClauseF ctx bound)))
  | .labelScope l body => do fpush (.labelScope l (← resolveStmtsF ctx bound body.toList).toArray)
  | _ => pure e

partial def resolveClauseF (ctx : Ctx) (bound : List String) (c : ClauseId) : RF ClauseId := do
  let ⟨pats, body⟩ := (← get).clause c
  -- `let name` in a pattern: the name is told from a constant of its
  -- spelling by being written another way, in the pattern and wherever the
  -- body means it.
  let forced := pats.flatMap forcedNames
  let pats := pats.map unforce
  let mut renamed := body.toList
  for x in forced do
    renamed ← fbuild (Flat.renameStmts x (x ++ letSuffix) [] renamed)
  let pats ← pats.mapM fun p => liftM (resolvePattern ctx p)
  let body ← resolveStmtsF ctx (pats.flatMap (·.2) ++ bound) renamed
  fpushC ⟨pats.map (·.1), body.toArray⟩

/-- A statement with its names resolved, and the names it binds for the rest. -/
partial def resolveStmtF (ctx : Ctx) (bound : List String) (s : StmtId) : RF (StmtId × List String) := do
  match (← get).stmt s with
  | .let_ pat value => do
    if (byRef? pat).isSome then
      throw "`let &mut Pattern = ..` is written as several statements: this is a compiler defect"
    let value ← resolveExprF ctx bound value
    let (pat, names) ← liftM (resolvePattern ctx pat)
    pure (← fpushS (.let_ pat value), names)
  | .letMut x value => do pure (← fpushS (.letMut x (← resolveExprF ctx bound value)), [x])
  | .expr e => do pure (← fpushS (.expr (← resolveExprF ctx bound e)), [])
  | .defer e => do pure (← fpushS (.defer (← resolveExprF ctx bound e)), [])
  | .assign target value => do
    let t ← resolveExprF ctx bound target
    let v ← resolveExprF ctx bound value
    pure (← fpushS (.assign t v), [])
  | .located line col inner => do
    let (inner, names) ← tryCatch (resolveStmtF ctx bound inner) fun err => throw (positioned line col err)
    pure (← fpushS (.located line col inner), names)

partial def resolveStmtsF (ctx : Ctx) (bound : List String) : List StmtId → RF (List StmtId)
  | [] => pure []
  | s :: rest => do
    -- `let &mut (a, b) = r;`: the reference is given a name, and each name
    -- of the pattern is a borrow of its part through it. The pattern has to
    -- be one that cannot fail.
    let b ← get
    let rec peel (s : StmtId) (fuel : Nat) : Option (List (Nat × Nat) × Bool × Pattern × ExprId) :=
      match fuel with
      | 0 => none
      | fuel + 1 =>
      match b.stmt s with
      | .located line col inner => (peel inner fuel).map fun (places, u, p, v) => ((line, col) :: places, u, p, v)
      | .let_ pat value => (byRef? pat).map fun (uniq, p) => ([], uniq, p, value)
      | _ => none
    if let some (places, uniq, pat, value) := peel s 64 then
      let wrap := fun (st : StmtId) => (places.foldr (fun (line, col) (acc : RF StmtId) => do
        fpushS (.located line col (← acc))) (pure st) : RF StmtId)
      let k ← liftM freshId
      let holder := s!"%given{k}_0"
      let (_, names) ← liftM (shapeOf (refNamesOf ctx) [] pat)
      let mut lets : List StmtId := [← wrap (← fpushS (.let_ (.var holder) value))]
      for (x, way) in names do
        let id := 900000000 + (← liftM freshId)
        let v ← if way.isEmpty then fpush (.reborrow uniq (← fpush (.name none holder)))
          else fpush (.refField id uniq holder way true)
        lets := lets ++ [← wrap (← fpushS (.let_ (.var x) v))]
      return ← resolveStmtsF ctx bound (lets ++ rest)
    let (s, names) ← resolveStmtF ctx bound s
    pure (s :: (← resolveStmtsF ctx (names ++ bound) rest))

end

/-- The name a trait's function has in the whole program: the module's,
or where another trait of the module has a function of the name, the
trait's own (`sharedMethodName`). -/
def methodName (ctx : Ctx) (trait m : String) : String :=
  let own := ctx.scope.filter fun b =>
    b.name == m && b.entry.home == ctx.here && b.entry.kind == .method && b.rank == 0
  match own.find? fun b => b.entry.global.endsWith (sharedMethodName (lastSegment trait) m) with
  | some b => b.entry.global
  | none => match own.head? with
    | some b => b.entry.global
    | none => mangle ctx.here m

/-- The name in the whole program of what this module declares as `name`. -/
def ownName (ctx : Ctx) (space : Space) (name : String) : String :=
  match ctx.scope.find? fun b =>
      b.name == name && b.entry.home == ctx.here && b.entry.kind.space == space && b.rank == 0 with
  | some b => b.entry.global
  | none => mangle ctx.here name

/-- An item that has no code with its names resolved: none for what only this
pass reads. (Items with code are `resolveItemF`'s.) -/
def resolveItem (ctx : Ctx) : Item → R (List Item)
  | .import _ _ _ => pure []
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
  | .unsafeFn name => pure [.unsafeFn (ownName ctx .value name)]
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
      -- (With the type parameters of its own, if it has some.)
      let (r, own) := methodGenerics r
      let known := "Self" :: extra ++ own
      pure (methodName ctx name m, ← ps.mapM (resolveType ctx known),
        withMethodGenerics (← r.mapM (resolveType ctx known)) own)
    pure [.trait (ownName ctx .trait name) methods]
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
    let ofType := (← unitOf ctx.here).bind fun u => u.items.findSome? fun item =>
      let item := match item with
        | .pub _ i => i
        | i => i
      match item with
      | .struct name ps _ => if name == fn then some (ps, Space.type) else none
      | .enum name ps _ => if name == fn then some (ps, Space.type) else none
      | .effect name ps _ => if name == fn then some (ps, Space.effect) else none
      | _ => none
    let generics := match (← unitOf ctx.here).bind fun u => u.items.findSome? fun
        | .fn name ps _ _ _ => if name == fn then some ps else none
        | .pub _ (.fn name ps _ _ _) => if name == fn then some ps else none
        | _ => none with
      | some ps => genericParams ps
      | none => genericParams ((ofType.map (·.1)).getD [])
    let bounds ← bounds.mapM fun b => do
      let sealed_ := ["Fn", "RunsIn", "Environment", "Use", "Label", "Returns"].contains b.trait || b.trait.startsWith "'"
      let trait ← if sealed_ then pure b.trait else (·.1) <$> resolveNamed ctx .trait [] b.trait
      let args ← b.args.mapM (resolveType ctx generics)
      let assoc ← b.assoc.mapM fun (name, t) => do pure (name, ← resolveType ctx generics t)
      pure { b with trait, args, assoc }
    -- (written of a type: under the type's name)
    pure [.bounds (ownName ctx ((ofType.map (·.2)).getD .value) fn) bounds]
  | .fieldNames ctor names pubs => pure [.fieldNames (ownName ctx .value ctor) names pubs]
  | .typeAlias name ps body => do
    pure [.typeAlias (ownName ctx .type name) ps (← resolveType ctx (genericParams ps) body)]
  | item => pure [item]

/-- A function with its names resolved, under the name it has in the
program, its body flat. -/
def resolveFnF (ctx : Ctx) (global : String) (generics : List String) (name : String) (ps : List String)
    (annots : List (Option TypeExpr)) (ret : Option TypeExpr) (body : Flat.Body) : R Syntax.Item := do
  let generics := genericParams ps ++ generics
  let ctx := { ctx with generics }
  let annots ← annots.mapM fun a => a.mapM (resolveType ctx generics)
  let ret ← ret.mapM (resolveType ctx generics)
  let run := (do
    let roots ← Flat.byReference (refNamesOfF ctx) (← nestedRefsF body.roots)
    roots.mapM (resolveClauseF ctx []) : RF (Array Flat.ClauseId))
  match (run.run body).run (← get) with
  | .ok ((roots, body), st) =>
    set st
    modify fun s => { s with homes := (global, key ctx.here) :: s.homes }
    pure (.fn global ps annots ret { body with roots })
  | .error e => throw (inFunction name e)

/-- An item with its names resolved, its bodies flat: none for what only this
pass reads. What has no code is resolved as it is (`resolveItem`). -/
partial def resolveItemF (ctx : Ctx) : Syntax.Item → R (List Syntax.Item)
  | .pub _ item => resolveItemF ctx item
  | .module _ _ => pure []
  | .fn name ps annots ret b => do
    pure [← resolveFnF ctx (ownName ctx .value name) [] name ps annots ret b]
  | .alias name b value => do
    let (value, b) ← (resolveExprF ctx [] value).run b
    pure [.alias (ownName ctx .value name) b value]
  | .traitInfo name supers defaults params assocs => do
    let supers ← supers.mapM fun s => (·.1) <$> resolveNamed ctx .trait [] s
    let generics := "Self" :: genericParams params ++ assocs
    let defaults ← defaults.mapM fun
      | .fn m ps annots ret b =>
        resolveFnF ctx (methodName ctx name m) generics m ps annots ret b
      -- (What a type parameter is where it is not written, or a type left
      -- to implementations: its names resolved, `Self` and the parameters
      -- before it as they are.)
      | .typeAlias n aps body =>
        if n.startsWith "%traitDefault" then do pure (.typeAlias n aps (← resolveType ctx (generics ++ aps) body))
        else pure (.typeAlias n aps body)
      | item => pure item
    pure [.traitInfo (ownName ctx .trait name) supers defaults params assocs]
  | .impl ps tr head args context methods => do
    let (tr', trEntry) ← resolveNamed ctx .trait [] tr.base
    let (head', headEntry) ← resolveNamed ctx .type [] head
    -- An implementation is written beside the trait or beside the type, so
    -- that there is one place to look for it and no two can disagree.
    let foreign := fun (e : Option Entry) => match e with
      | some e => e.home != ctx.here
      | none => true
    if foreign trEntry && foreign headEntry && (trEntry.isSome || headEntry.isSome) then
      let homes := (trEntry.toList ++ headEntry.toList).filter (·.home != preludePath)
      unless homes.isEmpty do
        throw s!"`impl {tr.shown} for {head}` is written in {showPath ctx.here}: an implementation is written in the module of its trait or of its type"
    let context ← context.mapM fun (c : Cond) => do
      let named := (← resolveNamed ctx .trait [] c.trait.base).1
      let c ← c.mapTypesM (resolveType ctx (genericParams ps))
      pure { c with trait := .at named c.trait.nth c.trait.written }
    let generics := "Self" :: genericParams ps
    let methods ← methods.mapM fun
      | .fn m mps annots ret b => do
        -- A function of the trait has the name the trait gave it.
        let units := (← get).units
        let member : Option Bound := match trEntry with
          | some t => (units.find? fun (u : Module) => u.path == t.home).bind fun u =>
              let named := u.own.filter fun (b : Bound) => b.name == m && b.entry.kind == Kind.method
              -- (The trait's own, where another of its module has one of the name.)
              (named.find? fun b => b.entry.global.endsWith (sharedMethodName (lastSegment t.global) m)) <|> named.head?
          | none => none
        let m' := (member.map (·.entry.global)).getD m
        let item ← resolveFnF ctx m' generics m mps annots ret b
        modify fun s => { s with homes := (implFnName tr' head' m', key ctx.here) :: s.homes }
        pure item
      -- A type the implementation says: an argument of its trait, or a type
      -- the trait leaves to it.
      | (.typeAlias name aps body) => do
        pure ((.typeAlias name aps (← resolveType ctx (genericParams ps) body)))
      | item => pure item
    let written ← tr.written.mapM (resolveType ctx (genericParams ps))
    pure [.impl ps (.at tr' tr.nth written) head' args context methods]
  | item => resolveItem ctx item

/-- The modules of a program, each with its items: `root` is the first, and a
module written inside another is taken out of it. -/
partial def gatherF (path : List String) (items : List Syntax.Item) :
    Except String (List (List String × List Syntax.Item)) := do
  let mut out : List (List String × List Syntax.Item) := [(path, items)]
  for item in items do
    let inner := match item with
      | .pub _ i => i
      | i => i
    match inner with
    | .module name (some body) =>
      if name == "crate" || name == "self" || name == "super" then
        throw s!"a module cannot be named `{name}`"
      let more ← gatherF (path ++ [name]) body
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

/-- What resolving a module's items added to what is known of the program,
besides them: kept with them (`UnitsKept`). -/
structure UnitMade where
  edges : List (List String × List String)
  homes : List (String × String)
  coerced : List (List String × String)
  dotAlts : List (Nat × List String)
  fresh : Nat
  made : Nat

/-- Each module's items as resolution made them, with what it added, under
a key of what they were made from (`resolve`): kept by one compile for the
next. -/
abbrev UnitsKept := Std.HashMap UInt64 (List Syntax.Item × UnitMade)

/-- What the checker is told of the modules of a program. -/
structure Resolved where
  items : List Syntax.Item
  info : ModuleInfo
  /-- Each module's items resolved, under its key, where `resolve` was given
  modules to keep. -/
  unitsMade : List (UInt64 × List Syntax.Item × UnitMade) := []

/-- A program of modules as one list of items, each name meaning one thing:
see above. `prelude` is a module every other can name without `use`. -/
def resolve (prelude root : List Syntax.Item) (kept : Option UnitsKept := none) : Except String Resolved := do
  let mods ← gatherF [] root
  -- The library's modules come straight after the prelude's, whatever the
  -- program is: what is checked first is then the same for every program.
  let library := fun (m : List String × List Syntax.Item) =>
    m.1.head? == some "std" || m.1.head? == some "core" || m.1.head? == some "alloc"
  let mods := (← gatherF preludePath prelude) ++ mods.filter library ++ mods.filter (!library ·)
  let mut units : List Module := []
  let mut fields : List (String × List String × List String × List Bool) := []
  let taken := (declared [] (root.map Syntax.Item.declared)).1.map (·.name)
  let mods := mods.map fun (path, items) => (path, qualifyShared items)
  for (path, fitems) in mods do
    let items := fitems.map Syntax.Item.declared
    let (own, fs) := declared path items taken
    -- A constructor has one name in its module: a `struct` is its own, and
    -- an `enum`'s are written without the type's name.
    let ctors := (own.filter (·.entry.kind == .ctor)).map (·.name)
    if let some twice := ctors.find? fun c => (ctors.filter (· == c)).length > 1 then
      throw s!"`{twice}` is the name of two constructors in one module (a `struct` is the constructor of its own name, and those of an `enum` are named as they are written): give one of them another name"
    units := units ++ [⟨path, items, own⟩]
    fields := fields ++ fs
  let hidden := mods.flatMap fun (path, items) =>
    items.filterMap fun
      | .module name _ => some (path ++ [name])
      | _ => none
  -- (A module's items are resolved from what every module declares, and
  -- their own: with both as they were, and the counters where they were,
  -- what an earlier compile made of them is taken.)
  let declaredKey := hash (units.map fun u => (u.path, u.items))
  let run : R (List Syntax.Item × List (String × List String) × List (UInt64 × List Syntax.Item × UnitMade)) := do
    let mut out : Array Syntax.Item := #[]
    let mut unitsMade : List (UInt64 × List Syntax.Item × UnitMade) := []
    for (u, (_, fitems)) in units.zip mods do
      let scope ← scopeOf u.path
      let ctx : Ctx := { here := u.path, scope := scope, named := byName scope, ctorsByLast := ctorsByLastName scope }
      unless u.path.head? == preludePath.head? do out := out.push ((.fieldNames unitMark [key u.path] []))
      let before ← get
      let unitKey := mixHash declaredKey (hash (u.path, fitems, before.fresh, before.made))
      match kept.bind (·[unitKey]?) with
      | some (items, m) =>
        modify fun s => { s with edges := m.edges ++ s.edges, homes := m.homes ++ s.homes,
                                 coerced := s.coerced ++ m.coerced, dotAlts := m.dotAlts ++ s.dotAlts,
                                 fresh := m.fresh, made := m.made }
        out := out ++ items.toArray
        unitsMade := (unitKey, items, m) :: unitsMade
      | none =>
        let start := out.size
        for item in fitems do
          out := out ++ (← resolveItemF ctx item).toArray
        if kept.isSome then
          let after ← get
          let grown := fun {α : Type} (now was : List α) => now.take (now.length - was.length)
          let m : UnitMade :=
            { edges := grown after.edges before.edges, homes := grown after.homes before.homes,
              coerced := after.coerced.drop before.coerced.length, dotAlts := grown after.dotAlts before.dotAlts,
              fresh := after.fresh, made := after.made }
          unitsMade := (unitKey, (out.extract start out.size).toList, m) :: unitsMade
    -- Where each coercion applies: in the module that declares it, in one
    -- that brings its function in with `use`, and in one that brings in
    -- anything of a library module that declares one: `&Vec<T>` is a
    -- `&[T]` wherever `Vec` is, as Rust's deref is.
    let coerced := (← get).coerced
    let mut applies : List (String × List String) := []
    for u in units do
      let scope ← scopeOf u.path
      let here := coerced.filterMap fun (home, g) =>
        let library := match home.head? with
          | some r => r == "std" || r == "core" || r == "alloc"
          | none => false
        let within := "::".intercalate home ++ "::"
        if home == u.path || home == preludePath
            || scope.any (fun b => b.rank ≤ 1 && b.entry.global == g && b.entry.kind == .fn)
            || (library && scope.any (fun b => b.rank ≤ 1 && b.entry.global.startsWith within))
        then some g else none
      applies := applies ++ [(key u.path, here)]
    pure (out.toList, applies, unitsMade)
  let bare := root.any fun
    | (.fieldNames mark _ _) => mark == attrMark "no_std" || mark == attrMark "no_implicit_prelude"
    | _ => false
  -- (For dot calls: see `St.typeFns`.)
  let typeFns := units.foldl (init := {}) fun (m : Std.HashMap String (Array (List String × Bound × String))) u =>
    u.own.foldl (init := m) fun m b => match b.name.splitOn "::" with
      | [ty, fn] => m.insert fn ((m.getD fn #[]).push (u.path, b, ty))
      | _ => m
  let typesOf := units.foldl (init := {}) fun (m : Std.HashMap (List String) (Std.HashSet String)) u =>
    m.insert u.path (u.own.foldl (init := m.getD u.path {}) fun s b =>
      if b.entry.kind == .type then s.insert b.name else s)
  let fieldsNamed := units.foldl (init := {}) fun (m : Std.HashMap String (Array (List String × Bool))) u =>
    u.items.foldl (init := m) fun m item =>
      match (match item with
        | .pub _ inner => inner
        | other => other) with
      | .fieldNames _ names pubs => (names.zip pubs).foldl (init := m) fun m (n, p) =>
        m.insert n ((m.getD n #[]).push (u.path, p))
      | _ => m
  let ((items, coercions, unitsMade), st) ← match run.run { units, fields, hidden, bare, typeFns, typesOf, fieldsNamed } with
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
  let text := match ctor Syntax.textEndName, ctor Syntax.textCharName with
    | some e, some c => some (e, c)
    | _, _ => none
  let preludeNames := (declared preludePath (prelude.map Syntax.Item.declared)).1.map (·.name)
  let mine := units.filter (·.path != preludePath)
  let pubFns := mine.flatMap fun u => u.own.filterMap fun b =>
    if b.entry.kind == .fn && !(b.entry.vis matches .priv) then some b.entry.global else none
  let privTypes := mine.flatMap fun u => u.own.filterMap fun b =>
    if b.entry.kind == .type && (b.entry.vis matches .priv) then some (b.entry.global, key u.path) else none
  let unitUses := (units.filter (·.path.head? != preludePath.head?)).map fun u =>
    (key u.path, ((st.edges.filter (·.1 == u.path)).map fun (_, t) => key t).eraseDups)
  pure ⟨items, ⟨st.homes, fieldVis, text, preludeNames.any taken.contains, pubFns, privTypes, coercions,
    st.dotAlts, unitUses⟩, unitsMade⟩

end Glorious.Syntax.Modules
