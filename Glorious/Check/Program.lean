module

public import Glorious.Check.Group
public import Glorious.Check.Merge

public section

namespace Glorious.Check

open Syntax

/-- What one check keeps for the next of a program that changed a little: the
checker's state after the declarations and after each group of functions,
each under a key of everything it was made from, in order. -/
abbrev Kept := List (UInt64 × St)

/-- An item as its declarations have it: its functions without their bodies. -/
partial def withoutBodies : Item → Item
  | .fn name params annots ret _ => .fn name params annots ret []
  | .impl params tr head args ctx methods => .impl params tr head args ctx (methods.map withoutBodies)
  | .pub parent item => .pub parent (withoutBodies item)
  | other => other

/-- A group of functions, as what its check is made from. -/
def groupKey (key : UInt64) (group : List FnDecl) : UInt64 :=
  group.foldl (fun h d => mixHash h (hash (d.name, d.params, d.annots, d.ret, d.clauses, d.bounds))) key

/-- A state kept from an earlier check, with the functions of the
implementations declared after the first `before` replaced by `written`
(each implementation's trait and functions, in the order written), where
those line up: none where they do not. -/
def withImplBodies (st : St) (before : Nat) (written : List (String × List Item)) : Option St :=
  let given := st.impls.toList.drop before
  if written.length ≤ given.length && (written.zip given).all (fun (w, im) => w.1 == im.trait) then
    let replaced : List ImplDecl := given.zipIdx.map fun (im, k) =>
      match written[k]? with
      | some w => { im with methods := w.2 }
      | none => im
    some { st with impls := ((st.impls.toList.take before) ++ replaced).toArray }
  else none

/-- Take a state kept from an earlier compile as this one's, but for what is
this program's: what the resolver said of its modules (the dot calls'
alternatives and the rest), and whether its own items are checked. -/
def adopt (st : St) : M Unit := do
  let now ← get
  set { st with modules := now.modules, ownItems := now.ownItems }

/-- Does an implementation leave a type to be found from its functions,
`type Out = _;`? (What it says is then a variable of none of its own.) -/
def implHoled (im : ImplDecl) : Bool :=
  im.assocs.any fun (_, t) => match t with
    | .var id => !im.pvars.any (·.2 == id)
    | _ => false

/-- The functions an implementation gives, as functions to check. -/
def implFnDecls (im : ImplDecl) : M (List FnDecl) := do
  let mut out : List FnDecl := []
  for item in im.methods do
    if let .fn m written annots ret clauses := item then
      if let some sig := (← get).methods.lookup m then
        -- (Its type parameters: the head's arguments, and then those that
        -- are only inside one, or among the trait's own; and the lifetimes
        -- it writes of its own, `fn at<'a>(..)`.)
        let inner := (im.pvars.map (·.1)).filter (!im.params.contains ·)
        let lifetimes := (genericParams written).filter isLifetime
        out := out ++ [{ name := Syntax.implFnName im.trait im.head m,
                         params := im.params ++ inner ++ sig.mparams.map (·.1) ++ lifetimes, annots,
                         ret, clauses, impl := some (im, sig) }]
  pure out

/-- Check items. With `kept` from an earlier check of a program that began
alike (`seed`: what was checked before them), the state after each step whose
key is among them is taken from there instead of checked again: the
declarations' key is of every item without the bodies of its functions, each
group's is of the key before it and the group's functions whole. A step
depends on no more than that: a group follows calls only into groups before
it. What the functions of later groups are is put back as this program has
them. Gives what this check kept, the state after all of it first, under a
key of every item whole: where that is kept, nothing else is looked at, and
nothing else is kept. -/
def checkItems (items : List Item) (seed : UInt64 := 0) (kept : Kept := []) : M Kept := do
  let written := items.filterMap fun
    | .bounds fn bounds => some (fn, bounds)
    | _ => none
  let decls : List FnDecl := items.filterMap fun
    | .fn name params annots ret clauses =>
      some { name, params, annots, ret, clauses, bounds := (written.lookup name).getD [] }
    | _ => none
  -- What is asked of a declared type's parameters: a trait without arguments
  -- of its own, of the parameter at a place.
  let asked := items.filterMap fun
    | .struct name params _ => (written.lookup name).map (name, params, ·)
    | .enum name params _ => (written.lookup name).map (name, params, ·)
    | .effect name params _ => (written.lookup name).map (name, params, ·)
    | _ => none
  modify fun s =>
    { s with typeBounds := s.typeBounds ++ asked.map fun (name, params, bounds) =>
        (name, bounds.filterMap fun b =>
          if b.trait.startsWith "'" || !b.args.isEmpty then none
          else (params.idxOf? b.subject).map (b.trait, ·)) }
  let names := decls.map (·.name)
  -- (A name that stands for an expression, a constant's, mentions what that
  -- does: the function that works the constant out.)
  let aliasOf := items.filterMap fun
    | .alias name value => some (name, Elab.fvExpr [] value)
    | .pub _ (.alias name value) => some (name, Elab.fvExpr [] value)
    | _ => none
  let mentions := fun (name : String) =>
    match decls.find? (·.name == name) with
    | some d =>
      let fvs := d.clauses.flatMap (Elab.fvClause [])
      ((fvs ++ fvs.flatMap fun x => (aliasOf.lookup x).getD []).filter names.contains).eraseDups
    | none => []
  let coercing := items.filterMap fun
    | .coerce name => some name
    | _ => none
  for c in coercing do
    unless names.contains c do throw s!"`coerce {c}`: there is no function `{c}`"
  -- A coercion can be applied in any function, so the coercions are checked
  -- before all the others: all, that is, but the functions the coercions are
  -- themselves built from, in which none is applied.
  let builtFrom := Id.run do
    let mut seen := coercing
    for _ in [0:names.length] do
      seen := (seen ++ seen.flatMap mentions).eraseDups
    pure seen
  let deps := fun (name : String) =>
    if builtFrom.contains name then mentions name else (mentions name ++ coercing).eraseDups
  do
    -- (The unit whole, as an earlier compile left it: every step taken from
    -- there at once. A unit that is the same keeps only this.)
    let whole := mixHash seed (hash items)
    if let some st := kept.lookup whole then
      adopt st
      return [(whole, st)]
    let before := (← get).impls.size
    let mut made : Kept := []
    let mut key := mixHash seed (hash (items.map withoutBodies))
    -- (A state kept from before has the implementations that program
    -- declared, each with its functions whole; the declarations do not
    -- depend on the bodies, so the ones put in their place are this
    -- program's, in the order its implementations are written. Where they
    -- do not line up, nothing kept is taken.)
    let written : List (String × List Item) := items.filterMap fun
      | .impl _ tr _ _ _ methods => some (tr, methods)
      | _ => none
    let ours := fun (st : St) => withImplBodies st before written
    let look := fun (k : UInt64) => (kept.lookup k).bind ours
    match look key with
    | some st => adopt st
    | none =>
      declare items
      computeVariances
      declareTraits items
      checkUseDecls
    made := (key, ← get) :: made
    modify fun s =>
      { s with fnBodies := s.fnBodies ++ (decls.map fun d => (d.name, d.clauses)),
               runFns := decls.foldl (fun m d => m.insertIfNew d.name d.clauses) s.runFns }
    -- (A state kept from before has the bodies that program's later
    -- functions had: this one's are put in their place.)
    let restore := fun (st : St) (later : List FnDecl) => (do
      adopt st
      modify fun s =>
        { s with fnBodies := s.fnBodies.map fun (name, clauses) =>
                   match later.find? (·.name == name) with
                   | some d => (name, d.clauses)
                   | none => (name, clauses),
                 runFns := later.foldl (fun m d => m.insert d.name d.clauses) s.runFns } : M Unit)
    -- The functions of implementations that leave a type to be found from
    -- them (`type Out = _;`): checked before every function that may use
    -- what they find, but those they are themselves made from.
    let holed ← ((← get).impls.toList.drop before).filter implHoled |>.flatMapM implFnDecls
    let holeNames := holed.map (·.name)
    let allDecls := decls ++ holed
    let allNames := names ++ holeNames
    let mentionsAll := fun (name : String) =>
      match allDecls.find? (·.name == name) with
      | some d => ((d.clauses.flatMap (Elab.fvClause [])).filter allNames.contains).eraseDups
      | none => []
    let madeFrom := Id.run do
      let mut seen := holeNames
      for _ in [0:allNames.length] do
        seen := (seen ++ seen.flatMap mentionsAll).eraseDups
      pure seen
    let deps := fun (name : String) =>
      if holeNames.contains name then mentionsAll name
      else if madeFrom.contains name then deps name
      else (deps name ++ holeNames).eraseDups
    let groups := (components allNames deps).map fun comp => comp.filterMap fun n => allDecls.find? (·.name == n)
    for (group, k) in groups.zipIdx do
      key := groupKey key group
      match look key with
      | some st => restore st ((groups.drop (k + 1)).flatten)
      | none => checkGroup group
      made := (key, ← get) :: made
    -- The functions implementations give, each on its own: any function may
    -- call them, but only through a trait, whose types are declared.
    -- (Those of one that leaves a type to be found were checked with the
    -- rest, before what may use it.)
    for im in (← get).impls.toList.drop before do
      unless implHoled im do
        for d in ← implFnDecls im do
          key := groupKey key [d]
          match look key with
          | some st => restore st []
          | none => checkGroup [d]
          made := (key, ← get) :: made
    for c in coercing do
      unless (((← get).fnBounds.lookup c).getD 0) == 0 do
        throw s!"`coerce {c}`: a coercion cannot need a trait of a type it is used at"
    checkDups (← get).lateDups
    checkDrops (← get).lateDrops
    checkStays (← get).lateStays
    modify fun s => { s with lateDups := #[], lateDrops := #[], lateStays := #[] }
    pure ((whole, ← get) :: made)

/-- The declared types a type is made of. -/
partial def namedIn : Ty → List String
  | .var _ => []
  | .con name args => name :: args.flatMap namedIn
  | .tuple args => args.flatMap namedIn
  | .fn params ret effs _ _ =>
    params.flatMap namedIn ++ namedIn ret ++ effs.flatMap fun (_, args) => args.flatMap namedIn
  | .ref _ t _ => namedIn t

/-- What the checker tells the elaborator, once every item is checked. -/
def finish : M Elab.Blocks := do
  do
    -- One who calls a `pub` function has to be able to write its type.
    let info := (← get).modules
    for f in info.pubFns do
      if let some scheme := (← get).fns.lookup f then
        let t ← zonk (← instantiate scheme)
        for n in namedIn t do
          -- (A type's own function is named through the type: where the
          -- type cannot be written, neither can the function, `pub` or not.)
          if f.startsWith (n ++ "::") then continue
          if let some home := info.privTypes.lookup n then
            if info.homes.lookup f == some home then
              throw s!"`{Syntax.lastSegment f}` is `pub`, but its type, `{showTy t}`, has `{Syntax.lastSegment n}` in it, which is private to its module: one who calls `{Syntax.lastSegment f}` could not write that type (`pub struct` with fields that are not `pub` keeps what is inside private)"
    unless (((← get).fnBounds.lookup "main").getD 0) == 0 do
      throw "`main` needs a trait of a type that nothing decides"
    match (← get).fns.lookup "main" with
    | none => pure ()
    | some scheme =>
      match ← zonk (← instantiate scheme) with
      | .fn ps r effs _ _ =>
        unless ps.isEmpty do throw "`main` takes no arguments"
        unless effs.isEmpty do
          throw s!"`main` performs effects that nothing handles: {showEffs effs}"
        -- Nothing uses what the program gives.
        modify fun s => { s with pos := "", drops := #[] }
        mustDrop r "the result of `main` is let go when the program ends"
        checkDrops (← get).drops
      | _ => pure ()
    let s ← get
    let mut links : List (Nat × Nat) := []
    for (id, cap) in s.unrun do
      let root ← findCap cap
      let mut owners : List Nat := []
      for (owner, c) in s.blockCaps do
        if owner != id && owner != 0 && (← findCap c) == root && !owners.contains owner then
          owners := owner :: owners
      if let [owner] := owners then links := (id, owner) :: links
    -- A block taken to be given one particular block, where in the end it
    -- may be given another, lets go of whatever it is given.
    let mut unlinked : Array (Ty × String) := #[]
    for (id, owner, input, why) in s.assumedLinks do
      unless links.contains (id, owner) do unlinked := unlinked.push (input, why)
    -- (What such a block lets go of, nothing destroys.)
    checkDrops unlinked (callables := true)
    let implEs := s.impls.toList.map fun im =>
      let names := (s.traits.lookup (Syntax.traitBase im.trait)).getD []
      (⟨im.dictFn, im.context.length + im.extra.length, names.map fun m =>
        (Syntax.implFnName im.trait im.head m,
          if im.trait == Syntax.destroyTrait then 1
          else ((s.methods.lookup m).map (·.params.length)).getD 0)⟩ :
        Elab.ImplE)
    -- How each type is destroyed, for the elaborator to write the function:
    -- its own `Drop` first, if it has one, and then for each constructor
    -- which fields are destroyed, each by how its type is.
    let mut destroys : List Elab.Destroy := []
    for im in s.impls do
      if im.trait == Syntax.destroyTrait then
        let givens : Traits.Givens := im.context
        let place := fun (j : Nat) => (im.context.idxOf? (Syntax.destroyTrait, j)).map Elab.DictE.param
        let arity := im.params.length
        let hook := if s.kimpls.any fun I => I.trait == "Drop" && I.head == im.head then
            (Traits.solve s.kimpls givens 1000 "Drop"
              (.con im.head ((List.range arity).map Traits.STy.var))).map (toDictE s.impls)
          else none
        let mut ctors : List (String × List (Option Elab.DictE)) := []
        let isArray := some im.head == s.arrayType
        if isArray then ctors := [("%each", [place 0])]
        else if im.head.startsWith "(tuple" then
          ctors := [("", (List.range arity).map place)]
        else if let some decl := s.types.lookup im.head then
          for c in decl.ctors do
            if let some sig := s.ctors.lookup c then
              -- A field's type, as the solver knows types: a parameter of
              -- the type by its place among them.
              let places := (List.range arity).filter fun j => sig.kinds[j]? != some true
              let sty := fieldSTy sig.tvars places
              let mut parts : List (Option Elab.DictE) := []
              for f in sig.fields do
                let plain := (freeTys f).isEmpty && !(← needsDestroying [] f)
                parts := parts ++ [if plain then none
                  else (Traits.solve s.kimpls givens 1000 Syntax.destroyTrait (sty f)).map (toDictE s.impls)]
              ctors := ctors ++ [(c, parts)]
        destroys := destroys ++ [⟨im.head, im.context.length, hook, isArray, ctors⟩]
    pure ⟨s.given.toList, links ++ s.envLinks.toList, s.coercions.toList,
      ⟨s.dictTable.toList, s.methodCalls.toList, s.fnBounds, implEs, s.dropSites.toList, destroys⟩,
      s.fieldTable.toList, s.fieldReads.toList, s.packs.toList, s.envFns, s.envWraps.toList,
      s.derefReads.toList, s.siteTable, s.siteTypes, s.dotChosen, s.argsChosen⟩

/-- Check a whole program. Gives what the elaborator needs to know about its
blocks: which take an argument they do not name, and for each that is handed a
block which was not run, the identity of that block if it can only be one. The
elaborator then lets those two share what they capture. -/
def checkProgram (items : List Item) (modules : Syntax.ModuleInfo := {}) (drops : Bool := false) :
    Except String Elab.Blocks := do
  let action : M Elab.Blocks := do
    modify fun s => { s with modules }
    let _ ← checkItems items
    finish
  let (blocks, _) ← action.run { dropMode := drops }
  pure blocks

/-- What is known once some items are checked: for a program that is checked
after them, against what they declare. -/
def checkFirst (items : List Item) (modules : Syntax.ModuleInfo := {}) (drops : Bool := false) :
    Except String St := do
  let action : M Unit := do
    modify fun s => { s with modules }
    let _ ← checkItems items
  let (_, st) ← action.run { dropMode := drops }
  pure st

/-- Check a program whose first items are already checked. -/
def checkAfter (first : St) (items : List Item) (modules : Syntax.ModuleInfo := {}) :
    Except String Elab.Blocks := do
  let action : M Elab.Blocks := do
    modify fun s => { s with modules, ownItems := true }
    let _ ← checkItems items
    finish
  let (blocks, _) ← action.run first
  pure blocks


/-- How far apart the ids of units checked side by side start. -/
def unitGap : Nat := 1 <<< 20

/-- The state each unit of a level is checked from, its ids numbered from a
place of its own: the `j`-th from `j` gaps on. -/
def jumpedFor (s : St) (j : Nat) : St :=
  if j == 0 then s else
  let at_ := fun (n : Nat) => n + j * unitGap
  { s with
    tys := s.tys.jumpTo (at_ s.tys.size), rows := s.rows.jumpTo (at_ s.rows.size)
    caps := s.caps.jumpTo (at_ s.caps.size), capOut := s.capOut.jumpTo (at_ s.caps.size)
    capEdges := s.capEdges.jumpTo (at_ s.capEdges.size)
    capEdgeNames := s.capEdgeNames.jumpTo (at_ s.capEdges.size)
    loans := s.loans.jumpTo (at_ s.loans.size), rigidKeys := s.rigidKeys.jumpTo (at_ s.rigidKeys.size)
    brands := at_ s.brands, dropAsked := at_ s.dropAsked }

/-- Did the `j`-th unit of a level stay below where the next one's ids start? -/
def stayedBelow (s from_ : St) (j : Nat) : Bool :=
  let below := fun (now start : Nat) => now ≤ start + (j + 1) * unitGap
  below s.tys.size from_.tys.size && below s.rows.size from_.rows.size
    && below s.caps.size from_.caps.size && below s.capEdges.size from_.capEdges.size
    && below s.loans.size from_.loans.size && below s.rigidKeys.size from_.rigidKeys.size
    && below s.brands from_.brands && below s.dropAsked from_.dropAsked

/-- Check a program's units, each a module, in the order given, which has a
module after those it uses (`deps`: for each, the units before it that it
uses): each unit's declarations and groups are checked after the units before
it, and keyed by what they and those were made from (and, with each unit,
what it reads of the program's modules besides its own items), so what an
earlier check kept of a unit is taken from there where neither it nor any
unit before it changed. Units that do not use each other, the next ones
whose units used are all checked, are checked side by side, each on a
thread of its own, and what each added is put together (`mergeStates`);
where it cannot be, or one of them is refused, they are checked one after
another, as all were. -/
def checkUnitsKept (first : St) (units : List (List Item × UInt64)) (modules : Syntax.ModuleInfo)
    (seed : UInt64) (kept : Kept) (own : Bool := true) (library : Nat := 0)
    (deps : List (List Nat) := []) : Except String (Elab.Blocks × Kept × Kept) := do
  -- (Each unit's level: one more than the highest of the units it uses.)
  let levelOf := units.length.fold (init := (#[] : Array Nat)) fun i _ acc =>
    acc.push (((deps[i]?).getD []).foldl (fun m d => max m ((acc[d]?).getD 0 + 1)) 0)
  let levels := (List.range ((levelOf.foldl max 0) + 1)).map fun l =>
    (units.zipIdx.filter fun (_, k) => levelOf[k]? == some l)
  -- (Side by side only where each unit says what it uses.)
  let levels := if deps.length == units.length then levels else units.zipIdx.map ([·])
  let action : M (Elab.Blocks × Kept × Kept) := do
    modify fun s => { s with modules, ownItems := own }
    let mut key := seed
    let mut made : Kept := []
    -- (What the first `library` units made: the library's modules, which
    -- every program that begins with them can take.)
    let mut shared : Kept := []
    for level in levels do
      -- Side by side: each from the state before the level, under keys of
      -- their own, its ids from a place of its own.
      if level.length > 1 then
        let start ← get
        let side := mixHash key (hash "side by side")
        -- (After the level, what follows is keyed by what the level's units
        -- are made of, whichever way they were checked.)
        let after := level.foldl (fun h ((u, info), _) => mixHash h (mixHash info (hash u))) key
        -- (The level as an earlier compile put it together, where it is the
        -- same: each unit kept whole is not what this start grew into, so
        -- what it added could not be told.)
        let whole := mixHash side after
        let allLibrary := level.all fun (_, k) => k < library
        if let some st := kept.lookup whole then
          adopt st
          made := (whole, st) :: made
          if allLibrary then shared := (whole, st) :: shared
          key := after
          continue
        let tasks := level.zipIdx.map fun (((u, info), k), j) =>
          (k, j, Task.spawn fun _ => Trace.timed s!"check unit {k} (side by side)" fun _ =>
            (checkItems u (mixHash side info) kept).run (jumpedFor start j))
        let mut together : Option St := none
        let mut mines : List (Nat × Kept) := []
        let mut ok := true
        for (k, j, t) in tasks do
          match t.get with
          | .ok (mine, after) =>
            if !stayedBelow after start j then ok := false
            together := match together with
              | none => some after
              | some acc => mergeStates start acc after
            if together.isNone then ok := false
            mines := mines ++ [(k, mine)]
          | .error _ => ok := false
        if ok then
          if let some st := together then
            set st
            for (k, mine) in mines do
              made := mine ++ made
              if k < library then shared := mine ++ shared
            made := (whole, st) :: made
            if allLibrary then shared := (whole, st) :: shared
            key := after
            continue
        let _ := Trace.timed "units side by side could not be put together" fun _ => ()
      -- One after another.
      let levelStart := key
      for ((u, info), k) in level do
        let before ← get
        let (mine, after) ← match Trace.timed s!"check unit {k}" fun _ =>
            (checkItems u (mixHash key info) kept).run before with
          | .ok r => pure r
          | .error e => throw e
        set after
        if let some (k, _) := mine.head? then key := k
        made := mine ++ made
        if k < library then shared := mine ++ shared
      if level.length > 1 then
        key := level.foldl (fun h ((u, info), _) => mixHash h (mixHash info (hash u))) levelStart
    pure (← finish, made, shared)
  let (r, _) ← action.run first
  pure r

/-- The same, taking what an earlier check of a program that began alike kept
(`seed`: what the first items were), and giving what this one keeps. -/
def checkAfterKept (first : St) (items : List Item) (modules : Syntax.ModuleInfo) (seed : UInt64)
    (kept : Kept) : Except String (Elab.Blocks × Kept) := do
  let action : M (Elab.Blocks × Kept) := do
    modify fun s => { s with modules, ownItems := true }
    let made ← checkItems items (mixHash seed (hash modules)) kept
    pure (← finish, made)
  let (r, _) ← action.run first
  pure r

end Glorious.Check
