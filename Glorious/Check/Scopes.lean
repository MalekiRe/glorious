module

public import Glorious.Check.Declare

public section

namespace Glorious.Check

open Syntax

/-! ## Coverage of pattern clauses -/

/-- A pattern with its names resolved. -/
inductive NPat where
  | any
  | int (n : Int)
  | ctor (name : String) (args : List NPat)
  | tuple (args : List NPat)

partial def normPat : Pattern → M NPat
  | .wild => pure .any
  -- (`..` of a tuple before how many parts it stands for is written: as the
  -- parts it stands for, which a clause's tuple is covered by alike.)
  | .marked .rest [.int _] => pure .any
  | .marked m _ => throw s!"`{m.shown}` in a pattern where it cannot be; this is a compiler defect"
  | .int n => pure (.int n)
  | .tuple ps => do
    pure (.tuple (← ps.mapM normPat))
  | .var x => do
    match ← resolveCtor x none with
    | some (name, _) => pure (.ctor name [])
    | none =>
      match (← get).aliases[x]? with
      | some e => do normPat (← match Syntax.exprToPat e with | .ok p => pure p | .error m => throw m)
      | none => pure .any
  | .ctor x q ps => do
    if let some (_, n) := Syntax.scalarPattern (.ctor x q ps) then return .int n
    -- What an `is` found, taken apart: its names, which nothing can fail.
    if (Syntax.packNames x).isSome then return .any
    -- (A `[T; N]` taken apart is a tuple of its `N` elements.)
    if (Syntax.fixedPatLen x).isSome then return .tuple (← ps.mapM normPat)
    match ← resolveCtor x q with
    | some (name, _) => do
      pure (.ctor name (← ps.mapM normPat))
    | none =>
      if (Syntax.restPatParts x).isSome then
        throw "an array pattern with `..` is a whole clause's pattern, `[first, ..rest] => ..`: it is not read inside another pattern, nor where a function's parameters are"
      throw s!"unknown constructor `{x}` in a pattern"

/-- A case the rows do not cover, as patterns written for the columns; none
where they cover every value of the column types. A type is split by
constructor only where some clause tests for one: a recursive type would
otherwise be unfolded for ever. -/
partial def uncovered (tys : List Ty) (rows : List (List NPat)) : M (Option (List String)) := do
  match tys with
  | [] => pure (if rows.isEmpty then some [] else none)
  | t :: rest =>
    let fallback : M (Option (List String)) := do
      match ← uncovered rest (rows.filterMap fun
          | .any :: tl => some tl
          | _ => none) with
      | some w => pure (some ("_" :: w))
      | none => pure none
    match ← find t with
    | .tuple ts =>
      match ← uncovered (ts ++ rest) (rows.filterMap fun
          | .tuple ps :: tl => some (ps ++ tl)
          | .any :: tl => some (List.replicate ts.length .any ++ tl)
          | _ => none) with
      | some w => pure (some (s!"({", ".intercalate (w.take ts.length)})" :: w.drop ts.length))
      | none => pure none
    | .con "Fixed" (elem :: _) =>
      -- (Taken apart as a tuple of its elements, `[a, b, c]`.)
      match rows.findSome? fun | .tuple ps :: _ => some ps.length | _ => none with
      | some n => uncovered (.tuple (List.replicate n elem) :: rest) rows
      | none => fallback
    | .con name args =>
      match (← get).types[name]? with
      | some decl =>
        let tested := rows.any fun
          | .ctor _ _ :: _ => true
          | _ => false
        if !tested then fallback
        else
          for c in decl.ctors do
            let some sig := (← get).ctors[c]? | return some ["_"]
            let fields := sig.fieldsAt args
            let found ← uncovered (fields ++ rest) (rows.filterMap fun
              | .ctor c' ps :: tl => if c' == c then some (ps ++ tl) else none
              | .any :: tl => some (List.replicate fields.length .any ++ tl)
              | _ => none)
            if let some w := found then
              let parts := w.take fields.length
              -- (A `Result` whose error is `()` is an `Option`, and one
              -- whose value is `()` too is a `Bool`: named so.)
              let unitArg := fun (k : Nat) => (do
                match args[k]? with
                | some a => match ← find a with
                  | .tuple [] => pure true
                  | _ => pure false
                | none => pure false : M Bool)
              let short := Syntax.lastSegment c
              let isResult := Syntax.lastSegment name == "Result"
              let shown ← if isResult && (← unitArg 1) then
                  if ← unitArg 0 then pure (if short == "Ok" then "true" else "false")
                  else pure (if short == "Ok" then s!"Some({", ".intercalate parts})" else "None")
                else pure (short ++ (if parts.isEmpty then "" else s!"({", ".intercalate parts})"))
              return some (shown :: w.drop fields.length)
          pure none
      | none => fallback
    | .ref _ inner _ => uncovered (inner :: rest) rows
    | _ => fallback

/-- The types of a value's fields other than one, where they are known: what
is let go when that one is taken. -/
def otherFields (t : Ty) (idx : Nat) : M (Option (List Ty)) := do
  match ← find t with
  | .tuple ts => pure (some ((ts.zipIdx.filter (·.2 != idx)).map (·.1)))
  | .con name args =>
    match (← get).ctors[name]? with
    | some sig => pure (some (((sig.fieldsAt args).zipIdx.filter (·.2 != idx)).map (·.1)))
    | none => pure none
  | _ => pure none

/-- The type of field `idx` of a value of type `t`, if `t` is known. -/
partial def fieldType (t : Ty) (idx : Nat) : M (Option Ty) := do
  match ← find t with
  | .var _ => pure none
  | .tuple ts =>
    match ts[idx]? with
    | some t => pure (some t)
    | none => throw s!"a tuple of {ts.length} values has no field {idx}"
  -- (A tuple's first and the rest, `(H, ..R)`: the first, or of the rest.)
  | .con name [h, rest] =>
    if name == Traits.consHead then
      match idx with
      | 0 => pure (some h)
      | k + 1 => fieldType rest k
    else fieldOfCtor name [h, rest]
  | .con name args => fieldOfCtor name args
  | t => throw s!"`.{idx}` reads a field, but `{showTy (← zonk t)}` has none"
where
  fieldOfCtor (name : String) (args : List Ty) : M (Option Ty) := do
    match (← get).ctors[name]? with
    | some sig =>
      -- A field that is not `pub` is its module's to read and to borrow.
      let s ← get
      if let some (home, pubs) := s.modules.fieldVis.lookup name then
        if pubs[idx]? == some false then
          if let some here := s.modules.homes.lookup s.owner then
            unless here == home do
              throw s!"this field of `{Syntax.lastSegment name}` is not `pub`: only the module that declares `{Syntax.lastSegment name}` can read or borrow it"
      match (sig.fieldsAt args)[idx]? with
      | some t => pure (some t)
      | none => throw s!"`{name}` has no field {idx}"
    | none => throw s!"`{bareName name}` has no fields to read with `.{idx}`"

/-- Which field of a value of type `t` a step is: its number, or the place of
its name among the fields of the type's one constructor. None if the type is
not known yet and the step is a number. -/
def fieldIndex (t : Ty) (step : String) : M (Option Nat) := do
  if let some n := step.toNat? then return some n
  match ← find t with
  | .con name _ =>
    let ctor := match (← get).types[name]? with
      | some decl => match decl.ctors with
        | [c] => some c
        | _ => none
      | none => none
    let declared := (← get).fieldNames
    match ctor.bind fun c => declared[c]? with
    | some names =>
      match names.idxOf? step with
      | some i => pure (some i)
      | none => throwThe Elab.Said { msg := s!"`{showTy (← zonk t)}` has no field `{step}`", subject := some name }
    | none => throwThe Elab.Said { msg := s!"`{showTy (← zonk t)}` has no field `{step}`: its fields have no names", subject := some name }
  | .var _ =>
    throw s!"the field `{step}` is read from a value whose type is not known here; annotate it"
  | t => throw s!"`{showTy (← zonk t)}` has no field `{step}`"

/-- What a field is read through: a reference to a reference is read
through both, the read noted so (`Syntax.derefTwice`). -/
def peelTwice (id : Nat) (t : Ty) : M Ty := do
  if let .ref _ inner _ ← find t then
    if let .ref .. ← find inner then
      modify fun s => { s with derefReads := s.derefReads.push (id + Syntax.derefTwice) }
      return inner
  return t

/-- Settle the field reads that were waiting for their subject's type. When
`final`, one that still cannot be settled is an error. -/
partial def runProjections (final : Bool) : M Unit := do
  -- Fields read by name first: which field a name is depends on the type.
  let named := (← get).namedReads
  modify fun s => { s with namedReads := #[] }
  let mut unnamed : Array (Ty × String × Ty × Nat × String) := #[]
  for (subject, name, result, id, pos) in named do
    let subject ← peelTwice id subject
    let unknown := match ← find subject with
      | .var _ => true
      | _ => false
    -- (A reference, known only now: what is read through one is settled
    -- where it is read, with the reference's type known there. If the
    -- callable was first read with it known and something else was wrong,
    -- that is what is wrong.)
    -- (A reference, known only now: what it is to has the field, read
    -- through it, which copies it, as where it is known at once.)
    if let .ref _ inner _ ← find subject then
      if let .con .. ← find inner then
        if let some idx ← (try fieldIndex inner name catch e => throw (pos ++ e)) then
          if let some t ← (try fieldType inner idx catch e => throw (pos ++ e)) then
            try unifyAt s!"the field `{name}`" result t
            catch e => throw (pos ++ e)
            modify fun s => { s with fieldReads := s.fieldReads.push (id, idx), derefReads := s.derefReads.push id,
                                     dups := s.dups.push (t, pos ++ "reading through a reference copies the value (`replace` takes it out instead)") }
            continue
      -- (What it is to not known yet, as what a trait leaves to an
      -- implementation is until the implementation is found, `a[i].f`:
      -- settled later.)
      if !final then
        if let .var _ ← find inner then
          unnamed := unnamed.push (subject, name, result, id, pos)
          continue
      match (← get).firstSaid with
      | some said => throwThe Elab.Said said
      | none => throw s!"{pos}the field `{name}` is read through a reference, and where it is read the type of what it is read from is not known: say what that is"
    let found ← if unknown then pure none else
      match ← (try fieldIndex subject name catch e => throw (pos ++ e)) with
      | some idx => do
        match ← fieldType subject idx with
        | some t => pure (some (idx, t))
        | none => pure none
      | none => pure none
    match found with
    | some (idx, t) =>
      try unifyAt s!"the field `{name}`" result t
      catch e => throw (pos ++ e)
      modify fun s => { s with fieldReads := s.fieldReads.push (id, idx) }
    | none => unnamed := unnamed.push (subject, name, result, id, pos)
  if final then
    if let some (_, name, _, _, pos) := unnamed[0]? then
      throw s!"{pos}the field `{name}` is read from a value whose type is not known here; annotate it"
  modify fun s => { s with namedReads := unnamed ++ s.namedReads }
  let waiting := (← get).projections
  modify fun s => { s with projections := #[] }
  let mut left : Array (Ty × Nat × Ty × String × Nat) := #[]
  for (subject, idx, result, pos, id) in waiting do
    -- (Of what turns out to be a reference, read where it has a node: what
    -- it is to has the field, read through it, which copies it.)
    let subject ← if id != 0 then peelTwice id subject else pure subject
    let (subject, through) ← match ← find subject with
      | .ref _ inner _ => pure (if id != 0 then (inner, true) else (subject, false))
      | _ => pure (subject, false)
    match ← (try fieldType subject idx catch e => throw (pos ++ e)) with
    | some t =>
      try unifyAt s!"the field `.{idx}`" result t
      catch e => throw (pos ++ e)
      if through then
        modify fun s =>
          { s with derefReads := s.derefReads.push id,
                   dups := s.dups.push (t, pos ++ "reading through a reference copies the value (`replace` takes it out instead)") }
    | none => left := left.push (subject, idx, result, pos, id)
  if left.isEmpty then pure ()
  else if left.size < waiting.size then
    modify fun s => { s with projections := left ++ s.projections }
    runProjections final
  else if !final then
    modify fun s => { s with projections := left ++ s.projections }
  else
    match left[0]? with
    | some (_, idx, _, pos, _) =>
      throw s!"{pos}`.{idx}` reads a field of a value whose type is not known here; \
        annotate the value it is read from"
    | none => pure ()

/-- What a trait leaves to an implementation that `t` stands for, where `t`
is a type not yet known that was read from one (`unproject`): as written,
`<H as Assoc>::Out`, with what it is of as now known. -/
def projectionOf (t : Ty) : M (Option Ty) := do
  let .var v ← find t | return none
  for (tr, self, name, a, _, _) in (← get).assocUses do
    if let .var w ← find a then
      if w == v then return some (.con Syntax.projMark [← zonk self, .con tr [], .con name []])
  return none

/-- A type as it is written in the name of a trait at its arguments: the
spelling `TypeExpr.spell` gives the type an implementation writes. A type not
yet known is spelt by its variable. -/
partial def spellTy (t : Ty) (seen : List Nat := []) : M String := do
  match ← find t with
  -- (One read from what a trait leaves to an implementation, not known
  -- yet: as that is written, as a condition of it is. One that is part of
  -- what it is asked of, `Output` of `Add` for `(?a, ?b)` that is `?a`, is
  -- spelt by its variable.)
  | .var id => do
    if seen.contains id then return s!"?{id}"
    match ← projectionOf (.var id) with
    | some p => spellTy p (id :: seen)
    | none => pure s!"?{id}"
  | .rigid r => pure r.spelled
  | .con n [] => pure n
  | .con n args => do pure s!"{n}<{", ".intercalate (← args.mapM (spellTy · seen))}>"
  | .tuple args => do pure s!"({", ".intercalate (← args.mapM (spellTy · seen))})"
  | .fn ps r _ _ _ => do pure s!"fn({", ".intercalate (← ps.mapM (spellTy · seen))}) -> {← spellTy r seen}"
  | .ref how inner _ => do
    let uniq := match ← find how with
      | .con "&mut" [] => true
      | _ => false
    pure ((if uniq then "&mut " else "&") ++ (← spellTy inner seen))

/-- What a trait is asked of, taken apart: the type, and the trait's own
arguments if it has some. -/
def subjectOf (trait : String) (subject : Ty) : M (Ty × List Ty) := do
  let arity := (((← get).traitShape[trait]?).map (·.1)).getD 0
  if arity == 0 then return (subject, [])
  match ← find subject with
  | .tuple (self :: args) => pure (self, args)
  | other => pure (other, [])

/-- The same of a bound's trait: one at its arguments is asked of the type
alone. -/
def subjectOfKey (trait : Syntax.TraitKey) (subject : Ty) : M (Ty × List Ty) :=
  if trait.plain then subjectOf trait.base subject else pure (subject, [])

/-- A trait asked of a type at arguments not decided, of a trait whose
parameters there are the type where not written (`trait Add<R = Self>`):
those arguments the type, as a use that does not write them has. With
`known`, only where the type is decided. Whether one was. -/
def defaultTraitArgs (trait : Syntax.TraitKey) (subject : Ty) (keyed : List Ty := []) (known : Bool := false)
    (only : Option Nat := none) : M Bool := do
  let some places := (← get).selfDefaults[trait.base]? | return false
  -- (Of a bound keyed by its arguments, `Add<Int>`, they are `keyed`.)
  let (self, args) ← if keyed.isEmpty then subjectOfKey trait subject else pure (subject, keyed)
  if known && only.isNone then if let .var _ ← find self then return false
  -- (For a whole number written: only where the other is a type of whole
  -- numbers, which it may then be.)
  if known then
    let scalar := fun (t : Ty) => match t with
      | .con n [] => n == "Int" || (Syntax.scalars.lookup n).isSome
      | _ => false
    let others ← (self :: places.filterMap (args[·]?)).mapM find
    unless others.any scalar do return false
  let mut moved := false
  for i in places do
    if let some a := args[i]? then
      match ← find a, ← find self with
      | .var v, _ =>
        if only.all (· == v) then
          unify a self
          moved := true
      | _, .var w =>
        if only.all (· == w) then
          unify a self
          moved := true
      | _, _ => pure ()
  pure moved

/-- What an implementation's type parameters are for a type it is asked of:
each that is an argument of its head, that argument of the type; each that
is only inside one (`impl<T> .. for Wrap<Option<T>>`), something to be found
by making the arguments fit. -/
def implAt (im : ImplDecl) (hargs : List Ty) : M (List (Nat × Ty)) := do
  let mut at_ := (im.params.zip hargs).filterMap fun (p, a) => (im.pvars.lookup p).map (·, a)
  for (_, id) in im.pvars do
    unless at_.any (·.1 == id) do
      at_ := at_ ++ [(id, ← freshTy)]
  pure at_

/-- A type an implementation says an argument has to be, for one use: its
type parameters as that use has them, and its lifetimes that use's own. -/
def fixedAt (at_ : List (Nat × Ty)) (want : Ty) : M Ty := do
  let cm ← (freeCaps want).eraseDups.mapM fun c => do pure (c, ← freshCap)
  pure (subst at_ [] cm want)

/-- A type as a key's argument is written (`Syntax.TraitKey`): as
`spellTy` spells it, a type not known yet by its variable. -/
partial def keyTy (t : Ty) (seen : List Nat := []) : M TypeExpr := do
  match ← find t with
  | .var id => do
    if seen.contains id then return .name s!"?{id}" []
    match ← projectionOf (.var id) with
    | some p => keyTy p (id :: seen)
    | none => pure (.name s!"?{id}" [])
  | .rigid r => pure (.name r.spelled [])
  | .con n args => do pure (.name n (← args.mapM (keyTy · seen)))
  | .tuple args => do pure (.tuple (← args.mapM (keyTy · seen)))
  | .fn ps r _ _ _ => do pure (.fn (← ps.mapM (keyTy · seen)) (← keyTy r seen))
  | .ref how inner _ => do
    let uniq := match ← find how with
      | .con "&mut" [] => true
      | _ => false
    pure (.ref uniq (← keyTy inner seen) none)

/-- The trait at its arguments, as the key an implementation of it has. -/
def traitKey (trait : String) (args : List Ty) : M Syntax.TraitKey := do
  pure (.at trait 0 (← args.mapM keyTy))

/-- An implementation fitted to a use of it: its type parameters as the use
has them (`hargs` the head's arguments, `args` the trait's). The
implementation's new variables are made what is asked, and not the other
way: a type what the function is given is said of keeps its number. None
where they do not fit; with `said`, what does not fit is said, under it. -/
def fitHead (im : ImplDecl) (hargs args : List Ty) (said : Option String := none) :
    M (Option (List (Nat × Ty))) := do
  let at_ ← implAt im hargs
  let fit := fun (want got : Ty) => (do
    match said with
    | some what => unifyAt what want got; pure true
    | none => try unify want got; pure true catch _ => pure false : M Bool)
  for (j, want) in im.fixed do
    if let some got := hargs[j]? then
      unless ← fit (← fixedAt at_ want) got do return none
  -- (Those only in the trait's arguments are what it is asked at; their
  -- lifetimes this use's own, `+ &str` of `impl<'a> Add<&'a str> for String`
  -- once with each text.)
  for (want, got) in im.targs.zip args do
    unless ← fit (← fixedAt at_ want) got do return none
  pure (some at_)

/-- Whether a type has the variable in it. -/
partial def mentionsVar (v : Nat) : Ty → Bool
  | .var w => w == v
  | .rigid _ => false
  | .con _ args | .tuple args => args.any (mentionsVar v)
  | .ref _ t _ => mentionsVar v t
  | .fn ps r _ _ _ => ps.any (mentionsVar v) || mentionsVar v r

/-- A type not yet known that is an argument of a trait asked of a known
type, which has one implementation of the trait: that implementation's
argument there, as Rust's single implementation decides it (`owned + &more`
of `impl Add<&str> for String`: `&more` is then fitted to `&str`). Whether
one was. -/
def argDecidedAt (v : Nat) : M Bool := do
  -- (Of the argument or a part of it: `(s, n)` of `Convert<(B, A)>`.)
  let has := fun (t : Ty) => mentionsVar v t
  for bd in (← get).bounds do
    let base := bd.trait.base
    let (self, args) ← if bd.args.isEmpty then subjectOf base bd.ty else pure (bd.ty, bd.args)
    let mine ← args.anyM fun a => do pure (has (← zonk a))
    unless mine do continue
    let some (head, hargs) ← headFor base (← find self) | continue
    match (← implsOfHead base head).filter (·.targs.length == args.length) with
    | [im] =>
      let saved ← get
      match ← fitHead im hargs args with
      | some _ => return true
      | none => set saved
    | _ => pure ()
  return false

/-- What an implementation is for, as one list: the trait's arguments, then
the type's (its own type parameters, as variables, where it takes any). -/
def implPattern (im : ImplDecl) (arity : Nat) : List Ty :=
  im.targs ++ (List.range arity).map fun j =>
    match im.fixed.lookup j with
    | some t => t
    | none => (((im.params[j]?).bind fun p => im.pvars.lookup p).map Ty.var).getD (.var 0)

/-- Does what is known of a type and the trait's arguments fit an
implementation, as they are, nothing of them made anything to fit? -/
def implFitsAsIs (im : ImplDecl) (hargs args : List Ty) : M Bool := do
  let goal ← (args ++ hargs).mapM zonk
  pure (Ty.fitsAll (im.pvars.map (·.2)) (implPattern im hargs.length) goal []).isSome

/-- The name of an implementation of a trait at arguments for a type. Where
the type's implementation gives the trait arguments made of its own type
parameters (`impl<T> From<T> for Wrap<T>`), the arguments asked are made
those, and the name is that implementation's. -/
def implKey (trait : String) (self : Ty) (args : List Ty) : M Syntax.TraitKey := do
  -- (Of a type made of the function's own type parameters that the
  -- function is said to have it of, `(H, ..R): PutEach<S>`: met so, not by
  -- the implementation for its head.)
  let zself ← zonk self
  unless (Ty.rigidNames zself).isEmpty do
    let key ← traitKey trait args
    if (← get).implConds.contains (key, ← spellTy zself) then return key
  let head ← headFor trait (← find self)
  if let some (h, hargs) := head then
    let family := (← implsOfHead trait h).filter fun im => im.targs.length == args.length
    -- The implementation to make the arguments fit, and its name.
    let commit := fun (im : ImplDecl) => do
      let _ ← fitHead im hargs args (said := some s!"`{bareName trait}` for `{bareName h}`")
      pure im.trait
    match family with
    | [] => pure ()
    | [im] => if im.generic then return ← commit im
    | _ =>
      -- Several for the one trait and type: the one whose arguments the
      -- type's fit, and of two that do, the one that asks more of them.
      let goal ← (args ++ hargs).mapM zonk
      let pattern := fun (im : ImplDecl) =>
        im.targs ++ (List.range hargs.length).map fun j =>
          match im.fixed.lookup j with
          | some t => t
          | none => (((im.params[j]?).bind fun p => im.pvars.lookup p).map Ty.var).getD (.var 0)
      let vars := fun (im : ImplDecl) => im.pvars.map (·.2)
      let narrower := fun (a b : ImplDecl) => (Ty.fitsAll (vars b) (pattern b) (pattern a) []).isSome
      let exact := family.filter fun im => (Ty.fitsAll (vars im) (pattern im) goal []).isSome
      -- (Nothing may yet fit a type all of which is known.)
      -- (One whose variables could be made what the goal needs, the same
      -- everywhere each is written: a type parameter of the function the
      -- goal is in may be anything.)
      let rigids := (goal.flatMap Ty.rigidNames).eraseDups
      let open_ := goal.map (Ty.openRigids (rigids.zipIdx.map fun (n, k) => (n, Ty.var (1000000000000 + k))))
      let maybe := if goal.all Ty.ground then [] else family.filter fun im =>
        !exact.any (·.dictFn == im.dictFn) && ((pattern im).zip goal).all (fun (p, g) => p.mayFit g)
          && (Ty.meetAll (pattern im) open_ []).isSome
      match exact.find? fun a => exact.all fun b => narrower a b with
      | some im =>
        -- (One that may yet fit and asks more would be the one, if it
        -- came to fit: that is not known here.)
        if let some other := maybe.find? fun m => !narrower im m then
          -- (Of a type made of the function's own type parameters that the
          -- function is said to have it of, `(..R): Registers<S>`: met so,
          -- not by one of these.)
          if !rigids.isEmpty then
            let key ← traitKey trait args
            let spelled ← spellTy (← zonk self)
            if (← get).implConds.contains (key, spelled) then return key
          throw s!"which implementation of `{bareName trait}` this is, is not known here: `{showTy (← zonk self)}` may turn out to be a type that another implementation of `{other.trait.shown}` is for. Say it of the type, `where .. : {bareName trait}`"
        return ← commit im
      | none =>
        match exact, maybe with
        | [], [im] => return ← commit im
        | [], _ => pure ()
        | _, _ =>
          throw s!"two implementations of `{bareName trait}` fit `{showTy (← zonk self)}`, and neither asks more than the other"
  traitKey trait args

/-- Does the type asked have an implementation of the trait for every
argument? Then what the arguments are need not be known to find it. -/
def hasGenericImpl (trait : String) (self : Ty) : M Bool := do
  match ← find self with
  | .con h _ =>
    pure ((← implsOfHead trait h).any (·.generic))
  | _ => pure false

/-- What an implementation's conditions say of the types other traits leave
to implementations (`H: Parameter<Asks = HA>`), asked: its own type
parameters that only those decide are answered as each is
(`settleAssocs`). -/
def equalUses (im : ImplDecl) (at_ : List (Nat × Ty)) (hargs : List Ty) (owner pos : String) : M Unit := do
  for (j, asked, name, said) in im.equal do
    if let some subject := hargs[j]? then
      modify fun s => { s with assocUses := s.assocUses.push (asked, subject, name, subst at_ [] [] said, owner, pos) }
  for (whole, asked, name, said) in im.extraEqual do
    modify fun s => { s with assocUses := s.assocUses.push (asked, subst at_ [] [] whole, name, subst at_ [] [] said, owner, pos) }

/-- The type a trait leaves to its implementations, for a type whose
implementation is known: `Elem` of `Index` for an array of `Int`. Nothing
where the type is not known enough to say which implementation is its. -/
def assocAt (tr : String) (subject : Ty) (name : String) : M (Option Ty) := do
  -- (Asked at types, `F::Of<Int>`: those go with the type asked.)
  let (subject, asked) ← match ← find subject with
    | .con mark (inner :: asked) => pure (if mark == Syntax.gatMark then (inner, asked) else (subject, []))
    | _ => pure (subject, [])
  let (self, args) ← subjectOf tr subject
  let known ← match ← find self with
    | .rigid _ => pure none
    | .con n hargs => pure (if n.startsWith "'" then none else some (n, hargs))
    | other => headFor tr other
  let some (head, hargs) := known | return none
  let key ← try implKey tr self args catch _ => return none
  let some im := (← implsOfHead key.base head).find? fun im => im.trait == key | return none
  let some said := im.assocs.lookup name | return none
  let some at_ ← fitHead im hargs args | return none
  equalUses im at_ hargs (← get).owner (← get).pos
  pure (some (← unproject (gatAt at_ ((im.gatParams.lookup name).getD []) asked said)))

/-- Settle what can be settled of the types traits leave to implementations:
where the type asked of is known, the answer is what its implementation says;
and the same question asked twice has one answer. -/
def settleAssocs : M Unit := do
  let uses := (← get).assocUses
  modify fun s => { s with assocUses := #[] }
  let mut left : Array (String × Ty × String × Ty × String × String) := #[]
  for (tr, subject, name, a, owner, pos) in uses do
    let fit := fun (what : String) (found : Ty) => do
      try unifyAt what found a catch e => throw (pos ++ e)
    -- (Asked before of the same type, all known: the same answer.)
    let zsubject ← zonk subject
    let spelled ← spellTy zsubject
    let memoKey := if (freeTys zsubject).isEmpty then some s!"{tr}|{name}|{spelled}" else none
    if let some found := memoKey.bind ((← get).assocMemo[·]?) then
      fit s!"`{name}` of `{Syntax.lastSegment tr}`" found
      continue
    let remember := do
      if let some k := memoKey then modify fun s => { s with assocMemo := s.assocMemo.insert k a }
    -- (Asked at types, `F::Of<Int>`: found as any other is, once the type
    -- asked is known.)
    if let .con mark (_ :: _) ← find subject then
      if mark == Syntax.gatMark then
        match ← assocAt tr subject name with
        | some found =>
          fit s!"`{name}` of `{Syntax.lastSegment tr}`" found
          remember
        | none => left := left.push (tr, subject, name, a, owner, pos)
        continue
    let (self, args) ← subjectOf tr subject
    let known ← match ← find self with
      | .rigid _ => pure none
      | .con n hargs => pure (if n.startsWith "'" then none else some (n, hargs))
      | other => headFor tr other
    let ground ← args.allM fun x => do pure (freeTys (← zonk x)).isEmpty
    let ground := ground || (← hasGenericImpl tr self)
    match known, ground with
    | some (head, hargs), true =>
      -- (Which of several it is, where the type is not all known yet: once
      -- it is, `(HA, RN)` an implementation's conditions decide.)
      let open_ := !(freeTys (← zonk self)).isEmpty
      let key ← try implKey tr self args catch e => do
        if open_ then
          left := left.push (tr, subject, name, a, owner, pos)
          continue
        throw e
      let family ← implsOfHead key.base head
      match family.find? fun im => im.trait == key with
      | some im =>
        -- (Of several for the type, the one it fits as it is: of `impl<X>
        -- Either for (Yes, X)` and `(No, X)`, neither while the first is
        -- not known, though the first is spelled as the trait is.)
        if family.length > 1 && !(← implFitsAsIs im hargs args) then
          left := left.push (tr, subject, name, a, owner, pos)
          continue
        match im.assocs.lookup name with
        | some said =>
          -- The implementation's type parameters are the type's arguments,
          -- or inside them.
          let at_ ← match ← fitHead im hargs args with
            | some at_ => pure at_
            | none => implAt im hargs
          equalUses im at_ hargs owner pos
          fit s!"`{name}` of `{key}` for `{bareName head}`" (← unproject (subst at_ [] [] said))
          remember
        | none => left := left.push (tr, subject, name, a, owner, pos)
      | none => left := left.push (tr, subject, name, a, owner, pos)
    | _, _ => left := left.push (tr, subject, name, a, owner, pos)
  -- Asked of the same type, the same answer.
  let mut seen : List (String × Ty) := []
  for (tr, subject, name, a, _, _) in left do
    let question := s!"{tr}|{name}|{← spellTy subject}"
    match seen.lookup question with
    | some first => unify first a
    | none => seen := (question, a) :: seen
  -- One answer to the same question at lifetimes (`T::Got<'a>` and a
  -- `T::Got<'b>` that is the same type): the lifetimes are one. What a
  -- function gives of a type its parameter's trait leaves, borrowed from
  -- what it was given, is so tied to what it was given.
  let mut answers : List (Nat × String × String × List Ty) := []
  for (tr, subject, name, a, _, _) in left do
    let .var id ← find a | continue
    let .con mark (_ :: asked) ← find subject | continue
    unless mark == Syntax.gatMark do continue
    match answers.find? (·.1 == id) with
    | some (_, tr2, name2, asked2) =>
      if tr2 == tr && name2 == name then
        for (x, y) in asked.zip asked2 do
          if let (.ref (.con "'" []) _ _, .ref (.con "'" []) _ _) := (← find x, ← find y) then unify x y
    | none => answers := (id, tr, name, asked) :: answers
  modify fun s => { s with assocUses := left ++ s.assocUses }

/-- `settleAssocs` of those asked from the `k`-th on alone. -/
def settleAssocsFrom (k : Nat) : M Unit := do
  let uses := (← get).assocUses
  modify fun s => { s with assocUses := uses.extract k uses.size }
  settleAssocs
  modify fun s => { s with assocUses := uses.extract 0 k ++ s.assocUses }

/-- `settleAssocs` until it settles nothing more (a list of sixteen's types,
each made of the rest's, take some dozens of rounds). -/
partial def settleAssocsAll (fuel : Nat := 256) : M Unit := do
  let before := (← get).assocUses
  settleAssocs
  let after := (← get).assocUses
  -- (Again while any was answered: an answer may itself ask another,
  -- `<Q as ItemTouches>::List`, which is then there in its place.)
  if fuel > 0 && (after.size < before.size || after.map (·.1) != before.map (·.1)
      || (← after.mapM fun u => spellTy u.2.1) != (← before.mapM fun u => spellTy u.2.1)) then
    settleAssocsAll (fuel - 1)


/-- What an implementation's conditions say of types left to other traits'
implementations (`where I: Iterator<Item = A>`), said of a use of it at
`at_`: false where what is known says otherwise. What is not known yet is
found once what it is asked of is. -/
def fitConditions (im : ImplDecl) (at_ : List (Nat × Ty)) (hargs : List Ty) (owner pos : String) :
    M Bool := do
  for (j, asked, name, said) in im.equal do
    if let some subject := hargs[j]? then
      if let some found ← assocAt asked subject name then
        try unify (subst at_ [] [] said) found catch _ => return false
  for (whole, asked, name, said) in im.extraEqual do
    match ← assocAt asked (subst at_ [] [] whole) name with
    | some found => try unify (subst at_ [] [] said) found catch _ => return false
    | none =>
      let use := (asked, subst at_ [] [] whole, name, subst at_ [] [] said, owner, pos)
      modify fun s => { s with assocUses := s.assocUses.push use }
  -- (What those decide, before the conditions on what they decide.)
  unless im.equal.isEmpty && im.extraEqual.isEmpty do settleAssocsAll
  pure true

def runPending : M Unit := do
  -- (Until it settles: a field read of what a trait leaves to an
  -- implementation of what another leaves, `K::Got` of `R`'s `Kind`, is
  -- known once both are.)
  settleAssocsAll
  runProjections true
  settleRows (some fun _ => true) true
  -- (Each `..` of a tuple pattern written as the parts it stands for, as
  -- found where it was read, `Elab.Adjust.rest`.)
  let rests := (← get).adjust.filterMap fun
    | .rest id count => some (id, count)
    | _ => none
  let pending := (← get).pending.map fun p =>
    if rests.isEmpty then p
    else { p with rows := p.rows.map (·.map fun pat => rests.foldl (fun q (id, c) => Elab.restPat id c q) pat) }
  modify fun s => { s with pending := #[] }
  for p in pending do
    let rows ← p.rows.mapM (·.mapM normPat)
    if let some ws ← uncovered p.tys rows then
      -- (Not where it says nothing: any value, or a number.)
      let telling := fun (w : String) => w.toList.any fun c => c.isAlpha
      let case_ := match ws with
        | [w] => if telling w then s!": not `{w}`" else ""
        | ws => if ws.isEmpty || !ws.any telling then ""
          else s!": not `{", ".intercalate ws}`"
      throw s!"{p.pos}{p.what} not cover every case{case_}"
    -- A clause that tests for something the clauses before it have already
    -- taken every case of is never reached (6.2). One that takes whatever
    -- is left is not said to be: the compiler writes such clauses itself.
    for i in [1:rows.length] do
      let tests := (rows.getD i []).any fun
        | .any => false
        | _ => true
      if tests then
        if (← uncovered p.tys (rows.take i)).isNone then
          throw s!"{p.pos}clause {i + 1} is never reached: the clauses before it take every case"

/-! ## Scopes that values cannot outlive

A label is only meaningful while its scope is running. A callable that mentions
a label captures the scope's brand, as does any callable that captures such a
value. When a scope ends, no type that is still visible may mention a callable
holding its brand: not the scope's result, not a variable declared outside, not
a payload sent to a handler outside, and not a declaration's shared field type.

This is deliberately conservative. A function type mentions every callable
type in its parameters and result, so handing a callable that holds the brand
to a *variable* of function type counts as an escape: nothing says that
function will not keep it. Top-level functions are generalised, so passing such
a callable to one of them is fine.
-/

mutual

partial def capHolds (brand : Nat) (cap : Nat) : M Bool := do
  let some edges ← unseenEdges cap | return false
  for (_, what) in edges do
    match what with
    | .brand b => if b == brand then return true
    | .ty t => if ← tyHolds brand t then return true
    | .once | .must | .loan _ | .touch _ _ | .inner _ => pure ()
  return false

/-- Does the type mention a callable that holds the brand? -/
partial def tyHolds (brand : Nat) (t : Ty) : M Bool := do
  match ← find t with
  | .var v =>
    -- (A type a trait leaves at a lifetime, not known here: it may hold
    -- what that lifetime holds.)
    for (w, lives) in (← get).gatHolds do
      if let .var r' ← find (.var w) then
        if r' == v then
          if ← lives.anyM (capHolds brand ·) then return true
    pure false
  | .rigid _ => pure false
  | .con _ args | .tuple args => args.anyM (tyHolds brand)
  | .fn ps r effs tail cap => do
    if ← capHolds brand cap then return true
    if ← ps.anyM (tyHolds brand) then return true
    if ← tyHolds brand r then return true
    let row ← flattenRow ⟨effs, tail⟩
    row.effs.anyM fun e => e.2.anyM (tyHolds brand)
  | .ref _ t cap => do
    if ← capHolds brand cap then return true
    tyHolds brand t

end

/-- Reject a scope whose label could still be reached after the scope has ended.
`roots` are the types that outlive the scope, each with a description: what
can be settled of the types now is, and the search made once the function is
read (`escapeSearch`, `St.escapesLater`). -/
def checkEscape (brand : Nat) (what : String) (roots : List (String × Ty)) (amb : Row) :
    M Unit := do
  runProjections false
  settleRows none false
  settleAssocs
  modify fun s => { s with escapesLater := s.escapesLater.push (brand, what, roots, amb, s.within) }

/-- What `checkEscape` asks, of the types as the function has them once read. -/
def escapeSearch (brand : Nat) (what : String) (roots : List (String × Ty)) (amb : Row) :
    M Unit := do
  -- (What was gone through without finding the brand does not hold it
  -- however it is reached again: gone through once for all the roots.)
  modify fun s => { s with seen := {} }
  let holds := fun (t : Ty) => tyHolds brand t
  let escape := fun (how : String) =>
    (throw s!"{what}: {how}" : M Unit)
  -- (A function that calls itself, or one checked with it, whose signature
  -- is not written whole, is given the same lifetime at each of those calls
  -- for each of its references: one made inside it, given where its
  -- caller's is given too, is taken to last as long as the caller's. Said
  -- so where that is how it could be held.)
  let s0 ← get
  let recursive := s0.groupUses.any fun u => u.owner == s0.owner && !s0.groupSigned.contains u.owner
  for (how, t) in roots do
    if ← holds t then
      if recursive && (← match ← find t with | .ref .. => pure true | _ => pure false) then
        escape s!"{how}: a function that calls itself and does not write the type of each of its parameters and of its result is checked with one lifetime for each of its references, the same at every call of itself, so a reference to a value made inside it, given where its caller's reference is given too, is taken to last as long as the caller's (write its signature whole, and each call of itself is at lifetimes of its own)"
      escape how
  let row ← flattenRow amb
  for (e, args) in row.effs do
    for a in args do
      if ← holds a then escape s!"it is passed to a handler of `{e}` outside"
  let s ← get
  if let some cap := s.staticCap then
    if ← capHolds brand cap then
      escape "it is borrowed for `'static`, and no variable lasts that long"
  for cap in s.monoCaps do
    if ← capHolds brand cap then
      escape "it is stored in a declaration's `fn` field; give that declaration a \
        type parameter for the field"

def jumpsAfter (label : String) : String :=
  s!"a callable that jumps to `@{label}` could be called after `@{label}` has ended"

/-- The types of the bindings in scope, described for an escape message. -/
def scopeRoots (scope : Scope) : List (String × Ty) :=
  scope.map fun (name, b) =>
    match b with
    | .val t _ | .cell t _ => (s!"`{name}`, which outlives the scope, could hold it", t)
    | .label t _ => (s!"it can be passed out through `{name}`", t)
    | .poly s => (s!"`{name}`, which outlives the scope, could hold it", s.ty)

/-! ## Values that can be used only once

A resumption can be used once. So can anything that holds one: a tuple or data
value with a resumption inside, and a callable that has captured one. A
reference holds nothing, and neither does a function merely because it accepts
or returns such a value.

A binding used more than once must therefore be of a type that holds no
resumption. The requirement is recorded when the uses are counted and checked
once types are known; for a type that depends on a function's parameters it
becomes part of the function's contract and is checked at each call.

Uses are counted from the shape of the program. Clauses of one callable are
alternatives. A callable that mentions a binding uses it once, by capturing it.
The arm of an operation that can be resumed may run any number of times, so a
binding from outside used in one counts as used repeatedly. The count knows
nothing about which callables a function goes on to call, so two callables that
each use a resumption count as two uses even if only one of them ever runs.
-/

/-- The first thing found in a type, gone through as a value holds what it
holds: a tuple's parts; at a declared type, what `atCon` finds of its name,
then its arguments, then each constructor's fields (once for each type,
`visiting`); at a callable, what `atFn` finds of its capture, with the types
being gone through. Nothing in a reference, which is another's value, or in a
type not yet known. -/
partial def walkTy {α : Type} (atCon : String → M (Option α)) (atFn : List String → Nat → M (Option α))
    (visiting : List String) (t : Ty) (stop : String → M Bool := fun _ => pure false) : M (Option α) := do
  match ← find t with
  | .tuple args => args.findSomeM? (walkTy atCon atFn visiting · stop)
  | .fn _ _ _ _ cap => atFn visiting cap
  | .con name args => do
    -- (A `[T; 0]` holds no `T`.)
    if name == "Fixed" then
      if let [_, len] := args then
        if numberOf (← zonk len) == some 0 then return none
    if let some a ← atCon name then return some a
    if ← stop name then return none
    if let some a ← args.findSomeM? (walkTy atCon atFn visiting · stop) then return some a
    if visiting.contains name then return none
    match (← get).types[name]? with
    | none => pure none
    | some decl =>
      decl.ctors.findSomeM? fun c => do
        match (← get).ctors[c]? with
        | none => pure none
        | some sig => (sig.fieldsAt args).findSomeM? (walkTy atCon atFn (name :: visiting) · stop)
  | _ => pure none

/-- A declared type that says its values are used once. -/
def usedOnceDecl (name : String) : M (Option String) := do
  pure (match (← get).useDecls[name]? with
    | some (_, true) => some name
    | _ => none)

/-- A declared type that says its values may be used any number of times,
`impl Use<[_, *]>`: whatever it holds (`Mutex<Vec<T>>`, a handle), it is
not looked into to see whether it is used once. (What it holds was checked
against what it says, `checkUseDecls`.) -/
def usedAnyNumber (name : String) : M Bool := do
  pure (match (← get).useDecls[name]? with
    | some (_, false) => true
    | _ => false)

/-- A declared type with a `drop` of its own. -/
def dropDecl (name : String) : M (Option String) := do
  pure (if (← get).kimpls.has (.of "Drop") name then some (bareName name) else none)

mutual

partial def capOwnsOnce (cap : Nat) : M Bool := do
  let some edges ← unseenEdges cap | return false
  for (_, what) in edges do
    match what with
    | .once => return true
    | .must => pure ()
    | .ty t => if ← tyOwnsOnce [] t then return true
    | .brand _ | .loan _ | .touch _ _ | .inner _ => pure ()
  return false

/-- Can a value of this type be used only once? One that holds a resumption,
and one of a declared type that says so, or that has a `drop` of its own (a
copy would run it again). -/
partial def tyOwnsOnce (visiting : List String) (t : Ty) : M Bool := do
  let atCon := fun (name : String) => do
    pure ((← usedOnceDecl name) <|> (← dropDecl name))
  let atFn := fun (_ : List String) (cap : Nat) => do pure (if ← capOwnsOnce cap then some "" else none)
  pure (← walkTy atCon atFn visiting t usedAnyNumber).isSome

end

/-- Does a value of a type hold values of a type variable? Not through a
reference, which is another's value, nor as what a callable takes or gives.
So a `&mut [T]` used twice is not a `T` used twice. -/
partial def tyHoldsVar (visiting : List String) (id : Nat) (t : Ty) : M Bool := do
  match ← find t with
  | .var v => pure (v == id)
  | .rigid _ => pure false
  | .tuple args => args.anyM (tyHoldsVar visiting id)
  | .fn _ _ _ _ _ | .ref _ _ _ => pure false
  -- (A `[T; 0]` holds no `T`.)
  | .con "Fixed" [elem, len] => do
    if numberOf (← zonk len) == some 0 then return false
    tyHoldsVar visiting id elem
  | .con name args => do
    if visiting.contains name then return false
    match (← get).types[name]? with
    | none => args.anyM (tyHoldsVar visiting id)
    | some decl =>
      let s ← get
      -- (A type whose constructors are not known here is taken to hold
      -- what it is given.)
      if decl.ctors.isEmpty then return ← args.anyM (tyHoldsVar visiting id)
      decl.ctors.anyM fun c => do
        match s.ctors[c]? with
        | none => args.anyM (tyHoldsVar visiting id)
        | some sig => (sig.fieldsAt args).anyM (tyHoldsVar (name :: visiting) id)

/-- Require that values of a type may be used more than once. -/
def mustDup (t : Ty) (why : String) : M Unit :=
  modify fun s => { s with dups := s.dups.push (t, s.pos ++ why) }

/-- The declared type, if any, that makes a type one whose values are used
only once. Only to say why. -/
def onceBy (visiting : List String) (t : Ty) : M (Option String) :=
  walkTy usedOnceDecl (fun _ _ => pure none) visiting t usedAnyNumber

/-- A type whose values have a `drop` of their own to run, or hold one that
has: the name of the first such type found. A callable holds what it has
taken hold of. -/
partial def tyHasDrop (visiting : List String) (t : Ty) : M (Option String) :=
  walkTy dropDecl (fun visiting cap => do
    let some edges ← unseenEdges cap | return none
    for (_, what) in edges do
      if let .ty held := what then
        if let some name ← tyHasDrop visiting held then return some name
    return none) visiting t
    -- (A handle, said to be used any number of times, is never destroyed:
    -- what it names is not looked into.)
    (stop := usedAnyNumber)

def checkDups (dups : Array (Ty × String)) : M Unit := do
  for (t, why) in dups do
    modify fun s => { s with seen := {} }
    if ← tyOwnsOnce [] t then
      if let some name ← onceBy [] t then
        throw s!"{why}, but a `{name}` can be used only once"
      -- A value with a `drop` to run is not copied: each copy would run it.
      -- (Its `drop` may read one through a reference, as it takes one apart,
      -- to see what to do; nothing else may.)
      modify fun s => { s with seen := {} }
      if let some name ← tyHasDrop [] t then
        let s ← get
        let through := (why.splitOn "reading through a reference").length > 1
        -- (Of a `drop`: the function being checked, or the one a requirement
        -- checked again at the end was made in, which its message names.)
        let inDrop := (s.owner.splitOn "@").head? == some "Drop::drop" || (why.splitOn "in `Drop::drop@").length > 1
        let home := inDrop && s.kimpls.impls.any fun I => I.trait == .of "Drop" && bareName I.head == name
        let observed := (why.splitOn "to choose a clause").length > 1
        if through && (home || observed) then continue
        throw s!"{why}, but a `{name}` has a `drop`, which would then run once for each"
      throw s!"{why}, but a value that holds a resumption can be used only once"

/-- Does a value of this type hold a callable that can be called only once: a
resumption, or a callable that holds what is used once? -/
def tyHoldsOnceCallable (visiting : List String) (t : Ty) : M Bool := do
  pure (← walkTy (fun _ => pure none) (fun _ cap => do pure (if ← capOwnsOnce cap then some () else none))
    visiting t).isSome

/-- A field left behind where nothing destroys it has no `drop` to run. -/
def checkUnrun : M Unit := do
  let apart := (← get).takenApart
  modify fun s => { s with takenApart := #[] }
  for (t, why) in apart do
    modify fun s => { s with seen := {} }
    if ← tyHoldsOnceCallable [] t then
      throw s!"{why}, but a value that holds a resumption can be used only once"
  let left := (← get).leftBehind
  modify fun s => { s with leftBehind := #[] }
  for (t, why) in left do
    modify fun s => { s with seen := {} }
    if let some name ← tyHasDrop [] t then
      throw s!"{why}, and here nothing would run the `drop` of a `{name}` in it: take the value apart with a pattern, which destroys what it does not name"

/-- What a variable gives away is read out of it by the machine, which is a
copy: fine for a value that is counted as used once here and can be copied
there, and not for one that holds a resumption. -/
def checkGivenReads : M Unit := do
  let reads := (← get).givenReads
  modify fun s => { s with givenReads := #[] }
  for (t, why) in reads do
    modify fun s => { s with seen := {} }
    if ← tyOwnsOnce [] t then
      if (← onceBy [] t).isNone then
        modify fun s => { s with seen := {} }
        if (← tyHasDrop [] t).isNone then
          throw s!"{why}, but a value that holds a resumption can be used only once"

end Glorious.Check
