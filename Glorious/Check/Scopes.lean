import Glorious.Check.Declare

namespace Glorious.Check

open Syntax

/-! ## Coverage of pattern clauses -/

/-- A pattern with its names resolved. -/
inductive NPat where
  | any
  | int (n : Int)
  | ctor (name : String) (args : List NPat)
  | tuple (args : List NPat)
  deriving Inhabited

partial def normPat : Pattern → M NPat
  | .wild => pure .any
  | .int n => pure (.int n)
  | .tuple ps => do
    pure (.tuple (← ps.mapM normPat))
  | .var x => do
    match ← resolveCtor x none with
    | some (name, _) => pure (.ctor name [])
    | none =>
      match (← get).aliases.lookup x with
      | some e => do normPat (← exprToPat e)
      | none => pure .any
  | .ctor x q ps => do
    if let some (_, n) := Syntax.scalarPattern (.ctor x q ps) then return .int n
    -- What an `is` found, taken apart: its names, which nothing can fail.
    if (Syntax.packNames x).isSome then return .any
    match ← resolveCtor x q with
    | some (name, _) => do
      pure (.ctor name (← ps.mapM normPat))
    | none => throw s!"unknown constructor `{x}` in a pattern"

/-- Do the rows of patterns cover every value of the column types? -/
partial def exhaustive (tys : List Ty) (rows : List (List NPat)) : M Bool := do
  match tys with
  | [] => pure !rows.isEmpty
  | t :: rest =>
    let fallback : M Bool := exhaustive rest (rows.filterMap fun
      | .any :: tl => some tl
      | _ => none)
    match ← find t with
    | .tuple ts =>
      exhaustive (ts ++ rest) (rows.filterMap fun
        | .tuple ps :: tl => some (ps ++ tl)
        | .any :: tl => some (List.replicate ts.length .any ++ tl)
        | _ => none)
    | .con name args =>
      match (← get).types.lookup name with
      | some decl =>
        -- Split by constructor only where some clause tests for one; a recursive
        -- type would otherwise be unfolded for ever.
        let tested := rows.any fun
          | .ctor _ _ :: _ => true
          | _ => false
        if !tested then fallback
        else decl.ctors.allM fun c => do
          match (← get).ctors.lookup c with
          | none => pure false
          | some sig =>
            let fields := sig.fieldsAt args
            exhaustive (fields ++ rest) (rows.filterMap fun
              | .ctor c' ps :: tl => if c' == c then some (ps ++ tl) else none
              | .any :: tl => some (List.replicate fields.length .any ++ tl)
              | _ => none)
      | none => fallback
    | _ => fallback

/-- The type of field `idx` of a value of type `t`, if `t` is known. -/
def fieldType (t : Ty) (idx : Nat) : M (Option Ty) := do
  match ← find t with
  | .var _ => pure none
  | .tuple ts =>
    match ts[idx]? with
    | some t => pure (some t)
    | none => throw s!"a tuple of {ts.length} values has no field {idx}"
  | .con name args =>
    match (← get).ctors.lookup name with
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
  | t => throw s!"`.{idx}` reads a field, but `{showTy (← zonk t)}` has none"

/-- Which field of a value of type `t` a step is: its number, or the place of
its name among the fields of the type's one constructor. None if the type is
not known yet and the step is a number. -/
def fieldIndex (t : Ty) (step : String) : M (Option Nat) := do
  if let some n := step.toNat? then return some n
  match ← find t with
  | .con name _ =>
    let ctor := match (← get).types.lookup name with
      | some decl => match decl.ctors with
        | [c] => some c
        | _ => none
      | none => none
    let declared := (← get).fieldNames
    match ctor.bind fun c => declared.lookup c with
    | some names =>
      match names.idxOf? step with
      | some i => pure (some i)
      | none => throw s!"`{showTy (← zonk t)}` has no field `{step}`"
    | none => throw s!"`{showTy (← zonk t)}` has no field `{step}`: its fields have no names"
  | .var _ =>
    throw s!"the field `{step}` is read from a value whose type is not known here; annotate it"
  | t => throw s!"`{showTy (← zonk t)}` has no field `{step}`"

/-- Settle the field reads that were waiting for their subject's type. When
`final`, one that still cannot be settled is an error. -/
partial def runProjections (final : Bool) : M Unit := do
  -- Fields read by name first: which field a name is depends on the type.
  let named := (← get).namedReads
  modify fun s => { s with namedReads := #[] }
  let mut unnamed : Array (Ty × String × Ty × Nat × String) := #[]
  for (subject, name, result, id, pos) in named do
    let unknown := match ← find subject with
      | .var _ => true
      | _ => false
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
  let mut left : Array (Ty × Nat × Ty × String) := #[]
  for (subject, idx, result, pos) in waiting do
    match ← fieldType subject idx with
    | some t =>
      try unifyAt s!"the field `.{idx}`" result t
      catch e => throw (pos ++ e)
    | none => left := left.push (subject, idx, result, pos)
  if left.isEmpty then pure ()
  else if left.size < waiting.size then
    modify fun s => { s with projections := left ++ s.projections }
    runProjections final
  else if !final then
    modify fun s => { s with projections := left ++ s.projections }
  else
    match left[0]? with
    | some (_, idx, _, pos) =>
      throw s!"{pos}`.{idx}` reads a field of a value whose type is not known here; \
        annotate the value it is read from"
    | none => pure ()

/-- A type as it is written in the name of a trait at its arguments: the
spelling `TypeExpr.spell` gives the type an implementation writes. A type not
yet known is spelt by its variable. -/
partial def spellTy (t : Ty) : M String := do
  match ← find t with
  | .var id => pure s!"?{id}"
  | .con n [] => pure n
  | .con n args => do pure s!"{n}<{", ".intercalate (← args.mapM spellTy)}>"
  | .tuple args => do pure s!"({", ".intercalate (← args.mapM spellTy)})"
  | .fn ps r _ _ _ => do pure s!"fn({", ".intercalate (← ps.mapM spellTy)}) -> {← spellTy r}"
  | .ref how inner _ => do
    let uniq := match ← find how with
      | .con "&mut" [] => true
      | _ => false
    pure ((if uniq then "&mut " else "&") ++ (← spellTy inner))

/-- What a trait is asked of, taken apart: the type, and the trait's own
arguments if it has some. -/
def subjectOf (trait : String) (subject : Ty) : M (Ty × List Ty) := do
  let arity := (((← get).traitShape.lookup trait).map (·.1)).getD 0
  if arity == 0 then return (subject, [])
  match ← find subject with
  | .tuple (self :: args) => pure (self, args)
  | other => pure (other, [])

/-- The trait at its arguments, as the one name an implementation of it has. -/
def traitKey (trait : String) (args : List Ty) : M String := do
  pure (Syntax.traitAt trait (← args.mapM spellTy))

/-- The name of an implementation of a trait at arguments for a type. Where
the type's implementation gives the trait arguments made of its own type
parameters (`impl<T> From<T> for Wrap<T>`), the arguments asked are made
those, and the name is that implementation's. -/
def implKey (trait : String) (self : Ty) (args : List Ty) : M String := do
  let head ← match ← find self with
    | .con n hargs => pure (some (n, hargs))
    | .tuple parts => pure (some (s!"(tuple{parts.length})", parts))
    | _ => pure none
  if let some (h, hargs) := head then
    if let some im := (← get).impls.toList.find? fun im =>
        im.generic && Syntax.traitBase im.trait == trait && im.head == h then
      let at_ := (im.params.zip hargs).filterMap fun (p, a) => (im.pvars.lookup p).map (·, a)
      for (want, got) in (im.targs.map (subst at_ [] [])).zip args do
        unifyAt s!"`{bareName trait}` for `{bareName h}`" want got
      return im.trait
  traitKey trait args

/-- Does the type asked have an implementation of the trait for every
argument? Then what the arguments are need not be known to find it. -/
def hasGenericImpl (trait : String) (self : Ty) : M Bool := do
  match ← find self with
  | .con h _ =>
    pure ((← get).impls.toList.any fun im =>
      im.generic && Syntax.traitBase im.trait == trait && im.head == h)
  | _ => pure false

/-- Settle what can be settled of the types traits leave to implementations:
where the type asked of is known, the answer is what its implementation says;
and the same question asked twice has one answer. -/
def settleAssocs : M Unit := do
  let uses := (← get).assocUses
  modify fun s => { s with assocUses := #[] }
  let mut left : Array (String × Ty × String × Ty × String × String) := #[]
  for (tr, subject, name, a, owner, pos) in uses do
    let (self, args) ← subjectOf tr subject
    let known ← match ← find self with
      | .con n hargs => pure (if n.startsWith "'" then none else some (n, hargs))
      | .tuple parts => pure (some (s!"(tuple{parts.length})", parts))
      | _ => pure none
    let ground ← args.allM fun x => do pure (freeTys (← zonk x)).isEmpty
    let ground := ground || (← hasGenericImpl tr self)
    match known, ground with
    | some (head, hargs), true =>
      let key ← implKey tr self args
      match (← get).impls.toList.find? fun im => im.trait == key && im.head == head with
      | some im =>
        match im.assocs.lookup name with
        | some said =>
          -- The implementation's type parameters are the type's arguments.
          let at_ := (im.params.zip hargs).filterMap fun (p, h) =>
            (im.pvars.lookup p).map fun id => (id, h)
          try unifyAt s!"`{name}` of `{key}` for `{bareName head}`" (subst at_ [] [] said) a
          catch e => throw (pos ++ e)
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
  modify fun s => { s with assocUses := left ++ s.assocUses }

def runPending : M Unit := do
  settleAssocs
  runProjections true
  settleRows (some fun _ => true) true
  let pending := (← get).pending
  modify fun s => { s with pending := #[] }
  for p in pending do
    let rows ← p.rows.mapM (·.mapM normPat)
    unless ← exhaustive p.tys rows do
      throw s!"{p.pos}{p.what} not cover every case"
    -- A clause that tests for something the clauses before it have already
    -- taken every case of is never reached (6.2). One that takes whatever
    -- is left is not said to be: the compiler writes such clauses itself.
    for i in [1:rows.length] do
      let tests := (rows.getD i []).any fun
        | .any => false
        | _ => true
      if tests then
        if ← exhaustive p.tys (rows.take i) then
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
  let root ← findCap cap
  if (← get).seen.contains root then return false
  modify fun s => { s with seen := root :: s.seen }
  for (src, what) in (← get).capEdges do
    if (← findCap src) == root then
      match what with
      | .brand b => if b == brand then return true
      | .ty t => if ← tyHolds brand t then return true
      | .once => pure ()
      | .must => pure ()
      | .loan _ => pure ()
      | .touch _ _ => pure ()
      | .inner _ => pure ()
  return false

/-- Does the type mention a callable that holds the brand? -/
partial def tyHolds (brand : Nat) (t : Ty) : M Bool := do
  match ← find t with
  | .var _ => pure false
  | .con _ args => args.anyM (tyHolds brand)
  | .tuple args => args.anyM (tyHolds brand)
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
`roots` are the types that outlive the scope, each with a description. -/
def checkEscape (brand : Nat) (what : String) (roots : List (String × Ty)) (amb : Row) :
    M Unit := do
  runProjections false
  settleRows none false
  let holds := fun (t : Ty) => do
    modify fun s => { s with seen := [] }
    tyHolds brand t
  let escape := fun (how : String) =>
    (throw s!"{what}: {how}" : M Unit)
  for (how, t) in roots do
    if ← holds t then escape how
  let row ← flattenRow amb
  for (e, args) in row.effs do
    for a in args do
      if ← holds a then escape s!"it is passed to a handler of `{e}` outside"
  let s ← get
  for id in s.mono do
    if ← holds (.var id) then
      escape "it is stored in a declaration whose field types are inferred; \
        give that declaration a type parameter"
  if let some cap := s.staticCap then
    modify fun s => { s with seen := [] }
    if ← capHolds brand cap then
      escape "it is borrowed for `'static`, and no variable lasts that long"
  for cap in s.monoCaps do
    modify fun s => { s with seen := [] }
    if ← capHolds brand cap then
      escape "it is stored in a declaration's `fn` field; give that declaration a \
        type parameter for the field"

def jumpsAfter (label : String) : String :=
  s!"a callable that jumps to `@{label}` could be called after `@{label}` has ended"

/-- The types of the bindings in scope, described for an escape message. -/
def scopeRoots (scope : Scope) : List (String × Ty) :=
  scope.map fun (name, b) =>
    match b with
    | .val t _ => (s!"`{name}`, which outlives the scope, could hold it", t)
    | .cell t _ => (s!"`{name}`, which outlives the scope, could hold it", t)
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

mutual

partial def capOwnsOnce (cap : Nat) : M Bool := do
  let root ← findCap cap
  if (← get).seen.contains root then return false
  modify fun s => { s with seen := root :: s.seen }
  for (src, what) in (← get).capEdges do
    if (← findCap src) == root then
      match what with
      | .once => return true
      | .must => pure ()
      | .ty t => if ← tyOwnsOnce [] t then return true
      | .brand _ => pure ()
      | .loan _ => pure ()
      | .touch _ _ => pure ()
      | .inner _ => pure ()
  return false

/-- Can a value of this type be used only once? One that holds a resumption,
and one of a declared type that says so. -/
partial def tyOwnsOnce (visiting : List String) (t : Ty) : M Bool := do
  match ← find t with
  | .var _ => pure false
  | .tuple args => args.anyM (tyOwnsOnce visiting)
  | .fn _ _ _ _ cap => capOwnsOnce cap
  | .ref _ _ _ => pure false
  | .con name args => do
    if let some (_, once) := (← get).useDecls.lookup name then
      if once then return true
    -- A type with a `drop` of its own: a copy would run it again.
    if (← get).kimpls.any (fun I => I.trait == "Drop" && I.head == name) then return true
    if ← args.anyM (tyOwnsOnce visiting) then return true
    if visiting.contains name then return false
    match (← get).types.lookup name with
    | none => pure false
    | some decl =>
      decl.ctors.anyM fun c => do
        match (← get).ctors.lookup c with
        | none => pure false
        | some sig =>
          (sig.fieldsAt args).anyM
            (tyOwnsOnce (name :: visiting))

end

/-- Does a value of a type hold values of a type variable? Not through a
reference, which is another's value, nor as what a callable takes or gives.
So a `&mut [T]` used twice is not a `T` used twice. -/
partial def tyHoldsVar (visiting : List String) (id : Nat) (t : Ty) : M Bool := do
  match ← find t with
  | .var v => pure (v == id)
  | .tuple args => args.anyM (tyHoldsVar visiting id)
  | .fn _ _ _ _ _ => pure false
  | .ref _ _ _ => pure false
  | .con name args => do
    if visiting.contains name then return false
    match (← get).types.lookup name with
    | none => args.anyM (tyHoldsVar visiting id)
    | some decl =>
      let s ← get
      -- (A type whose constructors are not known here is taken to hold
      -- what it is given.)
      if decl.ctors.isEmpty then return ← args.anyM (tyHoldsVar visiting id)
      decl.ctors.anyM fun c => do
        match s.ctors.lookup c with
        | none => args.anyM (tyHoldsVar visiting id)
        | some sig => (sig.fieldsAt args).anyM (tyHoldsVar (name :: visiting) id)

/-- Require that values of a type may be used more than once. -/
def mustDup (t : Ty) (why : String) : M Unit :=
  modify fun s => { s with dups := s.dups.push (t, s.pos ++ why) }

/-- The declared type, if any, that makes a type one whose values are used
only once. Only to say why. -/
partial def onceBy (visiting : List String) (t : Ty) : M (Option String) := do
  match ← find t with
  | .tuple args => args.findSomeM? (onceBy visiting)
  | .con name args => do
    if let some (_, once) := (← get).useDecls.lookup name then
      if once then return some name
    if let some n ← args.findSomeM? (onceBy visiting) then return some n
    if visiting.contains name then return none
    match (← get).types.lookup name with
    | none => pure none
    | some decl =>
      decl.ctors.findSomeM? fun c => do
        match (← get).ctors.lookup c with
        | none => pure none
        | some sig =>
          (sig.fieldsAt args).findSomeM?
            (onceBy (name :: visiting))
  | _ => pure none

/-- A type whose values have a `drop` of their own to run, or hold one that
has: the name of the first such type found. A callable holds what it has
taken hold of. -/
partial def tyHasDrop (visiting : List String) (t : Ty) : M (Option String) := do
  match ← find t with
  | .tuple args => args.findSomeM? (tyHasDrop visiting)
  | .fn _ _ _ _ cap => do
    let root ← findCap cap
    if (← get).seen.contains root then return none
    modify fun s => { s with seen := root :: s.seen }
    for (src, what) in (← get).capEdges do
      if (← findCap src) == root then
        if let .ty held := what then
          if let some name ← tyHasDrop visiting held then return some name
    return none
  | .con name args => do
    if (← get).kimpls.any (fun I => I.trait == "Drop" && I.head == name) then
      return some (bareName name)
    if let some w ← args.findSomeM? (tyHasDrop visiting) then return some w
    if visiting.contains name then return none
    match (← get).types.lookup name with
    | none => pure none
    | some decl =>
      decl.ctors.findSomeM? fun c => do
        match (← get).ctors.lookup c with
        | none => pure none
        | some sig => (sig.fieldsAt args).findSomeM? (tyHasDrop (name :: visiting))
  | _ => pure none

def checkDups (dups : Array (Ty × String)) : M Unit := do
  for (t, why) in dups do
    modify fun s => { s with seen := [] }
    if ← tyOwnsOnce [] t then
      if let some name ← onceBy [] t then
        throw s!"{why}, but a `{name}` can be used only once"
      -- A value with a `drop` to run is not copied: each copy would run it.
      -- (The module that declares the type may read one through a reference,
      -- as it may take one apart: its `drop` does, to see what to do.)
      modify fun s => { s with seen := [] }
      if let some name ← tyHasDrop [] t then
        let s ← get
        let through := (why.splitOn "reading through a reference").length > 1
        let home := s.kimpls.any fun I =>
          I.trait == "Drop" && bareName I.head == name
            && s.modules.homes.lookup s.owner == some ("::".intercalate ((I.head.splitOn "::").dropLast))
        if through && home then continue
        throw s!"{why}, but a `{name}` has a `drop`, which would then run once for each"
      throw s!"{why}, but a value that holds a resumption can be used only once"

/-- What a variable gives away is read out of it by the machine, which is a
copy: fine for a value that is counted as used once here and can be copied
there, and not for one that holds a resumption. -/
def checkGivenReads : M Unit := do
  let reads := (← get).givenReads
  modify fun s => { s with givenReads := #[] }
  for (t, why) in reads do
    modify fun s => { s with seen := [] }
    if ← tyOwnsOnce [] t then
      if (← onceBy [] t).isNone then
        modify fun s => { s with seen := [] }
        if (← tyHasDrop [] t).isNone then
          throw s!"{why}, but a value that holds a resumption can be used only once"

end Glorious.Check
