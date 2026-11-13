import Glorious.Check.Borrows

namespace Glorious.Check

open Syntax

mutual

partial def inferExpr (scope : Scope) (amb : Row) : Expr → M Ty
  | .int _ => pure .int
  | .name q x => do
    match ← resolveName scope q x with
    | .local (.val t _) => lend scope x t
    | .local (.cell t brand) => do
      -- What a variable that is never changed holds can be given away:
      -- that is counted as a use of the value, as a name's is.
      if (← get).movedCells.contains brand then
        modify fun s => { s with givenReads := s.givenReads.push (t, s.pos ++ readsCell x) }
        use scope (.var brand x .move)
      else
        mustDup t (readsCell x)
        use scope (.var brand x .read)
      pure t
    | .local (.label t brand) => labelType t brand
    | .local (.poly s) => instantiate s (some x)
    | .fn t bounds inGroup => do
      unless bounds.isEmpty do
        throw s!"`{x}` needs a trait of a type it is used at, so it is called where it is named: write a block that calls it"
      if ((← get).fnGroups.lookup x).isSome then
        throw s!"`{x}` gives callables one environment to share, so it is called where it is named: write a block that calls it"
      if inGroup then
        modify fun s => { s with groupUses := s.groupUses.push ⟨0, x, s.owner, s.pos⟩ }
      pure t
    | .method sig =>
      throw s!"`{x}` is a function of the trait `{sig.trait}`, so it is called where it is named: write a block that calls it"
    | .ctor sig written => do
      let (fields, result) ← instCtor sig
      unless fields.isEmpty do arityError s!"constructor `{x}`" fields.length 0
      if let some ty := written then
        unifyAt s!"`{x}` is written with a type" (← resolveType [] false (TypeExpr.ofExpr ty)) result
      pure result
    | .op _ => throw s!"operation `{x}` must be called"
    | .prim => throw s!"intrinsic `{x}` must be called"
    | .cast _ _ => throw s!"intrinsic `{x}` must be called"
    | .pack _ => throw "what an `is` found is built where it is found"
    | .host _ => throw s!"host operation `{x}` must be called"
    | .cancel => throw "`cancel` must be applied to a resumption"
    | .replace => throw "`replace` must be called"
    | .swap => throw "`swap` must be called"
    | .overwrite => throw "`overwrite` must be called"
    | .const e => inferExpr [] amb e
  | .label l =>
    match scope.lookup ("@" ++ l) with
    | some (.label t brand) => labelType t brand
    | _ => throw s!"unknown label `@{l}`"
  | .tuple es => withTemps do
    let mut ts : Array Ty := #[]
    for e in es do
      let t ← inferExpr scope amb e
      pushTemp t
      pushAnon e t
      ts := ts.push t
    pure (.tuple ts.toList)
  | .refField id uniq x path star =>
    match scope.lookup x with
    | some (.cell t brand) => do
      if star then
        throw s!"`{x}` is a mutable variable, not a reference: its field is `{x}.{path.headD ""}`"
      let (field, numbered, chosen) ← fieldAt t path
      use scope (.var brand x (if uniq then .lend else .share) numbered)
      let cap ← freshCap
      captures cap (.brand brand)
      captures cap (.loan (← freshLoan (some brand) uniq none numbered))
      modify fun s =>
        { s with fieldSites := s.fieldSites.push (id, false, t, numbered, chosen, s.owner, s.pos)
                 blockFieldCaps := s.blockFieldCaps.push (cap, s.pos) }
      pure (.ref (if uniq then .uniq else .shared) field cap)
    | some (.val t _) => do
      -- A field of what a reference points to: borrowed from the reference,
      -- which is in the way only of that field meanwhile.
      let whole ← freshTy
      let cap ← freshCap
      let how ← if uniq then pure Ty.uniq else freshTy
      match ← find t with
      | .ref _ _ _ => pure ()
      | .var _ => pure ()
      | _ =>
        if x.startsWith "%through" || x.startsWith "%given" then
          throw "what a field is borrowed of here is a value that nothing holds, not a reference: give it a `let mut` first"
        throw s!"`{x}` is not a mutable variable or a reference, so no field of it can be borrowed"
      unifyAt (if uniq then "a field is borrowed for writing through a `&mut` reference"
        else "a field is borrowed through a reference") (.ref how whole cap) t
      let (field, numbered, chosen) ← fieldAt whole path
      use scope (.through cap s!"`{x}`" uniq numbered)
      let cap' ← freshCap
      captures cap' (.loan (← freshLoan none uniq (some (cap, cap')) numbered))
      captures cap' (.ty t)
      modify fun s =>
        { s with fieldSites := s.fieldSites.push (id, true, whole, numbered, chosen, s.owner, s.pos) }
      pure (.ref (if uniq then .uniq else .shared) field cap')
    | some _ => do
      if x.startsWith "%through" || x.startsWith "%given" then
        throw "what a field is borrowed of here is a value that nothing holds, not a reference: give it a `let mut` first"
      throw s!"`{x}` is not a mutable variable or a reference, so no field of it can be borrowed"
    | none => throw s!"unknown name `{x}`"
  | .fieldOf id e name => do
    if let some field ← inferFieldOfPlace scope (.fieldOf id e name) then return field
    -- A field by number of a value whose type is not known yet is settled
    -- once the rest of the function is inferred, as `e.0` of any value is.
    if let some n := name.toNat? then
      modify fun s => { s with fieldReads := s.fieldReads.push (id, n) }
      return ← inferExpr scope amb (.proj e n)
    let subject ← inferExpr scope amb e
    modify fun s => { s with aparts := s.aparts.push (subject, s.pos) }
    let unknown := match ← find subject with
      | .var _ => true
      | _ => false
    let known ← if unknown then pure none else
      match ← fieldIndex subject name with
      | some idx => do
        match ← fieldType subject idx with
        | some t => pure (some (idx, t))
        | none => pure none
      | none => pure none
    match known with
    | some (idx, t) =>
      modify fun s => { s with fieldReads := s.fieldReads.push (id, idx) }
      -- The fields not taken are what is let go. Of a name, that is seen
      -- once every part read of it is known: one name may give several.
      let named := match e with
        | .name none x => match scope.lookup x with
          | some (.val _ bid) => some (bid, x)
          | _ => none
        | _ => none
      match named with
      | some (bid, x) =>
        modify fun s => { s with partReads := s.partReads.push (bid, x, subject, idx, name, s.pos) }
      | none =>
        match ← otherFields subject idx with
        | some rest =>
          for r in rest do
            mustDrop r "taking one field of a value lets go of the rest"
            modify fun s => { s with leftBehind := s.leftBehind.push (r, s.pos ++ "taking one field of a value lets go of the rest") }
        | none => mustDrop subject "taking one field of a value lets go of the rest"
      pure t
    | none =>
      -- Not known yet: settled once the rest of the function is inferred.
      mustDrop subject "taking one field of a value lets go of the rest"
      let t ← freshTy
      modify fun s => { s with namedReads := s.namedReads.push (subject, name, t, id, s.pos) }
      pure t
  | .proj e idx => do
    if let some field ← inferFieldOfPlace scope (.proj e idx) then return field
    let subject ← inferExpr scope amb e
    modify fun s => { s with aparts := s.aparts.push (subject, s.pos) }
    match ← fieldType subject idx with
    | some t =>
      let named := match e with
        | .name none x => match scope.lookup x with
          | some (.val _ bid) => some (bid, x)
          | _ => none
        | _ => none
      match named with
      | some (bid, x) =>
        modify fun s => { s with partReads := s.partReads.push (bid, x, subject, idx, toString idx, s.pos) }
      | none =>
        match ← otherFields subject idx with
        | some rest =>
          for r in rest do
            mustDrop r "taking one field of a value lets go of the rest"
            modify fun s => { s with leftBehind := s.leftBehind.push (r, s.pos ++ "taking one field of a value lets go of the rest") }
        | none => mustDrop subject "taking one field of a value lets go of the rest"
      pure t
    | none => do
      -- Not known yet: settle it once the rest of the function is inferred.
      mustDrop subject "taking one field of a value lets go of the rest"
      let t ← freshTy
      modify fun s => { s with projections := s.projections.push (subject, idx, t, s.pos) }
      pure t
  | .call id f args => do
    -- Whether what a reference points to was built by a constructor: the
    -- compiler's question where a pattern binds by reference. The reference
    -- is not used up, and nothing is read out of what it points to.
    if let (.name none mark, r :: _) := (f, args) then
      if mark == Syntax.ctorIsMark then
        let inner ← freshTy
        unifyAt "a pattern that binds by reference" (.ref (← freshTy) inner (← freshCap))
          (← inferPlace scope amb r)
        return .int
    -- What the clauses of such a callable ask of the values they are given,
    -- as patterns: these have to cover every case, and say what the types
    -- are. A value written `*r` is what the reference points to.
    if let .name none "%shapes" := f then
      if let some (.closure _ clauses) := args.getLast? then
        let mut tys : Array Ty := #[]
        for a in args.dropLast do
          match a with
          | .deref r =>
            let inner ← freshTy
            unifyAt "a pattern that binds by reference" (.ref (← freshTy) inner (← freshCap))
              (← inferPlace scope amb r)
            tys := tys.push inner
          | a => tys := tys.push (← inferPlace scope amb a)
        -- What a pattern lets go of is let go of by the clause, not here.
        let drops := (← get).drops
        modify fun s => { s with shapes := true }
        for c in clauses do
          let .mk pats _ := c
          let _ ← inferPats pats tys.toList
        modify fun s => { s with drops := drops, shapes := false }
        let check : Pending := ⟨(← get).pos, "the clauses of this callable do", tys.toList,
          clauses.map fun
            | .mk pats _ => pats⟩
        modify fun s => { s with pending := s.pending.push check }
      return .unit
    withTemps (inferCall scope amb f args id)
  | .tailCall id f args => do
    -- The case that cannot be: of whatever type is wanted.
    if let .name none "%never" := f then return ← freshTy
    withTemps (inferCall scope amb f args id)
  | .closure id clauses => do
    let t ← inferCallable scope [] none none clauses "the clauses of this callable do" id
    if let .fn _ _ _ _ cap := t then
      modify fun s => { s with blockCaps := s.blockCaps.push (id, cap) }
    pure t
  | .handle subject arms => inferHandle scope amb subject arms
  | .labelScope l body => do
    let t ← freshTy
    let brand ← freshBrand
    let found ← inferStmts (("@" ++ l, .label t brand) :: scope) amb body
    unifyAt s!"the result of the scope `@{l}`" t found
    checkEscape brand (jumpsAfter l) (("it is the result of the scope", t) :: scopeRoots scope) amb
    pure t
  | .ref uniq x =>
    match scope.lookup x with
    | some (.cell t brand) => do
      use scope (.var brand x (if uniq then .lend else .share))
      let cap ← freshCap
      captures cap (.brand brand)
      captures cap (.loan (← freshLoan (some brand) uniq none))
      pure (.ref (if uniq then .uniq else .shared) t cap)
    | some _ => throw s!"`{x}` is not a mutable variable, so it cannot be borrowed"
    | none => throw s!"unknown name `{x}`"
  | .reborrow uniq e => do
    -- What is borrowed from is the reference itself, not one lent from it.
    let t ← inferPlace scope amb e
    let inner ← freshTy
    let cap ← freshCap
    let how ← freshTy
    unifyAt "`&*` borrows from a reference" (.ref how inner cap) t
    let cap' ← freshCap
    if uniq then
      unifyAt "`&mut *` borrows from a `&mut` reference" (.ref .uniq inner cap) t
      use scope (.through cap (placeName e) true)
      captures cap' (.loan (← freshLoan none true (some (cap, cap'))))
      captures cap' (.ty t)
      pure (.ref .uniq inner cap')
    else
      use scope (.through cap (placeName e) false)
      captures cap' (.loan (← freshLoan none false (some (cap, cap'))))
      captures cap' (.ty t)
      pure (.ref .shared inner cap')
  | .deref e => do
    let t ← inferPlace scope amb e
    let inner ← freshTy
    let cap ← freshCap
    unifyAt "`*` reads through a reference" (.ref (← freshTy) inner cap) t
    use scope (.through cap (placeName e) false)
    mustDup inner "reading through a reference copies the value (`replace` takes it out instead)"
    pure inner

/-- A field of what a mutable variable holds, or of what a reference points
to, is read where it is: only the field is copied, and only a borrow of that
field is in the way. None if the expression is not that. -/
partial def inferFieldOfPlace (scope : Scope) (whole : Expr) : M (Option Ty) := do
  if let some (x, path) := fieldOfName whole then
    if let some (.cell t brand) := scope.lookup x then
      let (field, numbered, _) ← fieldAt t (path.map (·.1))
      noteFieldReads path numbered
      mustDup field (readsCell x)
      use scope (.var brand x .read numbered)
      return some field
    -- `p.name` where `p` is a reference: the field of what it points to.
    -- Only where the first field is read by name, which is how the
    -- elaborator is told.
    if let some (.val t _) := scope.lookup x then
      if let .ref _ inner cap ← find t then
        if let some (_, some first) := path.head? then
          let (field, numbered, _) ← fieldAt inner (path.map (·.1))
          noteFieldReads path numbered
          modify fun s => { s with derefReads := s.derefReads.push first }
          mustDup field "reading through a reference copies the value (`replace` takes it out instead)"
          use scope (.through cap s!"`{x}`" false numbered)
          return some field
  if let some (x, path) := fieldOfDeref whole then
    if let some (.val t _) := scope.lookup x then
      let inner ← freshTy
      let cap ← freshCap
      unifyAt "`*` reads through a reference" (.ref (← freshTy) inner cap) t
      let (field, numbered, _) ← fieldAt inner (path.map (·.1))
      noteFieldReads path numbered
      mustDup field "reading through a reference copies the value (`replace` takes it out instead)"
      use scope (.through cap s!"`{x}`" false numbered)
      return some field
  return none

/-- The reference that `*e` goes through. A name is the reference it stands
for, not one lent from it. -/
partial def inferPlace (scope : Scope) (amb : Row) : Expr → M Ty
  | .name none x => do
    match scope.lookup x with
    | some (.val t _) => pure t
    | _ => inferExpr scope amb (.name none x)
  | e => inferExpr scope amb e

/-- Check one argument. Gives the mismatch if it does not fit. -/
partial def checkArg (scope : Scope) (amb : Row) (what : String) (p : Ty) (a : Expr)
    (site : Option Elab.Site) : M (Option String) := do
  -- A whole number written where a type of whole numbers is wanted is of it.
  if let .int n := a then
    if let some fits ← literalAt p n then return fits.map fun e => s!"{what}: {e}"
  -- A block where what is wanted is known and is no callable: it is run
  -- there, and is its value (5.4).
  if let some (id, _) := Elab.plainBlock a then
    let wanted ← find p
    let callable := match wanted with
      | .fn _ _ _ _ _ => true
      | .var _ => true
      | _ => false
    unless callable do
      let t ← inferExpr scope amb (.call 0 a [])
      modify fun s => { s with packs := s.packs.push (id, [Syntax.nowMark]) }
      return ← fitAt scope amb what site p t
  match Elab.plainBlock a, ← find p with
  | some (id, body), .fn [input] _ _ _ _ =>
    -- A callable taking one argument is expected, and a block is written
    -- without parameters: it takes the argument without naming it. Given
    -- what an `is` found, it has the names that found.
    let pack ← match ← find input with
      | .con name _ => pure ((Syntax.packNames name).map fun names => (name, names))
      | _ => pure none
    let taken := match pack with
      | some (name, names) => Pattern.ctor name none (names.map Pattern.var)
      | none => .var "%given"
    let t ← inferCallable scope [some input] none none [.mk [taken] body]
      "the clauses of this callable do" id
    let own := match t with
      | .fn _ _ _ _ c => c
      | _ => 0
    match ← fitAt scope amb what none p t with
    | some e => pure (some e)
    | none =>
      if let some (_, names) := pack then
        modify fun s =>
          { s with packs := s.packs.push (id, names), blockCaps := s.blockCaps.push (id, own) }
        return none
      -- It is a block like any other to one that is given it unrun.
      modify fun s => { s with given := s.given.push id, blockCaps := s.blockCaps.push (id, own) }
      -- What it is given and does not name, it lets go. Given a block that
      -- was not run, it lets go of what that block held and it does not
      -- itself mention: looked at once the types are known.
      let why := "a block that does not name what it is given lets it go"
      -- The bindings the block mentions, each told from others of its name.
      let mentioned := (Elab.fvStmts [] body).filterMap fun x =>
        match scope.lookup x with
        | some (.val _ id) => some (x, id)
        | _ => none
      match ← find input with
      | .fn _ _ _ _ cap =>
        if (← get).anyMust then
          modify fun s =>
            { s with unrunGiven :=
                s.unrunGiven.push (id, cap, input, mentioned, s.pos ++ why, own) }
      | _ => mustDrop input why
      -- A callable that takes no arguments, given to a block: a block that was
      -- not run, whose environment this one can take over.
      if let .fn _ _ _ _ cap ← find input then
        modify fun s => { s with unrun := s.unrun.push (id, cap) }
      pure none
  | _, _ => do
    -- A name whose type is not known yet, where a `&mut` reference is wanted:
    -- it is one, so it is lent rather than handed over.
    if let .name none x := a then
      if let some (.val t _) := scope.lookup x then
        if let .var _ ← find t then
          if let .ref how inner _ ← find p then
            if let .con "&mut" [] ← find how then
              unify t (.ref how inner (← freshCap))
    -- `{ (x, y) => .. }` where a callable of several arguments is wanted:
    -- each clause's one tuple is the arguments (5.4).
    if let (.closure id clauses, .fn ps _ _ _ _) := (a, ← find p) then
      let spread := clauses.filterMap fun
        | .mk [.tuple parts] body => if parts.length == ps.length then some (Clause.mk parts body) else none
        | _ => none
      if ps.length ≥ 2 && !clauses.isEmpty && spread.length == clauses.length then
        let t ← inferCallable scope (ps.map some) none none spread "the clauses of this callable do" id
        if let .fn _ _ _ _ cap := t then
          modify fun s =>
            { s with blockCaps := s.blockCaps.push (id, cap)
                     packs := s.packs.push (id, [Syntax.spreadMark]) }
        return ← fitAt scope amb what site p t
    -- A callable written where one is wanted whose parameters are types of
    -- whole numbers: a whole number among its patterns is of that type.
    if let (.closure id clauses, .fn ps _ _ _ _) := (a, ← find p) then
      let arity := match clauses.head? with
        | some (.mk pats _) => pats.length
        | none => 0
      let mut annots : List (Option Ty) := []
      -- A parameter known to be of a declared type is said too, so that
      -- what the clauses do with it, a field read by name, is looked at
      -- knowing it. That is tried, and given up where it does not fit:
      -- what is given may yet be converted to what is wanted.
      let mut wider : List (Option Ty) := []
      let mut widened := false
      for q in ps do
        let declared := match ← find q with
          | .con _ _ => true
          | _ => false
        let whole := (← literalAt q 0).isSome
        annots := annots ++ [if whole then some q else none]
        wider := wider ++ [if declared || whole then some q else none]
        if declared && !whole then widened := true
      if arity == ps.length && widened then
        let saved ← get
        let tried ← try
            let t ← inferCallable scope wider none none clauses "the clauses of this callable do" id
            if let .fn _ _ _ _ cap := t then
              modify fun s => { s with blockCaps := s.blockCaps.push (id, cap) }
            pure ((← fitAt scope amb what site p t).isNone)
          catch _ => pure false
        if tried then return none
        set saved
      if arity == ps.length && annots.any (·.isSome) then
        let t ← inferCallable scope annots none none clauses "the clauses of this callable do" id
        if let .fn _ _ _ _ cap := t then
          modify fun s => { s with blockCaps := s.blockCaps.push (id, cap) }
        return ← fitAt scope amb what site p t
    fitAt scope amb what site p (← inferExpr scope amb a)

/-- Check arguments in the given order. Gives the first that does not fit. -/
partial def checkArgsIn (scope : Scope) (amb : Row) (what : String) (params : List Ty)
    (args : List Expr) (call : Nat) (order : List Nat) : M (Option (Nat × String)) := do
  for i in order do
    match params[i]?, args[i]? with
    | some p, some a =>
      let site := if call == 0 then none else some (Elab.Site.arg call i)
      if let some e ← checkArg scope amb s!"argument {i + 1} of {what}" p a site then
        return some (i, e)
      pushTemp p
      pushAnon a p
    | _, _ => pure ()
  return none

/-- Check the arguments of a call against the parameter types. An argument that
does not fit is converted by a coercion the program declares, if one applies.
If none does, the arguments are checked once more with that one first: what it
needs is then known when the others are looked at, and one of them may be what
has to be converted. -/
partial def checkArgs (scope : Scope) (amb : Row) (what : String) (params : List Ty)
    (args : List Expr) (call : Nat := 0) : M Unit := do
  unless params.length == args.length do arityError what params.length args.length
  -- Whole numbers written without a type are looked at last: by then what
  -- is wanted of them may be known from the other arguments.
  let written := fun (i : Nat) => match args[i]? with
    | some (.int _) => true
    | _ => false
  let natural := List.range args.length
  let later := natural.filter (!written ·) ++ natural.filter written
  -- (What was known before is kept only where there may be a second try: in
  -- another order, or with a coercion the program declares. Keeping it makes
  -- every table that is then written a copy of itself, which for the calls
  -- of a whole program is most of the work.)
  let again := later != natural || !(← get).coercing.isEmpty
  let saved ← if again then some <$> get else pure none
  let back := fun (saved : Option St) => match saved with
    | some s => set s
    | none => pure ()
  -- What does not fit so is said of the arguments in the order written.
  let order ← if later == natural then pure natural else
    match ← checkArgsIn scope amb what params args call later with
    | none => return
    | some _ => do
      back saved
      pure natural
  match ← checkArgsIn scope amb what params args call order with
  | none => pure ()
  | some (i, e) =>
    back saved
    if (← get).coercing.isEmpty then throw e
    match ← checkArgsIn scope amb what params args call (i :: order.erase i) with
    | none => pure ()
    | some _ =>
      back saved
      throw e

/-- Apply a callee of a given type in the ambient effects. -/
partial def applyTy (scope : Scope) (amb : Row) (what : String) (callee : Ty) (args : List Expr)
    (call : Nat := 0) : M Ty := do
  abandons (← get).anon what call
  pushTemp callee
  -- A callable for every lifetime is called at lifetimes of this call's own.
  let (callee, _) ← openRanked callee
  match ← find callee with
  | .fn ps r effs tail _ => do
    checkArgs scope amb what ps args call
    if call != 0 && (← get).anyMust then
      let row ← flattenRow ⟨effs, tail⟩
      let silent ← match row.effs.isEmpty, row.tail with
        | true, none => pure true
        | true, some ρ => do
          if (← get).instRows.contains ρ then
            pure !((← ps.mapM zonk).flatMap freeRows).contains ρ
          else pure false
        | false, _ => pure false
      modify fun s => { s with calls := s.calls.push (call, callee, silent) }
    use scope (.call what (callee :: ps))
    includeRow ⟨effs, tail⟩ amb what
    pure r
  | t => do
    let mut argTys : Array Ty := #[]
    for a in args do
      let ty ← inferExpr scope amb a
      pushTemp ty
      argTys := argTys.push ty
    let r ← freshTy
    let row ← freshRow
    unifyAt s!"{what} is called with {arguments args.length}"
      (.func argTys.toList r row (← freshCap)) t
    use scope (.call what (callee :: argTys.toList))
    includeRow row amb what
    pure r

partial def inferCall (scope : Scope) (amb : Row) (f : Expr) (args : List Expr)
    (call : Nat := 0) : M Ty := do
  -- `let x: Type = value`: the value is made that type.
  if let (.name none mark, [operand]) := (f, args) then
    if mark == Syntax.moveMark then
      -- `move x`: the value of `x`. That `x` is not used after is looked at
      -- where its statement is.
      match operand with
      | .name none x =>
        match scope.lookup x with
        | some (.cell _ _) =>
          throw s!"`move {x}`: `{x}` is a mutable variable, which holds a value while it is there; `replace({x}, value)` takes what it holds and leaves another"
        | _ => return ← inferExpr scope amb operand
      | .deref _ =>
        throw "`move *reference` would leave the reference pointing at nothing until it is written again, and that is not followed: `replace(reference, value)` takes what is there and leaves another"
      | _ => return ← inferExpr scope amb operand
  if let (.name none mark, [value, ty]) := (f, args) then
    if mark == Syntax.instMark then
      -- `f<A, B>(..)`: the call, with the types written kept for when the
      -- function called is found.
      let tys ← match TypeExpr.ofExpr ty with
        | .tuple tys => (tys.filter fun
            | .name l [] => !l.startsWith "'"
            | _ => true).mapM (resolveType (← get).rigidParams false)
        | _ => pure []
      modify fun s => { s with instWith := some tys }
      let t ← inferExpr scope amb value
      if (← get).instWith.isSome then
        modify fun s => { s with instWith := none }
        throw "types are written, `f<A, B>(..)`, for a function of a module that has type parameters; what is called here is not one"
      return t
    if mark == Syntax.ascribeMark then
      let expected ← resolveType (← get).rigidParams false (TypeExpr.ofExpr ty)
      if let .int n := value then
        match ← literalAt expected n with
        | some none => return expected
        | some (some why) => throw why
        | none => pure ()
      match ← fitAt scope amb "the value of a `let` with a type" none expected
          (← inferExpr scope amb value) with
      | none => return expected
      | some e => throw e
  match f with
  | .name q x =>
    match ← resolveName scope q x with
    | .ctor sig written => do
      let (fields, result) ← instCtor sig
      -- A name given to the constructor with a type: built at that type.
      if let some ty := written then
        let said ← resolveType [] false (TypeExpr.ofExpr ty)
        unifyAt s!"`{x}` is written with a type" said (.fn fields result [] none (← freshCap))
      checkArgs scope amb s!"constructor `{x}`" fields args call
      -- What the type's declaration asks of its parameters.
      if let .con owner targs := result then
        if let some asked := (← get).typeBounds.lookup owner then
          -- (Asked, and not handed over: under a number no call has.)
          if call != 0 then
            needBounds (100000000000000000 + call) (asked.filterMap fun (tr, i) => targs[i]?.map (tr, ·))
      pure result
    | .op sig => do
      -- (An operation declared `[1, 1]` comes back: its resumption is resumed.)
      unless sig.must && sig.result.isSome do abandons (← get).anon s!"operation `{x}`"
      let decl := ((← get).effects.lookup sig.effect).getD ⟨[], [], []⟩
      let inst ← decl.fresh
      let (payload, result) := instOp sig inst
      try unifyRow amb ⟨[(sig.effect, inst)], some (← freshRowVar)⟩
      catch e => throw s!"operation `{x}` cannot be performed here: {e}"
      -- What the effect's declaration asks of its parameters.
      if let some asked := (← get).typeBounds.lookup sig.effect then
        if call != 0 then
          needBounds (100000000000000000 + call) (asked.filterMap fun (tr, i) => inst[i]?.map (tr, ·))
      checkArgs scope amb s!"operation `{x}`" payload args call
      -- The handler may run a callable it is given, there and then.
      use scope (.call s!"operation `{x}`" payload)
      match result with
      | some r => pure r
      | none => freshTy
    | .prim => do
      -- The intrinsics of arrays, of whatever their elements are. Reading a
      -- place and putting another value at one let go of what is not given
      -- back.
      let named := ((← get).arrayType).getD "Array"
      let array := fun (t : Ty) => Ty.con named [t]
      let t ← freshTy
      match x with
      | "arr_new" =>
        checkArgs scope amb s!"intrinsic `{x}`" [] args call
        pure (array t)
      | "arr_at" =>
        -- The reference to a place of an array, from a reference to the
        -- array: the same kind of reference, borrowing from the same things.
        let how ← freshTy
        let cap ← freshCap
        checkArgs scope amb s!"intrinsic `{x}`" [.ref how (array t) cap, .int] args call
        pure (.ref how t cap)
      | "arr_len_at" =>
        checkArgs scope amb s!"intrinsic `{x}`" [.ref (← freshTy) (array t) (← freshCap)] args call
        pure .int
      | "arr_get" =>
        checkArgs scope amb s!"intrinsic `{x}`" [array t, .int] args call
        mustDrop t "reading a place of an array lets go of the rest of it"
        pure t
      | "arr_set" =>
        checkArgs scope amb s!"intrinsic `{x}`" [array t, .int, t] args call
        mustDrop t "putting a value at a place of an array lets go of what was there"
        pure (array t)
      | "arr_len" =>
        checkArgs scope amb s!"intrinsic `{x}`" [array t, .int] args call
        pure .int
      | "arr_push" =>
        checkArgs scope amb s!"intrinsic `{x}`" [array t, t] args call
        pure (array t)
      | "arr_pop" =>
        checkArgs scope amb s!"intrinsic `{x}`" [array t, .int] args call
        pure (.tuple [array t, t])
      | _ =>
        checkArgs scope amb s!"intrinsic `{x}`" [.int, .int] args call
        pure .int
    | .pack name => do
      let ts ← args.mapM fun _ => freshTy
      checkArgs scope amb "what an `is` found" ts args call
      pure (.con name ts)
    | .cast scalar into => do
      checkArgs scope amb s!"intrinsic `{x}`" [if into then .int else .con scalar []] args call
      pure (if into then .con scalar [] else .int)
    | .host id => do
      if id ≥ 2 then
        let s ← get
        unless s.unsafeBlock || s.unsafeFns.contains s.owner do
          throw s!"`{x}` is unsafe: it can be named only in `unsafe \{ .. }` or in an `unsafe fn`"
      if id == 0 then
        checkArgs scope amb s!"`{x}`" [← freshTy] args call
        pure .unit
      else if id == 2 then
        -- A foreign function's name, how many bits it gives, and what it is given.
        checkArgs scope amb s!"`{x}`" (args.map fun _ => Ty.int) args call
        pure .int
      else if id == 3 then
        checkArgs scope amb s!"`{x}`" [.con "usize" [], .int] args call
        pure .int
      else if id == 4 then
        checkArgs scope amb s!"`{x}`" [.con "usize" [], .int, .int] args call
        pure .unit
      else if id == 5 then
        -- The callable is given to C for as long as the program runs. What
        -- it takes and gives is C's to get right: whole numbers and
        -- addresses, as `usize`.
        -- An effect cannot pass C, so the callable performs none.
        let arity ← match args with
          | [_, .int n] => pure n.toNat
          | _ => throw s!"`{x}` is given a callable and how many whole numbers C gives it, written out: `{x}(f, 2)`"
        unless arity ≤ 5 do throw s!"`{x}`: C gives a callable at most five whole numbers"
        let given := Ty.func (List.replicate arity (.con "usize" [])) .int ⟨[], none⟩ (← freshCap)
        checkArgs scope amb s!"`{x}`" [given, .int] args call
        pure (.con "usize" [])
      else
        checkArgs scope amb s!"`{x}`" [] args call
        pure (.tuple [.int, .int])
    | .cancel => do
      -- Giving up a callable: a resumption, or anything else applied to one value.
      let row ← freshRow
      let given := Ty.func [← freshTy] (← freshTy) row (← freshCap)
      checkArgs scope amb "`cancel`" [given] args call
      -- A resumption of an operation declared `[1, 1]` is resumed: giving
      -- it up is letting it go.
      mustDrop given "`cancel` lets go of what it is given"
      -- A cleanup of a cancelled computation may jump to a label inside it, and
      -- the computation then runs on from there, where it is being cancelled.
      -- So what it may perform must be handled here, as if it were called.
      includeRow row amb "`cancel`"
      pure .unit
    | .replace => do
      let t ← freshTy
      let cap ← freshCap
      checkArgs scope amb "`replace`" [.ref .uniq t cap, t] args call
      use scope (.through cap "the reference given to `replace`" true)
      pure t
    | .swap => do
      -- What two references point to, exchanged: nothing is asked of the
      -- type, since nothing is copied or let go.
      let t ← freshTy
      let first ← freshCap
      let second ← freshCap
      checkArgs scope amb "`swap`" [.ref .uniq t first, .ref .uniq t second] args call
      use scope (.through first "the first reference given to `swap`" true)
      use scope (.through second "the second reference given to `swap`" true)
      pure .unit
    | .overwrite => do
      -- A value put where a reference points, with what was there neither
      -- given back nor destroyed. Nothing is asked of the type, which is
      -- why it is unsafe: whoever writes it says that nothing is there.
      let s ← get
      unless s.unsafeBlock || s.unsafeFns.contains s.owner do
        throw "`overwrite` is unsafe: what the reference pointed to is neither given back nor destroyed. It can be named only in `unsafe { .. }` or in an `unsafe fn`; `replace` gives what was there back"
      let t ← freshTy
      let cap ← freshCap
      checkArgs scope amb "`overwrite`" [.ref .uniq t cap, t] args call
      use scope (.through cap "the reference given to `overwrite`" true)
      pure .unit
    | .local (.val t _) => applyTy scope amb s!"`{x}`" t args call
    | .local (.cell t brand) => do
      mustDup t (readsCell x)
      use scope (.var brand x .read)
      applyTy scope amb s!"`{x}`" t args call
    | .local (.label t brand) => do
      applyTy scope amb s!"the label `{x}`" (← labelType t brand) args call
    | .local (.poly s) => do
      applyTy scope amb s!"`{x}`" (← instantiate s (some x)) args call
    | .fn t bounds inGroup => do
      -- Callables that share an environment: the first holds it, and each
      -- other is built over what the first captured, to run in its place.
      for group in ((← get).fnGroups.lookup x).getD [] do
        let holder := (group.head?.bind fun i => args[i]?).bind Elab.plainBlock
        let mut named : List Nat := []
        for i in group.drop 1 do
          match args[i]? with
          | some (.name none _) => named := named ++ [i]
          | some a =>
            match Elab.plainBlock a with
            | some (id, _) =>
              modify fun s => { s with given := s.given.push id }
              if let some (owner, _) := holder then
                modify fun s => { s with envLinks := s.envLinks.push (id, owner) }
            | none =>
              throw s!"argument {i + 1} of `{x}` shares an environment with another: write a block there, or a name"
          | none => pure ()
        unless named.isEmpty do
          if call == 0 then throw s!"`{x}` is called where the checker has no name for the call; this is a compiler defect"
          modify fun s => { s with envWraps := s.envWraps.push (call, named) }
      let before := (← get).blockCaps.size
      let r ← applyTy scope amb s!"`{x}`" t args call
      -- One of them is certainly called, and the rest let go: what has to be
      -- used must then be held by every one, and nothing but a block may
      -- hold such a thing.
      if (← get).envMust.contains x then
        for group in ((← get).fnGroups.lookup x).getD [] do
          let mut caps : List Nat := []
          for i in group do
            match args[i]? with
            | some a =>
              match Elab.plainBlock a with
              | some (id, _) =>
                let made := ((← get).blockCaps.toList.drop before).filter (·.1 == id)
                caps := caps ++ made.map (·.2)
              | none =>
                if let .fn ps _ _ _ _ ← find t then
                  if let some p := ps[i]? then
                    mustDrop p s!"argument {i + 1} of `{x}` may not be the one that is called"
            | none => pure ()
          modify fun s => { s with envHeld := s.envHeld.push (s.pos, x, caps) }
      needBounds call bounds
      if inGroup then
        modify fun s => { s with groupUses := s.groupUses.push ⟨call, x, s.owner, s.pos⟩ }
      pure r
    | .method sig => do
      if sig.trait == "Drop" then
        throw s!"`{x}` is run when what holds a value ends; a program does not call it"
      -- A trait's function at the type it is used at, which must have the trait.
      let self ← freshTy
      -- The trait's own arguments are found from how the function is used,
      -- and so is what each type it leaves to an implementation is.
      let targs ← sig.tparams.mapM fun _ => freshTy
      -- `<Type as Trait<A>>::f(..)`: the type, and the trait's arguments,
      -- are the ones written.
      if let some written := (← get).instWith then
        modify fun s => { s with instWith := none }
        if written.length > 1 + targs.length then
          throw s!"`{x}` is a function of `{Syntax.lastSegment sig.trait}`, which takes {targs.length} argument{if targs.length == 1 then "" else "s"}"
        for (w, t) in written.zip (self :: targs) do
          unifyAt s!"the type written for `{x}`" t w
      -- (A row it leaves to an implementation is asked for as the type of a
      -- callable that performs it.)
      let mut rm : List (Nat × Nat) := []
      let mut found : List Ty := []
      for (name, _) in sig.assocs do
        match sig.rowAssocs.lookup name with
        | some k =>
          let k' ← freshRowVar
          rm := (k, k') :: rm
          found := found ++ [.fn [] .unit [] (some k') (← freshCap)]
        | none => found := found ++ [← freshTy]
      let tm := (sig.self, self) :: sig.tparams.zip targs ++ (sig.assocs.map (·.2)).zip found
      let subject := if targs.isEmpty then self else Ty.tuple (self :: targs)
      for ((name, _), a) in sig.assocs.zip found do
        modify fun s =>
          { s with assocUses := s.assocUses.push (sig.trait, subject, name, a, s.owner, s.pos) }
      let row : Row :=
        ⟨sig.row.effs.map fun (e, args) => (e, args.map (subst tm rm [])),
          sig.row.tail.map fun k => (rm.lookup k).getD k⟩
      let callee ← freshenCaps
        (.func (sig.params.map (subst tm rm [])) (subst tm rm [] sig.ret) row (← freshCap))
      let r ← applyTy scope amb s!"`{x}`" callee args call
      needBounds call [(sig.trait, subject)]
      modify fun s => { s with methodCalls := s.methodCalls.push (call, sig.index) }
      pure r
    | .const e => do
      applyTy scope amb s!"`{x}`" (← inferExpr [] amb e) args call
  | .label l => do
    applyTy scope amb s!"the label `@{l}`" (← inferExpr scope amb f) args call
  | _ => do
    applyTy scope amb "this callee" (← inferExpr scope amb f) args call

/-- The type of a block: that of its last expression, or unit. -/
partial def inferStmts (scope : Scope) (amb : Row) (stmts : List Stmt)
    (want : Option (Ty × Option Elab.Site) := none) : M Ty := do
  -- The value a body ends with is made the type wanted of it where it is
  -- computed, inside whatever the body's statements have put around it.
  let finish := fun (t : Ty) (convertible : Bool) => (do
    match want with
    | none => pure t
    | some (expected, site) =>
      let site := if convertible then site else none
      let before := (← get).givingBack
      modify fun s => { s with givingBack := true }
      let fitted ← fitAt scope amb "the result of a clause" site expected t
      modify fun s => { s with givingBack := before }
      match fitted with
      | none => pure expected
      | some e => throw (resultMark ++ e) : M Ty)
  match stmts with
  | [] => finish .unit false
  | .located line col s :: rest => do
    modify fun st => { st with pos := s!"{line}:{col}: ", at_ := (line, col) }
    -- What `move x` hands on is not there for the statements after.
    for x in Elab.movedStmt s do
      if (Elab.fvStmts [] rest).contains x then
        throw (positioned line col s!"`{x}` is used after `move {x}` handed it on")
    try inferStmts scope amb (s :: rest) want
    catch e => throw (positioned line col e)
  | .expr (.name none "%unsafe") :: rest => do
    -- What follows in this block may name what is unsafe.
    let before := (← get).unsafeBlock
    modify fun s => { s with unsafeBlock := true }
    let t ← inferStmts scope amb rest want
    modify fun s => { s with unsafeBlock := before }
    pure t
  | [.expr e] => do
    -- A whole number a body ends with is of the type wanted of the body.
    if let (.int n, some (expected, _)) := (e, want) then
      match ← literalAt expected n with
      | some none => return expected
      | some (some why) => throw (resultMark ++ s!"the result of a clause: {why}")
      | none => pure ()
    finish (← inferExpr scope amb e) true
  | .expr e :: rest => do
    let t ← withLater (Elab.fvStmts [] rest) (inferExpr scope amb e)
    mustDrop t "the value of a statement is let go"
    -- If it is one to destroy, that happens here.
    modify fun s =>
      { s with dropCands := s.dropCands.push (⟨s.owner, s.at_.1, s.at_.2, Elab.stmtValue, false⟩, t, s.pos) }
    inferStmts scope amb rest want
  | .let_ (.var x) (.closure id clauses) :: rest => do
    let t ← withLater (Elab.fvStmts [x] rest) (inferExpr scope amb (.closure id clauses))
    if (← resolveCtor x none).isSome || ((← get).aliases.lookup x).isSome then
      let binds ← inferPat (.var x) t
      inferStmts (binds ++ scope) amb rest want
    else
      -- A callable bound by `let` is a value, so it can be used at several types.
      -- Everything its surroundings already depend on stays fixed.
      let s ← get
      let mut keep : List Ty := [.func [] .unit amb (← freshCap)]
      for (_, b) in scope do
        keep := (match b with
          | .val t _ => t
          | .cell t _ => t
          | .label t _ => t
          | .poly p => p.ty) :: keep
      for (_, t) in s.group do
        keep := t :: keep
      for (subject, _, result, _) in s.projections do
        keep := subject :: result :: keep
      -- Decide the effects of what the callable calls, where nothing outside
      -- depends on them; calls still undecided keep their effects fixed.
      let mut fixedRows : List Nat := []
      for k in keep do
        fixedRows := fixedRows ++ freeRows (← zonk k)
      settleRows (some fun ρ => !fixedRows.contains ρ) false
      for (callee, permitted, _) in (← get).rowIncl do
        keep := .func [] .unit callee (← freshCap) :: .func [] .unit permitted (← freshCap) :: keep
      let scheme ← generalize t keep (top := false)
      let here := (← get).pos
      let result ← inferStmts ((x, .poly scheme) :: scope) amb rest want
      checkUses here scope [(x, .poly scheme)] rest
      pure result
  | .let_ pat value :: rest => do
    let (at_, pos) := ((← get).at_, (← get).pos)
    let t ← withLater (Elab.fvStmts (Elab.patVars pat) rest) (inferExpr scope amb value)
    -- A value given a name that nothing then uses is owned by the name: if it
    -- is one to destroy, that happens when the block ends.
    if let .var x := pat then
      unless (Elab.fvStmts [] rest).contains x || (← resolveCtor x none).isSome
          || ((← get).aliases.lookup x).isSome do
        modify fun s =>
          { s with dropCands := s.dropCands.push (⟨s.owner, at_.1, at_.2, x, false⟩, t, pos) }
    let binds ← inferPat pat t
    if let .var _ := pat then
      for (_, b) in binds do
        if let .val _ bid := b then
          modify fun s => { s with bindSites := (bid, at_.1, at_.2) :: s.bindSites }
    let check : Pending := ⟨(← get).pos, "the pattern of this `let` does", [t], [[pat]]⟩
    modify fun s => { s with pending := s.pending.push check }
    let here := (← get).pos
    let result ← inferStmts (binds ++ scope) amb rest want
    checkUses here scope binds rest
    pure result
  | .letMut x value :: rest => do
    let (at_, pos) := ((← get).at_, (← get).pos)
    let t ← withLater (Elab.fvStmts [x] rest) (inferExpr scope amb value)
    -- The variable lives until the end of this block: nothing that can reach
    -- it may be left over afterwards.
    let brand ← freshBrand
    -- A variable that is never assigned, borrowed for writing or bound
    -- again holds one value for as long as it lasts. Where that value is
    -- also used as it is, outside any callable, the variable is a name
    -- that can be borrowed: the value is given away by the use, counted as
    -- a name's uses are, and is not the variable's to destroy.
    -- (And is not borrowed again once it has been.)
    let given := Syntax.givenAway x rest
    modify fun s =>
      { s with
        cells := s.cells.push (brand, x, t)
        movedCells := if given then brand :: s.movedCells else s.movedCells
        -- A variable owns what it holds. One that gives it away owns it
        -- where it has not: whether that is anywhere is seen once the
        -- uses are counted, and its cleanup is put in then.
        dropCands := if given then s.dropCands
          else s.dropCands.push (⟨s.owner, at_.1, at_.2, x, false⟩, t, pos) }
    -- Nothing says the variable is empty when its block ends: what it holds
    -- then is let go. Unless the very next statement is a cleanup that takes
    -- it out, leaving something that holds nothing: that runs last of all
    -- that the block does to the variable, however the block is left.
    let finalised ← match rest.head?.map Elab.unlocated with
      | some (.defer e) =>
        match takesOut x e with
        | some put => holdsNothing put
        | none => pure false
      | _ => pure false
    unless finalised || given do
      mustDrop t s!"the mutable variable `{x}` lets go of what it holds when its block ends (a `defer` straight after it can take that out with `replace`)"
    let here := (← get).pos
    if given then
      modify fun s =>
        { s with
          flagged := here :: s.flagged
          givenSites := (here, ⟨s.owner, at_.1, at_.2, Syntax.givenSite x, false⟩, t, pos) :: s.givenSites }
    let result ← inferStmts ((x, .cell t brand) :: scope) amb rest want
    if given then checkUses here scope [(x, .val t brand)] (Syntax.lessPartsStmts x rest)
    checkEscape brand s!"`{x}` could be used after its block has ended"
      (("something that uses it is the block's result", result) :: scopeRoots scope) amb
    pure result
  | .assign target value :: rest => do
    withLater (Elab.fvStmts [] rest) do
      -- The value is computed first, and then the place is written.
      let (expected, written) ← match target with
        | .name none x =>
          match scope.lookup x with
          | some (.cell t brand) => do
            -- What the variable held is destroyed.
            modify fun s =>
              { s with dropCands :=
                  s.dropCands.push (⟨s.owner, s.at_.1, s.at_.2, x, true⟩, t, s.pos) }
            mustDrop t s!"assigning to `{x}` lets go of what it holds (`replace` takes it out instead)"
            pure (t, UseKind.var brand x .write)
          | some _ => throw s!"`{x}` is not a mutable variable"
          | none => throw s!"unknown name `{x}`"
        | .deref e => do
          let inner ← freshTy
          let cap ← freshCap
          unifyAt "`*` assigns through a reference" (.ref .uniq inner cap)
            (← inferPlace scope amb e)
          mustDrop inner "assigning through a reference lets go of what was there"
          pure (inner, UseKind.through cap (placeName e) true)
        | _ => throw "only a mutable variable or `*reference` can be assigned"
      let whole ← match value with
        | .int n => literalAt expected n
        | _ => pure none
      match whole with
      | some none => pure ()
      | some (some why) => throw s!"the assigned value: {why}"
      | none => unifyAt "the assigned value" expected (← inferExpr scope amb value)
      use scope written
    inferStmts scope amb rest want
  | .defer e :: rest => do
    -- A cleanup performs no effects: it may run while its surroundings are
    -- being left, when no handler should be asked to do anything.
    try
      let t ← withLater (Elab.fvStmts [] rest) (inferExpr scope ⟨[], none⟩ e)
      mustDrop t "what a `defer` gives is let go"
    catch err => throw s!"a `defer` cannot perform effects: {err}"
    -- It runs when the rest is left, so what it mentions is still to be used
    -- throughout the rest.
    withLater (Elab.fvExpr [] e) (inferStmts scope amb rest want)

/-- Check a pattern against a type; the names it binds. -/
partial def inferPat (p : Pattern) (t : Ty) : M Scope := do
  -- (Where patterns only say which cases are taken, one that asks something
  -- of a value is met by a reference to one: the clauses reach through it.)
  if (← get).shapes then
    let through := match p with
      | .wild => false
      | .var _ => false
      | _ => true
    if through then
      if let .ref _ inner _ ← find t then return ← inferPat p inner
  match p with
  | .wild => do
    mustDrop t "`_` lets go of a value"
    -- If it is one to destroy, that happens when its clause is done.
    if let some place := (← get).wildAt then
      modify fun s =>
        { s with
          wildCount := s.wildCount + 1
          dropCands := s.dropCands.push
            (⟨s.owner, place.1, place.2, Elab.wildName s.wildCount, false⟩, t, s.pos) }
    pure []
  | .int n => do
    -- A whole number is of the type wanted of it, if that is one of whole
    -- numbers; else an `Int`.
    match ← literalAt t n with
    | some none => pure []
    | some (some e) => throw e
    | none =>
      unifyAt "an integer pattern" .int t
      pure []
  | .tuple ps => do
    let ts ← ps.mapM fun _ => freshTy
    unifyAt "a tuple pattern" (.tuple ts) t
    inferPats ps ts
  | .var x => do
    match ← resolveCtor x none with
    | some (_, sig) => do
      let (fields, result) ← instCtor sig
      unless fields.isEmpty do arityError s!"constructor `{x}`" fields.length 0
      unifyAt s!"the pattern `{x}`" result t
      pure []
    | none =>
      match (← get).aliases.lookup x with
      | some e => do inferPat (← exprToPat e) t
      | none => do
        let id ← freshBrand
        pure [(x, .val t id)]
  | .ctor x q ps => do
    if let some (scalar, _) := Syntax.scalarPattern (.ctor x q ps) then
      unifyAt s!"a pattern of type `{scalar}`" (.con scalar []) t
      return []
    if (Syntax.packNames x).isSome then
      let ts ← ps.mapM fun _ => freshTy
      unifyAt "what an `is` found" (.con x ts) t
      return ← inferPats ps ts
    match ← resolveCtor x q with
    | some (_, sig) => do
      let (fields, result) ← instCtor sig
      unless fields.length == ps.length do arityError s!"constructor `{x}`" fields.length ps.length
      unifyAt s!"the pattern `{x}(..)`" result t
      -- A type with `Drop` is taken apart only by the module that declares
      -- it: anywhere else its function would not have run.
      if let .con n _ := result then
        let s ← get
        if !ps.isEmpty && s.kimpls.any (fun I => I.trait == "Drop" && I.head == n) then
          if let some here := s.modules.homes.lookup s.owner then
            let home := "::".intercalate ((n.splitOn "::").dropLast)
            unless here == home do
              throw s!"`{Syntax.lastSegment n}` has `Drop`, so only the module that declares it can take one apart with a pattern: what `drop` does would not be done"
      inferPats ps fields
    | none => throw s!"unknown constructor `{x}` in a pattern"

/-- Read the patterns of a clause whose body is `body`. What the clause is
given under a name and does not mention is the name's, and what a `_` takes is
let go: if either is one to destroy, that happens when the clause is done. The
place it is known by is the clause's first statement. -/
partial def clauseGiven (body : List Stmt) (patterns : M Scope) : M Scope := do
  let first := Elab.firstPlace body
  modify fun s => { s with wildAt := some first, wildCount := 0 }
  let binds ← patterns
  modify fun s => { s with wildAt := none }
  let mentioned := Elab.fvStmts [] body
  for (x, b) in binds do
    if let .val t bid := b then
      modify fun s => { s with bindSites := (bid, first.1, first.2) :: s.bindSites }
      unless mentioned.contains x || x.startsWith "%" do
        modify fun s =>
          { s with dropCands := s.dropCands.push (⟨s.owner, first.1, first.2, x, false⟩, t, s.pos) }
  pure binds

partial def inferPats (ps : List Pattern) (ts : List Ty) : M Scope := do
  let mut out : Scope := []
  for (p, t) in ps.zip ts do
    out := (← inferPat p t) ++ out
  pure out

/-- The type of a callable given by clauses. Parameter and result annotations
are checked if present; the clauses must cover every argument. -/
partial def inferCallable (scope : Scope) (annots : List (Option Ty)) (ret : Option Ty)
    (self : Option String) (clauses : List Clause) (what : String) (id : Nat := 0) : M Ty := do
  let arity := match clauses with
    | .mk pats _ :: _ => pats.length
    | [] => 0
  let params ← (List.range arity).mapM fun i => do
    match annots[i]? with
    | some (some t) => pure t
    | _ => freshTy
  let result ← match ret with
    | some t => pure t
    | none => freshTy
  let row ← freshRow
  -- The body runs when the callable is called, perhaps again and again: what
  -- it mentions from outside is still to be used wherever the body has got to,
  -- and the values the expression around it has computed are not its concern.
  let outerLater := (← get).later
  let outerTemps := (← get).temps
  let outerAnon := (← get).anon
  -- A callable that uses a variable's value is where the value may go, any
  -- time from here on: what is still to be used here must not be able to
  -- look at the variable.
  for x in (clauses.flatMap (Elab.fvClause [])).eraseDups do
    if let some (.cell _ brand) := scope.lookup x then
      if (← get).movedCells.contains brand then
        let u := clauses.foldl (fun u c => u.or (Syntax.nameUseClause x c)) ({} : Syntax.NameUse)
        if u.valued || u.valuedInside then
          modify fun s =>
            { s with heldMoves := s.heldMoves.push ⟨s.owner, s.pos, .var brand x .move [], scope, s.later, s.temps⟩ }
  modify fun s =>
    { s with later := (clauses.flatMap (Elab.fvClause [])).eraseDups, temps := [], anon := [] }
  -- What the callable captures from the scope it is written in.
  let cap ← freshCap
  captureAll scope cap (clauses.flatMap (Elab.fvClause [])) (fun x => clauses.any (assignsClause x))
    (fun x => clauses.any fun c =>
      let u := Syntax.nameUseClause x c
      u.valued || u.valuedInside)
  let loansBefore := (← get).loans.size
  -- What `unsafe { .. }` allows is allowed where it is written, not in a
  -- callable written inside it, which runs later.
  let unsafeBefore := (← get).unsafeBlock
  modify fun s => { s with unsafeBlock := false }
  let fieldsBefore := (← get).blockFieldCaps.size
  let outerScope := scope
  let brand ← freshBrand
  let scope := match self with
    | some name => ("@" ++ name, Binding.label result brand) :: scope
    | none => scope
  -- Where the result of clause `j` can be converted, if this callable is one
  -- the elaborator can be told about.
  let site := fun (j : Nat) => match self with
    | some name => some (Elab.Site.fnResult name j)
    | none => if id == 0 then none else some (Elab.Site.result id j)
  let checkClause := fun (j : Nat) => (do
    match clauses[j]? with
    | none => pure none
    | some (.mk pats body) =>
      unless pats.length == arity do
        throw "the clauses of a callable take different numbers of arguments"
      let binds ← clauseGiven body (inferPats pats params)
      let names := binds.map (·.1)
      if let some x := names.find? fun x => (names.filter (· == x)).length > 1 then
        throw s!"`{x}` is bound twice by the patterns of one clause"
      let here := (← get).pos
      let at_ := if (Elab.wrapResult "" body).isSome then site j else none
      let failure ← try
          (do
            let _ ← inferStmts (binds ++ scope) row body (some (result, at_))
            pure none)
        catch e =>
          if (e.splitOn resultMark).length > 1 then pure (some (e.replace resultMark ""))
          else throw e
      match failure with
      | some e => pure (some e)
      | none =>
        -- Uses are counted in the body as it will be elaborated.
        let cs := (← get).coercions.toList
        let body := if cs.isEmpty then body else
          match Elab.coerceClause cs ((site j).bind fun k => List.lookup k cs) (.mk pats body) with
          | .mk _ body => body
        checkUses here scope binds body
        pure none : M (Option String))
  -- As with arguments: a clause whose result does not fit is looked at first
  -- on a second attempt, so that the others can be converted to what it gives.
  let order := List.range clauses.length
  -- (Kept only where a coercion could make a second attempt worth it.)
  let saved ← if (← get).coercing.isEmpty then pure none else some <$> get
  let mut failed : Option (Nat × String) := none
  for j in order do
    if let some e ← checkClause j then
      failed := some (j, e)
      break
  if let some (j, e) := failed then
    match saved with
    | none => throw e
    | some saved =>
      set saved
      for k in j :: order.erase j do
        if (← checkClause k).isSome then
          set saved
          throw e
  let check : Pending := ⟨(← get).pos, what, params, clauses.map fun
    | .mk pats _ => pats⟩
  modify fun s => { s with pending := s.pending.push check }
  -- A function's own label returns from it, so nothing holding that label may
  -- be handed back to the caller.
  if let some name := self then
    let roots := ("it is returned from the function", result) ::
      params.map fun p => ("the caller could hold it through a parameter", p)
    checkEscape brand (jumpsAfter name) roots row
  -- A borrow of a field is a variable of the block it is made in: it cannot
  -- be what the block gives, nor be kept in something outside the block.
  let made := (← get).blockFieldCaps.extract fieldsBefore (← get).blockFieldCaps.size
  unless made.isEmpty do
    let given ← capsReached result
    for (c, pos) in made do
      if given.contains (← findCap c) then
        throw (pos ++ "a borrow of a field lasts only inside the block that makes it, and here the block gives it back: give back the whole reference, or the field's value, or borrow the field where it is used")
    for (x, b) in outerScope do
      let held := match b with
        | .val t _ => some t
        | .cell t _ => some t
        | _ => none
      if let some held := held then
        let reached ← capsReached held
        for (c, pos) in made do
          if reached.contains (← findCap c) then
            throw (pos ++ s!"a borrow of a field lasts only inside the block that makes it, and here it is kept in `{x}`, outside the block")
  -- The borrows made while it runs: a computation suspended inside it holds
  -- them.
  for id in [loansBefore:(← get).loans.size] do
    captures cap (.inner id)
  modify fun s =>
    { s with later := outerLater, temps := outerTemps, anon := outerAnon, unsafeBlock := unsafeBefore }
  pure (.func params result row cap)

/--
`handle subject { arms }`. The subject may perform the handled effects on top
of the ambient ones. An effect whose every operation has an arm that cannot
fail to match is handled completely; any other handled effect may still reach
an outer handler, so it must be permitted outside as well.
-/
partial def inferHandle (scope : Scope) (amb : Row) (subject : Expr) (arms : List Clause) :
    M Ty := do
  let s ← get
  let mut completions : Array (Pattern × List Stmt) := #[]
  let mut opArms : Array (String × OpSig × List Pattern × List Stmt) := #[]
  for arm in arms do
    match arm with
    | .mk [.ctor x q ps] body =>
      match s.ops.lookup x with
      | some sig =>
        if let some owner := q then
          unless owner == sig.effect do throw s!"`{x}` is not an operation of `{owner}`"
        opArms := opArms.push (x, sig, ps, body)
      | none => completions := completions.push (.ctor x q ps, body)
    | .mk [p] body => completions := completions.push (p, body)
    | .mk _ _ => throw "a handler arm has exactly one head pattern"
  -- One instance of each handled effect.
  let mut insts : List (String × List Ty) := []
  for e in (opArms.toList.map (·.2.1.effect)).eraseDups do
    let decl := (s.effects.lookup e).getD ⟨[], [], []⟩
    insts := insts ++ [(e, ← decl.fresh)]
  let ambFlat ← flattenRow amb
  -- An arm can run whenever the subject performs, and the subject goes on
  -- when an arm resumes it: what either mentions is still to be used
  -- throughout the other.
  let outerLater := (← get).later
  modify fun st => { st with later := Elab.fvExpr [] (.handle subject arms) ++ outerLater }
  let loansBefore := (← get).loans.size
  let subjectTy ← inferExpr scope ⟨insts ++ ambFlat.effs, ambFlat.tail⟩ subject
  -- The borrows the handled computation makes. While it is suspended in an
  -- arm, its resumption holds them: the arm must not use what they exclude.
  let suspendedLoans := (List.range (← get).loans.size).drop loansBefore
  let result ← freshTy
  if completions.isEmpty then unify result subjectTy
  else
    for (p, body) in completions do
      let binds ← clauseGiven body (inferPat p subjectTy)
      let here := (← get).pos
      unifyAt "the result of a completion clause" result
        (← inferStmts (binds ++ scope) amb body)
      checkUses here scope binds body
    let check : Pending := ⟨(← get).pos, "the completion clauses of this handler do", [subjectTy],
      completions.toList.map fun (p, _) => [p]⟩
    modify fun st => { st with pending := st.pending.push check }
  let mut covered : List String := []
  for (x, sig, ps, body) in opArms do
    let inst := (insts.lookup sig.effect).getD []
    let (payload, opResult) := instOp sig inst
    match opResult with
    | none =>
      unless ps.length == payload.length do
        arityError s!"an arm for the operation `{x}`" payload.length ps.length
      let binds ← clauseGiven body (inferPats ps payload)
      let here := (← get).pos
      unifyAt s!"the result of the arm for `{x}`" result (← inferStmts (binds ++ scope) amb body)
      checkUses here scope binds body
      if ← ps.allM irrefutable then covered := x :: covered
    | some o =>
      if ps.length == payload.length + 1 then
        -- The resumption holds the handled computation and, because resuming
        -- reinstalls the handler, the arms too: everything either of them uses.
        let held ← freshCap
        captures held .once
        if sig.must then captures held .must
        for id in suspendedLoans do
          captures held (.inner id)
        captureAll scope held (Elab.fvExpr [] (.handle subject arms)) fun x =>
          assignsExpr x (.handle subject arms)
        let binds ← clauseGiven body (inferPats ps (payload ++ [.func [o] result amb held]))
        let here := (← get).pos
        unifyAt s!"the result of the arm for `{x}`" result
          (← inferStmts (binds ++ scope) amb body)
        checkUses here scope binds body
        if ← (ps.take payload.length).allM irrefutable then covered := x :: covered
      else if ps.length == payload.length then
        let binds ← clauseGiven body (inferPats ps payload)
        let here := (← get).pos
        -- The arm resumes with what it gives: the computation is suspended,
        -- holding its borrows, for as long as the arm runs.
        let held ← freshCap
        captures held .once
        for id in suspendedLoans do
          captures held (.inner id)
        captureAll scope held (Elab.fvExpr [] (.handle subject arms)) fun x =>
          assignsExpr x (.handle subject arms)
        let resumption := ("%resumed", Binding.val (.func [o] result amb held))
        unifyAt s!"the value the arm for `{x}` resumes with" o
          (← withLater ["%resumed"] (inferStmts (binds ++ resumption :: scope) amb body))
        checkUses here scope binds body
        if ← ps.allM irrefutable then covered := x :: covered
      else arityError s!"an arm for the operation `{x}`" payload.length ps.length
  for (e, inst) in insts do
    let decl := (s.effects.lookup e).getD ⟨[], [], []⟩
    unless decl.ops.all covered.contains do
      try unifyRow amb ⟨[(e, inst)], some (← freshRowVar)⟩
      catch err =>
        throw s!"this handler does not handle every `{e}` operation, and the rest cannot \
          be passed on: {err}"
  modify fun st => { st with later := outerLater }
  pure result

end

end Glorious.Check
