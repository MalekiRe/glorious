module

public import Glorious.Check.Borrows

public section

namespace Glorious.Check

open Syntax

/-- A borrow of a field of what a reference points to: borrowed from the
reference, which is in the way only of that field meanwhile. `t` is the type
of what holds the reference, the name `x`. -/
def fieldThrough (scope : Scope) (id : Nat) (uniq : Bool) (x : String) (path : List String)
    (t : Ty) : M Ty := do
  let whole ← freshTy
  let cap ← freshCap
  let how ← if uniq then pure Ty.uniq else freshTy
  unifyAt (if uniq then "a field is borrowed for writing through a `&mut` reference"
    else "a field is borrowed through a reference") (.ref how whole cap) t
  let (field, numbered, chosen, through) ← fieldAtThrough whole path
  use scope (.through cap s!"`{x}`" uniq numbered)
  let cap' ← freshCap
  captures cap' (.loan (← freshLoan none uniq (some (cap, cap')) numbered))
  captures cap' (.ty t)
  throughBorrowed through uniq cap'
  modify fun s =>
    { s with fieldSites := s.fieldSites.push (id, true, whole, numbered, chosen, s.owner, s.pos) }
  pure (.ref (if uniq then .uniq else .shared) field cap')

/-- The variable an expression is, if it is one: its binding and its name. -/
def namedVal (scope : Scope) (e : Flat.ExprId) : M (Option (Nat × String)) := do
  match ← node e with
  | .name none x => pure (match scope.lookup x with
    | some (.val _ bid) => some (bid, x)
    | _ => none)
  | _ => pure none

/-- A field of `subject`, written `e`, read: where `e` is a variable, the
part read is noted (by number `idx`, or by `name` until its type says);
otherwise, if `known`, what is not taken is let go, and if not, the whole. -/
def readPart (scope : Scope) (e : Flat.ExprId) (subject : Ty) (idx : Nat) (name : String) (known : Bool)
    (part : Ty) (node : Flat.ExprId) : M Unit := do
  let why := "taking one field of a value lets go of the rest"
  match ← namedVal scope e with
  | some (bid, x) =>
    -- (Where the part has something to destroy, taking it gives the name's
    -- value away: its flag is set there, `Elab.takenSite`.)
    modify fun s =>
      { s with partReads := s.partReads.push (bid, x, subject, idx, name, s.pos)
               dropCands := s.dropCands.push (Elab.takenSite s.owner (s.body.idOf node) x, part, s.pos) }
  | none =>
    unless known do return ← mustDrop subject why
    -- A value that is in no variable and has a `drop` of its own to
    -- run: taking a field of it would let it go without that.
    ownDropRead subject
    match ← otherFields subject idx with
    | some rest =>
      for r in rest do
        mustDrop r why
        modify fun s => { s with leftBehind := s.leftBehind.push (r, s.pos ++ why) }
    | none => mustDrop subject why

/-- Is `x` a value made where a dot call is made on it (`borrowed%..`, the
call the first of `rest` to take it first), whose type has a function of
its own of the name that takes it whole, where the function the resolver
took borrows it? -/
def wholeReceiver (b : Flat.Body) (x : String) (t : Ty) (rest : List Flat.StmtId) : M Bool := do
  unless x.startsWith "borrowed%" do return false
  let takes := fun (e : Flat.ExprId) => match b.expr e with
    | .call call _ args | .tailCall call _ args =>
      match args[0]?.map b.expr with
      | some (.ref _ y) | some (.name none y) => if y == x then some call else none
      | _ => none
    | _ => none
  let rec find? (fuel : Nat) (e : Flat.ExprId) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel + 1 => (takes e).orElse fun _ => (b.children e).findSome? (find? fuel)
  let some call := rest.findSome? fun s => (b.stmtExprs s).toList.findSome? (find? 256) | return false
  let some alts := dotAltsOf (← get).modules call | return false
  let some (h, _) := (← find t).head | return false
  let some alt := alts.find? (·.startsWith (h ++ "::")) | return false
  let some scheme := (← get).fns[alt]? | return false
  let saved ← get
  let whole ← match ← instantiate scheme with
    | .fn (p :: _) _ _ _ _ =>
      match ← find p with
      | .ref .. => pure false
      | _ => pure true
    | _ => pure false
  set saved
  pure whole

/-- A callable type made for every lifetime of the references it is given
(`St.ranked`), where it is one. -/
def rankParams (t : Ty) : M Unit := do
  if let .fn ps _ _ _ cap ← find t then
    let lives ← ps.filterMapM fun p => do
      match ← find p with
      | .ref _ _ c => pure (some (← findCap c))
      | _ => pure none
    unless lives.isEmpty do
      modify fun s => { s with ranked := (cap, lives.eraseDups.map (·, "'_")) :: s.ranked }


/-- Is the field `step` of a value of type `t` (or of what a reference of the
type points to) one the value does not show here, its type implementing
`Deref`? It is then of what `deref` gives. -/
def derefsFor (t : Ty) (step : String) : M Bool := do
  let t ← match ← find t with
    | .ref _ inner _ => find inner
    | t => pure t
  let .con n _ := t | return false
  if (← implsOfHead "Deref" n).isEmpty then return false
  let saved ← get
  let shown ← try
      match ← fieldIndex t step with
      | some idx => pure (← fieldType t idx).isSome
      | none => pure true
    catch _ => pure false
  set saved
  pure !shown

/-- The field `step` of `x`, read (borrowed `&mut` where `uniq`): where it
is one `x` does not show and `x`'s type implements `Deref`, and it was not
written where it is (`derefHere`, `derefRefHere`: a value borrowed for
writing), refused. -/
def derefAt (scope : Scope) (x step : String) : M Unit := do
  let t := match scope.lookup x with
    | some (.val t _) => some t
    | some (.cell t _) => some t
    | _ => none
  if let some t := t then
    if ← derefsFor t step then
      throw s!"`{x}.{step}` is a field of what `{x}` stands for (`Deref`), which can be reached here only through a variable (`let mut {x}`) or a reference"


/-- The field `step` read of the name `x` (the read `id`), where it is one
`x` does not show and `x`'s type implements `Deref`: written where it is of
what `deref` gives (`Elab.derefNode`), the name borrowed, given as it is
where it holds a reference. Said for the elaborator
(`Elab.Decision.derefHere`). -/
def derefHere (scope : Scope) (id : Nat) (x step : String) : M Bool := do
  let t := match scope.lookup x with
    | some (.val t _) => some t
    | some (.cell t _) => some t
    | _ => none
  let some t := t | return false
  unless ← derefsFor t step do return false
  let borrow := match ← find t with
    | .ref .. => none
    | _ => some false
  let some b' := Elab.derefNode id borrow (← get).body | return false
  modify fun s => { s with body := b', decided := s.decided ++ [.derefHere id borrow] }
  pure true

/-- The field borrow `id`, `&x.f` (`&mut` where `uniq`), where `f` is a
field `x` does not show and `x`'s type implements `Deref`: written where it
is of what `deref` (`deref_mut`) gives (`Elab.derefRefNode`), `x` a place
borrowed, or a name holding a reference given as it is. Said for the
elaborator (`Elab.Decision.derefRefHere`). -/
def derefRefHere (scope : Scope) (id : Nat) (uniq : Bool) (x step : String) : M Bool := do
  let (t, cell) ← match scope.lookup x with
    | some (.val t _) => pure (t, false)
    | some (.cell t _) => pure (t, true)
    | _ => return false
  unless ← derefsFor t step do return false
  let borrow ← match ← find t with
    | .ref .. => pure none
    | _ => if uniq && !cell then return false else pure (some uniq)
  let some b' := Elab.derefRefNode id uniq borrow (← get).body | return false
  modify fun s => { s with body := b', decided := s.decided ++ [.derefRefHere id uniq borrow] }
  pure true

/-- The assignment `s`, `x.f = v` where `f` is a field `x` does not show and
`x`'s type implements `Deref`: written where it is of what `deref_mut`
gives (`Elab.derefAssignNode`), `x` a variable borrowed or a name holding
a reference given as it is. Said for the elaborator
(`Elab.Decision.derefAssignHere`). -/
def derefAssignHere (scope : Scope) (s : Flat.StmtId) : M Bool := do
  let b := (← get).body
  let some (id, x, step) := (match b.stmt s with
    | .assign t _ => match b.expr t with
      | .deref r => match b.expr r with
        | .refField id true x path false => some (id, x, path.headD "")
        | _ => none
      | _ => none
    | _ => none) | return false
  let (t, cell) ← match scope.lookup x with
    | some (.val t _) => pure (t, false)
    | some (.cell t _) => pure (t, true)
    | _ => return false
  unless ← derefsFor t step do return false
  let borrow ← match ← find t with
    | .ref .. => pure none
    | _ => if cell then pure (some true) else return false
  let some b' := Elab.derefAssignNode id borrow b | return false
  modify fun s => { s with body := b', decided := s.decided ++ [.derefAssignHere id borrow] }
  pure true

/-- What a reading of a call records, by where each record stood before it
(`Marks.of`): what a first reading recorded is taken back before the call
is read again written otherwise (`Marks.undo`). Only sizes held, and the
small lists that are put back whole: held, the state would be copied
where the call grows it. Taken back: how names were read and what was
asked of their types, of traits and of coverage; the values the call's
surroundings held; and what the elaborator is told by the call
(`argsChosen`, `dotChosen`, coercions, packs, field reads), of which it
takes the first. Asked again of the same call, one kept would be met
twice, once with what the first reading had. -/
structure Marks where
  valReads : Std.HashMap Nat (List (Ty × List (Nat × Nat)))
  temps : List (Ty × Nat)
  later : List String
  anon : List Ty
  uses : Nat
  givenReads : Nat
  heldMoves : Nat
  dups : Nat
  drops : Nat
  bounds : Nat
  pending : Nat
  fieldSites : Nat
  partReads : Nat
  instSites : Nat
  groupUses : Nat
  dropCands : Nat
  dotChosen : List (Nat × String × Nat)
  argsChosen : List ((Nat × Nat) × Expr)
  packs : Nat
  derefReads : Nat
  fieldReads : Nat
  given : Nat
  coercions : Nat
  methodCalls : Nat

/-- Where `s`'s records stand (`Marks`). -/
def Marks.of (s : St) : Marks :=
  { valReads := s.valReads, temps := s.temps, later := s.later, anon := s.anon, uses := s.uses.size,
    givenReads := s.givenReads.size, heldMoves := s.heldMoves.size, dups := s.dups.size, drops := s.drops.size,
    bounds := s.bounds.size, pending := s.pending.size,
    fieldSites := s.fieldSites.size, partReads := s.partReads.size, instSites := s.instSites.size,
    groupUses := s.groupUses.size, dropCands := s.dropCands.size, dotChosen := s.dotChosen,
    argsChosen := s.argsChosen, packs := s.packs.size, derefReads := s.derefReads.size,
    fieldReads := s.fieldReads.size, given := s.given.size, coercions := s.coercions.size,
    methodCalls := s.methodCalls.size }

/-- `s` with what was recorded since `m` taken back. -/
def Marks.undo (m : Marks) (s : St) : St :=
  { s with valReads := m.valReads, temps := m.temps, later := m.later, anon := m.anon,
           uses := s.uses.shrink m.uses, givenReads := s.givenReads.shrink m.givenReads,
           heldMoves := s.heldMoves.shrink m.heldMoves, dups := s.dups.shrink m.dups,
           drops := s.drops.shrink m.drops, bounds := s.bounds.shrink m.bounds,
           pending := s.pending.shrink m.pending,
           fieldSites := s.fieldSites.shrink m.fieldSites, partReads := s.partReads.shrink m.partReads,
           instSites := s.instSites.shrink m.instSites, groupUses := s.groupUses.shrink m.groupUses,
           dropCands := s.dropCands.shrink m.dropCands, dotChosen := m.dotChosen, argsChosen := m.argsChosen,
           packs := s.packs.shrink m.packs, derefReads := s.derefReads.shrink m.derefReads,
           fieldReads := s.fieldReads.shrink m.fieldReads, given := s.given.shrink m.given,
           coercions := s.coercions.shrink m.coercions, methodCalls := s.methodCalls.shrink m.methodCalls }

/-- Can what was read in the arms `read` and what is in the arms `now` both
run? Not where they are in two of a set of which one runs. -/
def bothRun (read now : List (Nat × Nat)) : Bool :=
  match read, now with
  | (g, i) :: read, (h, j) :: now => if g == h then i == j && bothRun read now else true
  | _, _ => true

/-- `x`, with the brand `id`, borrowed now: what was read of it before where
the borrow can follow has to be copied. -/
def readBefore (id : Nat) (x : String) : M Unit := do
  let s ← get
  for (t, at_) in s.valReads.getD id [] do
    if bothRun at_ s.armPath then
      mustDup t s!"`{x}` is borrowed after its value is given away"

/-- `run` in the arm `arm` of a set of which one runs (`St.armPath`). -/
def inArm {α : Type} (arm : Nat × Nat) (run : M α) : M α := do
  let outer := (← get).armPath
  modify fun s => { s with armPath := s.armPath ++ [arm] }
  tryCatchThe Elab.Said (do let r ← run; modify fun s => { s with armPath := outer }; pure r)
    fun e => do modify fun s => { s with armPath := outer }; throwThe Elab.Said e

/-- Whether a comparison of `args` is of what is not copied, or of what is
not known yet, by what its operands are before it is read (names, whose
types are known, or literals, which are copied): compared by reference,
written where it is (`Elab.compareNode`), as Rust's operators always
compare. (One not known yet may be found copied later: by reference it
compares the same.) -/
def compareByType (scope : Scope) (args : Array Flat.ExprId) : M Bool := do
  let b := (← get).body
  let mut found : Option Ty := none
  for a in args do
    match b.expr a with
    | .name none x =>
      match scope.lookup x with
      | none => return false
      | some (.val t _) | some (.cell t _) =>
        match found with
        | none => found := some t
        | some f => if !(freeTys (← zonk f)).isEmpty then found := some t
      | _ => pure ()
    -- (A literal is of a type that is copied; a constant, `true`, a value
    -- made anew wherever it is named.)
    | _ => return false
  let some t := found | return true
  let t ← zonk t
  if !(freeTys t).isEmpty then return true
  modify fun s => { s with seen := {} }
  if (← tyHasDrop [] t).isSome then return true
  tyOwnsOnce [] t

/-- The dot call `call`, its receiver a name, written where it is
(`Elab.receiverNode`): the name borrowed as `fn` takes it, given as it is
where it holds a reference. Said for the elaborator
(`Elab.Decision.receiverHere`). False where it is not such a call, or the
name is a value borrowed for writing, which only a variable can be. -/
def receiverHere (scope : Scope) (call : Nat) (node : Option Nat) (fn : Option String)
    (borrow : Option Bool) : M Bool := do
  let b := (← get).body
  let some e0 := node | return false
  let recv := match b.expr e0 with
    | .call _ f args | .tailCall _ f args =>
      match b.expr f, fn with
      | .fieldOf _ r _, some _ => some r
      | _, _ => args[0]?
    | _ => none
  let some recv := recv | return false
  let recv := Elab.unmarked b recv
  let some x := (match b.expr recv with
    | .name none x => some x
    | .ref _ x => some x
    | _ => none) | do
      -- (A field of a name, borrowed: the place, where it is,
      -- `Elab.receiverFieldNode`; through the reference the name holds,
      -- where it holds one.)
      -- (What is no name, given whole: as it is written, the node itself.)
      if borrow.isNone then
        let some b' := Elab.receiverNode call fn none b (some e0) | return false
        modify fun s => { s with body := b', decided := s.decided ++ [.receiverHere call fn none] }
        return true
      let some uniq := borrow | return false
      -- (Or of what a reference points to, `v[0].s`: through it.)
      let rec root (e : Flat.ExprId) (fuel : Nat) : Option (Option String) :=
        match fuel, b.expr e with
        | fuel + 1, .fieldOf _ inner _ =>
          match b.bare? inner, b.expr inner with
          | some x, _ => some (some x)
          | none, .deref _ => some none
          | none, .call _ g _ => if Elab.elementCall b g then some none else root inner fuel
          | none, _ => root inner fuel
        | _, _ => none
      let some r := root recv 64 | return false
      let star ← match r with
        | none => pure true
        | some x =>
          match scope.lookup x with
          | some (.val t _) | some (.cell t _) =>
            match ← find t with
            | .ref .. => pure true
            | _ => pure false
          | _ => return false
      let some b' := Elab.receiverFieldNode call fn uniq star b (some e0) | return false
      modify fun s => { s with body := b', decided := s.decided ++ [.receiverField call fn uniq star] }
      return true
  let holdsRef := fun (t : Ty) => do
    match ← find t with
    | .ref .. => pure true
    | _ => pure false
  let borrow ← match scope.lookup x, borrow with
    | some (.val t _), some u => if ← holdsRef t then pure none else if u then return false else pure (some u)
    | some (.cell t _), some u => if ← holdsRef t then pure none else pure (some u)
    | some _, some _ => return false
    | _, none => pure none
    | none, _ => return false
  let some b' := Elab.receiverNode call fn borrow b (some e0) | return false
  modify fun s => { s with body := b', decided := s.decided ++ [.receiverHere call fn borrow] }
  pure true

mutual

/-- A value of a type with a `'static` lifetime in it, `&'static str`, read:
of any lifetime it is asked, as nothing outlives `'static` (Rust's
`&'static str` where a `&'a str` is wanted). Only of the type's own
arguments, as `l.names[0] == name` compares a `'static` text with a
borrowed one. -/
partial def shortenStatic (t : Ty) : M Ty := do
  let some st := (← get).staticCap | return t
  -- (Through what is read only: a `Vec<&'static str>` is one of shorter
  -- texts, but a `&mut Vec<&'static str>` is written through, and is not.)
  let rec go (t : Ty) (fuel : Nat) : M Ty := do
    match fuel with
    | 0 => pure t
    | fuel + 1 =>
    match ← find t with
    | .ref how inner cap =>
      match ← find how with
      | .con "'" [] => if cap == st then pure (.ref how inner (← freshCap)) else pure t
      | .con "&" [] => pure (.ref how (← go inner fuel) cap)
      | _ => pure t
    | .con n args => pure (.con n (← args.mapM (go · fuel)))
    | .tuple args => pure (.tuple (← args.mapM (go · fuel)))
    | t => pure t
  go t 8

partial def inferExpr (scope : Scope) (amb : Row) (e0 : Flat.ExprId) : M Ty := do
  shortenStatic (← inferExprAt scope amb e0)

partial def inferExprAt (scope : Scope) (amb : Row) (e0 : Flat.ExprId) : M Ty := do
  -- A text written is a `&'static str`: its UTF-8 bytes, where the program
  -- has them from its start.
  -- (Of any lifetime it is asked, as Rust's `'static` one is wherever a
  -- shorter is wanted: `["<", n.to_string().as_str()]`.)
  if ((← get).body.textCodes e0).isSome then
    let t ← match ← resolveType [] false (.name "StrRef" [.name "'static" []]) with
      | .con n [_] => pure (Ty.con n [← freshTy])
      | t => pure t
    if ← textAt t e0 then return t
  -- (Its parts are read as what they are.)
  let n ← node e0
  match n with
  | .int _ => pure .int
  | .mark m => throw s!"`{m.shown}` is the compiler's mark of a call, not a value; this is a compiler defect"
  | .type _ => throw "a type written among expressions is no value; this is a compiler defect"
  | .name _ x =>
    -- (A function that needs a trait of a type it is used at, named as a
    -- value: written where it is as a block that calls it, and read on,
    -- `etaHere`. Nothing was read of it before.)
    fun s => match inferExprNamed scope amb n s with
    | .ok t s => .ok t s
    | .error e s =>
      match e.decision with
      | some (.eta owner y arity) =>
        if owner != s.owner || y != x then .error e s else
        let node := s.body.idOf e0
        let id := 700000000000000 + (hash (owner, node)).toNat % 100000000000000 * 2
        match Elab.etaNode node x arity id s.body with
        | some b' => inferExprAt scope amb e0 { s with body := b', decided := s.decided ++ [.etaHere owner node x arity id] }
        | none => .error e s
      | _ => .error e s
  | .label _ | .tuple _ => inferExprNamed scope amb n
  | .refField .. | .fieldOf .. | .proj .. => inferExprField scope amb e0 n
  | .call id f args =>
    -- (`if(c) { a } else { b }`, `else(if(c, a), b)`: `a` and `b` are two
    -- arms of which one runs, `St.armPath`.)
    if let #[i, other] := args then
      let b := (← get).body
      if let (some (_, "else"), .call _ g #[_, first]) := (b.name? f, b.expr i) then
        if (b.name? g).map (·.2) == some "if" then
          if let (.closure a _, .closure o _) := (b.expr first, b.expr other) then
            modify fun s => { s with altArms := (s.altArms.insert (s.owner, a) (id, 0)).insert (s.owner, o) (id, 1) }
    -- (A comparison of what is not copied, or of what is not known yet:
    -- by reference, `eq(&a, &b)`, written where it is before it is read,
    -- as Rust's operators compare. Its operands are names or literals, the
    -- rest named first by the front end, so what it compares is known.)
    if args.size == 2 && (((← get).body.name? f).bind fun (_, op) => compareOps.lookup op).isSome then
      if ← compareByType scope args then
        let b := (← get).body
        -- (A name that holds a reference is given as it is: `&T` compares
        -- as `T`.)
        let refs ← args.toList.mapM fun a => do
          match (b.bare? a).bind (fun x => scope.lookup x) with
          | some (.val t _) | some (.cell t _) =>
            match ← find t with
            | .ref .. => pure true
            | _ => pure false
          | _ => pure false
        if let some b' := Elab.compareNode id refs b then
          modify fun s => { s with body := b' }
          return ← inferExprAt scope amb e0
      return ← receiverRetry scope amb e0 id n
    receiverRetry scope amb e0 id n
  | .tailCall id _ _ => receiverRetry scope amb e0 id n
  | .closure .. => inferExprCall scope amb n
  | .handle subject arms => inferHandle scope amb e0 subject arms
  | .labelScope l body => do
    let t ← freshTy
    let brand ← freshBrand
    let found ← inferStmts (("@" ++ l, .label t brand) :: scope) amb body.toList
    unifyAt s!"the result of the scope `@{l}`" t found
    checkEscape brand (jumpsAfter l) (("it is the result of the scope", t) :: scopeRoots scope) amb
    pure t
  | .ref .. | .reborrow .. | .deref _ => inferExprRef scope amb e0 n

/-- A field read of `e` (`read`): where `e` is a name holding a value, what
of it is read is the field, not the whole (`St.valReads`). -/
partial def fieldRead (scope : Scope) (e : Flat.ExprId) (read : M Ty) : M Ty := do
  let some x := (← get).body.bare? e | return ← read
  let some (.val _ id) := scope.lookup x | return ← read
  let before := (← get).valReads[id]?
  let t ← read
  modify fun s => { s with valReads := s.valReads.insert id ((t, s.armPath) :: before.getD []) }
  pure t

/-- A name, a label or a tuple (`inferExpr`). -/
partial def inferExprNamed (scope : Scope) (amb : Row) (n : Flat.FExpr) : M Ty := do
  match n with
  | .name q x => do
    match ← resolveName scope q x with
    | .local (.val t id) => do
      -- (Of one borrowed before: a use of the place, `placeVal`.)
      if (← get).placedVals.contains id then use scope (.var id x .move)
      modify fun s => { s with valReads := s.valReads.insert id ((t, s.armPath) :: s.valReads.getD id []) }
      lend scope x t
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
      if Elab.isIntrinsic x then throw s!"intrinsic `{x}` must be called"
      unless bounds.isEmpty do
        -- (Read again with the naming a block that calls it, whose type the
        -- use decides, and so what the function needs.)
        let arity := match ← find t with
          | .fn ps _ _ _ _ => some ps.length
          | _ => none
        let owner := (← get).owner
        let decision := match arity with
          | some n => if inGroup then none else some (Elab.Decision.eta owner x n)
          | none => none
        throwThe Elab.Said { msg := s!"`{x}` needs a trait of a type it is used at, so it is called where it is named: write a block that calls it", decision }
      if inGroup then
        modify fun s => { s with groupUses := s.groupUses.push ⟨0, x, s.owner, s.pos⟩ }
      else
        let sites := (← get).lastSites
        unless sites.isEmpty do
          modify fun s => { s with instSites := s.instSites.push (s.owner, 0, "ref", x, sites) }
        -- (Named as a value, it is for every lifetime of the references it
        -- is given, as it is where it is called: it holds none of them.)
        rankParams t
      pure t
    | .method sig =>
      throw s!"`{x}` is a function of the trait `{sig.trait}`, so it is called where it is named: write a block that calls it"
    | .ctor sig written => do
      let (fields, result) ← instCtor sig
      unless fields.isEmpty do arityError s!"constructor `{x}`" fields.length 0
      if let some ty := written then
        unifyAt s!"`{x}` is written with a type" (← resolveType [] false (ty.typeWritten)) result
      pure result
    | .op _ => throw s!"operation `{x}` must be called"
    | .prim => throw s!"intrinsic `{x}` must be called"
    | .pack _ => throw "what an `is` found is built where it is found"
    | .host _ => throw s!"host operation `{x}` must be called"
    | .cancel => throw "`cancel` must be applied to a resumption"
    | .replace => throw "`replace` must be called"
    | .swap => throw "`swap` must be called"
    | .overwrite => throw "`overwrite` must be called"
    | .readOut => throw "`read_out` must be called"
    | .transmute => throw "`transmute` must be called"
    | .const e =>
      let (cb, ce) := Flat.ofExpr e
      withBody cb (inferExpr [] amb ce)
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
  | _ => throw "an expression was taken for one of another kind; this is a compiler defect"

/-- A field or a trait's function taken out (`inferExpr`). -/
partial def inferExprField (scope : Scope) (amb : Row) (e0 : Flat.ExprId) (n : Flat.FExpr) : M Ty := do
  match n with
  | .refField id uniq x path star => do
    if !star then
      if ← derefRefHere scope id uniq x (path.headD "") then return ← inferExprAt scope amb e0
    derefAt scope x (path.headD "")
    match scope.lookup x with
    | some (.cell t brand) => do
      -- A variable that holds a reference: the field is of what that points
      -- to, and the variable is read for the reference.
      if let .ref _ _ _ ← find t then
        use scope (.var brand x .read)
        return ← fieldThrough scope id uniq x path t
      if star then
        throw s!"`{x}` is a mutable variable, not a reference: its field is `{x}.{path.headD ""}`"
      let (field, numbered, chosen, through) ← fieldAtThrough t path
      use scope (.var brand x (if uniq then .lend else .share) numbered)
      let cap ← freshCap
      captures cap (.brand brand)
      captures cap (.loan (← freshLoan (some brand) uniq none numbered))
      throughBorrowed through uniq cap
      modify fun s =>
        { s with fieldSites := s.fieldSites.push (id, false, t, numbered, chosen, s.owner, s.pos) }
      pure (.ref (if uniq then .uniq else .shared) field cap)
    | some (.val t bid) => do
      match ← find t with
      | .ref _ _ _ => pure ()
      | .var _ => pure ()
      | _ =>
        -- (A field of a value a name holds, borrowed: of the place,
        -- `placeVal`, as of a variable.)
        if !uniq && !star && !x.startsWith "%" then
          readBefore bid x
          placeVal bid x t
          let (field, numbered, chosen, through) ← fieldAtThrough t path
          use scope (.var bid x .share numbered)
          let cap ← freshCap
          captures cap (.brand bid)
          captures cap (.loan (← freshLoan (some bid) false none numbered))
          throughBorrowed through false cap
          modify fun s =>
            { s with fieldSites := s.fieldSites.push (id, false, t, numbered, chosen, s.owner, s.pos) }
          return .ref .shared field cap
        if x.startsWith "%through" || x.startsWith "%given" then
          throw "what a field is borrowed of here is a value that nothing holds, not a reference: give it a `let mut` first"
        throw s!"`{x}` is neither a variable nor a reference, so no field of it can be borrowed here: say what it is where it is bound (`let {x}: Type = ..`), or bind it with `let mut`"
      fieldThrough scope id uniq x path t
    | some _ => do
      if x.startsWith "%through" || x.startsWith "%given" then
        throw "what a field is borrowed of here is a value that nothing holds, not a reference: give it a `let mut` first"
      throw s!"`{x}` is not a mutable variable or a reference, so no field of it can be borrowed"
    | none => throw s!"unknown name `{x}`"
  | .fieldOf id e name => fieldRead scope e do
    if let some x := (← get).body.bare? e then
      if ← derefHere scope id x name then return ← inferExprAt scope amb e0
      derefAt scope x name
    if let some field ← inferFieldOfPlace scope e0 then return field
    let subject ← peelTwice id (← inferExpr scope amb e)
    -- A field of what a reference is to, the reference given by what is
    -- written (`m.get().0`, `r.x`): read through it, which copies it, as a
    -- field of what a name holding one is to is.
    if let .ref _ inner _ ← find subject then
      -- (What it is to not known yet, as what a trait leaves to an
      -- implementation is until that is found, `a[i].f`: settled once it
      -- is, `runProjections`.)
      if let (.var _, none) := (← find inner, name.toNat?) then
        let t ← freshTy
        modify fun s => { s with namedReads := s.namedReads.push (subject, name, t, id, s.pos) }
        return t
      let idx ← match name.toNat? with
        | some n => pure (some n)
        | none => fieldIndex inner name
      if let some idx := idx then
        match ← fieldType inner idx with
        | some t =>
          modify fun s => { s with fieldReads := s.fieldReads.push (id, idx), derefReads := s.derefReads.push id }
          mustDup t "reading through a reference copies the value (`replace` takes it out instead)"
          return t
        | none =>
          -- (Of a reference to what is not known yet, `deref(&m).0`: the
          -- field is settled once it is.)
          if name.toNat?.isSome then
            let t ← freshTy
            modify fun s => { s with fieldReads := s.fieldReads.push (id, idx), derefReads := s.derefReads.push id,
                                     projections := s.projections.push (inner, idx, t, s.pos, id) }
            mustDup t "reading through a reference copies the value (`replace` takes it out instead)"
            return t
    -- (Of which name it is a part, where it is one of a name's.)
    let named ← namedVal scope e
    modify fun s => { s with aparts := s.aparts.push (subject, s.pos, named.map (·.1)) }
    -- A field by number of a value whose type is not known yet is settled
    -- once the rest of the function is inferred, as `e.0` of any value is.
    if let some n := name.toNat? then
      modify fun s => { s with fieldReads := s.fieldReads.push (id, n) }
      match ← fieldType subject n with
      | some t =>
        readPart scope e subject n name true t e0
        return t
      | none =>
        let t ← freshTy
        readPart scope e subject n name false t e0
        modify fun s => { s with projections := s.projections.push (subject, n, t, s.pos, id) }
        return t
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
      readPart scope e subject idx name true t e0
      pure t
    | none =>
      -- Not known yet: settled once the rest of the function is inferred.
      -- (Of a name, the part read is noted, by its name until the type
      -- says which it is.)
      let t ← freshTy
      readPart scope e subject Syntax.partUnknown name false t e0
      modify fun s => { s with namedReads := s.namedReads.push (subject, name, t, id, s.pos) }
      pure t
  | .proj e idx => fieldRead scope e do
    if let some field ← inferFieldOfPlace scope e0 then return field
    let subject ← inferExpr scope amb e
    -- (Of which name it is a part, where it is one of a name's.)
    let named ← namedVal scope e
    modify fun s => { s with aparts := s.aparts.push (subject, s.pos, named.map (·.1)) }
    match ← fieldType subject idx with
    | some t =>
      readPart scope e subject idx (toString idx) true t e0
      pure t
    | none => do
      -- Not known yet: settle it once the rest of the function is inferred.
      -- (Of a name, the part read is noted as it is where the type is
      -- known: what the name's value is left with is seen once it is.)
      let t ← freshTy
      readPart scope e subject idx (toString idx) false t e0
      modify fun s => { s with projections := s.projections.push (subject, idx, t, s.pos, 0) }
      pure t
  | _ => throw "an expression was taken for one of another kind; this is a compiler defect"

/-- The call `id` at `e0`; where a dot call of a name is decided of a
function only now, or taking its receiver otherwise than written: written
where it is and read again (`receiverHere`, once a call). From the state
where it was found, not one held while the call is read: holding it, every
array the call grew was copied (a quarter of covey/fleet's check of `main`).
What the first reading recorded of how names were read is taken back; the
rest is recorded again, which asks no less. -/
partial def receiverRetry (scope : Scope) (amb : Row) (e0 : Flat.ExprId) (id : Nat) (n : Flat.FExpr) : M Ty := fun s =>
  let undo := Marks.of s
  match inferExprCall scope amb n s with
  | .ok a s => .ok a s
  | .error e s =>
    match e.decision with
    -- (A callable given here whose clauses match what a reference points
    -- to: written so where it is, `refPatsHere`, once.)
    | some (.refPats cid clauses) =>
      let b := s.body
      let isArg := match b.expr e0 with
        | .call _ _ args | .tailCall _ _ args => args.any fun a => match b.expr a with
          | .closure i _ => i == cid
          | _ => false
        | _ => false
      if !isArg || s.decided.any (fun | .refPatsHere c' _ => c' == cid | _ => false) then .error e s else
      match Elab.refPatsNode cid clauses b with
      | none => .error e s
      | some b' =>
        inferExprAt scope amb e0 { undo.undo s with body := b', decided := s.decided ++ [Elab.Decision.refPatsHere cid clauses] }
    | some (.receiver c fn borrow) =>
      if c != id || s.decided.any (fun | .receiverHere c' _ _ => c' == c | _ => false) then .error e s else
      let s := undo.undo s
      match receiverHere scope c (some e0) fn borrow s with
      | .ok true s => inferExprAt scope amb e0 s
      | .ok false s => .error e s
      | .error e' s => .error e' s
    | _ => .error e s

/-- A statement's expression, `e`. -/
partial def inferRoot (scope : Scope) (amb : Row) (e : Flat.ExprId) : M Ty := inferExpr scope amb e

/-- A call or a callable (`inferExpr`). -/
partial def inferExprCall (scope : Scope) (amb : Row) (n : Flat.FExpr) : M Ty := do
  match n with
  | .call id f args => do
    let b := (← get).body
    -- Whether what a reference points to was built by a constructor: the
    -- compiler's question where a pattern binds by reference. The reference
    -- is not used up, and nothing is read out of what it points to.
    if let (some .ctorIs, some r) := (b.mark? f, args[0]?) then
      let inner ← freshTy
      unifyAt "a pattern that binds by reference" (.ref (← freshTy) inner (← freshCap))
        (← inferPlace scope amb r)
      return .int
    -- What the clauses of such a callable ask of the values they are given,
    -- as patterns: these have to cover every case, and say what the types
    -- are. A value written `*r` is what the reference points to.
    if b.mark? f == some .shapes then
      if let some (.closure _ clauses) := args.back?.map b.expr then
        let mut tys : Array Ty := #[]
        for a in args.pop do
          match b.expr a with
          | .deref r =>
            let inner ← freshTy
            unifyAt "a pattern that binds by reference" (.ref (← freshTy) inner (← freshCap))
              (← inferPlace scope amb r)
            tys := tys.push inner
          | _ => tys := tys.push (← inferPlace scope amb a)
        -- What a pattern lets go of is let go of by the clause, not here.
        let drops := (← get).drops
        modify fun s => { s with shapes := true }
        -- (Whatever goes wrong, patterns are read as usual again after.)
        let wrong ← tryCatchThe Elab.Said (do
            for c in clauses do
              let _ ← inferPats (b.clause c).pats tys.toList
            pure none) fun e => pure (some e)
        modify fun s => { s with drops := drops, shapes := false }
        if let some e := wrong then throwThe Elab.Said e
        let check : Pending := ⟨(← get).pos, "the clauses of this callable do", tys.toList,
          clauses.toList.map fun c => (b.clause c).pats⟩
        modify fun s => { s with pending := s.pending.push check }
      return .unit
    withTemps (inferCall scope amb f args id)
  | .tailCall id f args => do
    -- The case that cannot be: of whatever type is wanted.
    if (← get).body.bare? f == some "%never" then return ← freshTy
    withTemps (inferCall scope amb f args id)
  | .closure id clauses => do
    let t ← inferCallable scope [] none none clauses "the clauses of this callable do" id
    if let .fn ps _ _ _ cap := t then
      modify fun s => { s with blockCaps := s.blockCaps.push (id, cap) }
      -- A block written for a function named as a value (`Elab.etaBody`)
      -- is for every lifetime of the references it is given, as the
      -- function is: it holds none of them.
      if let #[c] := clauses then
        let pats := ((← get).body.clause c).pats
        if !pats.isEmpty && pats.all (fun | .var x => x.startsWith "%eta" | _ => false) then
          rankParams (.fn ps .unit [] none cap)
    pure t
  | _ => throw "an expression was taken for one of another kind; this is a compiler defect"

/-- A borrow, a borrow again or what a reference points to (`inferExpr`). -/
partial def inferExprRef (scope : Scope) (amb : Row) (e0 : Flat.ExprId) (n : Flat.FExpr) : M Ty := do
  match n with
  | .ref uniq x =>
    match scope.lookup x with
    | some (.cell t brand) => do
      use scope (.var brand x (if uniq then .lend else .share))
      let cap ← freshCap
      captures cap (.brand brand)
      captures cap (.loan (← freshLoan (some brand) uniq none))
      pure (.ref (if uniq then .uniq else .shared) t cap)
    -- (A name that holds a `&mut` reference is borrowed through: `a[i] = v`
    -- of an `a: &mut [T]` writes what `a` is to, as `(*a)[i] = v` does.)
    | some (.val t id) => do
      if uniq then
        if let Ty.ref how _ _ ← find t then
          if let .con "&mut" [] ← find how then
            -- (Written so where it is, `&mut *x`, for the elaborator too:
            -- borrowed elsewhere, `x` may be a variable there, whose `&mut`
            -- would be of the variable, `Elab.Decision.reborrowHere`.)
            let node := (← get).body.idOf e0
            match Elab.reborrowNode node x (← get).body with
            | some b' =>
              modify fun s => { s with body := b', decided := s.decided ++ [.reborrowHere s.owner node x] }
              return ← inferExprAt scope amb e0
            | none =>
              let named ← pushE (.name none x)
              return ← inferExpr scope amb (← pushE (.reborrow true named))
        -- (A value made where a dot call is made on it, named for it,
        -- `Mark.held`: a place, as Rust's temporary is, which the call may
        -- change. And a `&mut [T]`, a `SliceMut`, written through, `xs[i] =
        -- v`, as Rust's is without `mut`.)
        let sliceMut := match ← find t with
          | .con n _ => Syntax.lastSegment n == "SliceMut"
          | _ => false
        unless x.startsWith "borrowed%" || sliceMut do
          throw s!"`{x}` is not a mutable variable, so it cannot be borrowed"
      do
        -- A value a name holds is a place: borrowed, it is one from where
        -- it is first borrowed, its reads after uses of it (`placeVal`).
        -- (One whose value was given away before: borrowed, it would be
        -- read after, as only what is copied can be.)
        readBefore id x
        placeVal id x t
        use scope (.var id x (if uniq then .lend else .share))
        let cap ← freshCap
        captures cap (.brand id)
        captures cap (.loan (← freshLoan (some id) uniq none))
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
      use scope (.through cap (placeName (← get).body e) true)
      captures cap' (.loan (← freshLoan none true (some (cap, cap'))))
      captures cap' (.ty t)
      pure (.ref .uniq inner cap')
    else
      use scope (.through cap (placeName (← get).body e) false)
      captures cap' (.loan (← freshLoan none false (some (cap, cap'))))
      captures cap' (.ty t)
      pure (.ref .shared inner cap')
  | .deref e => do
    let t ← inferPlace scope amb e
    let inner ← freshTy
    let cap ← freshCap
    unifyAt "`*` reads through a reference" (.ref (← freshTy) inner cap) t
    use scope (.through cap (placeName (← get).body e) false)
    -- (What a clause that binds by reference is chosen by, `*%given..`, is
    -- a copy only for that: nothing of it is destroyed.)
    let choosing := match (← get).body.bare? e with
      | some x => x.startsWith "%given"
      | none => false
    -- (`a[i]` read where the element is, `*element_at(&a, i)`.)
    let body := (← get).body
    let element : Bool := match body.expr e with
      | .call _ f _ => (body.name? f).map (·.2) == some "element_at"
      | _ => false
    if choosing then
      mustDup inner "reading through a reference copies the value to choose a clause"
    else if element then
      mustDup inner "`a[i]` copies the element (take it out with `pop` or `remove`, or borrow it, `&a[i]`)"
    else mustDup inner "reading through a reference copies the value (`replace` takes it out instead)"
    pure inner
  | _ => throw "an expression was taken for one of another kind; this is a compiler defect"


/-- A field of what a mutable variable holds, or of what a reference points
to, is read where it is: only the field is copied, and only a borrow of that
field is in the way. None if the expression is not that. -/
partial def inferFieldOfPlace (scope : Scope) (whole : Flat.ExprId) : M (Option Ty) := do
  if let some (x, path) := fieldOfName (← get).body whole then
    if let some (.cell t brand) := scope.lookup x then
      let (field, numbered, _, through) ← fieldAtThrough t (path.map (·.1))
      noteFieldReads path numbered through
      mustDup field (readsCell x)
      use scope (.var brand x .read numbered)
      return some field
    -- `p.name` where `p` is a reference: the field of what it points to.
    -- Only where the first field is read by name, which is how the
    -- elaborator is told.
    if let some (.val t _) := scope.lookup x then
      if let .ref _ inner cap ← find t then
        if let some (_, some first) := path.head? then
          modify fun s => { s with derefReads := s.derefReads.push first }
          return some (← readThrough x path inner cap)
  if let some (x, path) := fieldOfDeref (← get).body whole then
    if let some (.val t _) := scope.lookup x then
      let inner ← freshTy
      let cap ← freshCap
      unifyAt "`*` reads through a reference" (.ref (← freshTy) inner cap) t
      return some (← readThrough x path inner cap)
  return none
where
  /-- A field read through a reference: copied out. -/
  readThrough (x : String) (path : List (String × Option Nat)) (inner : Ty) (cap : Nat) : M Ty := do
    let (field, numbered, _, through) ← fieldAtThrough inner (path.map (·.1))
    noteFieldReads path numbered through
    -- (What the reference is to is a reference too, `r.0` of an `r:
    -- &&Name`: read through both.)
    if through.any (·.1 == 0) then
      if let some (_, some first) := path.head? then
        modify fun s => { s with derefReads := s.derefReads.push (first + Syntax.derefTwice) }
    mustDup field "reading through a reference copies the value (`replace` takes it out instead)"
    use scope (.through cap s!"`{x}`" false numbered)
    pure field

/-- The reference that `*e` goes through. A name is the reference it stands
for, not one lent from it. -/
partial def inferPlace (scope : Scope) (amb : Row) (e : Flat.ExprId) : M Ty := do
  match (← get).body.bare? e with
  | some x =>
    match scope.lookup x with
    | some (.val t _) => pure t
    | _ => inferExpr scope amb e
  | none => inferExpr scope amb e

/-- Check one argument. Gives the mismatch if it does not fit. -/
partial def checkArg (scope : Scope) (amb : Row) (what : String) (p : Ty) (a : Flat.ExprId)
    (site : Option Elab.Site) : M (Option String) := do
  let b := (← get).body
  -- A whole number written where a type of whole numbers is wanted is of it.
  if let .int n := b.expr a then
    -- (Wanted where a trait asked of a decided type takes that type where a
    -- use does not say, `R` of `Add<R = Self>`: of that type, as `x + 1` of
    -- a `u8` is of two.)
    if let .var v ← find p then
      for bd in (← get).bounds do
        if ← defaultTraitArgs bd.trait bd.ty bd.args (known := true) (only := some v) then break
    if let some fits ← literalAt p n a then return fits.map fun e => s!"{what}: {e}"
  -- (Wanted where a trait's argument is, of a known type that has one
  -- implementation of the trait: that implementation's, `owned + "more"`.)
  if let .var v ← find p then
    let _ ← argDecidedAt v
  -- A text written where `&str` is wanted is one.
  if ← textAt p a then return none
  -- A block where what is wanted is known and is no callable: it is run
  -- there, and is its value (5.4).
  if let some (id, _) := b.plainBlock a then
    let wanted ← find p
    let callable := match wanted with
      | .fn _ _ _ _ _ => true
      | .var _ => true
      | _ => false
    unless callable do
      let t ← inferExpr scope amb (← pushE (.call 0 a #[]))
      modify fun s => { s with packs := s.packs.push (id, [Syntax.nowMark]), runNow := s.runNow.insert id }
      return ← fitAt scope amb what site p t
  match b.plainBlock a, ← find p with
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
    let given ← build (Flat.pushClause ⟨[taken], body⟩)
    let t ← inferCallable scope [some input] none none #[given]
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
      let mentioned := (b.fvStmts [] body.toList).filterMap fun x =>
        match scope.lookup x with
        | some (.val _ id) => some (x, id)
        | _ => none
      -- Given to run in an environment and given a callable: if that is a
      -- block given to run in one too, this runs in its place (whether it
      -- is, is known once the program is), taking over what it captured.
      match ← find input with
      | .fn _ _ _ _ cap =>
        if (← get).inPlace.contains id then
          if (← get).anyMust then
            modify fun s =>
              { s with unrunGiven :=
                  s.unrunGiven.push (id, cap, input, mentioned, s.pos ++ why, own) }
          modify fun s => { s with unrun := s.unrun.push (id, cap) }
        else mustDrop input why
      | _ => mustDrop input why
      pure none
  | _, _ => do
    -- `{ (x, y) => .. }` where a callable of several arguments is wanted:
    -- each clause's one tuple is the arguments (5.4).
    if let (.closure id clauses, .fn ps _ _ _ _) := (b.expr a, ← find p) then
      let spread := clauses.filterMap fun c => match b.clause c with
        | ⟨[.tuple parts], body⟩ => if parts.length == ps.length then some (⟨parts, body⟩ : Flat.FClause) else none
        | _ => none
      if ps.length ≥ 2 && !clauses.isEmpty && spread.size == clauses.size then
        let spread ← spread.mapM fun c => build (Flat.pushClause c)
        let t ← inferCallable scope (ps.map some) none none spread "the clauses of this callable do" id
        if let .fn _ _ _ _ cap := t then
          modify fun s =>
            { s with blockCaps := s.blockCaps.push (id, cap)
                     packs := s.packs.push (id, [Syntax.spreadMark]) }
        return ← fitAt scope amb what site p t
    -- A callable written where one is wanted whose parameters are types of
    -- whole numbers: a whole number among its patterns is of that type.
    if let (.closure id clauses, .fn ps _ _ _ _) := (b.expr a, ← find p) then
      let arity := match clauses[0]? with
        | some c => (b.clause c).pats.length
        | none => 0
      -- (What the callable is to give, where that is known: a whole number
      -- a clause ends with is then of it, `u8`.)
      let knownRet ← match ← find p with
        | .fn _ r _ _ _ => do
          match ← find r with
          | .con n [] => pure (if n == "Int" || Syntax.isScalar n then some r else none)
          | _ => pure none
        | _ => pure none
      let mut annots : List (Option Ty) := []
      -- A parameter known to be of a declared type is said too, so that
      -- what the clauses do with it, a field read by name, is looked at
      -- knowing it. That is tried, and given up where it does not fit:
      -- what is given may yet be converted to what is wanted.
      let mut wider : List (Option Ty) := []
      let mut widened := false
      for q in ps do
        -- (A tuple too: what its parts are is then known where the clauses
        -- read them.)
        let declared ← match ← find q with
          | .con _ _ => pure true
          | .tuple (_ :: _) => pure true
          -- (A reference to a type with named fields: what they are is
          -- known where the clauses read them through it.)
          | .ref _ inner _ => do
            match ← find inner with
            | .tuple (_ :: _) => pure true
            | .con name _ =>
              let st ← get
              pure (match st.types[name]? with
                | some decl => match decl.ctors with
                  | [c] => st.fieldNames.contains c
                  | _ => false
                | none => false)
            | _ => pure false
          | _ => pure false
        let whole := (← literalAt q 0).isSome
        annots := annots ++ [if whole then some q else none]
        wider := wider ++ [if declared || whole then some q else none]
        if declared && !whole then widened := true
      -- (The callable read with these types written of its parameters.)
      let plain := fun (annots : List (Option Ty)) => do
        if arity == ps.length && annots.any (·.isSome) then
          let t ← inferCallable scope annots knownRet none clauses "the clauses of this callable do" id
          if let .fn _ _ _ _ cap := t then
            modify fun s => { s with blockCaps := s.blockCaps.push (id, cap) }
          return ← fitAt scope amb what site p t
        fitAt scope amb what site p (← inferExpr scope amb a)
      if arity == ps.length && widened then
        let saved ← get
        let tried ← tryCatchThe Elab.Said (do
            pure (if (← plain wider).isNone then none else some ("" : Elab.Said))) fun e => pure (some e)
        match tried with
        | none => return none
        | some found =>
          -- (Found that a match is of a reference, or a dot call of a type's
          -- own function, knowing the types: the program is read again so.)
          if found.passOn then throwThe Elab.Said found
          let said := found.msg
          set saved
          -- What went wrong with the types known is what is said if the
          -- callable is wrong without them too: it was read knowing more.
          unless said.isEmpty do
            -- (Where it was said, as the statement it is in would say it.)
            let at_ := (← get).at_
            let said := if at_.1 == 0 then said else Syntax.positioned at_.1 at_.2 said
            modify fun s => { s with firstSaid := s.firstSaid <|> some { found with msg := said } }
            try return ← plain annots
            catch _ => throwThe Elab.Said { found with msg := said }
      return ← plain annots
    fitAt scope amb what site p (← inferExpr scope amb a)

/-- A dot call's own function of the receiver's type, if the resolver found
one of the name (`ModuleInfo.dotAlts`): the receiver's type is found on a
copy of what is known. -/
partial def dotAltFor (scope : Scope) (amb : Row) (call : Nat) (a : Flat.ExprId) : M (Option String) := do
  match dotAltsOf (← get).modules call with
  | none => pure none
  | some alts =>
    -- (Found already of this receiver: `St.altFound`.)
    if let some found := (← get).altFound[a]? then return found
    let found ← dotAltReading scope amb alts a
    modify fun s => { s with altFound := s.altFound.insert a found }
    pure found

/-- What `dotAltFor` finds, read anew. -/
partial def dotAltReading (scope : Scope) (amb : Row) (alts : List String) (a : Flat.ExprId) : M (Option String) := do
    let saved ← get
    -- (What the receiver itself is found to need read again, a dot call in
    -- it of a type's own function, is passed on first.)
    -- (Its type as it is, not as borrowed for the function in scope.)
    let a ← match ← node a with
      | .ref _ x => pushE (.name none x)
      | _ => pure a
    let found ← tryCatchThe Elab.Said (some <$> inferExpr scope amb a) fun e =>
      if e.passOn then throwThe Elab.Said e else pure none
    -- (Its head read before what was found on the way is let go; what a
    -- trait leaves to an implementation found first where it is one, the
    -- element of `g[0]`.)
    let h ← match found with
      | some ty => do
        match ← headName 8 ty with
        | some h => pure (some h)
        | none =>
          -- (Of a trait's argument a single implementation decides, as
          -- Rust's does: `convert(..).0.len()`.)
          let decided ← match ← find ty with
            | .var v => argDecidedAt v
            | .ref _ t _ => match ← find t with
              | .var v => argDecidedAt v
              | _ => pure false
            | _ => pure false
          if decided then headName 8 ty
          else do
            -- (What a trait leaves to an implementation, and the fields read
            -- of what that is: `pair.0` of `let pair = &fs[0]`.)
            unless (← get).assocUses.isEmpty do settleAssocsAll
            runProjections false
            headName 8 ty
      | none => pure none
    -- (What was found of receivers on the way is kept: `St.altFound`.)
    let found := (← get).altFound
    set { saved with altFound := found }
    let some h := h | return none
    if let some own := alts.find? (·.startsWith (h ++ "::")) then return some own
    -- (Or a function of another trait, where the type has that trait.)
    let s ← get
    pure (alts.find? fun alt => match s.methods[alt]? with
      | some sig => s.kimpls.has (.of sig.trait) h
      | none => false)

/-- How two functions take their first argument: `0` whole, `1` by a shared
reference, `2` by a `&mut` one (none where it is no function known so). -/
partial def receiverKinds (f g : String) : M (Option Nat × Option Nat) := do
  let first := fun (name : String) => (do
    match (← get).fns[name]? with
    | none =>
      -- (One of the group being checked: as its signature writes it.)
      if let some k := (← get).groupFirst.lookup name then return some k
      -- (A trait's function: as its first parameter is written.)
      match (← get).methods[name]? with
      | some sig =>
        match sig.params.head? with
        | some (.ref how _ _) =>
          match how with
          | .con "&mut" [] => pure (some 2)
          | _ => pure (some 1)
        | some _ => pure (some 0)
        | none => pure none
      | none => pure none
    | some scheme =>
      match ← instantiate scheme with
      | .fn (p :: _) _ _ _ _ =>
        match ← find p with
        | .ref how _ _ =>
          match ← find how with
          | .con "&mut" [] => pure (some 2)
          | _ => pure (some 1)
        | _ => pure (some 0)
      | _ => pure none : M (Option Nat))
  let saved ← get
  let a ← first f
  let b ← first g
  set saved
  pure (a, b)

/-- The dot calls on a variable `x` of type `t` that the function of `t`'s
own takes by reference where the one in scope takes it whole
(`inferDotAltCall`): each receiver's node, and whether it is borrowed for
writing. The variable is borrowed there, not given away. -/
partial def dotBorrows (b : Flat.Body) (x : String) (t : Ty) (rest : List Flat.StmtId) : M (List (Flat.ExprId × Bool)) := do
  let some h ← headName 8 t | return []
  let rec calls (fuel : Nat) (e : Flat.ExprId) : List (Flat.ExprId × Nat × String) :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      let here := match b.expr e with
        | .call id f args =>
          match b.bare? f, args[0]? with
          | some name, some a => if b.bare? a == some x then [(a, id, name)] else []
          | _, _ => []
        | _ => []
      here ++ (b.children e).flatMap (calls fuel)
  let found := rest.flatMap fun s => (b.stmtExprs s).toList.flatMap (calls 256)
  found.filterMapM fun (a, call, name) => do
    let some alts := dotAltsOf (← get).modules call | return none
    let some alt := alts.find? (·.startsWith (h ++ "::")) | return none
    if alt == name then return none
    match ← receiverKinds name alt with
    | (some 0, some k) => pure (if k != 0 then some (a, k == 2) else none)
    | _ => pure none

/-- `let x = element_at(r, i)` named by the front end for a dot call on a
field of the element, `v[0].items.push(..)` (`Syntax.receiverExpr`): where
the function takes the field by `&mut`, the element's place,
`place_at(i, &mut ..)`, for writing through. -/
partial def elementPlaceFor (x : String) (value : Flat.ExprId) (rest : List Flat.StmtId) : M Unit := do
  let b := (← get).body
  unless x.startsWith "borrowed%" do return
  let .call cid g #[base, i] := b.expr value | return
  unless (b.name? g).map (·.2) == some "element_at" do return
  let rec rooted (fuel : Nat) (e : Flat.ExprId) : Bool := match fuel, b.expr e with
    | fuel + 1, .fieldOf _ inner _ => b.bare? inner == some x || rooted fuel inner
    | _, _ => false
  let rec calls (fuel : Nat) (e : Flat.ExprId) : List String :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      let here := match b.expr e with
        | .call _ f args | .tailCall _ f args =>
          match b.bare? f, args[0]?.map b.expr with
          | some fx, some (.call _ m #[r]) => if b.mark? m == some .receiver && rooted 64 r then [fx] else []
          | _, _ => []
        | _ => []
      here ++ (b.children e).flatMap (calls fuel)
  for fx in rest.flatMap fun s => (b.stmtExprs s).toList.flatMap (calls 256) do
    if (← receiverKinds fx fx).1 == some 2 then
      let base' : Flat.FExpr := match b.expr base with
        | .ref _ y => .ref true y
        | .refField fid _ y path star => .refField fid true y path star
        | n => n
      let (be, b') := b.add base'
      let (pe, b') := b'.add (.name none "place_at")
      modify fun s => { s with body := { b' with exprs := b'.exprs.set! value (.call cid pe #[i, be]) } }
      return

/-- Each of `dotBorrows`' receivers borrowed where it is, `&x`. -/
partial def writeDotBorrows (x : String) (borrows : List (Flat.ExprId × Bool)) : M Unit :=
  modify fun s => { s with body := borrows.foldl (fun (bb : Flat.Body) (a, uniq) =>
    { bb with exprs := bb.exprs.set! a (.ref uniq x) }) s.body }

/-- `x.f.g` where `x` holds a reference: the name, the path of fields, and the
identity of the last read. -/
partial def fieldThroughRef (scope : Scope) (e : Flat.ExprId) : M (Option (String × List String × Nat)) := do
  let b := (← get).body
  match b.expr e with
  | .fieldOf fid inner field =>
    match b.bare? inner with
    | some x =>
      let held := match scope.lookup x with
        | some (.val t _) => some t
        | some (.cell t _) => some t
        | _ => none
      match held with
      | some t => do pure (match ← find t with
        | .ref .. => some (x, [field], fid)
        | _ => none)
      | none => pure none
    | none =>
      pure ((← fieldThroughRef scope inner).map fun (x, path, _) => (x, path ++ [field], fid))
  | _ => pure none

/-- The receiver at `a`, `%receiver(*element_at(r, i))`, an element read where
it is, of a dot call of `fx`: the element's reference where `fx` takes a
reference (`element_at(r, i)`, `place_at(i, &mut ..)` for writing), the
element as it is read otherwise. -/
partial def writeElementReceiver (a : Flat.ExprId) (fx : String) : M Unit := do
  let b := (← get).body
  let .call _ _ #[r] := b.expr a | return
  let .deref inner := b.expr r | return
  let .call cid _ #[base, i] := b.expr inner | return
  let given : Flat.FExpr ← match (← receiverKinds fx fx).1 with
    | some 1 => pure (b.expr inner)
    | some 2 =>
      let base' : Flat.FExpr := match b.expr base with
        | .ref _ x => .ref true x
        | .refField fid _ x path star => .refField fid true x path star
        | n => n
      let (be, b') := b.add base'
      let (pe, b') := b'.add (.name none "place_at")
      modify fun s => { s with body := b' }
      pure (.call cid pe #[i, be])
    | _ => pure (b.expr r)
  modify fun s => { s with body := { s.body with exprs := s.body.exprs.set! a given } }

/-- An element read's place, `element_at(&x, i)` or `place_at(i, &mut x)`, of
a name that holds a reference: through it, `element_at(x, i)`, as Rust's
`x[i]` is of what `x` points to (and `&x.f` where `x` holds one, through
it). -/
partial def elementBase (scope : Scope) (f : Flat.ExprId) (args : Array Flat.ExprId) : M Unit := do
  let b := (← get).body
  let some (_, g) := b.name? f | return
  let at_ ← match Syntax.lastSegment g with
    | "element_at" => pure 0
    | "place_at" => pure 1
    | _ => return
  let some base := args[at_]? | return
  let holdsRef := fun (x : String) => (do
    match scope.lookup x with
    | some (.val t _) | some (.cell t _) => do pure (match ← find t with | .ref .. => true | _ => false)
    | _ => pure false : M Bool)
  match b.expr base with
  | .ref _ x =>
    if ← holdsRef x then
      modify fun s => { s with body := { s.body with exprs := s.body.exprs.set! base (.name none x) } }
  | .refField fid uniq x path false =>
    if ← holdsRef x then
      modify fun s => { s with body := { s.body with exprs := s.body.exprs.set! base (.refField fid uniq x path true) } }
  | _ => pure ()

/-- A path of fields from a name, `x.f.g`: the name, the path, and the
outermost field's identity. -/
partial def fieldRoot (b : Flat.Body) (e : Flat.ExprId) : Option (String × List String × Nat) :=
  let rec go (e : Flat.ExprId) (fuel : Nat) : Option (String × List String × Nat) :=
    match fuel, b.expr e with
    | fuel + 1, .fieldOf fid inner name =>
      match b.bare? inner with
      | some x => some (x, [name], fid)
      | none => (go inner fuel).map fun (x, path, _) => (x, path ++ [name], fid)
    | _, _ => none
  (go e 64).filter (·.2.2 != 0)

/-- The receiver at `a`, `%receiver(x.f)`, of a dot call of `fx`: borrowed
where it is as `fx` takes it (`&x.f`, through the reference `x` holds
where `star`), read as it is otherwise. -/
partial def writeFieldReceiver (a : Flat.ExprId) (fx : String) (star : Bool) : M Unit := do
  let b := (← get).body
  let .call _ _ #[r] := b.expr a | return
  let some (x, path, fid) := fieldRoot b r | return
  let given : Flat.FExpr ← match (← receiverKinds fx fx).1 with
    | some 0 | none => pure (b.expr r)
    | some k => pure (.refField fid (k == 2) x path star)
  modify fun s => { s with body := { s.body with exprs := s.body.exprs.set! a given } }

/-- The dot calls on the variable `x` in `rest` (`f(%receiver(x), ..)`),
each receiver borrowed as the function in scope takes it (`receiverKinds`),
written where it is before the variable's uses are looked at: whether it
gives its value away (`givenAway`) is seen of them so. One whose function
says nothing is left for the parameter's type (`receiverByType`). -/
partial def variableReceivers (x : String) (rest : List Flat.StmtId) : M Unit := do
  let b := (← get).body
  let rec calls (fuel : Nat) (e : Flat.ExprId) : List (Flat.ExprId × String) :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      let here := match b.expr e with
        | .call _ f args | .tailCall _ f args =>
          match b.bare? f, args[0]? with
          | some fx, some a =>
            match b.expr a with
            | .call _ m #[r] => if b.mark? m == some .receiver && b.bare? r == some x then [(a, fx)] else []
            | _ => []
          | _, _ => []
        | _ => []
      here ++ (b.children e).flatMap (calls fuel)
  let found := rest.flatMap fun s => (b.stmtExprs s).toList.flatMap (calls 256)
  for (a, fx) in found do
    let given : Option Flat.FExpr := match (← receiverKinds fx fx).1 with
      | some 0 => some (.name none x)
      | some k => some (.ref (k == 2) x)
      | none => none
    if let some n := given then
      modify fun s => { s with body := { s.body with exprs := s.body.exprs.set! a n } }
  -- (And a field of it, `v.items.len()`: borrowed where it is.)
  let rec fields (fuel : Nat) (e : Flat.ExprId) : List (Flat.ExprId × String) :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      let here := match b.expr e with
        | .call _ f args | .tailCall _ f args =>
          match b.bare? f, args[0]? with
          | some fx, some a =>
            match b.expr a with
            | .call _ m #[r] =>
              if b.mark? m == some .receiver && ((fieldRoot b r).map (·.1)) == some x then [(a, fx)] else []
            | _ => []
          | _, _ => []
        | _ => []
      here ++ (b.children e).flatMap (fields fuel)
  for (a, fx) in rest.flatMap fun s => (b.stmtExprs s).toList.flatMap (fields 256) do
    writeFieldReceiver a fx false
  -- (And an element of it, `v[i].push(..)`: its place, for writing.)
  let rooted := fun (base : Flat.ExprId) => match b.expr base with
    | .ref _ y => y == x
    | .refField _ _ y _ _ => y == x
    | _ => false
  let rec elements (fuel : Nat) (e : Flat.ExprId) : List (Flat.ExprId × String) :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      let here := match b.expr e with
        | .call _ f args | .tailCall _ f args =>
          match b.bare? f, args[0]? with
          | some fx, some a =>
            match b.expr a with
            | .call _ m #[r] =>
              match b.mark? m == some .receiver, b.expr r with
              | true, .deref inner =>
                match b.expr inner with
                | .call _ _ #[base, _] => if rooted base then [(a, fx)] else []
                | _ => []
              | _, _ => []
            | _ => []
          | _, _ => []
        | _ => []
      here ++ (b.children e).flatMap (elements fuel)
  for (a, fx) in rest.flatMap fun s => (b.stmtExprs s).toList.flatMap (elements 256) do
    writeElementReceiver a fx

/-- A dot call `f(%receiver(x), ..)` of a function in scope `f`: the
receiver borrowed as `f` takes it (`receiverKinds`), given as it is where
`x` holds a reference, written where it is; what the call's choice of a
function of the receiver's type does after (`inferDotAltCall`) starts from
that, as from the resolver's. Left where `f` says nothing of it, for the
parameter's type (`receiverByType`). -/
partial def receiverByName (scope : Scope) (f : Flat.ExprId) (args : Array Flat.ExprId) : M Unit := do
  let b := (← get).body
  let some a := args[0]? | return
  let .call _ m #[r] := b.expr a | return
  unless b.mark? m == some .receiver do return
  let some fx := b.bare? f | return
  let some x := b.bare? r | do
    -- (An element read where it is, `v[i].len()`.)
    if let .deref _ := b.expr r then return ← writeElementReceiver a fx
    -- (A field of a name, `p.items.len()`: borrowed where it is, through
    -- the reference the name holds where it holds one.)
    let some (x, _, _) := fieldRoot b r | return
    let star ← match scope.lookup x with
      | some (.val t _) | some (.cell t _) => do
        match ← find t with
        | .ref .. => pure true
        | _ => pure false
      | _ => pure false
    writeFieldReceiver a fx star
  let held ← match scope.lookup x with
    | some (.val t _) | some (.cell t _) => do pure (some (← find t))
    | _ => pure none
  let given : Option Flat.FExpr := match (← receiverKinds fx fx).1, held with
    | _, some (.ref ..) => some (.name none x)
    | some 0, _ => some (.name none x)
    | some k, _ => some (.ref (k == 2) x)
    | none, _ => none
  if let some n := given then
    modify fun s => { s with body := { s.body with exprs := s.body.exprs.set! a n } }

/-- A dot call's receiver `%receiver(x)` at `a`, given to a parameter of
type `p`: `&x` (`&mut x`) where `p` is a reference and `x` holds no
reference, `x` where `p` is known otherwise; left where `p` is not known
yet, and read as `x` (`inferMarkedCall`). Written where it is, as Rust
borrows a method's receiver by the method's type. -/
partial def receiverByType (scope : Scope) (p : Ty) (a : Flat.ExprId) : M Unit := do
  let b := (← get).body
  let .call _ m #[r] := b.expr a | return
  unless b.mark? m == some .receiver do return
  let some x := b.bare? r | return
  let held ← match scope.lookup x with
    | some (.val t _) | some (.cell t _) => do pure (some (← find t))
    | _ => pure none
  let given : Option Flat.FExpr ← match ← find p, held with
    | .var _, _ => pure none
    | .ref .., some (.ref ..) => pure (some (.name none x))
    | .ref how _ _, some _ => do
      let uniq := match ← find how with
        | .con "&mut" [] => true
        | _ => false
      pure (some (.ref uniq x))
    | _, _ => pure (some (.name none x))
  if let some n := given then
    modify fun s => { s with body := { s.body with exprs := s.body.exprs.set! a n } }

/-- Check arguments in the given order. Gives the first that does not fit. -/
partial def checkArgsIn (scope : Scope) (amb : Row) (what : String) (params : List Ty)
    (args : Array Flat.ExprId) (call : Nat) (order : List Nat) : M (Option (Nat × String)) := do
  for i in order do
    match params[i]?, args[i]? with
    | some p, some a =>
      let site := if call == 0 then none else some (Elab.Site.arg call i)
      -- (A dot call's receiver, a name: borrowed where the function takes a
      -- reference and the name holds none, given as it is otherwise,
      -- written where it is.)
      receiverByType scope p a
      let b := (← get).body
      -- Clauses that match what a reference points to with patterns of a
      -- value: the program is read again with those patterns written
      -- `&Pattern`, binding references, as Rust's binding modes have them.
      if let .closure id clauseIds := b.expr a then
        let clauses := clauseIds.toList.map (Flat.treeClause b)
        -- (What the arguments before it leave to implementations is found
        -- first where it can be: what the clauses are given is then of a
        -- type that is known, and a field read through a reference in them
        -- is seen as one.)
        unless (← get).assocUses.isEmpty do settleAssocsAll
        -- (Which clauses' first patterns are of a value: a constructor, a
        -- tuple, a constructor without fields written as a name.)
        -- (Not a tuple that is each of several parameters, `{ (a, b) => .. }`
        -- given two.)
        let arity := match ← find p with
          | .fn ps .. => ps.length
          | _ => 0
        let mut valuePats : List Nat := []
        for (c, k) in clauses.zipIdx do
          match c with
          | .mk (.ctor n _ _ :: _) _ => if !n.startsWith "%" then valuePats := valuePats ++ [k]
          | .mk [.tuple _] _ => if arity ≤ 1 then valuePats := valuePats ++ [k]
          | .mk (.tuple _ :: _) _ => valuePats := valuePats ++ [k]
          -- (Or a constant that is a constructor's other name, `None`.)
          | .mk (.var x :: _) _ =>
            if (← resolveCtor x none).isSome || (Syntax.lastSegment x).front.isUpper then
              valuePats := valuePats ++ [k]
          | _ => pure ()
        if !valuePats.isEmpty then
          if let .fn (first :: _) _ _ _ _ ← find p then
            if let .ref how _ _ ← find first then
              let uniq := match ← find how with
                | .con "&mut" [] => true
                | _ => false
              let shown := if uniq then "&mut " else "&"
              -- (Written `&Pattern` and written out as the resolver writes
              -- out what a program writes so, its names known.)
              let wrapped := clauses.zipIdx.map fun (c, k) => match c with
                | .mk (p :: ps) body =>
                  if valuePats.contains k then Clause.mk (.marked (.byRef uniq) [p] :: ps) body else c
                | c => c
              -- (A constant, a constructor's other name too, is a test of a
              -- value read, as the resolver has it.)
              -- (Written out in a body of their own, as the resolver writes
              -- them out, `Flat.byReference`.)
              let kindOf := fun (x : String) => (do
                let s ← getThe St
                if (s.ctors[x]?).isSome then return 1
                if (s.aliases[x]?).isSome then return 2
                return 0 : StateT Flat.Body (StateT Nat M) Nat)
              let rn : Syntax.RefNames (StateT Flat.Body (StateT Nat M)) :=
                { kind := kindOf
                  ctor := fun name qual args => do
                    match ← (resolveCtor name qual : M _) with
                    | some (global, _) => pure (global, args)
                    | none => pure (name, args)
                  ctorTest := fun name qual => do
                    pure ((← (resolveCtor name qual : M _)).map fun (global, _) => Expr.name none global)
                  fresh := modifyGetThe Nat fun n => (n, n + 1) }
              let own := Flat.ofClauses wrapped
              let (ids, own) ← ((Syntax.Flat.byReference rn own.roots).run own).run' (500000000000000000 + id * 10000)
              let lowered := ids.toList.map (Flat.treeClause own)
              throwThe Elab.Said { msg := s!"argument {i + 1} of {what}: what is matched is a reference: a pattern of what it points to is written `{shown}Pattern`, and binds references (`{shown}Some(x) => *x`)", decision := some (.refPats id lowered) }
      -- (A value made where a dot call is made on it, named and borrowed for
      -- the call (`Flat.receiverExpr`), that is a reference already: the
      -- reference is given.)
      let a ← match b.expr a with
        | .ref uniq x =>
          -- (A variable that holds a reference, borrowed for a call that
          -- takes a reference to what that one is to, `q.reach(0)` of a
          -- `let mut q: &mut P`: what it holds, borrowed again, as Rust
          -- borrows through it.)
          let through ← match scope.lookup x, ← find p with
            | some (.cell t _), .ref _ wantInner _ => do
              match ← find t, ← find wantInner with
              | .ref how _ _, .con .. =>
                let holdsUniq := match ← find how with
                  | .con "&mut" [] => true
                  | _ => false
                pure (i == 0 && call != 0 && (holdsUniq || !uniq))
              | _, _ => pure false
            | _, _ => pure false
          if through then do
            let given := Expr.reborrow uniq (.name none x)
            modify fun s => { s with argsChosen := ((call, i), given) :: s.argsChosen }
            flatIn given
          else if i == 0 && call != 0 && x == s!"borrowed%{call}" then do
            let held := match scope.lookup x with
              | some (.val t _) => some t
              | some (.cell t _) => some t
              | _ => none
            match held with
            | some t => do
              match ← find t with
              | .ref .. =>
                modify fun s => { s with argsChosen := ((call, i), .name none x) :: s.argsChosen }
                pushE (.name none x)
              | _ => pure a
            | none => pure a
          else pure a
        | _ => pure a
      -- (A dot call's receiver, a name of a type not known yet, where the
      -- function takes a reference: given as what it is, and whether it is
      -- a reference told where its type is known, `checkLateReceivers`.)
      let late ← if i == 0 && call != 0 && (dotAltsOf (← get).modules call).isSome then do
          let some x := (← get).body.bare? a | pure false
          let some (.val t _) := scope.lookup x | pure false
          match ← find p, ← find t with
          | .ref .., .var _ => pure true
          | _, _ => pure false
        else pure false
      let p ← if late then do
          let given ← freshTy
          modify fun s => { s with lateReceivers := s.lateReceivers.push (call, given, p) }
          pure given
        else pure p
      -- (A dot call whose receiver is of a type with a function of its own of
      -- the name: that one, if the function in scope does not fit.)
      let before ← get
      -- (A receiver the function in scope borrows in a way it cannot be,
      -- `&mut app` of an `app` that is not mutable, where its type has a
      -- function of its own of the name that takes it otherwise: that one.)
      let checked ← if i == 0 && call != 0 then
          tryCatchThe Elab.Said (checkArg scope amb s!"argument {i + 1} of {what}" p a site) fun ex => do
            if ex.passOn then throwThe Elab.Said ex
            let failed ← get
            set before
            let alt ← dotAltFor scope amb call a
            set failed
            match alt with
            | some alt =>
              if (what.splitOn s!"`{alt}`").length > 1 then throwThe Elab.Said ex
              else throwThe Elab.Said { ex with decision := some (← receiverDecision call alt) }
            | none => throwThe Elab.Said ex
        else checkArg scope amb s!"argument {i + 1} of {what}" p a site
      if let some e := checked then
        -- (A dot call's receiver, a name that holds a value, where the
        -- function takes a reference to it: read again with it borrowed, as
        -- Rust borrows it.)
        if i == 0 && call != 0 then
          if let some x := (← get).body.bare? a then
            if let some (.val t _) := scope.lookup x then
              if let .ref how _ _ ← find p then
                match ← find t with
                | .ref .. | .var _ => pure ()
                | _ =>
                  let uniq := match ← find how with
                    | .con "&mut" [] => true
                    | _ => false
                  -- (A value, which only a variable lets be borrowed for
                  -- writing: the type's own function of the name, where it
                  -- has one, as the program was read before.)
                  if uniq then
                    let before ← get
                    let alt ← dotAltFor scope amb call a
                    set { before with body := (← get).body, decided := (← get).decided, altFound := (← get).altFound }
                    if let some alt := alt then
                      if (what.splitOn s!"`{alt}`").length == 1 then
                        throwThe Elab.Said { msg := e, decision := some (← receiverDecision call alt) }
                  throwThe Elab.Said { msg := e, decision := some (.receiver call none (some uniq)) }
        -- (Asked only once the function in scope does not fit: the program
        -- is read again, so what this finds on the way is not kept. The
        -- receiver's type is found as it was before it was made to fit.)
        if i == 0 then
          let failed ← get
          set before
          let alt ← dotAltFor scope amb call a
          set failed
          if let some alt := alt then throwThe Elab.Said { msg := e, decision := some (← receiverDecision call alt) }
        -- (Clauses one of which ends with a braced block, which is a callable
        -- there: likely meant to be run.)
        let b := (← get).body
        let blocky := match b.expr a with
          | .closure _ clauses => clauses.any fun c =>
            match (b.clause c).body.back? with
            | some s =>
              let inner := match b.stmt s with
                | .located _ _ i => i
                | _ => s
              match b.stmt inner with
              | .expr e => (b.plainBlock e).isSome
              | _ => false
            | none => false
          | _ => false
        if blocky && (e.splitOn "fn() ->").length > 1 then
          return some (i, e ++ ". A block `{ .. }` a clause ends with is a callable; to run its statements there, write them without the braces: `pattern => a; b`")
        -- (`a + if(c) { x } else { y }` is `(a + if(c) { x }) else { y }`:
        -- `else` binds loosest of all.)
        if let .call _ f _ := b.expr a then
          if (b.name? f).map (·.2) == some "if" then
            if (e.splitOn "found `Result<").length > 1 then
              return some (i, e ++ ". `else` binds more loosely than any other operator: `a + if(c) { x } else { y }` is `(a + if(c) { x }) else { y }`; write the conditional in parentheses")
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
    (args : Array Flat.ExprId) (call : Nat := 0) : M Unit := do
  unless params.length == args.size do
    -- (A dot call of a function in scope that takes another number of
    -- arguments, of a value whose type has one of the name of its own.)
    if let some a := args[0]? then
      if let some alt ← dotAltFor scope amb call a then
        throwThe Elab.Said { msg := s!"{what} takes {params.length} arguments", decision := some (← receiverDecision call alt) }
    arityError what params.length args.size
  -- Whole numbers written without a type are looked at last: by then what
  -- is wanted of them may be known from the other arguments.
  let b := (← get).body
  let written := fun (i : Nat) => match args[i]?.map b.expr with
    | some (.int _) => true
    | _ => false
  let natural := List.range args.size
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

/-- A call of a constructor, an operation, a primitive, what an `is` found, a
cast or a host function (`inferCall`). -/
partial def inferCallBuiltin (scope : Scope) (amb : Row) (args : Array Flat.ExprId) (call : Nat) (x : String)
    (head : Head) : M Ty := do
  let b := (← get).body
  match head with
  | .ctor sig written => do
    let (fields, result) ← instCtor sig
    -- A name given to the constructor with a type: built at that type.
    if let some ty := written then
      let said ← resolveType [] false (ty.typeWritten)
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
    -- `operation<A>(..)`: which instance of its effect, said.
    if let some written := (← get).instWith then
      modify fun s => { s with instWith := none }
      let types := (inst.zip (decl.lifetimes ++ List.replicate inst.length false)).filterMap fun (t, life) =>
        if life then none else some t
      unless written.length == types.length do
        throw s!"`{sig.effect}` has {types.length} type parameters, and `{x}` is written with {written.length}"
      for (t, w) in types.zip written do
        unify t w
    let own ← sig.caps.mapM fun c => do pure (c, ← freshCap)
    let (payload, result) := instOp sig inst own
    -- (What a type parameter of the effect leaves to an implementation,
    -- `S::Out`: asked now, of the type this use gives.)
    let payload ← payload.mapM unproject
    let result ← result.mapM unproject
    -- (What it is given first: that can say which instance of its effect
    -- this is, where there are several.)
    checkArgs scope amb s!"operation `{x}`" payload args call
    try
      match ← findInstance (← flattenRow amb).effs (sig.effect, inst) with
      | some (_, args') => unifyAll inst args'
      | none => unifyRow amb ⟨[(sig.effect, inst)], some (← freshRowVar)⟩
    catch e => throw s!"operation `{x}` cannot be performed here: {e}"
    -- Which instance of its effect this is, for when each is made an
    -- effect of its own.
    let which := (inst.zip (decl.lifetimes ++ List.replicate inst.length false)).filterMap fun (t, life) =>
      if life then none else some t
    unless which.isEmpty do
      modify fun s => { s with instSites := s.instSites.push (s.owner, call, "op", sig.effect, which) }
    -- What the effect's declaration asks of its parameters.
    if let some asked := (← get).typeBounds.lookup sig.effect then
      if call != 0 then
        needBounds (100000000000000000 + call) (asked.filterMap fun (tr, i) => inst[i]?.map (tr, ·))
    -- The handler may run a callable it is given, there and then.
    use scope (.call s!"operation `{x}`" payload)
    match result with
    | some r => pure r
    | none => freshTy
  | .prim => do
    -- The intrinsics of `[T; N]`, of whatever their elements are. Reading a
    -- place and putting another value at one let go of what is not given
    -- back.
    let t ← freshTy
    match x with
    | "fixed_make" =>
      checkArgs scope amb "the array" (List.replicate args.size t) args call
      pure (.con "Fixed" [t, lengthTy 64 args.size])
    -- Of `[T; N]`: `N` of one value, the element at a place, one with
    -- another there, and a place in one.
    | "fixed_fill" =>
      let n ← freshTy
      checkArgs scope amb s!"intrinsic `{x}`" [t, .int] args call
      mustDup t "`[x; n]` is `n` of one value, copied"
      pure (.con "Fixed" [t, n])
    | "fixed_get" =>
      checkArgs scope amb s!"intrinsic `{x}`" [.con "Fixed" [t, ← freshTy], .int] args call
      mustDrop t "reading a place of a `[T; N]` lets go of the rest of it"
      pure t
    | "fixed_set" =>
      let n ← freshTy
      checkArgs scope amb s!"intrinsic `{x}`" [.con "Fixed" [t, n], .int, t] args call
      mustDrop t "putting a value at a place of a `[T; N]` lets go of what was there"
      pure (.con "Fixed" [t, n])
    | "fixed_len" =>
      checkArgs scope amb s!"intrinsic `{x}`" [.con "Fixed" [t, ← freshTy]] args call
      mustDrop t "measuring a `[T; N]` lets go of it"
      pure .int
    | "fixed_len_at" =>
      checkArgs scope amb s!"intrinsic `{x}`" [.ref (← freshTy) (.con "Fixed" [t, ← freshTy]) (← freshCap)] args call
      pure .int
    | "fixed_at" =>
      let how ← freshTy
      let cap ← freshCap
      checkArgs scope amb s!"intrinsic `{x}`" [.ref how (.con "Fixed" [t, ← freshTy]) cap, .int] args call
      pure (.ref how t cap)
    | _ => throw s!"`{x}`: an intrinsic not declared; this is a compiler defect"
  | .pack name => do
    let ts ← args.toList.mapM fun _ => freshTy
    checkArgs scope amb "what an `is` found" ts args call
    pure (.con name ts)
  | .host id => do
    -- (The host's operations are declared in the prelude, each with its
    -- type, but for these three: bytes the program has from its start, a
    -- foreign function's call, of however many whole numbers, and a
    -- callable given to C.)
    if id == 19 then
      -- The address of a block of these bytes, written out.
      checkArgs scope amb s!"`{x}`" (args.toList.map fun _ => Ty.int) args call
      return .con "usize" []
    let s ← get
    unless s.unsafeBlock || s.unsafeFns.contains s.owner do
      throw s!"`{x}` is unsafe: it can be named only in `unsafe \{ .. }` or in an `unsafe fn`"
    if id == 2 then
      -- A foreign function's name, how many bits it gives, and what it is given.
      checkArgs scope amb s!"`{x}`" (args.toList.map fun _ => Ty.int) args call
      pure .int
    else
      -- The callable is given to C for as long as the program runs. What
      -- it takes and gives is C's to get right: whole numbers and
      -- addresses, as `usize`.
      -- An effect cannot pass C, so the callable performs none.
      let arity ← match args.toList.map b.expr with
        | [_, .int n] => pure n.toNat
        | _ => throw s!"`{x}` is given a callable and how many whole numbers C gives it, written out: `{x}(f, 2)`"
      unless arity ≤ 5 do throw s!"`{x}`: C gives a callable at most five whole numbers"
      let given := Ty.func (List.replicate arity (.con "usize" [])) .int ⟨[], none⟩ (← freshCap)
      checkArgs scope amb s!"`{x}`" [given, .int] args call
      pure (.con "usize" [])
  | _ => throw "a call's callee was taken for one of another kind; this is a compiler defect"

/-- A call of what works on a place (`cancel`, `replace`, `swap`,
`overwrite`, `transmute`) or of a local (`inferCall`). -/
partial def inferCallPlace (scope : Scope) (amb : Row) (args : Array Flat.ExprId) (call : Nat) (x : String)
    (head : Head) : M Ty := do
  let b := (← get).body
  match head with
  | .cancel => do
    -- Giving up a callable: a resumption, or any other callable, which
    -- destroys what it holds. (Of one argument unless it is a name whose
    -- type says otherwise.)
    let row ← freshRow
    let known ← match args.toList.map b.expr with
      | [.name none y] =>
        match scope.lookup y with
        | some (.val t _) => pure (some t)
        | some (.poly p) => pure (some p.ty)
        | _ => pure none
      | _ => pure none
    let arity ← match known with
      | some t => do
        match ← find t with
        | .fn ps .. => pure ps.length
        | _ => pure 1
      | none => pure 1
    let given := Ty.func (← (List.range arity).mapM fun _ => freshTy) (← freshTy) row (← freshCap)
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
  | .readOut => do
    -- What a reference points to read out of it and left there as it is:
    -- the value is then in two places, which is why it is unsafe: whoever
    -- writes it says the one left is not used again.
    let s ← get
    unless s.unsafeBlock || s.unsafeFns.contains s.owner do
      throw "`read_out` is unsafe: what the reference points to is read out and also left where it is. It can be named only in `unsafe { .. }` or in an `unsafe fn`"
    let t ← freshTy
    let cap ← freshCap
    checkArgs scope amb "`read_out`" [.ref .shared t cap] args call
    use scope (.through cap "the reference given to `read_out`" false)
    pure t
  | .transmute => do
    -- A value seen as of another type, which nothing is asked of: a
    -- reference's borrow, given, is not one the result is said to hold.
    -- What the two types are is the writer's word, which is why it is
    -- unsafe.
    let s ← get
    unless s.unsafeBlock || s.unsafeFns.contains s.owner do
      throw "`transmute` is unsafe: a value is seen as of another type, which nothing checks. It can be named only in `unsafe { .. }` or in an `unsafe fn`"
    checkArgs scope amb "`transmute`" [← freshTy] args call
    freshTy
  | .local (.val t _) => applyTy scope amb s!"`{x}`" t args call
  | .local (.cell t brand) => do
    mustDup t (readsCell x)
    use scope (.var brand x .read)
    applyTy scope amb s!"`{x}`" t args call
  | .local (.label t brand) => do
    applyTy scope amb s!"the label `{x}`" (← labelType t brand) args call
  | .local (.poly s) => do
    applyTy scope amb s!"`{x}`" (← instantiate s (some x)) args call
  | _ => throw "a call's callee was taken for one of another kind; this is a compiler defect"

/-- A call of a function, a trait's function or a constant (`inferCall`). -/
partial def inferCallFn (scope : Scope) (amb : Row) (args : Array Flat.ExprId) (call : Nat) (x : String)
    (head : Head) : M Ty := do
  let b := (← get).body
  match head with
  | .fn t bounds inGroup => do
    -- The instances of effects the function called is about, at this call.
    unless inGroup do
      let sites := (← get).lastSites
      unless sites.isEmpty do
        modify fun s => { s with instSites := s.instSites.push (s.owner, call, "call", x, sites) }
    -- Blocks given to run in an environment, as the function says; of
    -- them, those given what holds it run in its place (`checkArg`).
    for (i, inPlace) in ((← get).fnRunsIn.lookup x).getD [] do
      if let some (id, _) := (args[i]?).bind b.plainBlock then
        modify fun s =>
          { s with envBlocks := s.envBlocks.insert id
                   inPlace := if inPlace then s.inPlace.insert id else s.inPlace }
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
            match b.plainBlock a with
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
    -- (Its own type parameters anew, and an answer for each place its
    -- types ask a type the trait leaves at types.)
    let mut anew : List (Nat × Ty) := []
    for (g, id) in sig.mparams do
      let t ← freshTy
      anew := anew ++ [(id, t)]
      -- (How often it uses a value of one, as the trait says: at most
      -- once, where it says nothing.)
      let (lower, upper) := (sig.uses.find? (·.1 == g)).map (·.2) |>.getD (0, some 1)
      let pos := (← get).pos
      if lower == 0 then
        modify fun s => { s with drops := s.drops.push (t, s!"{pos}`{x}` may leave a `{g}` unused") }
      if upper.isNone then
        modify fun s => { s with dups := s.dups.push (t, s!"{pos}`{x}` may use a `{g}` more than once") }
    for (_, _, id) in sig.gats do
      anew := anew ++ [(id, ← freshTy)]
    let tm := (sig.self, self) :: sig.tparams.zip targs ++ (sig.assocs.map (·.2)).zip found ++ anew
    let subject := if targs.isEmpty then self else Ty.tuple (self :: targs)
    let ownUses := (← get).assocUses.size
    for ((name, _), a) in sig.assocs.zip found do
      modify fun s =>
        { s with assocUses := s.assocUses.push (sig.trait, subject, name, a, s.owner, s.pos) }
    let row : Row :=
      ⟨sig.row.effs.map fun (e, args) => (e, args.map (subst tm rm [])),
        sig.row.tail.map fun k => (rm.lookup k).getD k⟩
    -- (Where a type left at types is asked at a lifetime, that lifetime
    -- is the one of this use: the function's lifetimes and those asked
    -- are made new together.)
    let asking := sig.gats.map fun (_, asked, _) => Ty.tuple (asked.map (subst tm [] []))
    let both ← freshenCaps (← unproject (.tuple
      (.func (sig.params.map (subst tm rm [])) (subst tm rm [] sig.ret) row (← freshCap) :: asking)))
    let (callee, asking) := match both with
      | .tuple (c :: rest) => (c, rest)
      | other => (other, asking)
    for ((name, _, id), asked) in sig.gats.zip asking do
      let asked := match asked with
        | .tuple ts => ts
        | t => [t]
      let answer := subst tm [] [] (.var id)
      let use := (sig.trait, Ty.con Syntax.gatMark (self :: asked), name, answer, (← get).owner, (← get).pos)
      modify fun s => { s with assocUses := s.assocUses.push use }
      let lives := asked.filterMap fun | .ref (.con "'" []) _ c => some c | _ => none
      if let .var v := answer then
        unless lives.isEmpty do modify fun s => { s with gatHolds := s.gatHolds.push (v, lives) }
    -- (A callable it is given may be called any number of times, or not
    -- at all, by an implementation, as a function's may: what it holds
    -- is asked to be one that can be.)
    if let .fn ps _ _ _ _ ← find callee then
      let pos := (← get).pos
      for p in ps do
        if let .fn .. ← find p then
          modify fun s =>
            { s with dups := s.dups.push (p, s!"{pos}`{x}` may call what it is given more than once")
                     drops := s.drops.push (p, s!"{pos}`{x}` may leave what it is given uncalled") }
    -- (Needed first: what it asks may decide what its arguments are wanted
    -- to be, `x + 1` of `Add<R = Self>`. Kept after those its arguments
    -- need, as they would have been.)
    let at_ := (← get).bounds.size
    -- (Wanted to be a whole number of a type, `n + 1` a clause of a `u8`
    -- ends with: of a trait whose other arguments are its type where not
    -- written, the type it is asked of is that one.)
    if let some (id, wanted) := (← get).wantResult then
      if id == call && (← get).selfDefaults.contains (sig.trait) then
        if let .var _ ← find self then unify self wanted
    needBounds call [(sig.trait, subject)]
    let r ← applyTy scope amb s!"`{x}`" callee args call
    modify fun s =>
      match s.bounds[at_]? with
      | some own => { s with bounds := (s.bounds.eraseIdx! at_).push own }
      | none => s
    -- (Of a type not decided at an argument that is a type of whole numbers
    -- where the trait's argument is its type where not written, `n + 1`:
    -- of that type, as an implementation that does not write it is.)
    if let some places := (← get).selfDefaults[sig.trait]? then
      if let .var _ ← find self then
        for i in places do
          if let some a := targs[i]? then
            if let .con n [] ← find a then
              if n == "Int" || (Syntax.scalars.lookup n).isSome then
                unify self a
                break
    -- (What the trait leaves to the implementation, there now if the
    -- arguments decided which: `Output` of `x + 1`.)
    if ((← get).assocUses.size > ownUses) && (← find r) matches .var _ then
      settleAssocsFrom ownUses
    modify fun s => { s with methodCalls := s.methodCalls.push (call, sig.index) }
    -- (`a[i]` copies the element out: one that cannot be copied is taken
    -- out with `pop` or `remove`, or borrowed.)
    if x == "index" && Syntax.lastSegment sig.trait == "Index" then
      mustDup r "`a[i]` copies the element (take it out with `pop` or `remove`, or borrow it, `&a[i]`)"
    pure r
  | .const e => do
    let (cb, ce) := Flat.ofExpr e
    applyTy scope amb s!"`{x}`" (← withBody cb (inferExpr [] amb ce)) args call
  | _ => throw "a call's callee was taken for one of another kind; this is a compiler defect"

/-- A call that is a mark the parser wrote, `move x`, `f<A>(..)` or `let x:
Type = value`: its type; none where it is not one (`inferCall`). -/
partial def inferMarkedCall (scope : Scope) (amb : Row) (f : Flat.ExprId) (args : Array Flat.ExprId) :
    M (Option Ty) := do
  let b := (← get).body
  -- (A dot call's receiver the front end left as it is: what it is.)
  if let (some .receiver, #[r]) := (b.mark? f, args) then
    return some (← inferExpr scope amb r)
  -- `let x: Type = value`: the value is made that type.
  if let (some .move, #[operand]) := (b.mark? f, args) then
    -- `move x`: the value of `x`. That `x` is not used after is looked at
    -- where its statement is.
    match b.expr operand with
    | .name none x =>
      match scope.lookup x with
      | some (.cell _ _) =>
        throw s!"`move {x}`: `{x}` is a mutable variable, which holds a value while it is there; `replace({x}, value)` takes what it holds and leaves another"
      | _ => return some (← inferExpr scope amb operand)
    | .deref _ =>
      throw "`move *reference` would leave the reference pointing at nothing until it is written again, and that is not followed: `replace(reference, value)` takes what is there and leaves another"
    | _ => return some (← inferExpr scope amb operand)
  if let (some mark, #[value, ty]) := (b.mark? f, args) then
    if mark == .inst then
      -- `f<A, B>(..)`: the call, with the types written kept for when the
      -- function called is found.
      let tys ← match b.typeAt ty with
        | .tuple tys => (tys.filter fun
            | .name l [] => !l.startsWith "'"
            | _ => true).mapM (resolveType (← get).rigidParams false)
        | _ => pure []
      modify fun s => { s with instWith := some tys }
      let t ← inferExpr scope amb value
      if (← get).instWith.isSome then
        modify fun s => { s with instWith := none }
        throw "types are written, `f<A, B>(..)`, for a function of a module that has type parameters; what is called here is not one"
      return some t
    if mark == .ascribe then
      let expected ← resolveType (← get).rigidParams false (b.typeAt ty)
      if ← textAt expected value then return some expected
      if let .int n := b.expr value then
        match ← literalAt expected n value with
        | some none => return some expected
        | some (some why) => throw why
        | none => pure ()
      -- A callable written with its parameters' types: its clauses are
      -- read knowing them, so a field read through a parameter that is a
      -- reference is found.
      let found ← match b.expr value, ← find expected with
        | .closure id clauses, .fn ps _ _ _ _ =>
          let arity := match clauses[0]? with
            | some c => (b.clause c).pats.length
            | none => 0
          if arity == ps.length && arity != 0 then
            inferCallable scope (ps.map some) none none clauses "the clauses of this callable do" id
          else inferExpr scope amb value
        | _, _ => inferExpr scope amb value
      match ← fitAt scope amb "the value of a `let` with a type" none expected found with
      | none => return some expected
      | some e => throw e
  pure none

/-- A dot call of a reference to a value of the function's type, where the
function takes the value whole: of the value it points to, as Rust's
receiver is dereferenced (`part.len()` of a `part: &&str`). Its type; none
where the receiver is no such reference. -/
partial def derefReceiver (scope : Scope) (amb : Row) (args : Array Flat.ExprId) (alt : String)
    (call : Nat) : M (Option Ty) := do
  let some a := args[0]? | return none
  let b := (← get).body
  -- (A name, as written or as borrowed for another function: its type as
  -- the scope has it, nothing read again.)
  let some v := (match b.expr a with
    | .ref _ v => some v
    | .name none v => some v
    | _ => none) | return none
  let found := match scope.lookup v with
    | some (.val t _) => some t
    | some (.cell t _) => some t
    | _ => none
  let through ← match found with
    | some t => do
      match ← find t with
      | .ref _ inner _ => do pure ((← headName 8 inner).any fun h => alt.startsWith (h ++ "::"))
      | _ => pure false
    | none => pure false
  unless through do return none
  let given := Expr.deref (.name none v)
  modify fun s => { s with dotChosen := (call, alt, 0) :: s.dotChosen,
                           argsChosen := ((call, 0), given) :: s.argsChosen }
  let given ← flatIn given
  return some (← inferCall scope amb (← pushE (.name none alt)) (#[given] ++ args.extract 1 args.size) call)

/-- A dot call of a field of what a name points to, where the function
borrows its receiver (`k` of `receiverKinds`) and the resolver could not
tell to: the field, borrowed where it is, as Rust's receiver is
(`fuel.0.to_string()`). Its type; none where the receiver is no such
field. -/
partial def borrowFieldReceiver (scope : Scope) (amb : Row) (args : Array Flat.ExprId) (alt : String)
    (kind : Option Nat) (call : Nat) : M (Option Ty) := do
  let some k := kind | return none
  if k == 0 then return none
  let some a := args[0]? | return none
  let some (v, path, fid) ← fieldThroughRef scope a | return none
  -- (What the name points to known, as a field borrowed through it is read
  -- where it is: else the read waits, as it would unborrowed.)
  let pointee : M Bool := do
    match scope.lookup v with
    | some (.val t _) | some (.cell t _) =>
      match ← find t with
      | .ref _ inner _ => do pure (match ← find inner with | .var _ => false | _ => true)
      | _ => pure false
    | _ => pure false
  unless ← pointee do
    unless (← get).assocUses.isEmpty do settleAssocsAll
    unless ← pointee do return none
  let bt := Expr.refField fid (k == 2) v path true
  modify fun s => { s with dotChosen := (call, alt, 0) :: s.dotChosen,
                           argsChosen := ((call, 0), bt) :: s.argsChosen }
  let given ← flatIn bt
  return some (← inferCall scope amb (← pushE (.name none alt)) (#[given] ++ args.extract 1 args.size) call)

/-- A dot call taken as the function of the value's type: its type; none
where it is not taken so (`inferCall`). -/
partial def inferDotAltCall (scope : Scope) (amb : Row) (f : Flat.ExprId) (args : Array Flat.ExprId)
    (call : Nat) : M (Option Ty) := do
  let b := (← get).body
  -- A dot call the resolver could not tell: the function of the value's
  -- type, where it takes its first argument as the one written does (so
  -- that the receiver is borrowed as it should be); the program is read
  -- again only where it does not.
  if let some x := b.bare? f then
    if let some alts := dotAltsOf (← get).modules call then
      -- (The only one of the name: as it is, or through the reference; or,
      -- where it borrows and the resolver could not tell to, of a field of
      -- what a name points to, `fuel.0.to_string()`, borrowed where it is,
      -- as Rust's receiver is.)
      if alts.isEmpty then
        match (← receiverKinds x x).2 with
        | some 0 =>
          if let some t ← derefReceiver scope amb args x call then return some t
        | some _ =>
          if let some t ← borrowFieldReceiver scope amb args x (← receiverKinds x x).2 call then return some t
        | none => pure ()
        return none
      if let some a := args[0]? then
        if let some alt ← dotAltFor scope amb call a then
          if alt != x && alts.contains alt then
            let (mine, theirs) ← receiverKinds x alt
            if theirs == some 0 then
              if let some t ← derefReceiver scope amb args alt call then return some t
            if let some t ← borrowFieldReceiver scope amb args alt theirs call then return some t
            if mine.isSome && mine == theirs then
              modify fun s => { s with dotChosen := (call, alt, 0) :: s.dotChosen }
              return some (← inferCall scope amb (← pushE (.name none alt)) args call)
            -- (The one in scope takes a reference, the type's own the value
            -- whole: the receiver, a name borrowed for the one in scope, is
            -- given as it is.)
            if let (some k, some 0, .ref _ v) := (mine, theirs, b.expr a) then
              let moved := (← get).movedCells
              -- (A value named for the call, not a variable: the type's own
              -- function is given it, as `wholeReceiver` says of a variable.)
              let held := match scope.lookup v with
                | some (.cell _ brand) => moved.contains brand
                | some (.val ..) => true
                | _ => false
              if k != 0 && (!v.startsWith "borrowed%" || held) then
                let given := Expr.name none v
                modify fun s => { s with dotChosen := (call, alt, 0) :: s.dotChosen,
                                         argsChosen := ((call, 0), given) :: s.argsChosen }
                let given ← flatIn given
                return some (← inferCall scope amb (← pushE (.name none alt)) (#[given] ++ args.extract 1 args.size) call)
            -- (The one in scope takes the value whole, the type's own a
            -- reference: a mutable variable is borrowed for it.)
            if let (some 0, some k, .name none v) := (mine, theirs, b.expr a) then
              if k != 0 then
                if let some (.cell held _) := scope.lookup v then
                  -- (One that holds a reference already is given as it is.)
                  if let .ref .. ← find held then
                    modify fun s => { s with dotChosen := (call, alt, 0) :: s.dotChosen }
                    return some (← inferCall scope amb (← pushE (.name none alt)) args call)
                  modify fun s => { s with dotChosen := (call, alt, k) :: s.dotChosen }
                  let given ← pushE (.ref (k == 2) v)
                  return some (← inferCall scope amb (← pushE (.name none alt)) (#[given] ++ args.extract 1 args.size) call)
            if let (some 0, some k) := (mine, theirs) then
              if k != 0 then
                -- (What is a reference already, a name that holds one or a
                -- call that gives one, is given as it is.)
                let saved ← get
                let given ← try some <$> inferExpr scope amb a catch _ => pure none
                let isRef ← match given with
                  | some t => do pure (match ← find t with | .ref .. => true | _ => false)
                  | none => pure false
                set saved
                if isRef then
                  modify fun s => { s with dotChosen := (call, alt, 0) :: s.dotChosen }
                  return some (← inferCall scope amb (← pushE (.name none alt)) args call)
                -- (Else: read again with the receiver borrowed where it is,
                -- as the resolver borrows one, `g[0].push(5)`, `v[0].s.len()`.)
                throwThe Elab.Said { msg := s!"the receiver of `{alt}` is borrowed", decision := some (← receiverDecision call alt) }
  pure none

/-- Apply a callee of a given type in the ambient effects. -/
partial def applyTy (scope : Scope) (amb : Row) (what : String) (callee : Ty) (args : Array Flat.ExprId)
    (call : Nat := 0) : M Ty := do
  abandons (← get).anon what call
  pushTemp callee
  -- A callable for every lifetime is called at lifetimes of this call's own.
  let (callee, _) ← openRanked callee
  match ← find callee with
  | .fn ps r effs tail _ => do
    -- (What the call's result is wanted to be, where a body ends with it and
    -- the result is open: known before the arguments are read, so that a
    -- whole number a clause given ends with is of it.)
    if let some (c, w) := (← get).wantResult then
      if c == call && call != 0 then
        modify fun s => { s with wantResult := none }
        if let .var _ ← find r then
          let saved ← get
          try unify r w catch _ => set saved
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
    unifyAt s!"{what} is called with {arguments args.size}"
      (.func argTys.toList r row (← freshCap)) t
    use scope (.call what (callee :: argTys.toList))
    includeRow row amb what
    pure r

partial def inferCall (scope : Scope) (amb : Row) (f : Flat.ExprId) (args : Array Flat.ExprId)
    (call : Nat := 0) : M Ty := do
  if let some t ← inferMarkedCall scope amb f args then return t
  elementBase scope f args
  receiverByName scope f args
  let b := (← get).body
  if let some t ← inferDotAltCall scope amb f args call then return t
  -- `T::f(..)` of a type parameter `T` and a trait's function `f`: as
  -- `<T as Trait>::f(..)` is.
  if let .name (some q) x := b.expr f then
    if let some self := (← get).rigidParams.lookup q then
      if let some sig := (← get).methods[x]? then
        if (← get).instWith.isNone then
          modify fun s => { s with instWith := some [self] }
          let t ← inferCall scope amb (← pushE (.name (some sig.trait) x)) args call
          if (← get).instWith.isSome then modify fun s => { s with instWith := none }
          return t
  match b.expr f with
  | .name q x =>
    -- (A dot call of a function in scope that cannot be called as written,
    -- `v.get<T>(..)` of one without type parameters, of a value whose type
    -- has a function of the name of its own: that one.)
    let head ← tryCatchThe Elab.Said (resolveName scope q x) fun e => do
      if e.passOn || e.decision.isSome || call == 0 then throwThe Elab.Said e
      if let some a := args[0]? then
        if let some alt ← dotAltFor scope amb call a then
          if alt != x then throwThe Elab.Said { e with decision := some (← receiverDecision call alt) }
      throwThe Elab.Said e
    match head with
    | .ctor .. | .op _ | .prim | .pack _ | .host _ => inferCallBuiltin scope amb args call x head
    | .fn .. | .method _ | .const _ => inferCallFn scope amb args call x head
    | _ => inferCallPlace scope amb args call x head
  | .label l => do
    applyTy scope amb s!"the label `@{l}`" (← inferExpr scope amb f) args call
  | _ => do
    -- (`value.name(..)` where `name` is no field: if types have a function of
    -- their own of that name, that is what was meant, and which one could
    -- not be told by the name alone.)
    -- (Read, and where it fails put back as it was but for what was written
    -- in place while it was read, which is of the program: read again, it
    -- would be decided again, and a chain of calls was read anew at each
    -- link, three times a link.)
    let before ← get
    let callee ← (fun s => match inferExpr scope amb f s with
      | .ok t s => .ok (Sum.inl t) s
      | .error e s => .ok (Sum.inr e) { before with body := s.body, decided := s.decided, altFound := s.altFound } : M (Ty ⊕ Elab.Said))
    let callee ← match callee with
      | .inl t => pure t
      | .inr said => do
      let e := said.msg
      match b.expr f with
      | .fieldOf _ recv name =>
        let theirs := (((← get).fns.toList.filter fun (fn, _) => fn.endsWith s!"::{name}").map (·.1)).mergeSort (· ≤ ·)
        -- (Taken for a field because some type has a field of the name: the
        -- function of the value's type's own, if it has one; the type said
        -- where the field was not found, or the receiver read again.)
        if call != 0 && (e.splitOn "has no field").length > 1 then
          let saved ← get
          let head ← match said.subject with
            | some h => pure (some h)
            | none => do
              let found ← try some <$> inferExpr scope amb recv catch _ => pure none
              match found with
              | some ty => do
                let rec go (fuel : Nat) (t : Ty) : M (Option String) := do
                  match fuel, ← find t with
                  | fuel + 1, .ref _ inner _ => go fuel inner
                  | _, .con n _ => pure (some n)
                  | _, _ => pure none
                go 8 ty
              | none => pure none
          set saved
          if let some h := head then
            let own := s!"{h}::{name}"
            if ((← get).fns[own]?).isSome then
              throwThe Elab.Said { said with decision := some (← receiverDecision call own) }
        if (e.splitOn "has no field").length > 1 && theirs.length > 1 then
          throw s!"{e}. More than one type has a function `{name}` of its own ({", ".intercalate (theirs.map fun fn => s!"`{bareName fn}`")}): say which, `Type::{name}(value, ..)`"
        else throwThe Elab.Said said
      | _ => throwThe Elab.Said said
    -- (A field that holds no callable, `p.x()` where `x` is a field and the
    -- type's own function: the function, the program read again so.)
    if let .fieldOf _ recv name := b.expr f then
      if call != 0 then
        match ← find callee with
        | .fn .. | .var _ => pure ()
        | _ =>
          let saved ← get
          let found ← try some <$> inferExpr scope amb recv catch _ => pure none
          let rec headOf (fuel : Nat) (t : Ty) : M (Option String) := do
            match fuel, ← find t with
            | fuel + 1, .ref _ inner _ => headOf fuel inner
            | _, .con n _ => pure (some n)
            | _, _ => pure none
          let h ← match found with
            | some ty => headOf 8 ty
            | none => pure none
          set saved
          if let some h := h then
            let own := s!"{h}::{name}"
            if ((← get).fns[own]?).isSome then
              throwThe Elab.Said { msg := s!"the field `{name}` is no callable", decision := some (← receiverDecision call own) }
    applyTy scope amb "this callee" callee args call

/-- `let pattern = value` and the statements after it (`inferStmts`). -/
partial def inferLetStmt (scope : Scope) (amb : Row) (rest : List Flat.StmtId)
    (want : Option (Ty × Option Elab.Site)) (pat : Pattern) (value : Flat.ExprId) : M Ty := do
  let b := (← get).body
  let closure := match pat, b.expr value with
    | .var x, .closure _ _ => some x
    | _, _ => none
  match closure with
  | some x => do
  let (at_, pos) := ((← get).at_, (← get).pos)
  let t ← withLater (b.fvStmts [x] rest) (inferExpr scope amb value)
  if (← resolveCtor x none).isSome || ((← get).aliases[x]?).isSome then
    let binds ← inferPat (.var x) t
    inferStmts (binds ++ scope) amb rest want
  else
    -- A callable nothing then uses is let go when the block ends: if it
    -- holds something to destroy, it is given up there.
    unless (b.fvStmts [] rest).contains x do
      modify fun s =>
        { s with dropCands := s.dropCands.push (⟨s.owner, at_.1, at_.2, .name x, false⟩, t, pos) }
    -- A callable bound by `let` is a value, so it can be used at several types.
    -- Everything its surroundings already depend on stays fixed.
    let s ← get
    let mut keep : List Ty := [.func [] .unit amb (← freshCap)]
    for (_, bd) in scope do
      keep := (match bd with
        | .val t _ | .cell t _ | .label t _ => t
        | .poly p => p.ty) :: keep
    for (_, t) in s.group do
      keep := t :: keep
    for (subject, _, result, _, _) in s.projections do
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
    -- What it lets go of, or reads a part of, where that is of a type it
    -- is general in: a callable is given nothing by which it could be
    -- told how each type is destroyed, so each use is asked that the
    -- type it is used at has nothing to destroy.
    let mut quiets : List (Ty × String) := []
    for held in (← get).dropCands.toList.map (·.2.1) ++ (← get).lateKeeps.toList.map (·.2.1) do
      let held ← zonk held
      if (freeTys held).any scheme.tvars.contains then
        quiets := quiets ++ [(held, s!"`{x}` lets go of what it is given, whatever type that is, and is used here at a type with something to destroy, which it has no way to: say the type where `{x}` takes it, `fn(value: Type) \{ .. }`")]
    let scheme := { scheme with quiets := quiets }
    let here := (← get).pos
    let result ← inferStmts ((x, .poly scheme) :: scope) amb rest want
    checkUses (← get).body here scope [(x, .poly scheme)] rest
    pure result
  | none => do
  let (at_, pos) := ((← get).at_, (← get).pos)
  if let .var x := pat then elementPlaceFor x value rest
  let b := (← get).body
  let t ← withLater (b.fvStmts (Elab.patVars pat) rest) (inferRoot scope amb value)
  -- A value given a name that nothing then uses is owned by the name: if it
  -- is one to destroy, that happens when the block ends.
  if let .var x := pat then
    unless (b.fvStmts [] rest).contains x || (← resolveCtor x none).isSome
        || ((← get).aliases[x]?).isSome do
      modify fun s =>
        { s with dropCands := s.dropCands.push (⟨s.owner, at_.1, at_.2, .name x, false⟩, t, pos) }
  -- (A type left to an implementation is found now where it can be: what
  -- the pattern takes, and what is read of it after, is then of a type
  -- that is known, and what has a `drop` to run is seen to have one.)
  settleAssocs
  let binds ← match pat with
    | .var _ => inferPat pat t
    | _ => do
      -- What a pattern takes under a name that nothing then uses, or
      -- under `_`, is destroyed when the block ends, as a clause's is.
      modify fun s => { s with wildAt := some at_, wildCount := 0, wildLet := true }
      let binds ← inferPat pat t
      modify fun s => { s with wildAt := none, wildLet := false }
      let mentioned := b.fvStmts [] rest
      for (x, bd) in binds do
        if let .val tx bid := bd then
          modify fun s => { s with bindSites := (bid, at_.1, at_.2) :: s.bindSites, letBinds := bid :: s.letBinds }
          unless mentioned.contains x || x.startsWith "%" do
            let site : Elab.DropSite := ⟨(← get).owner, at_.1, at_.2, .letBound x, false⟩
            modify fun s => { s with dropCands := s.dropCands.push (site, tx, pos) }
      pure binds
  if let .var x := pat then
    for (_, bd) in binds do
      if let .val _ bid := bd then
        modify fun s => { s with bindSites := (bid, at_.1, at_.2) :: s.bindSites }
    -- (Its dot calls the function of its type's own borrows it for are not
    -- uses that give it away, as a variable's are, `dotBorrows`: it is a
    -- place where they are made, borrowed there.)
    writeDotBorrows x (← dotBorrows b x t rest)
  let check : Pending := ⟨(← get).pos, "the pattern of this `let` does", [t], [[pat]]⟩
  modify fun s => { s with pending := s.pending.push check }
  let here := (← get).pos
  -- (What has a `drop` to run where the block ends, and is not given away
  -- before, holds what it borrows till then.)
  let held ← binds.filterMapM fun (x, bd) => do
    match bd with
    | .val tx _ => pure (if !b.givenAway x rest && (← hasDropOwn tx) then some x else none)
    | _ => pure none
  let outerLive := (← get).dropLive
  modify fun s => { s with dropLive := held ++ s.dropLive }
  let result ← inferStmts (binds ++ scope) amb rest want
  modify fun s => { s with dropLive := outerLive }
  checkUses (← get).body here scope binds rest
  -- A name borrowed (`placeVal`) is a place till its block ends: nothing
  -- borrowed of it may be left after, and the elaborator keeps it as a
  -- variable (`St.placedLets`).
  do
    for (x, bd) in binds do
      if let .val _ bid := bd then
        if (← get).placedVals.contains bid then
          checkEscape bid s!"`{x}` could be used after its block has ended"
            (("something that uses it is the block's result", result) :: scopeRoots scope) amb
          -- (Only borrowed, never given away, nor a part of it read, which
          -- may give that part away: destroyed where its block ends, as a
          -- variable's value is.)
          let u := b.nameUseStmts false x rest
          let tx := match bd with
            | .val tx _ => tx
            | _ => t
          modify fun s =>
            { s with placedLets := s.placedLets.push (s.owner, at_.1, at_.2, x)
                     placedLetIds := bid :: s.placedLetIds
                     dropCands := if u.valued || u.valuedInside || u.looked then s.dropCands
                       else s.dropCands.push (⟨s.owner, at_.1, at_.2, .name x, false⟩, tx, pos) }
  pure result

/-- `let mut x = value` and the statements after it (`inferStmts`). -/
partial def inferLetMutStmt (scope : Scope) (amb : Row) (rest : List Flat.StmtId)
    (want : Option (Ty × Option Elab.Site)) (x : String) (value : Flat.ExprId) : M Ty := do
  variableReceivers x rest
  let b := (← get).body
  let (at_, pos) := ((← get).at_, (← get).pos)
  let t ← withLater (b.fvStmts [x] rest) (inferRoot scope amb value)
  -- The variable lives until the end of this block: nothing that can reach
  -- it may be left over afterwards.
  let brand ← freshBrand
  -- A variable that is never assigned, borrowed for writing or bound
  -- again holds one value for as long as it lasts. Where that value is
  -- also used as it is, outside any callable, the variable is a name
  -- that can be borrowed: the value is given away by the use, counted as
  -- a name's uses are, and is not the variable's to destroy.
  -- (And is not borrowed again once it has been.)
  -- (A value made where a dot call is made on it, named to be borrowed for
  -- the function the resolver took, whose type's own function of the name
  -- takes it whole: given to that one, `wholeReceiver`.)
  -- (Its dot calls the function of its type's own borrows it for are not
  -- uses that give it away, `dotBorrows`.)
  writeDotBorrows x (← dotBorrows b x t rest)
  let b := (← get).body
  let given := b.givenAway x rest || (← wholeReceiver b x t rest)
  modify fun s =>
    { s with
      cells := s.cells.push (brand, x, t)
      movedCells := if given then brand :: s.movedCells else s.movedCells
      -- A variable owns what it holds. One that gives it away owns it
      -- where it has not: whether that is anywhere is seen once the
      -- uses are counted, and its cleanup is put in then.
      dropCands := if given then s.dropCands
        else s.dropCands.push (⟨s.owner, at_.1, at_.2, .name x, false⟩, t, pos) }
  -- Nothing says the variable is empty when its block ends: what it holds
  -- then is let go. Unless the very next statement is a cleanup that takes
  -- it out, leaving something that holds nothing: that runs last of all
  -- that the block does to the variable, however the block is left.
  let finalised ← match rest.head?.map fun s => b.stmt (b.unlocated s) with
    | some (.defer e) =>
      match takesOut b x e with
      | some put => holdsNothing (Flat.treeExpr b put)
      | none => pure false
    | _ => pure false
  unless finalised || given do
    mustDrop t s!"the mutable variable `{x}` lets go of what it holds when its block ends (a `defer` straight after it can take that out with `replace`)"
  let here := (← get).pos
  if given then
    modify fun s =>
      { s with
        flagged := (s.owner, here) :: s.flagged
        givenSites := (here, ⟨s.owner, at_.1, at_.2, .given x, false⟩, t, pos) :: s.givenSites }
  -- (What it holds has a `drop` to run where the block ends: what that
  -- borrows is held till then.)
  let outerLive := (← get).dropLive
  if !given && (← hasDropOwn t) then modify fun s => { s with dropLive := x :: s.dropLive }
  let result ← inferStmts ((x, .cell t brand) :: scope) amb rest want
  modify fun s => { s with dropLive := outerLive }
  if given then
    let (lb, less) := Flat.lessPartsStmts (← get).body x rest
    checkUses lb here scope [(x, .val t brand)] less
  checkEscape brand s!"`{x}` could be used after its block has ended"
    (("something that uses it is the block's result", result) :: scopeRoots scope) amb
  pure result

/-- `target = value` and the statements after it (`inferStmts`). -/
partial def inferAssignStmt (scope : Scope) (amb : Row) (rest : List Flat.StmtId)
    (want : Option (Ty × Option Elab.Site)) (target value : Flat.ExprId) : M Ty := do
  let b := (← get).body
  withLater (b.fvStmts [] rest) do
    -- The value is computed first, and then the place is written.
    let (expected, written) ← match b.expr target with
      | .name none x =>
        match scope.lookup x with
        | some (.cell t brand) => do
          -- What the variable held is destroyed.
          modify fun s =>
            { s with dropCands :=
                s.dropCands.push (⟨s.owner, s.at_.1, s.at_.2, .name x, true⟩, t, s.pos) }
          mustDrop t s!"assigning to `{x}` lets go of what it holds (`replace` takes it out instead)"
          pure (t, UseKind.var brand x .write)
        | some _ => throw s!"`{x}` is not a mutable variable: write `let mut {x}` where it is bound to change it"
        | none => throw s!"unknown name `{x}`"
      | .deref e => do
        let inner ← freshTy
        let cap ← freshCap
        unifyAt "`*` assigns through a reference" (.ref .uniq inner cap)
          (← inferPlace scope amb e)
        mustDrop inner "assigning through a reference lets go of what was there"
        -- What was there is destroyed.
        modify fun s =>
          { s with dropCands :=
              s.dropCands.push (⟨s.owner, s.at_.1, s.at_.2, .deref, true⟩, inner, s.pos) }
        pure (inner, UseKind.through cap (placeName b e) true)
      | _ => throw "only a mutable variable or `*reference` can be assigned"
    let whole ← match b.expr value with
      | .int n => literalAt expected n value
      | _ => pure none
    match whole with
    | some none => pure ()
    | some (some why) => throw s!"the assigned value: {why}"
    | none => unifyAt "the assigned value" expected (← inferRoot scope amb value)
    use scope written
  inferStmts scope amb rest want

/-- The type of a block: that of its last expression, or unit. -/
partial def inferStmts (scope : Scope) (amb : Row) (stmts : List Flat.StmtId)
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
      | some e => throwThe Elab.Said { msg := e, result := true } : M Ty)
  match stmts with
  | [] => finish .unit false
  | s0 :: rest => do
  -- (An assignment through `DerefMut`, written where it is, and read on.)
  if ← derefAssignHere scope s0 then return ← inferStmts scope amb (s0 :: rest) want
  let b := (← get).body
  match b.stmt s0 with
  | .located line col s => do
    modify fun st => { st with pos := s!"{line}:{col}: ", at_ := (line, col) }
    -- What `move x` hands on is not there for the statements after.
    for x in b.movedStmt s do
      if (b.fvStmts [] rest).contains x then
        throw (positioned line col s!"`{x}` is used after `move {x}` handed it on")
    onError (inferStmts scope amb (s :: rest) want) (positioned line col)
  | .expr e =>
    match b.mark? e with
    | some .observed => inferStmts scope amb rest want
    | some .unsafe_ => do
      -- What follows in this block may name what is unsafe.
      let before := (← get).unsafeBlock
      modify fun s => { s with unsafeBlock := true }
      let t ← inferStmts scope amb rest want
      modify fun s => { s with unsafeBlock := before }
      pure t
    | _ =>
    if rest.isEmpty then do
      -- (A call a body ends with whose result is wanted to be a whole number
      -- of a type: said to the call, `match x { .. => 5 }` of a `u8`.)
      if let (.call id _ _, some (expected, _)) := (b.expr e, want) then
        if let .con n [] ← find expected then
          if Syntax.isScalar n then
            modify fun s => { s with wantResult := some (id, expected) }
      -- A text a body ends with, where `&str` is wanted of the body.
      if let some (expected, _) := want then
        if ← textAt expected e then return expected
      -- A whole number a body ends with is of the type wanted of the body.
      if let (.int n, some (expected, _)) := (b.expr e, want) then
        match ← literalAt expected n e with
        | some none => return expected
        | some (some why) => throwThe Elab.Said { msg := s!"the result of a clause: {why}", result := true }
        | none => pure ()
      -- (`if(c) { a }` without `else` gives a `Result`: where a value is
      -- wanted, `else` is what is missing.)
      let isIf := match b.expr e with
        | .call _ f _ => (b.name? f).map (·.2) == some "if"
        | _ => false
      if let (true, some (expected, _)) := (isIf, want) then
        match ← find expected with
        | .con n _ =>
          unless Syntax.lastSegment n == "Result" do
            let t ← inferExpr scope amb e
            return ← onError (finish t true) (· ++ ". `if(c) { a }` without `else` gives `Ok(a)` or `Err(..)`: write `else { b }` for the value where the condition fails")
        | _ => pure ()
      -- (A block a clause ends with is a callable, `{ .. }` as anywhere: one
      -- wanted to be run there is written without its braces.)
      if let (some _, some (expected, _)) := (b.plainBlock e, want) then
        match ← find expected with
        | .fn _ _ _ _ _ | .var _ => pure ()
        | _ =>
          let t ← inferExpr scope amb e
          return ← onError (finish t true) (· ++ ". A block `{ .. }` a clause ends with is a callable; to run its statements there, write them without the braces: `pattern => a; b`")
      finish (← inferRoot scope amb e) true
    else do
      let t ← withLater (b.fvStmts [] rest) (inferRoot scope amb e)
      mustDrop t "the value of a statement is let go"
      -- If it is one to destroy, that happens here.
      modify fun s =>
        { s with dropCands := s.dropCands.push (⟨s.owner, s.at_.1, s.at_.2, .name Elab.stmtValue, false⟩, t, s.pos) }
      inferStmts scope amb rest want
  | .let_ pat value => inferLetStmt scope amb rest want pat value
  | .letMut x value => inferLetMutStmt scope amb rest want x value
  | .assign target value => inferAssignStmt scope amb rest want target value
  | .defer e => do
    -- A cleanup performs no effects: it may run while its surroundings are
    -- being left, when no handler should be asked to do anything.
    -- (What it reads of a name's value is read when the rest is left, after
    -- what the rest reads: not before, `St.valReads`.)
    let readsBefore := (← get).valReads
    onError (do
      let t ← withLater (b.fvStmts [] rest) (inferExpr scope ⟨[], none⟩ e)
      mustDrop t "what a `defer` gives is let go") fun err => s!"a `defer` cannot perform effects: {err}"
    modify fun s => { s with valReads := readsBefore }
    -- It runs when the rest is left, so what it mentions is still to be used
    -- throughout the rest.
    let result ← withLater (b.fvExpr [] e) (inferStmts scope amb rest want)
    -- (A name it borrows whose value the rest gives away: borrowed after.)
    for x in (b.fvExpr [] e).eraseDups do
      if let some (.val _ id) := scope.lookup x then
        let u := b.nameUseExpr false x e
        if !u.valued && !u.valuedInside then readBefore id x
    pure result

/-- Check a pattern against a type; the names it binds. -/
partial def inferPat (p : Pattern) (t : Ty) : M Scope := do
  -- (A pattern that asks something of a value whose type is not known yet:
  -- what traits leave to implementations is settled first, where it can
  -- be. `let (Box(n), rest) = rest_first(s)` of a `&[Box]` is of `Part` of
  -- `RestOf` for it, which is `&Box`: matched, the pattern reaches through
  -- the reference, as Rust's do.)
  match p with
  | .wild | .var _ => pure ()
  | _ =>
    if let .var _ ← find t then
      unless (← get).assocUses.isEmpty do settleAssocsAll
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
  | .marked m _ => throw s!"`{m.shown}` in a pattern where it cannot be; this is a compiler defect"
  | .wild => do
    mustDrop t "`_` lets go of a value"
    -- If it is one to destroy, that happens when its clause is done.
    if let some place := (← get).wildAt then
      modify fun s =>
        { s with
          wildCount := s.wildCount + 1
          dropCands := s.dropCands.push
            (⟨s.owner, place.1, place.2,
              (if s.wildLet then .letBound (Elab.letWildName place.1 place.2 s.wildCount)
               else .name (Elab.wildName s.wildCount)), false⟩, t, s.pos) }
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
    -- `(first, ..)`: how many parts `..` stands for is what the tuple has
    -- beyond those written. Said to whoever is reading the program, which
    -- is then read with them written.
    if let some id := ps.findSome? fun
        | .marked .rest [.int id] => some id.toNat
        | _ => none then
      match ← find t with
      | .tuple parts =>
        if parts.length + 1 < ps.length then
          throw s!"a tuple pattern with {ps.length - 1} parts and `..`, of a tuple of {parts.length}"
        -- (Written where it is, in the body as in the pattern read here,
        -- `Elab.restNode`: nothing was read of it before.)
        let count := parts.length + 1 - ps.length
        match Elab.restNode id count (← get).body with
        | some b' =>
          modify fun s => { s with body := b', decided := s.decided ++ [.restHere id count] }
          return ← inferPat (Elab.restPat id count (.tuple ps)) t
        | none => throw "`..` in a tuple pattern that is not where the program has it; this is a compiler defect"
      | _ => throw "`..` in a tuple pattern stands for the parts not written, and how many the tuple has is not known here: say its type"
    -- (`()` of a reference to `()`: there is nothing in it to borrow.)
    if ps.isEmpty then
      if let .ref _ inner _ ← find t then
        unifyAt "a tuple pattern" (.tuple []) inner
        return []
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
      match (← get).aliases[x]? with
      | some e => do inferPat (← match Syntax.exprToPat e with | .ok p => pure p | .error m => throw m) t
      | none => do
        let id ← freshBrand
        modify fun s => { s with bindLoans := s.bindLoans.insert id s.loans.size }
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
        if !ps.isEmpty && s.kimpls.has (.of "Drop") n then
          if let some here := s.modules.homes.lookup s.owner then
            let home := "::".intercalate ((n.splitOn "::").dropLast)
            unless here == home do
              throw s!"`{Syntax.lastSegment n}` has `Drop`, so only the module that declares it can take one apart with a pattern: what `drop` does would not be done"
      inferPats ps fields
    | none =>
      if (Syntax.restPatParts x).isSome then
        throw "an array pattern with `..` is a whole clause's pattern, `[first, ..rest] => ..`: it is not read inside another pattern, nor where a function's parameters are"
      throw s!"unknown constructor `{x}` in a pattern"

/-- Read the patterns of a clause whose body is `body`. What the clause is
given under a name and does not mention is the name's, and what a `_` takes is
let go: if either is one to destroy, that happens when the clause is done. The
place it is known by is the clause's first statement. -/
partial def clauseGiven (body : List Flat.StmtId) (patterns : M Scope) (spared : List String := []) :
    M Scope := do
  let b := (← get).body
  let first := b.clausePlace body
  -- (A clause that looks at a copy of what a reference points to owns none
  -- of it: nothing its patterns take is destroyed.)
  let observed := match body.head?.map fun s => b.stmt (b.unlocated s) with
    | some (.expr e) => b.mark? e == some .observed
    | _ => false
  modify fun s => { s with wildAt := if observed then none else some first, wildCount := 0 }
  let binds ← patterns
  modify fun s => { s with wildAt := none }
  let mentioned := b.fvStmts [] body
  for (x, b) in binds do
    if let .val t bid := b then
      modify fun s => { s with bindSites := (bid, first.1, first.2) :: s.bindSites }
      unless mentioned.contains x || x.startsWith "%" || observed || spared.contains x do
        modify fun s =>
          { s with dropCands := s.dropCands.push (⟨s.owner, first.1, first.2, .name x, false⟩, t, s.pos) }
  pure binds

partial def inferPats (ps : List Pattern) (ts : List Ty) : M Scope := do
  let mut out : Scope := []
  for (p, t) in ps.zip ts do
    out := (← inferPat p t) ++ out
  pure out

/-- The names a clause's patterns bind (`binds`) that are places
(`placeVal`): each kept in a variable where the clause's statements start
(`Elab.heldFirst`), which destroys what it holds where the clause ends if
the body only borrows it and reads its parts, as a `let`'s does. -/
partial def placedParams (binds : Scope) (body : List Flat.StmtId) : M Unit := do
  let b := (← get).body
  let some (.located l c _) := body.head?.map b.stmt | return
  for (x, bd) in binds do
    if let .val tx bid := bd then
      if (← get).placedVals.contains bid then
        let u := b.nameUseStmts false x body
        unless u.valued || u.valuedInside || u.looked do
          modify fun s =>
            { s with dropCands := s.dropCands.push (⟨s.owner, l, c, .name x, false⟩, tx, s.pos) }

/-- The type of a callable given by clauses. Parameter and result annotations
are checked if present; the clauses must cover every argument. -/
partial def inferCallable (scope : Scope) (annots : List (Option Ty)) (ret : Option Ty)
    (self : Option String) (clauses : Array Flat.ClauseId) (what : String) (id : Nat := 0) : M Ty := do
  let b := (← get).body
  let arity := match clauses[0]? with
    | some c => (b.clause c).pats.length
    | none => 0
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
  let free := (b.fvClauses clauses).eraseDups
  for x in free do
    if let some (.cell _ brand) := scope.lookup x then
      if (← get).movedCells.contains brand then
        let u := b.nameUseClauses x clauses
        if u.valued || u.valuedInside then
          modify fun s =>
            { s with heldMoves := s.heldMoves.push ⟨s.owner, s.pos, .var brand x .move [], scope, s.later, s.temps⟩ }
  modify fun s =>
    { s with later := free, temps := [], anon := [] }
  -- What the callable captures from the scope it is written in.
  let cap ← freshCap
  -- (A value it only borrows, `&x` of one not a reference: as a place.)
  let seen := b
  let borrowsOnly := fun (x : String) => clauses.all fun c =>
    let u := seen.nameUseClause false x c
    !u.valued && !u.valuedInside && !u.looked
  captureAll scope cap (b.fvClauses clauses) (fun x => clauses.any (assignsClause b x))
    (fun x => clauses.any fun c =>
      let u := seen.nameUseClause false x c
      u.valued || u.valuedInside)
    (fun x => match scope.lookup x with
      | some (.val _ _) => borrowsOnly x
      | _ => false)
  -- A value it captures is the callable's: if the callable is let go without
  -- being called, it destroys the value. The elaborator asks how, by the
  -- callable as written and the name.
  let written := b.hashClosure id clauses
  for x in free do
    let held := match scope.lookup x with
      | some (.val tx _) => if borrowsOnly x then none else some tx
      -- (A callable kept by `let`: the value is the one callable.)
      | some (.poly p) => some p.ty
      | _ => none
    if let some tx := held then
      let site := Elab.captureDropSite (← get).owner written x
      modify fun s => { s with dropCands := s.dropCands.push (site, tx, s.pos) }
  let loansBefore := (← get).loans.size
  -- What `unsafe { .. }` allows is allowed where it is written, not in a
  -- callable written inside it, which runs later.
  let unsafeBefore := (← get).unsafeBlock
  modify fun s => { s with unsafeBlock := false }
  let brand ← freshBrand
  -- (Written `@f` also for a function of a module or a type's own,
  -- `m::f` or `T::f`.)
  let scope := match self with
    | some name =>
      let short := Syntax.labelShort name
      let scope := ("@" ++ name, Binding.label result brand) :: scope
      if short != name then ("@" ++ short, Binding.label result brand) :: scope else scope
    | none => scope
  -- Where the result of clause `j` can be converted, if this callable is one
  -- the elaborator can be told about.
  let site := fun (j : Nat) => match self with
    | some name => some (Elab.Site.fnResult name j)
    | none => if id == 0 then none else some (Elab.Site.result id j)
  let checkClause := fun (j : Nat) => (do
    match clauses[j]?.map b.clause with
    | none => pure none
    | some ⟨pats, body⟩ =>
      let body := body.toList
      unless pats.length == arity do
        throw "the clauses of a callable take different numbers of arguments"
      let binds ← clauseGiven body (inferPats pats params)
      let names := binds.map (·.1)
      if let some x := names.find? fun x => (names.filter (· == x)).length > 1 then
        throw s!"`{x}` is bound twice by the patterns of one clause"
      let here := (← get).pos
      let at_ := if b.wrapsResult body then site j else none
      -- (In an arm: the branch of an `if` it is, or the clause.)
      let arm := match (← get).altArms[((← get).owner, id)]? with
        | some (g, k) => (2 * g + 1, k)
        | none => (2 * id, j)
      -- (Where the clause's statements are is theirs: what follows it is
      -- where the callable is, as is what the compiler wrote at no place in
      -- the next clause.)
      let place := ((← get).pos, (← get).at_)
      let failure ← tryCatchThe Elab.Said
          (do
            let _ ← inArm arm (inferStmts (binds ++ scope) row body (some (result, at_)))
            modify fun s => { s with pos := place.1, at_ := place.2 }
            placedParams binds body
            pure none) fun e =>
          if e.result then pure (some e.msg)
          else throwThe Elab.Said e
      match failure with
      | some e => pure (some e)
      | none =>
        -- Uses are counted in the body as it will be elaborated.
        let cs := Elab.firstOf (← get).coercions.toList
        if cs.isEmpty then checkUses (← get).body here scope binds body
        else
          let (c, coerced) := (Elab.coerceClause cs ((site j).bind (cs[·]?)) clauses[j]!).run (← get).body
          checkUses coerced here scope binds (coerced.clause c).body.toList
        pure none : M (Option String))
  -- As with arguments: a clause whose result does not fit is looked at first
  -- on a second attempt, so that the others can be converted to what it gives.
  let order := List.range clauses.size
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
  let check : Pending := ⟨(← get).pos, what, params, clauses.toList.map fun c => (b.clause c).pats⟩
  modify fun s => { s with pending := s.pending.push check }
  -- A function's own label returns from it, so nothing holding that label may
  -- be handed back to the caller.
  if let some name := self then
    let roots := ("it is returned from the function", result) ::
      params.map fun p => ("the caller could hold it through a parameter", p)
    checkEscape brand (jumpsAfter name) roots row
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
partial def inferHandle (scope : Scope) (amb : Row) (whole subject : Flat.ExprId) (arms : Array Flat.ClauseId) :
    M Ty := do
  let s ← get
  let b := s.body
  let mut completions : Array (Pattern × List Flat.StmtId) := #[]
  let mut opArms : Array (String × OpSig × List Pattern × List Flat.StmtId) := #[]
  for arm in arms do
    let ⟨pats, body⟩ := b.clause arm
    let body := body.toList
    match pats with
    | [.ctor x q ps] =>
      match s.ops.lookup x with
      | some sig =>
        if let some owner := q then
          unless owner == sig.effect do throw s!"`{x}` is not an operation of `{owner}`"
        opArms := opArms.push (x, sig, ps, body)
      | none => completions := completions.push (.ctor x q ps, body)
    | [p] => completions := completions.push (p, body)
    | _ => throw "a handler arm has exactly one head pattern"
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
  modify fun st => { st with later := b.fvExpr [] whole ++ outerLater }
  let loansBefore := (← get).loans.size
  let subjectTy ← inferExpr scope ⟨insts ++ ambFlat.effs, ambFlat.tail⟩ subject
  -- The borrows the handled computation makes. While it is suspended in an
  -- arm, its resumption holds them: the arm must not use what they exclude.
  let suspendedLoans := List.range' loansBefore ((← get).loans.size - loansBefore)
  -- (What holds the suspended computation: its loans, and all it uses.)
  let suspended := fun (must : Bool) => do
    let held ← freshCap
    captures held .once
    if must then captures held .must
    for id in suspendedLoans do
      captures held (.inner id)
    captureAll scope held (b.fvExpr [] whole) fun x =>
      assignsExpr b x whole
    pure held
  let result ← freshTy
  if completions.isEmpty then unify result subjectTy
  else
    for (p, body) in completions do
      let binds ← clauseGiven body (inferPat p subjectTy)
      let here := (← get).pos
      unifyAt "the result of a completion clause" result
        (← inferStmts (binds ++ scope) amb body)
      checkUses (← get).body here scope binds body
      placedParams binds body
    let check : Pending := ⟨(← get).pos, "the completion clauses of this handler do", [subjectTy],
      completions.toList.map fun (p, _) => [p]⟩
    modify fun st => { st with pending := st.pending.push check }
  let mut covered : List String := []
  for (x, sig, ps, body) in opArms do
    let inst := (insts.lookup sig.effect).getD []
    -- (What the payload borrows from the performer is borrowed from it for
    -- as long as the arm runs: as from a variable of the arm's own.)
    let own ← sig.caps.mapM fun c => do pure (c, ← freshCap)
    let lent ← freshBrand
    for (_, c) in own do
      captures c (.brand lent)
    let (payload, opResult) := instOp sig inst own
    let payload ← payload.mapM unproject
    let opResult ← opResult.mapM unproject
    let borrowed := !own.isEmpty && (← payload.anyM fun p => do
      pure (own.any fun (_, c) => (freeCaps p).contains c))
    if borrowed then
      if opResult.isNone then
        throw s!"the operation `{x}` does not return, so its performer is gone before an arm runs: what it is given cannot borrow"
      unless ps.length == payload.length do
        throw s!"the arm for `{x}` is given what borrows from its performer, which is gone once it is resumed: write the arm without the resumption, `{x}(..) => value`, which resumes with the value when the arm is done"
    match opResult with
    | none =>
      unless ps.length == payload.length do
        arityError s!"an arm for the operation `{x}`" payload.length ps.length
      let binds ← clauseGiven body (inferPats ps payload)
      let here := (← get).pos
      unifyAt s!"the result of the arm for `{x}`" result (← inferStmts (binds ++ scope) amb body)
      checkUses (← get).body here scope binds body
      placedParams binds body
      if ← ps.allM irrefutable then covered := x :: covered
    | some o =>
      if ps.length == payload.length + 1 then
        -- The resumption holds the handled computation and, because resuming
        -- reinstalls the handler, the arms too: everything either of them uses.
        let held ← suspended sig.must
        -- (A resumption the arm does not use is given up as the arm starts,
        -- by the elaborator: nothing destroys it when the arm is done.)
        let resumptionTy := Ty.func [o] result amb held
        -- (`_` for it too: its pattern is read with no place for what it
        -- lets go.)
        let patterns : M Scope := do
          let before ← inferPats ps.dropLast payload
          modify fun s => { s with wildAt := none }
          match ps.getLast? with
          | some last => pure ((← inferPat last resumptionTy) ++ before)
          | none => pure before
        let binds ← clauseGiven body patterns (match ps.getLast? with
          | some (.var k) => [k]
          | _ => [])
        let here := (← get).pos
        unifyAt s!"the result of the arm for `{x}`" result
          (← inferStmts (binds ++ scope) amb body)
        checkUses (← get).body here scope binds body
        placedParams binds body
        if ← (ps.take payload.length).allM irrefutable then covered := x :: covered
      else if ps.length == payload.length then
        let binds ← clauseGiven body (inferPats ps payload)
        let here := (← get).pos
        -- The arm resumes with what it gives: the computation is suspended,
        -- holding its borrows, for as long as the arm runs.
        let held ← suspended false
        let resumption := ("%resumed", Binding.val (.func [o] result amb held))
        unifyAt s!"the value the arm for `{x}` resumes with" o
          (← withLater ["%resumed"] (inferStmts (binds ++ resumption :: scope) amb body))
        checkUses (← get).body here scope binds body
        placedParams binds body
        if borrowed then
          checkEscape lent s!"what the operation `{x}` was given borrows from its performer and could be used after the arm" (scopeRoots scope) amb
        if ← ps.allM irrefutable then covered := x :: covered
      else arityError s!"an arm for the operation `{x}`" payload.length ps.length
  for (e, inst) in insts do
    let decl := (s.effects.lookup e).getD ⟨[], [], []⟩
    let which := (inst.zip (decl.lifetimes ++ List.replicate inst.length false)).filterMap fun (t, life) =>
      if life then none else some t
    unless which.isEmpty do
      -- (Told by the number of the call that is the computation handled.)
      let subjectId := b.subjectCall subject
      modify fun st => { st with instSites := st.instSites.push (st.owner, subjectId, "handle", e, which) }
    unless decl.ops.all covered.contains do
      try unifyRow amb ⟨[(e, inst)], some (← freshRowVar)⟩
      catch err =>
        throw s!"this handler does not handle every `{e}` operation, and the rest cannot \
          be passed on: {err}"
  modify fun st => { st with later := outerLater }
  pure result

end

end Glorious.Check
