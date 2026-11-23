module

public import Glorious.Check.Uses

public section

namespace Glorious.Check

open Syntax

/-! ## Borrows

`&x` borrows a mutable variable for reading, `&mut x` for writing too. A
borrow lasts for as long as something that holds it may still be used: the
reference itself, a value it was put in, a callable that captured it, a
variable it was assigned to. While a `&mut` borrow lasts, the variable can be
used only through it; while a `&` borrow lasts, the variable cannot be assigned
or borrowed with `&mut`.

A callable that mentions a mutable variable does not borrow it. It uses the
variable when it runs, so what a borrow forbids is calling it. This is what
lets a condition and a body, or the arms of a handler, be separate callables
over the same variables, with no rule that knows what `while` or `if` is.

A `&mut` reference used as a value is lent rather than copied: what receives it
borrows from it, and the reference cannot be used again until that is over.

Each use is recorded with what was still to be used when it happened, and
checked once the types say what holds which borrow.
-/

def withLater {α : Type} (names : List String) (act : M α) : M α := do
  let outer := (← get).later
  -- (A name whose value has a `drop` to run where its block ends is used
  -- there: what it holds is held till then.)
  modify fun s => { s with later := names ++ s.dropLive ++ outer }
  let r ← act
  modify fun s => { s with later := outer }
  pure r

/-- Does a value of this type have a `drop` of its own to run, or hold one
that has, as far as its type's arguments say? -/
partial def hasDropOwn (t : Ty) : M Bool := do
  match ← find t with
  | .con n args =>
    if (← get).kimpls.has "Drop" n then return true
    args.anyM hasDropOwn
  | .tuple parts => parts.anyM hasDropOwn
  | _ => pure false

/-- Run a part of an expression, forgetting the values it computed on the way. -/
def withTemps {α : Type} (act : M α) : M α := do
  let outer := (← get).temps
  let anon := (← get).anon
  let r ← act
  modify fun s => { s with temps := outer, anon := anon }
  pure r

def pushTemp (t : Ty) : M Unit := modify fun s => { s with temps := (t, s.loans.size) :: s.temps }

/-- A value just computed that has no name: until it is passed on, nothing
but the expression holds it. A name's value is the name's to account for. -/
def pushAnon (e : Flat.ExprId) (t : Ty) : M Unit := do
  unless (← get).anyMust do return
  match ← node e with
  | .name _ _ => pure ()
  | .int _ => pure ()
  | .label _ => pure ()
  | .closure _ _ => pure ()
  | .ref _ _ => pure ()
  | _ => modify fun s => { s with anon := t :: s.anon }

/-- Something that may not come back is about to run: the values still waiting
are let go if it does not. -/
def abandons (waiting : List Ty) (what : String) (call : Nat := 0) : M Unit := do
  unless (← get).anyMust do return
  for t in waiting do
    let why := s!"a value computed before {what} is let go if that does not return (give it a name first)"
    -- A call with an identity is looked at again once its type is known.
    if call == 0 then mustDrop t why
    else modify fun s => { s with abandoned := s.abandoned.push (call, t, s.pos ++ why) }

def use (scope : Scope) (kind : UseKind) : M Unit :=
  modify fun s =>
    { s with uses := s.uses.push ⟨s.owner, s.pos, kind, scope, s.later, s.temps⟩ }

def freshLoan (root : Option Nat) (uniq : Bool) (parent : Option (Nat × Nat))
    (path : List Nat := []) : M Nat := do
  let id := (← get).loans.size
  modify fun s => { s with loans := s.loans.push ⟨id, root, uniq, parent, path⟩ }
  pure id

mutual

partial def capHoldsLoan (loan : Nat) (cap : Nat) (suspended : Bool := false)
    (plain : Bool := false) : M Bool := do
  let root ← findCap cap
  let s ← get
  -- A resumption is a computation set aside: the borrows its callables make
  -- while they run are borrows it holds. `plain` asks only for what a value
  -- holds as a value.
  let mut suspended := suspended
  unless suspended || plain do
    for (_, what) in ← edgesFrom root do
      if let .once := what then suspended := true
  let mark := 2 * root + (if suspended then 1 else 0)
  if s.seen.contains mark then return false
  modify fun s => { s with seen := s.seen.insert mark }
  for (_, what) in ← edgesFrom root do
    match what with
    | .loan l => if l == loan then return true
    | .inner l => if suspended && l == loan then return true
    | .ty t =>
      -- What a function gives back at a lifetime it declares is not
      -- thereby held by everything else of that lifetime: a parameter
      -- holds what it was given, and what is put into it.
      let given := match t with
        | .ref (.con "'given" []) (.tuple []) _ => true
        | _ => false
      if !given then
        if ← tyHoldsLoan loan t suspended plain then return true
    | .brand b | .touch b _ => if ← cellHoldsLoan loan b suspended plain then return true
    | .once | .must => pure ()
  return false

/-- A callable that uses a mutable variable can reach what the variable holds. -/
partial def cellHoldsLoan (loan : Nat) (brand : Nat) (suspended : Bool := false)
    (plain : Bool := false) : M Bool := do
  for (b, _, t) in (← get).cells do
    if b == brand then
      if ← tyHoldsLoan loan t suspended plain then return true
  return false

/-- Does a value of this type hold the borrow? What a callable takes and gives
back is not what it holds: only what it captured is. -/
partial def tyHoldsLoan (loan : Nat) (t : Ty) (suspended : Bool := false)
    (plain : Bool := false) : M Bool := do
  match ← find t with
  | .var v =>
    -- (A type a trait leaves at a lifetime, not known here: it may hold
    -- what that lifetime borrows.)
    for (w, lives) in (← get).gatHolds do
      if let .var r' ← find (.var w) then
        if r' == v then
          if ← lives.anyM (capHoldsLoan loan · suspended plain) then return true
    pure false
  | .con _ args | .tuple args => args.anyM (tyHoldsLoan loan · suspended plain)
  | .fn _ _ _ _ cap => capHoldsLoan loan cap suspended plain
  | .ref _ t cap => do
    if ← capHoldsLoan loan cap suspended plain then return true
    tyHoldsLoan loan t suspended plain

end

mutual

partial def capTouches (cap : Nat) (out : List (Nat × Bool)) : M (List (Nat × Bool)) := do
  let some edges ← unseenEdges cap | return out
  let mut out := out
  for (_, what) in edges do
    match what with
    | .touch b w => unless out.contains (b, w) do out := (b, w) :: out
    | .ty t => out ← tyTouches t out
    | _ => pure ()
  return out

/-- The mutable variables that running the callables a value holds may read or
assign. -/
partial def tyTouches (t : Ty) (out : List (Nat × Bool)) : M (List (Nat × Bool)) := do
  match ← find t with
  | .fn _ _ _ _ cap => capTouches cap out
  | t => t.parts.foldlM (fun o a => tyTouches a o) out

end

mutual

/-- Could running a callable look at a variable other than by being where its
value goes? One that takes the value uses the variable for that alone, or it
would not be given the value. -/
partial def capLooks (brand : Nat) (cap : Nat) : M Bool := do
  let some edges ← unseenEdges cap | return false
  let root ← findCap cap
  let mut takes := false
  for (c, b) in (← get).givers do
    if b == brand && (← findCap c) == root then takes := true
  for (_, what) in edges do
    match what with
    | .touch b _ => if b == brand && !takes then return true
    | .ty t => if ← tyLooks brand t then return true
    | _ => pure ()
  return false

partial def tyLooks (brand : Nat) (t : Ty) : M Bool := do
  match ← find t with
  | .fn _ _ _ _ cap => capLooks brand cap
  | t => t.parts.anyM (tyLooks brand)

end

/-- Whether doing this to a variable is forbidden by a borrow of it. -/
def Using.forbiddenBy (how : Using) (uniq : Bool) : Bool :=
  match how with
  | .read | .share => uniq
  | .write | .move | .lend => true

/-- The types a binding's value has, for looking into what it holds. -/
def Binding.held : Binding → Option Ty
  | .val t _ | .cell t _ => some t
  | .poly s => some s.ty
  | .label _ _ => none

def holdsLoan (loan : Nat) (t : Ty) : M Bool := do
  modify fun s => { s with seen := {} }
  tyHoldsLoan loan t

def touchesVar (brand : Nat) (write : Bool) (t : Ty) : M Bool := do
  modify fun s => { s with seen := {} }
  let touched ← tyTouches t []
  pure (touched.any fun (b, w) => b == brand && (w || !write))

/-- A value computed before a borrow was first made cannot hold it, unless it
came from something that was there before and does: a variable that keeps what
an earlier run of the same code borrowed. -/
def tempHolds (loan : Nat) (u : Use) (t : Ty) (made : Nat) : M Bool := do
  unless ← holdsLoan loan t do return false
  if loan < made then return true
  for (_, b) in u.scope do
    if let some t := b.held then
      if ← holdsLoan loan t then return true
  return false

/-- What still holds a borrow where a use happens, if anything does. A value
bound before the borrow was made does not hold it, as a value computed before
does not (`tempHolds`), unless a variable that keeps what an earlier run of
the same code borrowed does: its type may say it could (`m: &mut M<'a, T>`,
whose lifetime a result written `-> &mut T` is), but its value was there
first. -/
def holderOf (loan : Nat) (u : Use) (byTime : Bool := false) : M (Option String) := do
  let s ← get
  for name in u.later.eraseDups do
    if let some t := (u.scope.lookup name).bind Binding.held then
      let before := byTime && match u.scope.lookup name with
        | some (.val _ id) => (s.bindLoans[id]?).any (loan ≥ ·)
        | _ => false
      let kept ← if before then
          u.scope.anyM fun (_, b) => match b with
            | .cell t _ => holdsLoan loan t
            | _ => pure false
        else pure true
      if kept && (← holdsLoan loan t) then
        if name == "%resumed" then return some "the computation this arm resumes"
        return some s!"`{name}`"
  for (t, made) in u.temps do
    if ← tempHolds loan u t made then return some "a value this expression is still using"
  return none

/-- One value both holds a borrow of a variable and holds a callable that uses
the variable. That is a conflict only if it can be both at once: the fields of
one constructor are, the alternatives of a type are not. This is what lets a
value be either what a body gave or the body that was not run. -/
partial def bothAtOnce (loan brand : Nat) (write : Bool) (t : Ty) : M Bool := do
  unless (← holdsLoan loan t) && (← touchesVar brand write t) do return false
  let together := fun (fields : List Ty) => (do
    let mut holding : List Nat := []
    let mut touching : List Nat := []
    for (f, i) in fields.zipIdx do
      if ← holdsLoan loan f then holding := i :: holding
      if ← touchesVar brand write f then touching := i :: touching
    if holding.any fun i => touching.any (· != i) then return true
    for (f, i) in fields.zipIdx do
      if holding.contains i && touching.contains i then
        if ← bothAtOnce loan brand write f then return true
    return false : M Bool)
  match ← find t with
  | .tuple fields => together fields
  | .con name args =>
    match (← get).types[name]? with
    | none => pure true
    | some decl =>
      for c in decl.ctors do
        match (← get).ctors[c]? with
        | none => return true
        | some sig =>
          if ← together (sig.fieldsAt args) then return true
      return false
  | _ => pure true

/-- Check the uses recorded against the borrows, now that types are known. -/
def checkLoans (loansAt cellsAt : Nat := 0) : M Unit := do
  let s0 ← get
  -- (Of the loans and cells made since the group began: a use of the group
  -- meets no other function's.)
  let loans := (List.range' loansAt (s0.loans.size - loansAt)).toArray.filterMap s0.loans.get?
  let cells := s0.cells.extract cellsAt s0.cells.size
  let s := { s0 with cells }
  modify fun st => { st with uses := #[], heldMoves := #[] }
  let fail := fun (u : Use) (msg : String) => (throw (inFunction u.owner (u.pos ++ msg)) : M Unit)
  -- A variable that gives its value away is not looked at again: a callable
  -- that uses the variable, written before, must not be able to run after.
  for u in s.uses ++ s.heldMoves do
    if let .var brand x .move _ := u.kind then
      if let some (_, _, t) := s.cells.toList.find? (·.1 == brand) then
        modify fun st => { st with seen := {} }
        if (← tyOwnsOnce [] t) || (← tyHasDrop [] t).isSome then
          for name in u.later.eraseDups do
            if name != x then
              if let some held := (u.scope.lookup name).bind Binding.held then
                modify fun st => { st with seen := {} }
                if ← tyLooks brand held then
                  fail u s!"`{x}` is given away while `{name}`, which uses it, can still be called"
          for (held, _) in u.temps do
            modify fun st => { st with seen := {} }
            if ← tyLooks brand held then
              fail u s!"`{x}` is given away while a callable this expression is still using uses it"
  if loans.isEmpty then return
  for u in s.uses do
    match u.kind with
    | .var brand x how path =>
      -- Giving away a value that can be copied is reading it.
      let how ← match how with
        | .move => do
          match s.cells.toList.find? (·.1 == brand) with
          | some (_, _, t) =>
            modify fun st => { st with seen := {} }
            if (← tyOwnsOnce [] t) || (← tyHasDrop [] t).isSome then pure Using.move else pure Using.read
          | none => pure Using.read
        | other => pure other
      for l in loans do
        -- Two fields get in each other's way only if one is inside the other.
        let meet := path.isPrefixOf l.path || l.path.isPrefixOf path
        if l.root == some brand && how.forbiddenBy l.uniq && meet then
          if let some who ← holderOf l.id u then
            let kind := if l.uniq then "`&mut` reference" else "reference"
            fail u (match how with
              | .read => s!"`{x}` is read while {who} holds a {kind} to it"
              | .move => s!"`{x}` is given away while {who} holds a {kind} to it"
              | .write => s!"`{x}` is assigned while {who} holds a {kind} to it"
              | .share => s!"`{x}` is borrowed while {who} holds a {kind} to it"
              | .lend => s!"`{x}` is borrowed with `&mut` while {who} holds a {kind} to it")
    | .through cap name write path =>
      let root ← findCap cap
      for l in loans do
        if let some (parent, own) := l.parent then
          let meet := path.isPrefixOf l.path || l.path.isPrefixOf path
          -- A reference lent to the function it is a parameter of, from inside
          -- it, has become the same as what was lent from it: nothing to tell apart.
          if (l.uniq || write) && meet && (← findCap parent) == root && (← findCap own) != root then
            if let some who ← holderOf l.id u (byTime := true) then
              fail u s!"{name} is used while {who}, which borrows from it, is still in use"
    | .call what tys =>
      -- The values of the call are the last of the values computed: the
      -- callee and its arguments, each of which may hold callables.
      let mine := (u.temps.take tys.length).reverse
      let outer := { u with temps := u.temps.drop tys.length }
      for (t, i) in tys.zipIdx do
        modify fun st => { st with seen := {} }
        for (brand, write) in ← tyTouches t [] do
          for l in loans do
            if l.root == some brand && (write || l.uniq) then
              let mut found ← holderOf l.id outer
              for ((t', made), j) in mine.zipIdx do
                if found.isNone then
                  if ← tempHolds l.id u t' made then
                    -- A resumption both holds the borrows of the computation
                    -- it suspended and uses what that computation uses:
                    -- resuming it is that computation going on.
                    modify fun st => { st with seen := {} }
                    let own ← if i == j then tyHoldsLoan l.id t' false true else pure true
                    if i != j || (own && (← bothAtOnce l.id brand write t')) then
                      found := some "a value this expression is still using"
              if let some who := found then
                let x := ((s.cells.toList.find? (·.1 == brand)).map (·.2.1)).getD "a variable"
                let kind := if l.uniq then "`&mut` reference" else "reference"
                let does := if write then "assign or borrow" else "read"
                fail u s!"calling {what} may {does} `{x}` while {who} holds a {kind} to it"

open Flat in
mutual

/-- Does the code assign the mutable variable `x`, or borrow it with `&mut`? -/
partial def assignsExpr (b : Body) (x : String) (e : ExprId) : Bool :=
  match b.expr e with
  | .ref uniq y | .refField _ uniq y _ _ => uniq && y == x
  | .closure _ cs => cs.any fun c => assignsStmts b x (b.clause c).body
  | .handle s cs => assignsExpr b x s || cs.any fun c => assignsStmts b x (b.clause c).body
  | .labelScope _ body => assignsStmts b x body
  | _ => (b.direct e).any (assignsExpr b x)

partial def assignsStmts (b : Body) (x : String) (body : Array StmtId) : Bool :=
  body.any fun s =>
    match b.stmt (b.unlocated s) with
    | .assign t value =>
      match b.bare? t with
      | some y => y == x || assignsExpr b x value
      | none => (b.stmtExprs s).any (assignsExpr b x)
    | _ => (b.stmtExprs s).any (assignsExpr b x)

end

def assignsClause (b : Flat.Body) (x : String) (c : Flat.ClauseId) : Bool :=
  assignsStmts b x (b.clause c).body

/-- A `&mut` reference used as a value is lent: what is given is a reference
that borrows from it. Anything else is given as it is. -/
def lend (scope : Scope) (x : String) (t : Ty) : M Ty := do
  match ← find t with
  | .ref how inner cap =>
    match ← find how with
    | .con "&mut" [] =>
      use scope (.through cap s!"`{x}`" true)
      let cap' ← freshCap
      captures cap' (.loan (← freshLoan none true (some (cap, cap'))))
      captures cap' (.ty t)
      pure (.ref how inner cap')
    | _ => pure t
  | _ => pure t

open Flat in
/-- Does evaluating this certainly take what the mutable variable `x` holds
out of it, with `replace(&mut x, e)`, before anything else could happen? Then
`e`, what is put in its place. -/
partial def takesOut (b : Body) (x : String) (e : ExprId) : Option ExprId :=
  match b.expr e with
  | .call _ f args =>
    match b.expr f, args.toList with
    | .name none "replace", [r, v] =>
      match b.expr r with
      | .ref true y => if y == x then some v else none
      | _ => first args.toList
    -- (A block that is run where it is written: its first statement.)
    | .closure _ #[c], [] =>
      let ⟨pats, body⟩ := b.clause c
      if !pats.isEmpty then none else
      match body.toList with
      | s :: _ =>
        match b.stmt (b.unlocated s) with
        | .expr e | .let_ _ e | .letMut _ e => takesOut b x e
        | _ => none
      | [] => none
    | .name _ _, _ => first args.toList
    | _, _ => none
  | .tailCall _ f args =>
    match b.expr f with
    | .name _ _ => first args.toList
    | _ => none
  | .tuple es => first es.toList
  | _ => none
where
  -- The first part that is not just a name or a number is the one evaluated
  -- first that does anything.
  first : List ExprId → Option ExprId
    | [] => none
    | e :: rest =>
      match b.expr e with
      | .name _ _ | .int _ => first rest
      | _ => takesOut b x e

/-- Is this a value written out that holds nothing but numbers and
constructors: nothing, that is, that could have to be used? -/
partial def holdsNothing (e : Expr) : M Bool :=
  -- (A value written with its type is that value.)
  match Syntax.aliasValue e with
  | .int _ => pure true
  | .tuple es => es.allM holdsNothing
  | .name q x => do
    match ← resolveCtor x q with
    | some (_, sig) => pure (sig.fields.isEmpty && !(← mustByDecl sig.owner))
    | none =>
      match (← get).aliases[x]? with
      | some e => holdsNothing e
      | none => pure false
  | .call _ (.name q x) args => do
    match ← resolveCtor x q with
    | some (_, sig) => do
      if ← mustByDecl sig.owner then return false
      args.allM holdsNothing
    | none => pure false
  | _ => pure false
where
  -- A value of a type that says it has to be used is one, whatever is in it.
  mustByDecl (owner : String) : M Bool := do
    pure (match (← get).useDecls[owner]? with
      | some (must, _) => must
      | none => false)

/-! ## Expressions -/

/-- What a name in an expression refers to. -/
inductive Head where
  | local (b : Binding)
  /-- A function: its type at this use, the traits that use needs, and whether
  it is one of the group being inferred, whose needs are not yet known. -/
  | fn (t : Ty) (bounds : List (String × Ty)) (inGroup : Bool)
  | method (sig : MethodSig)
  /-- A constructor, and the type its name was written with, if the name is
  one given to it with a type. -/
  | ctor (sig : CtorSig) (written : Option Expr := none)
  | op (sig : OpSig)
  | prim
  /-- What an `is` found: the values, under the names in `name`. -/
  | pack (name : String)
  | host (id : Nat)
  | cancel
  | replace
  | swap
  | overwrite
  | readOut
  | transmute
  | const (e : Expr)

def resolveName (scope : Scope) (asked : Option String) (x : String) : M Head := do
  -- (`%prelude`: what `a[i]` and the like are written with. It is the
  -- prelude's function, whatever a program has given the same name.)
  let qual := if asked == some "%prelude" then none else asked
  if asked.isNone then
    if let some b := scope.lookup x then return .local b
    -- A name for a constructor that was written with a type is of that
    -- type where it is used as a value; a pattern looks through it.
    if let some e := (← get).aliases[x]? then
      if Syntax.aliasTyped e then
        match e, Syntax.aliasValue e with
        | .call _ _ [_, ty], .name q y =>
          -- (Of a constructor's own name: the constructor, at that type.)
          if let some (_, sig) ← resolveCtor y q then return .ctor sig (some ty)
          return .const e
        | _, _ => return .const e
  if let some (_, sig) ← resolveCtor x qual then return .ctor sig
  let s ← get
  if let some sig := s.ops.lookup x then
    if let some q := qual then
      unless q == sig.effect do throw s!"`{x}` is not an operation of `{q}`"
    return .op sig
  if let some sig := s.methods[x]? then
    if let some q := qual then
      unless q == sig.trait do throw s!"`{x}` is not a function of `{q}`"
    if s.unsafeFns.contains (unsafeMethodKey sig.trait x) && !(s.unsafeBlock || s.unsafeFns.contains s.owner) then
      throw s!"`{Syntax.lastSegment x}` is unsafe: it can be called only in `unsafe \{ .. }` or in an `unsafe fn`"
    return .method sig
  if let some t := s.group.lookup x then
    -- (`f<A>(..)` of the function being checked, or one checked with it:
    -- its type parameters are what they are in here.)
    modify fun st => { st with instWith := none }
    return .fn t [] true
  if let some scheme := s.fns[x]? then
    if s.unsafeFns.contains x && !(s.unsafeBlock || s.unsafeFns.contains s.owner) then
      throw s!"`{Syntax.lastSegment x}` is unsafe: it can be named only in `unsafe \{ .. }` or in an `unsafe fn`"
    -- `x<A, B>(..)`: the first type parameters are the types written.
    let fixed ← match s.instWith with
      | none => pure []
      | some tys => do
        modify fun st => { st with instWith := none }
        let ids := (s.typeParams.lookup x).getD []
        if tys.length > ids.length then
          throw s!"`{Syntax.lastSegment x}` has {ids.length} type parameter{if ids.length == 1 then "" else "s"}, and is given {tys.length}"
        pure ((ids.zip tys).filterMap fun
          | (some id, t) => some (id, t)
          | (none, _) => none)
    let t ← instantiate scheme (some x) fixed
    return .fn t (← get).lastBounds false
  -- (The machine's operations are declared in the prelude, but for those of
  -- arrays and these two of the host's.)
  if (Elab.prims.lookup x).isSome then return .prim
  if (Syntax.packNames x).isSome then return .pack x
  if x == "c_callback" then return .host 5
  if x == Syntax.foreignCall then return .host 2
  if x == "cancel" then return .cancel
  if x == "replace" then return .replace
  if x == "swap" then return .swap
  if x == "overwrite" then return .overwrite
  if x == "read_out" then return .readOut
  if x == "transmute" then return .transmute
  if let some e := s.aliases[x]? then return .const e
  throw s!"unknown name `{x}`"

/-- A call needs these traits of these types: to be met when the types are known. -/
def needBounds (call : Nat) (bs : List (String × Ty)) : M Unit := do
  if bs.isEmpty then return
  if call == 0 then
    throw s!"a trait is needed at a call the checker has no name for ({", ".intercalate (bs.map (·.1))}); this is a compiler defect"
  let s ← get
  let news := (bs.zip (List.range bs.length)).map fun ((tr, ty), k) =>
    (⟨tr, ty, call, k, s.owner, s.pos, []⟩ : Bound)
  set { s with bounds := s.bounds ++ news.toArray }

/-- `x.i.name` as the name and the way to the field, if that is what this
is: each step a field's number or its name, with the identity of the read
where it is by name. -/
partial def fieldOfName (b : Flat.Body) (e : Flat.ExprId)
    (root : Flat.ExprId → Option String := b.bare?) : Option (String × List (String × Option Nat)) :=
  let step := fun (inner : Flat.ExprId) (s : String × Option Nat) =>
    match root inner with
    | some x => some (x, [s])
    | none => (fieldOfName b inner root).map fun (x, path) => (x, path ++ [s])
  match b.expr e with
  | .proj inner idx => step inner (toString idx, none)
  | .fieldOf id inner name => step inner (name, some id)
  | _ => none

/-- `(*p).i.name` likewise. -/
def fieldOfDeref (b : Flat.Body) (e : Flat.ExprId) : Option (String × List (String × Option Nat)) :=
  fieldOfName b e fun inner => match b.expr inner with
    | .deref r => b.bare? r
    | _ => none

/-- The type of the field reached by `path` in a value of type `t`, and the
way to it by number. Where `t` is not known yet, a step by number is settled
once the rest of the function is inferred. -/
def fieldAtThrough (t : Ty) (path : List String) :
    M (Ty × List Nat × List (Option String) × List (Nat × Ty × Nat)) := do
  let mut cur := t
  let mut numbered : Array Nat := #[]
  let mut chosen : Array (Option String) := #[]
  -- (The steps that go past a reference a field before holds, with how
  -- it borrows and what it lasts as long as.)
  let mut through : Array (Nat × Ty × Nat) := #[]
  for (step, k) in path.zipIdx do
    if let .ref how inner cap ← find cur then
      cur := inner
      through := through.push (k, how, cap)
    -- A field of one of several constructors: the value was just found to
    -- be made by that one.
    if let some (ctor, idx) := Syntax.splitCtorStep step then
      match (← get).ctors[ctor]? with
      | some sig =>
        let (fields, result) ← instCtor sig
        unifyAt s!"a field of a `{Syntax.lastSegment ctor}`" result cur
        numbered := numbered.push idx
        chosen := chosen.push (some ctor)
        cur := fields.getD idx .unit
      | none => throw s!"unknown constructor `{ctor}`"
      continue
    let idx := (← fieldIndex cur step).getD 0
    numbered := numbered.push idx
    chosen := chosen.push none
    match ← fieldType cur idx with
    | some field => cur := field
    | none =>
      let field ← freshTy
      modify fun s => { s with projections := s.projections.push (cur, idx, field, s.pos, 0) }
      cur := field
  pure (cur, numbered.toList, chosen.toList, through.toList)

/-- A field reached past references fields hold, borrowed (`&mut g.w.c`,
`g.w: &mut W`): as long as each of those, and for writing only where each is
a `&mut`. -/
def throughBorrowed (through : List (Nat × Ty × Nat)) (uniq : Bool) (cap' : Nat) : M Unit := do
  for (_, how, cap) in through do
    if uniq then unifyAt "a field is borrowed for writing through a `&mut` reference a field holds" how .uniq
    captures cap' (.loan (← freshLoan none uniq (some (cap, cap')) []))

/-- Note, for each step that was a name, which field it turned out to be. -/
def noteFieldReads (path : List (String × Option Nat)) (numbered : List Nat) (through : List (Nat × Ty × Nat) := []) :
    M Unit := do
  for (((_, id), idx), k) in (path.zip numbered).zipIdx do
    if let some id := id then
      modify fun s => { s with fieldReads := s.fieldReads.push (id, idx) }
      -- (Read past a reference a field before holds.)
      if through.any (·.1 == k) then modify fun s => { s with derefReads := s.derefReads.push id }

/-- Record that `cap` captures the named bindings: a value by its type, a label
or a mutable variable by the brand of its scope as well. -/
def captureAll (scope : Scope) (cap : Nat) (names : List String) (assigns : String → Bool)
    (gives : String → Bool := fun _ => false) : M Unit := do
  -- Capturing a mutable variable holds the variable, not what is in it; and
  -- the callable reads or assigns the variable when it runs.
  for name in names.eraseDups do
    match scope.lookup name with
    | some (.val t id) => captures cap (.ty t) (some (name, id))
    | some (.cell t brand) =>
      captures cap (.brand brand)
      captures cap (.touch brand (assigns name))
      -- A variable that gives its value away, where the callable is what
      -- uses the value: the callable holds it, as it would a name's.
      if (← get).movedCells.contains brand && gives name then
        modify fun s => { s with givenEdges := s.givenEdges.insert s.capEdges.size, givers := (cap, brand) :: s.givers }
        captures cap (.ty t) (some (name, brand))
    | some (.label _ brand) => captures cap (.brand brand)
    | some (.poly s) => captures cap (.ty s.ty) (some (name, 0))
    | none => pure ()

def placeName (b : Flat.Body) (e : Flat.ExprId) : String :=
  match b.expr e with
  | .name _ x => s!"`{x}`"
  | _ => "this reference"

/-- A label is a callable that never returns: it accepts the value its scope
yields, and holds the scope's brand. -/
def labelType (t : Ty) (brand : Nat) : M Ty := do
  let cap ← freshCap
  captures cap (.brand brand)
  pure (.func [t] (← freshTy) (← freshRow) cap)

def readsCell (x : String) : String :=
  s!"reading the variable `{x}` copies its value (`replace` takes it out instead)"

def arguments (n : Nat) : String :=
  if n == 1 then "1 argument" else s!"{n} arguments"

def arityError (what : String) (expected found : Nat) : M Unit :=
  throw s!"{what} takes {arguments expected}, but is given {found}"

/-! ## Coercions

A program declares a function a coercion with `coerce name`. Where a value does
not have the type expected of it, and exactly one declared coercion takes what
was found to what is expected, that function is applied, as if the call had
been written. Nothing is converted in more than one step, and a coercion is not
applied where its name means something else.
-/

/-- The declared coercions that take what was found to what is expected. If
there is exactly one, the types are made to fit it: it is applied. -/
def coerceTo (scope : Scope) (amb : Row) (expected actual : Ty) : M (List String) := do
  let s ← get
  let mut fits : List String := []
  -- A coercion applies in the module that declares it and in one that brings
  -- its function in with `use`.
  let mine := (s.modules.homes.lookup s.owner).bind fun home => s.modules.coercions.lookup home
  for name in s.coercing.filter fun name => (mine.map (·.contains name)).getD true do
    if (scope.lookup name).isNone then
      if let some scheme := s.fns[name]? then
        let saved ← get
        let ok ← try
            (do
              match ← find (← instantiate scheme (some name)) with
              | .fn [a] b _ _ _ => do
                unify a actual
                unify b expected
                pure true
              | _ => pure false)
          catch _ => pure false
        set saved
        if ok then fits := name :: fits
  match fits with
  | [name] =>
    match s.fns[name]? with
    | some scheme =>
      match ← find (← instantiate scheme (some name)) with
      | .fn [a] b effs tail _ => do
        unify a actual
        unify b expected
        includeRow ⟨effs, tail⟩ amb s!"`{name}`"
        pure [name]
      | _ => pure []
    | none => pure []
  | several => pure several.reverse

/-- A `&mut` reference where a `&` reference is wanted is lent for reading:
what is given borrows from it, as a reader. -/
def shareRef (scope : Scope) (expected actual : Ty) : M Bool := do
  match ← find expected, ← find actual with
  | .ref how inner cap, .ref how' inner' cap' =>
    match ← find how, ← find how' with
    | .con "&" [], .con "&mut" [] =>
      let fits ← try (do unify inner inner'; pure true) catch _ => pure false
      unless fits do return false
      use scope (.through cap' "a reference" false)
      captures cap (.loan (← freshLoan none false (some (cap', cap))))
      captures cap (.ty actual)
      pure true
    | _, _ => pure false
  | _, _ => pure false

/-- Does the lifetime `a` last at least as long as `b`, by the bounds the
function wrote? `'static` outlasts every lifetime. -/
partial def outlasts (a b : Nat) : M Bool := do
  let s ← get
  if a == b || s.staticCap == some a then return true
  let rec go (seen : List Nat) (x : Nat) : Bool :=
    x == b || s.outlives.any fun (longer, shorter) =>
      longer == x && !seen.contains shorter && go (x :: seen) shorter
  pure (go [] a)

/-- Require that the lifetime `long` lasts at least as long as `short`. Between
two lifetimes a function declares, a bound must say so. Otherwise it is made
so: what lasts for the shorter holds what lasts for the longer. -/
def outlivesReq (long short : Nat) : M Unit := do
  let rl ← findCap long
  let rs ← findCap short
  if rl == rs then return
  let s ← get
  match s.rigidCaps.lookup rl, s.rigidCaps.lookup rs with
  | some x, some y =>
    unless ← outlasts rl rs do
      throw s!"lifetime `{x}` is not known to last as long as `{y}`: say `{x}: {y}`"
  | some _, none =>
    -- (`short` is the declared one here only where `long` is not.)
    captures short (.ty (Ty.life long))
  | none, some _ =>
    -- What the body of a function ends with, given at a lifetime the
    -- function declares: marked, so that it is not counted as held by the
    -- function's other values of that lifetime.
    if s.givingBack then captures short (.ty (.ref (.con "'given" []) (.tuple []) long))
    else captures short (.ty (Ty.life long))
  | none, none => captures short (.ty (Ty.life long))

/-- Relate the lifetime wanted and the lifetime given, at a position that
depends on it as `pos` says. -/
def lifeFits (pos : Variance) (wanted had : Nat) : M Unit := do
  match pos with
  | .bi => pure ()
  | .co => outlivesReq had wanted
  | .contra => outlivesReq wanted had
  | .inv => unifyCap wanted had

/-- Make a value of type `actual` do where `expected` is wanted, as far as
lifetimes go: the two types must be the same but for their lifetimes, and each
pair of lifetimes is related by the position it is in. A reference depends on
its lifetime the same way round, and so does a shared reference on what it
points to; a `&mut` reference does not vary in what it points to; a callable
depends on what it takes the other way round and on what it gives the same
way; a declared type depends on each parameter as its fields make it. -/
partial def fitLifetimes (pos : Variance) (expected actual : Ty) (whole : Bool := false) :
    M Unit := do
  let e ← find expected
  let a ← find actual
  if pos == .inv then
    unify e a
    return
  match e, a with
  | .ref how t cap, .ref how' t' cap' => do
    unify how how'
    lifeFits pos cap cap'
    match ← find how with
    | .con "&" [] => fitLifetimes pos t t' whole
    | .con "'" [] => pure ()
    | _ => unify t t'
  | .tuple es, .tuple as =>
    if es.length != as.length then unify e a
    else
      for (x, y) in es.zip as do
        fitLifetimes pos x y whole
  | .con n es, .con m as =>
    if n != m || es.length != as.length then unify e a
    else
      let variances := (((← get).types[n]?).map (·.variances)).getD []
      for ((x, y), i) in (es.zip as).zipIdx do
        fitLifetimes (pos.through (variances.getD i .inv)) x y whole
  | .fn ps r effs tail cap, .fn ps' r' effs' tail' cap' =>
    -- What a callable captured is one thing wherever the callable goes: two
    -- blocks are told to be one by it.
    if whole || ps.length != ps'.length then unify e a
    else
      for (x, y) in ps.zip ps' do
        fitLifetimes pos.flip x y
      fitLifetimes pos r r'
      unifyRow ⟨effs, tail⟩ ⟨effs', tail'⟩
      lifeFits pos cap cap'
  | _, _ => unify e a

/-- Try that, changing nothing if it does not work: then why not. -/
def tryLifetimes (expected actual : Ty) (whole : Bool := false) : M (Option String) := do
  let saved ← get
  try
    fitLifetimes .co expected actual whole
    pure none
  catch e =>
    set saved
    pure (some e)

/-- Does a type, as far as it is known, hold a reference or name a lifetime? -/
partial def mentionsRef (t : Ty) : M Bool := do
  match ← find t with
  | .ref _ _ _ => pure true
  | .tuple ts => ts.anyM mentionsRef
  | .con "'" _ => pure true
  | .con _ args => args.anyM mentionsRef
  | _ => pure false

/-- How each declared type depends on each of its parameters: found from the
fields of its constructors, and for a type that mentions itself or another,
by starting from no dependence and adding until nothing changes. -/
partial def computeVariances : M Unit := do
  let names := (← get).types.toList.map (·.1)
  -- A parameter is a type variable or a lifetime's capture variable.
  let keysOf := fun (sig : CtorSig) =>
    let rec go : List Bool → List Nat → List Nat → List (Bool × Nat)
      | true :: ks, ts, c :: cs => (true, c) :: go ks ts cs
      | false :: ks, t :: ts, cs => (false, t) :: go ks ts cs
      | _, _, _ => []
    go sig.kinds sig.tvars sig.cvars
  let mut changed := true
  let mut rounds := 0
  while changed && rounds < 16 do
    changed := false
    rounds := rounds + 1
    for name in names do
      let s ← get
      let some decl := s.types[name]? | continue
      let mut found : List ((Bool × Nat) × Variance) := []
      let mut keys : List (Bool × Nat) := []
      for c in decl.ctors do
        let some sig := s.ctors[c]? | continue
        keys := keysOf sig
        for field in sig.fields do
          found := found ++ occurrences s .co field
      let variances := keys.map fun k =>
        (found.filter (·.1 == k)).foldl (fun acc x => acc.both x.2) Variance.bi
      unless variances == decl.variances || keys.isEmpty do
        changed := true
        modify fun st =>
          { st with types := st.types.modify name fun d => { d with variances := variances } }
where
  /-- Where a type mentions type variables and capture variables, and how. -/
  occurrences (s : St) (pos : Variance) : Ty → List ((Bool × Nat) × Variance)
    | .var id => [((false, id), pos)]
    | .tuple ts => ts.flatMap (occurrences s pos)
    | .ref how inner cap =>
      ((true, cap), pos) :: (match how with
        | .con "&" [] => occurrences s pos inner
        | .con "'" [] => []
        | _ => occurrences s (pos.through .inv) inner)
    | .fn ps r effs _ cap =>
      ((true, cap), pos) :: ps.flatMap (occurrences s pos.flip) ++ occurrences s pos r
        ++ effs.flatMap fun (_, args) => args.flatMap (occurrences s (pos.through .inv))
    | .con n args =>
      let variances := ((s.types[n]?).map (·.variances)).getD []
      (args.zip (List.range args.length)).flatMap fun (arg, i) =>
        occurrences s (pos.through (variances.getD i .bi)) arg

/-- These capture variables and those reachable from them through what they
hold. -/
def reachFrom (start : List Nat) : M (List Nat) := do
  let mut reach := start
  let mut todo := start
  while !todo.isEmpty do
    let mut next : List Nat := []
    for from_ in todo do
      for (_, what) in ← edgesFrom (← findCap from_) do
        if let .ty held := what then
          for c in freeCaps (← zonk held) do
            let root ← findCap c
            unless reach.contains root || next.contains root do next := root :: next
    reach := reach ++ next
    todo := next
  pure reach

/-- A function is held to the lifetimes it writes: what lasts for one of them
may come to depend on what lasts for another only where a bound says the
other lasts at least as long. -/
def checkLifetimes : M Unit := do
  let s ← get
  for (a, x) in s.rigidCaps do
    if x == "'static" then continue
    -- The capture variables reachable from `a` through what it holds.
    let reach ← reachFrom [a]
    for (b, y) in s.rigidCaps do
      if b != a && reach.contains b then
        unless ← outlasts b a do
          throw s!"what lasts for `{x}` is made to depend on what lasts for `{y}`: say `{y}: {x}` if `{y}` lasts at least as long"

/-- Refuse the read of a field of a value that is in no variable, where the
value's own type has a `drop` to run: nothing would run it. (In the type's
own `drop` the value is being let go, and its fields are what is left.) -/
def ownDropRead (subject : Ty) : M Unit := do
  if let .con n _ ← find subject then
    let s ← get
    if s.dropMode && s.kimpls.has "Drop" n
        && s.owner != Syntax.implFnName "Drop" n "drop" then
      throw s!"{s.pos}a field is read of a `{bareName n}` that is in no variable, and a `{bareName n}` has a `drop` to run, which nothing then would: give the value a name first, `let value = ..; value.field`"

/-- A whole number written without a type, where a value of type `t` is
wanted: if `t` is known to be a type of whole numbers, the number is of that
type, and this is whether it fits. None if `t` is not such a type: then the
number is an `Int`. -/
def literalAt (t : Ty) (n : Int) (e : Option Nat := none) : M (Option (Option String)) := do
  match ← find t with
  | .con name [] =>
    match Syntax.scalars.lookup name with
    | some (some width) =>
      if Glorious.fits n width then
        -- (Where it is written, `e`: made that scalar in Core.)
        if let some e := e then
          modify fun s => { s with scalarLits := (s.owner, e, name) :: s.scalarLits }
        pure (some none)
      else pure (some (some s!"`{n}` does not fit in `{name}`"))
    | _ => pure none
  | _ => pure none

/-- The lifetimes a callable type is for every one of, if it is such a type. -/
def rankedOf (cap : Nat) : M (List (Nat × String)) := do
  let root ← findCap cap
  for (c, lifetimes) in (← get).ranked do
    if (← findCap c) == root then return lifetimes
  return []

/-- A callable type that is for every lifetime, at lifetimes of its own: new
ones, each holding what every one of them was said to hold. With `rigid` the
new ones are each itself and no other, as a function's own lifetimes are:
that is how a callable given where such a type is wanted is held to it. Gives
the type and the new lifetimes. -/
def openRanked (t : Ty) (rigid : Bool := false) : M (Ty × List Nat) := do
  match ← find t with
  | .fn ps r effs tail cap =>
    let lifetimes ← rankedOf cap
    if lifetimes.isEmpty then return (t, [])
    let mut cm : List (Nat × Nat) := []
    for (q, name) in lifetimes do
      let root ← findCap q
      let fresh ← freshCap
      cm := (root, fresh) :: cm
      for (_, what) in ← edgesFrom root do
        captures fresh what
      if rigid then
        modify fun s => { s with rigidCaps := (fresh, name) :: s.rigidCaps }
    match ← zonk (.fn ps r effs tail cap) with
    | .fn ps r effs tail cap =>
      pure (.fn (ps.map (subst [] [] cm)) (subst [] [] cm r) effs tail cap, cm.map (·.2))
    | t => pure (t, [])
  | t => pure (t, [])

/-- The capture variables reachable from a type through what they hold. -/
def capsReached (t : Ty) : M (List Nat) := do
  let mut reach : List Nat := []
  let t ← zonk t
  -- (A type a trait leaves at a lifetime, not known here, reaches it.)
  let mut asked : List Nat := []
  for v in freeTys t do
    for (w, lives) in (← get).gatHolds do
      if let .var r' ← find (.var w) then
        if r' == v then asked := asked ++ lives
  for c in freeCaps t ++ asked do
    let root ← findCap c
    unless reach.contains root do reach := root :: reach
  reachFrom reach

/-- Make what was found the type expected, by a declared coercion at `site` if
the two differ. Gives the mismatch if neither works. -/
def fitAtCore (scope : Scope) (amb : Row) (what : String) (site : Option Elab.Site)
    (expected actual : Ty) : M (Option String) := do
  -- Where references meet, their lifetimes are related as the position asks,
  -- not made one: a reference given where a shorter one will do is not
  -- thereby taken to borrow what the other one borrows.
  if (← mentionsRef expected) || (← mentionsRef actual) then
    if (← tryLifetimes expected actual true).isNone then return none
  try
    unifyAt what expected actual
    pure none
  catch e =>
    -- The same type but for lifetimes will do if each lifetime is related as
    -- its position asks.
    let lifetimes ← tryLifetimes expected actual
    if lifetimes.isNone then return none
    if ← shareRef scope expected actual then return none
    let e := match lifetimes with
      | some why => if why.startsWith "lifetime" then s!"{what}: {why}" else e
      | none => e
    match site with
    | none => pure (some e)
    | some site =>
      match ← coerceTo scope amb expected actual with
      | [name] =>
        modify fun s => { s with coercions := s.coercions.push (site, name) }
        pure none
      | [] => pure (some e)
      | several =>
        let names := ", ".intercalate (several.map fun name => s!"`{name}`")
        pure (some s!"{e} (the coercions {names} all apply here, so none is chosen)")

/-- Make what was found the type expected. Where a callable for every lifetime
is wanted, what is given must do for any: it is fitted at lifetimes that are
each itself, and nothing in scope may come to hold one of them, since a
reference the callable is given later would then be kept. A callable for
every lifetime that is given is given at lifetimes of its own. -/
def fitAt (scope : Scope) (amb : Row) (what : String) (site : Option Elab.Site)
    (expected actual : Ty) : M (Option String) := do
  let (expected, held) ← openRanked expected true
  let (actual, _) ← openRanked actual
  let found ← fitAtCore scope amb what site expected actual
  if found.isNone && !held.isEmpty then
    for (x, b) in scope do
      let t := match b with
        | .val t _ => some t
        | .cell t _ => some t
        | _ => none
      if let some t := t then
        let reached ← capsReached t
        for q in held do
          if reached.contains (← findCap q) then
            return some s!"{what}: a reference this callable is given is kept in `{x}`, and the callable is wanted for references of any lifetime"
    -- And what it gives for one of those lifetimes may borrow only from what
    -- it is given: whoever calls it chooses how long that lasts, and a
    -- variable or another lifetime of this function may not last as long.
    let s ← get
    let heldRoots ← held.mapM findCap
    let mut reach : List Nat := heldRoots
    let mut todo : List Nat := heldRoots
    while !todo.isEmpty do
      let mut next : List Nat := []
      for from_ in todo do
        for (_, held) in ← edgesFrom (← findCap from_) do
          if let .ty held := held then
            for c in freeCaps (← zonk held) do
              let root ← findCap c
              unless reach.contains root || next.contains root do next := root :: next
      reach := reach ++ next
      todo := next
    for from_ in reach do
     for (_, held) in ← edgesFrom (← findCap from_) do
      if let .loan id := held then
        if ((s.loans.get? id).bind (·.root)).isSome then
          return some s!"{what}: what this callable gives back borrows a variable, and the callable is wanted for references of any lifetime: it can give back only what borrows from what it is given"
    for (b, y) in s.rigidCaps do
      let root ← findCap b
      if y != "'static" && !heldRoots.contains root && reach.contains root then
        return some s!"{what}: what this callable gives back lasts for `{y}`, and the callable is wanted for references of any lifetime: it can give back only what borrows from what it is given"
  pure found

/-- How a function takes its first argument: borrowed (`&mut` where `some
true`), or whole (none). -/
def receiverTaken (fn : String) : M (Option Bool) := do
  let how := fun (t : Ty) => (do
    match ← find t with
    | .ref how _ _ =>
      match ← find how with
      | .con "&mut" [] => pure (some true)
      | _ => pure (some false)
    | _ => pure none : M (Option Bool))
  match (← get).fns[fn]? with
  | some scheme =>
    let saved ← get
    let taken ← match ← instantiate scheme with
      | .fn (p :: _) _ _ _ _ => how p
      | _ => pure none
    set saved
    pure taken
  | none =>
    match ((← get).methods[fn]?).bind (·.params.head?) with
    | some p => how p
    | none => pure none

/-- The decision that a dot call is of `fn`, its receiver given as `fn`
takes it. -/
def receiverDecision (call : Nat) (fn : String) : M Elab.Decision := do
  pure (.receiver call (some fn) (← receiverTaken fn))

end Glorious.Check
