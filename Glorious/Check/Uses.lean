module

public import Std.Data.HashSet
public import Glorious.Check.Scopes

public section

namespace Glorious.Check

open Syntax

/-! ## Values that have to be used

A type may say that its values have to be used: `impl Use<[1, 1]> for T {}`.
An operation may say it of its resumption: `[1, 1] op()`. A value that holds
one of either has to be used too. Wherever a value is let go without being
used, its type is recorded, and once types are known none of them may be such
a type. For a type that depends on a function's parameters the requirement is
part of the function's contract, as for use more than once.

A callable that mentions such a value does not thereby have to be called: the
value's own uses are counted along the paths the program can take, through the
callables that mention it.
-/

/-- What the capture variables say about having to be used, gathered once. -/
structure MustInfo where
  /-- The capture variables of callables written in the program. -/
  blocks : Std.HashSet Nat := {}

/-- What is asked of every type that is let go: found once for a function,
since the callables written do not change while its types are looked at. -/
def mustInfo : M MustInfo := do
  let s ← get
  unless s.anyMust do return {}
  -- (Of the block captures made since it was last asked: the rest are
  -- kept as they are joined, `unifyCap`.)
  let mut blocks := s.blockRoots
  for k in [s.blockRootsAt:s.blockCaps.size] do
    if let some (_, c) := s.blockCaps[k]? then blocks := blocks.insert (← findCap c)
  modify fun st => { st with blockRoots := blocks, blockRootsAt := s.blockCaps.size }
  pure { blocks }

/-- What in a type has to be used, if anything: said for the message. A
callable has to be called if it holds something that has to be used, or
something with a `drop` to run: nothing destroys what a callable holds, so
one that is let go without being called would take the value with it. -/
partial def tyMustUse (info : MustInfo) (visiting : List String) (t : Ty)
    (callables : Bool := false) : M (Option String) :=
  walkTy (fun name => do
      pure (match (← get).useDecls[name]? with
        | some (true, _) => some s!"a `{bareName name}`"
        | _ => none))
    (fun visiting cap => do
      let root ← findCap cap
      -- What it captures, by place among the program's captures.
      let s ← get
      let mine := (s.capOut.getD root #[]).filterMap fun i => (s.capEdges.get? i).map fun e => (i, e.2)
      -- A resumption that has to be used.
      if mine.any (fun (_, what) => match what with | .must => true | _ => false) then
        return some "a resumption of an operation declared `[1, 1]`"
      -- A resumption at all: what one mentions is the computation it
      -- suspended, not something it holds.
      if mine.any (fun (_, what) => match what with | .once => true | _ => false)
          && !info.blocks.contains root then return none
      if s.seen.contains root then return none
      modify fun s => { s with seen := s.seen.insert root }
      -- (What a block shares with the one it runs in place of, the other holds.)
      for (i, what) in mine do
        if let .ty held := what then
          unless s.sharedEdges.contains i || s.givenEdges.contains i do
            if let some what ← tyMustUse info visiting held callables then
              return some s!"a callable that holds {what}"
            -- (A callable let go is given up, which destroys what it holds;
            -- `callables` asks of one that is let go where nothing does.)
            if callables then
              if let some name ← tyHasDrop [] held then
                return some s!"a callable that holds a `{name}`, whose `drop` would then not run,"
      -- The value of a variable that gives it away: the variable's cleanup
      -- runs its `drop` where the callable did not use it, so only what has
      -- to be used makes the callable one that has to be called.
      for (i, what) in mine do
        if let .ty held := what then
          if s.givenEdges.contains i && !s.sharedEdges.contains i then
            if let some what ← tyMustUse info visiting held callables then
              return some s!"a callable that holds {what}"
      return none)
    visiting t

/-- Does a type mention a type parameter the function being checked wrote?
What such a type is, is known only where the function is used. -/
partial def hasParam : Ty → Bool
  | .rigid _ => true
  | .con n [] => n.startsWith "'" && n.length > 1
  | .con _ args => args.any hasParam
  | .tuple args => args.any hasParam
  | .fn ps r _ _ _ => ps.any hasParam || hasParam r
  | .ref _ t _ => hasParam t
  | _ => false

/-- Does a type borrow nothing, or only for `'static` (a text written,
`&'static str`)? Such a part read out of a value takes nothing out of it. -/
def borrowsOnlyStatic (t : Ty) : M Bool := do
  let statics ← match (← get).staticCap with
    | some c => pure [← findCap c]
    | none => pure []
  (freeCaps t).allM fun c => do pure (statics.contains (← findCap c))

/-- The type parameters a type mentions (`hasParam`'s). -/
partial def paramNames : Ty → List String
  | .rigid r => [r.spelled]
  | .con n [] => if n.startsWith "'" && n.length > 1 then [n] else []
  | .con _ args => args.flatMap paramNames
  | .tuple args => args.flatMap paramNames
  | .fn ps r _ _ _ => ps.flatMap paramNames ++ paramNames r
  | .ref _ t _ => paramNames t
  | _ => []

/-- Record that a value of this type is let go unused here. -/
def mustDrop (t : Ty) (why : String) : M Unit := do
  unless (← get).anyMust do return
  match ← find t with
  | .con "Int" [] => pure ()
  | .tuple [] => pure ()
  | .con name [] => unless Syntax.isScalar name do
      modify fun s => { s with drops := s.drops.push (t, s.pos ++ why) }
  | .ref _ _ _ => pure ()
  | _ => modify fun s => { s with drops := s.drops.push (t, s.pos ++ why) }

/-- A value a field is taken out of is let go without its `Drop` being run:
only the module that declares the type may do that. -/
def checkAparts : M Unit := do
  let s ← get
  modify fun st => { st with aparts := #[] }
  for (t, pos, _) in s.aparts do
    if let .con n _ ← find t then
      if s.kimpls.has (.of "Drop") n then
        if let some here := s.modules.homes.lookup s.owner then
          let home := "::".intercalate ((n.splitOn "::").dropLast)
          unless here == home do
            throw s!"{pos}`{Syntax.lastSegment n}` has `Drop`, so only the module that declares it can take a field out of one: what `drop` does would not be done. Borrow the field, or ask the module for it"

def checkDrops (drops : Array (Ty × String)) (callables : Bool := false) : M Unit := do
  if drops.isEmpty then return
  let info ← mustInfo
  -- (Each type once: what is said is of the first that has to be used, as
  -- the first of each type comes before the others.)
  let mut done : Std.HashSet String := {}
  for (t, why) in drops do
    let t ← zonk t
    -- (A callable's by what it captures too.)
    let key := s!"{showTy t} {← (freeCaps t).mapM findCap}"
    if done.contains key then continue
    done := done.insert key
    modify fun s => { s with seen := {} }
    if let some what ← tyMustUse info [] t callables then
      throw s!"{why}, but {what} has to be used"

def addUses (a b : Nat) : Nat := min 2 (a + b)

open Flat in
mutual

/-- How often an expression uses the binding `x`: 0, 1, or 2 for more.
`resumptive` says which operation names have arms that may run repeatedly. -/
partial def usesExpr (b : Body) (resumptive : String → Bool) (x : String) (e : ExprId) : Nat :=
  match b.expr e with
  | .name q y => if q.isNone && y == x then 1 else 0
  | .closure _ clauses => (clauses.map (usesClause b resumptive x)).foldl max 0
  | .handle subject arms =>
    let repeated := fun (arm : ClauseId) =>
      match (b.clause arm).pats with
      | [.ctor name _ _] => resumptive name
      | _ => false
    let once := ((arms.filter (!repeated ·)).map (usesClause b resumptive x)).foldl max 0
    let many := if (arms.filter repeated).any (usesClause b resumptive x · > 0) then 2 else 0
    addUses (addUses (usesExpr b resumptive x subject) once) many
  | .labelScope _ body => usesStmts b resumptive x body.toList
  | _ => b.foldDirect (fun n a => addUses n (usesExpr b resumptive x a)) 0 e

partial def usesClause (b : Body) (resumptive : String → Bool) (x : String) (c : ClauseId) : Nat :=
  let ⟨pats, body⟩ := b.clause c
  if (pats.flatMap Elab.patVars).contains x then 0 else usesStmts b resumptive x body.toList

partial def usesStmts (b : Body) (resumptive : String → Bool) (x : String) : List StmtId → Nat
  | [] => 0
  | s :: rest =>
    match b.stmt s with
    | .expr e => addUses (usesExpr b resumptive x e) (usesStmts b resumptive x rest)
    | .let_ pat value =>
      addUses (usesExpr b resumptive x value)
        (if (Elab.patVars pat).contains x then 0 else usesStmts b resumptive x rest)
    | .letMut y value =>
      addUses (usesExpr b resumptive x value) (if y == x then 0 else usesStmts b resumptive x rest)
    | .assign target value =>
      let inTarget := match b.expr target with
        | .deref e => usesExpr b resumptive x e
        | _ => 0
      addUses (addUses inTarget (usesExpr b resumptive x value)) (usesStmts b resumptive x rest)
    | .defer e => addUses (usesExpr b resumptive x e) (usesStmts b resumptive x rest)
    | .located _ _ s => usesStmts b resumptive x (s :: rest)

end


/-! ### Counting uses along the paths a program can take

The count above treats every callable that mentions a binding as one use. That
is too coarse where a function runs only one of several callables it is given,
which is how every conditional is written. So before a binding is held to
"used more than once", its uses are counted again by running the program
abstractly: constructors, callables and top-level functions are followed,
clauses are chosen by the constructor of the value they are applied to, and
anything not understood is treated as opaque, in which case every callable
handed to it counts as called.

This is an upper bound on the uses along any one path. If the analysis runs out
of budget it gives no answer and the coarse count stands.
-/

/-- What is known about a value during the count. -/
inductive AVal where
  | unknown
  /-- The binding whose uses are being counted. -/
  | tracked
  /-- A constructed value; a tuple has the empty tag. -/
  | data (tag : String) (args : List AVal)
  | clo (body : Flat.Body) (clauses : Array Flat.ClauseId) (env : List (String × AVal))
  | fn (name : String)
  /-- No value: the path left for somewhere else, an operation's handler
  (named by the operation), a label's scope (`@name`), or somewhere unknown. -/
  | gone (target : String)
  /-- A callable that runs in an environment it is lent, or a value one may be
  in: calling it may be the call whose place on the path is asked about. -/
  | probe

structure ACtx where
  fns : Std.HashMap String Flat.Body
  /-- The bodies as written, of those not checked yet (`St.declFns`). -/
  declFns : Std.HashMap String Flat.Body := {}
  ctors : Std.HashSet String
  aliases : Std.HashMap String Expr
  ops : Std.HashMap String Bool
  /-- Count the fewest uses along any path instead of the most. Then a call
  that cannot be followed may also not come back, a callable that leaves the
  count may never be called, and a path that leaves ends with what it has. -/
  lower : Bool := false
  /-- Names whose calls only compute: they always come back. -/
  quiet : Std.HashSet String := {}
  /-- The operations declared `[1, 1]`: whoever handles one resumes it, so
  performing it comes back. -/
  exact : Std.HashSet String := {}
  /-- Count the binding as used where it is given to something, whatever
  that then does with it: whoever takes a value has it. -/
  handed : Bool := false
  /-- Calls, by identity, whose types say they come back. -/
  sure : Std.HashSet Nat := {}
  /-- The count is of what comes before a call of a `probe`: a path ends at
  such a call, with the name below for where it left to, and a value one may
  be in cannot go where the count does not follow. -/
  probing : Bool := false
  /-- Where such a value goes is accounted for by whoever lets it go. -/
  lenient : Bool := false
  /-- The callable being evaluated is kept in a variable: what it captures
  is its own. -/
  owning : Bool := false
  /-- What is counted is a value a callable takes when it captures it (not a
  variable's, which the callable only reaches). -/
  capturesOwned : Bool := false
  /-- The blocks that are run where they are written, by their numbers. -/
  now : Std.HashSet Nat := {}
  /-- The functions being followed. One that calls itself is not followed
  again: what it is given goes where the count does not follow, which says
  of every later round what the first said. -/
  active : List String := []

/-- What only computes: the machine's own operations and what builds a value. -/
def intrinsics : Std.HashSet String :=
  Std.HashSet.ofList (Elab.prims.map (·.1) ++ Elab.casts ++ Elab.hosts.map (·.1)
    ++ ["cancel", "replace", "swap", "overwrite", "read_out", "transmute", "static_bytes", Syntax.foreignCall, "%never"])

/-- Where a path that ends at a call of a `probe` is said to leave to. -/
def probeTarget : String := "%probe"

def isGone : AVal → Bool
  | .gone _ => true
  | _ => false

def isTracked : AVal → Bool
  | .tracked => true
  | _ => false

/-- The target of the first value that is no value, if any is. -/
def goneOf (vs : List AVal) : Option String :=
  vs.findSome? fun
    | .gone t => some t
    | _ => none

/-- The most, or in the other direction the fewest, of some counts. -/
def ACtx.fold (ctx : ACtx) : List Nat → Nat
  | [] => 0
  | n :: ns => if ctx.lower then ns.foldl min n else ns.foldl max n

/-- A budget of steps, running out of which abandons the count; and what calls of functions it already
followed gave: by the call, what came of it and what it cost. -/
structure AState where
  fuel : Nat
  memo : Std.HashMap String (List (AVal × Nat) × Nat) := {}
  /-- The functions whose bodies were followed: what the count read of the
  program besides the body counted in. -/
  followed : Array String := #[]

abbrev A := StateT AState Option

/-- Spend one step of the budget. -/
def tick : A Unit := do
  let s ← get
  match s.fuel with
  | 0 => failure
  | n + 1 => set { s with fuel := n }

/-- A value written out, where it holds no callable: a call given the same
such values, in the same context, comes to the same. -/
partial def AVal.key? : AVal → Option String
  | .unknown => some "u"
  | .tracked => some "t"
  | .probe => some "p"
  | .fn n => some s!"f{n.length}:{n}"
  | .gone t => some s!"g{t.length}:{t}"
  | .data tag args => do
    let ks ← args.mapM AVal.key?
    pure s!"d{tag.length}:{tag}({args.length}:{String.join ks})"
  | .clo _ _ _ => none

/-- The outcomes of a computation: its value and the uses so far, per path. -/
abbrev Alts := List (AVal × Nat)

partial def ACtx.ctorOf (ctx : ACtx) (name : String) : Option String :=
  if ctx.ctors.contains name then some name
  else
    match (ctx.aliases[name]?).map Syntax.aliasValue with
    | some (.name _ y) => ctx.ctorOf y
    | _ => none

/-- The names a pattern binds, leaving out constructors and constants. -/
partial def binders (ctx : ACtx) : Pattern → List String
  | .wild | .int _ => []
  | .var x =>
    if (ctx.ctorOf x).isSome || (ctx.aliases[x]?).isSome then [] else [x]
  | .ctor _ _ ps | .tuple ps | .marked _ ps => ps.flatMap (binders ctx)

inductive Fit where
  | yes
  | no
  | maybe
  deriving Inhabited

def Fit.and : Fit → Fit → Fit
  | .no, _ => .no
  | _, .no => .no
  | .yes, .yes => .yes
  | _, _ => .maybe

mutual

/-- Does a value match a pattern, and what does the pattern bind? -/
partial def fit (ctx : ACtx) : Pattern → AVal → Fit × List (String × AVal)
  | .wild, _ => (.yes, [])
  | .int _, _ | .marked _ _, _ => (.maybe, [])
  | .var x, v =>
    match ctx.ctorOf x with
    | some c => fitData ctx c [] v
    | none =>
      match ctx.aliases[x]? with
      | some e =>
        match (exprToPat e).toOption with
        | some p => fit ctx p v
        | none => (.maybe, [])
      | none => (.yes, [(x, v)])
  | .ctor x _ ps, v =>
    match ctx.ctorOf x with
    | some c => fitData ctx c ps v
    | none => (.maybe, (ps.flatMap (binders ctx)).map (·, AVal.unknown))
  | .tuple ps, v => fitData ctx "" ps v

partial def fitData (ctx : ACtx) (tag : String) (ps : List Pattern) (v : AVal) :
    Fit × List (String × AVal) :=
  match v with
  | .data tag' args =>
    if tag' == tag && args.length == ps.length then fitAll ctx ps args else (.no, [])
  | _ => (.maybe, (ps.flatMap (binders ctx)).map (·, AVal.unknown))

partial def fitAll (ctx : ACtx) (ps : List Pattern) (vs : List AVal) :
    Fit × List (String × AVal) :=
  (ps.zip vs).foldl (fun (acc : Fit × List (String × AVal)) (p, v) =>
    let (f, binds) := fit ctx p v
    (acc.1.and f, binds ++ acc.2)) (.yes, [])

end

def maxUses (alts : Alts) : Nat := (alts.map (·.2)).foldl max 0

/-- Uses made by matching a value against a pattern: a binding taken apart by a
pattern that looks inside it is used. A plain name or `_` does not look. -/
partial def takenApart (ctx : ACtx) : Pattern → AVal → Nat
  | .wild, _ => 0
  | .var x, v =>
    if (binders ctx (.var x)).isEmpty then
      match v with
      | .tracked => 1
      | _ => 0
    else 0
  | _, .tracked => 1
  | .ctor _ _ ps, .data _ args =>
    ((ps.zip args).map fun (p, v) => takenApart ctx p v).foldl (· + ·) 0
  | .tuple ps, .data _ args =>
    ((ps.zip args).map fun (p, v) => takenApart ctx p v).foldl (· + ·) 0
  | _, _ => 0

/-- Does a value hold one `leaf` says yes of: in it, or in what a callable
in it has of where it was made? -/
partial def holdsVal (leaf : AVal → Bool) : AVal → Bool
  | .data _ args => args.any (holdsVal leaf)
  | .clo b clauses env =>
    (b.fvClauses clauses).eraseDups.any fun y =>
      match env.lookup y with
      | some v => holdsVal leaf v
      | none => false
  | v => leaf v

/-- Can a use of the binding come of this value? -/
def holdsTracked : AVal → Bool := holdsVal fun | .tracked => true | _ => false

/-- The name under which a callable keeps which functions were being followed
where it was made. -/
def activeMark : String := "%active"

/-- A callable runs as part of the functions it was made in, wherever it is
called: so a function that calls itself from a block it gives away is seen to,
and a block given to a function may call that function anew. -/
def ACtx.inside (ctx : ACtx) (env : List (String × AVal)) : ACtx :=
  match env.lookup activeMark with
  | some (.data _ fns) =>
    { ctx with active := fns.filterMap fun
        | .fn name => some name
        | _ => none }
  | _ => ctx

/-- A function's body as the count follows it: as checked, or as written. -/
def ACtx.bodyOf (ctx : ACtx) (f : String) : Option Flat.Body :=
  (ctx.fns[f]?).orElse fun _ => ctx.declFns[f]?

/-- May a call of a `probe` come of this value? -/
def holdsProbe : AVal → Bool := holdsVal fun | .probe => true | _ => false

open Flat in
mutual

/-- The uses made if a value goes somewhere the count cannot follow. For the
most uses, every callable in it is taken to be called; for the fewest, none. -/
partial def escapes (ctx : ACtx) (depth : Nat) : AVal → A Nat
  | .tracked => pure 1
  -- When it would be called is then not known.
  | .probe => if ctx.lenient then pure 0 else failure
  | .data _ args => do
    let ns ← args.mapM (escapes ctx depth)
    pure (ns.foldl (· + ·) 0)
  | .clo b clauses env => do
    if ctx.probing && !ctx.lenient && holdsProbe (.clo b clauses env) then failure
    let ctx := ctx.inside env
    -- For the fewest uses: a callable that mentions the binding has to be
    -- called, since the binding has to be used; one that does not, need not.
    if ctx.lower && !holdsTracked (.clo b clauses env) then return 0
    tick
    let mut ns : List Nat := []
    for clause in clauses do
      let ⟨pats, body⟩ := b.clause clause
      let params := (pats.flatMap (binders ctx)).map (·, AVal.unknown)
      let found ← runStmts ctx depth b (params ++ env) body.toList
      for (v, n) in found do
        ns := (n + (← escapes ctx depth v)) :: ns
    pure (ctx.fold ns)
  | _ => pure 0

/-- The paths that go on merged into one count, with what each yields going
where the count cannot follow; and the paths that have left. -/
partial def settle (ctx : ACtx) (depth : Nat) (alts : Alts) (leaves : Bool := true) :
    A (Option Nat × Alts) := do
  let mut ns : List Nat := []
  let mut left : Alts := []
  for (v, n) in alts do
    if isGone v then left := (v, n) :: left
    else if leaves then ns := (n + (← escapes ctx depth v)) :: ns
    else ns := n :: ns
  pure (if ns.isEmpty then none else some (ctx.fold ns), left)

/-- Keep the number of paths small: beyond a limit, merge them into one whose
value is unknown and whose uses are the most any of them made. -/
partial def cap (ctx : ACtx) (depth : Nat) (alts : Alts) : A Alts := do
  if alts.length ≤ 16 then pure alts
  else
    let (on, left) ← settle ctx depth alts
    let merged : Alts := match on with
      | some n => [(.unknown, n)]
      | none => []
    pure (merged ++ (if left.isEmpty then [] else [(.gone "*", ctx.fold (left.map (·.2)))]))

/-- A call the count cannot follow: its arguments escape. -/
partial def unfollowed (ctx : ACtx) (depth : Nat) (args : List AVal) (quiet : Bool := false) :
    A Alts := do
  -- What is called may call a `probe` it is given, now, or keep it in what
  -- it gives back.
  if ctx.probing && args.any holdsProbe then
    let mut n := 0
    for a in args do
      n := n + (← escapes { ctx with lenient := true } depth a)
    return [(.probe, n), (.gone probeTarget, n)]
  let mut n := 0
  for a in args do
    n := n + (← escapes ctx depth a)
  -- What is called may not come back.
  pure (if ctx.lower && !quiet then [(.unknown, n), (.gone "*", n)] else [(.unknown, n)])

partial def applyClauses (ctx : ACtx) (depth : Nat) (b : Body) (clauses : Array ClauseId)
    (env : List (String × AVal)) (args : List AVal) : A Alts := do
  let mut out : Alts := []
  for clause in clauses do
    let ⟨pats, body⟩ := b.clause clause
    -- A block without parameters that is given one argument drops it.
    let pats := if pats.isEmpty && args.length == 1 then [Pattern.wild] else pats
    -- A clause of one tuple, given that many arguments, takes them as its
    -- parts.
    let pats := match pats with
      | [.tuple parts] => if args.length ≥ 2 && parts.length == args.length then parts else pats
      | _ => pats
    if pats.length == args.length then
      let (fitness, binds) := fitAll ctx pats args
      -- A value a `probe` may be in is not followed through a pattern.
      if ctx.probing then
        for (p, v) in pats.zip args do
          match p, v with
          | .var _, _ => pure ()
          | .wild, _ => pure ()
          | _, .probe => failure
          | _, _ => pure ()
      let taken := ((pats.zip args).map fun (p, v) => takenApart ctx p v).foldl (· + ·) 0
      let run : A Alts := do
        let alts ← runStmts ctx depth b (binds ++ env) body.toList
        pure (alts.map fun (v, n) => (v, n + taken))
      match fitness with
      | .no => pure ()
      | .maybe => out := out ++ (← run)
      | .yes =>
        out := out ++ (← run)
        break
  if out.isEmpty then unfollowed ctx depth args else cap ctx depth out

partial def callValue (ctx : ACtx) (depth : Nat) (f : AVal) (args : List AVal) : A Alts := do
  tick
  match f with
  | .tracked => do
    -- Calling the binding uses it.
    let alts ← unfollowed ctx depth args
    pure (alts.map fun (v, n) => (v, n + 1))
  | .probe => do
    let mut n := 0
    for a in args do
      n := n + (← escapes { ctx with lenient := true } depth a)
    pure [(.gone probeTarget, n), (if args.any holdsProbe then .probe else .unknown, n)]
  | .clo b clauses env => applyClauses (ctx.inside env) depth b clauses env args
  | .fn name =>
    match depth, ctx.bodyOf name with
    | d + 1, some fb =>
      modify fun s => { s with followed := s.followed.push name }
      -- (A call of a function being followed, again: it comes back, or never
      -- does, as the first call does; that one's paths are counted there.)
      if ctx.active.contains name then unfollowed ctx depth args (quiet := true)
      else
        let follow := applyClauses { ctx with active := name :: ctx.active } d fb fb.roots [] args
        -- (A call followed before, with the same values and in the same
        -- context, comes to what it came to then, and costs what it cost.)
        match args.mapM AVal.key? with
        | none => follow
        | some ks =>
          let key := s!"{name}|{d}|{ctx.lower}{ctx.handed}{ctx.probing}{ctx.lenient}|{ctx.active}|{ks}"
          match (← get).memo[key]? with
          | some (alts, cost) =>
            let s ← get
            if s.fuel < cost then failure
            set { s with fuel := s.fuel - cost }
            pure alts
          | none =>
            let before := (← get).fuel
            let alts ← follow
            modify fun s => { s with memo := s.memo.insert key (alts, before - s.fuel) }
            pure alts
    | _, _ => unfollowed ctx depth args
  | _ => unfollowed ctx depth args

/-- Evaluate expressions left to right, over every combination of paths. A
path that left on the way has only the value that says so. -/
partial def runList (ctx : ACtx) (depth : Nat) (b : Body) (env : List (String × AVal)) :
    List ExprId → A (List (List AVal × Nat))
  | [] => pure [([], 0)]
  | e :: es => do
    let heads ← runExpr ctx depth b env e
    let mut out : List (List AVal × Nat) := []
    for (v, n) in heads do
      if isGone v then out := ([v], n) :: out
    let on := heads.filter fun (v, _) => !isGone v
    unless on.isEmpty do
      let tails ← runList ctx depth b env es
      out := out ++ on.flatMap fun (v, n) => tails.map fun (vs, m) =>
        if (goneOf vs).isSome then (vs, n + m) else (v :: vs, n + m)
    if out.length ≤ 16 then pure out
    else
      let mut ns : List Nat := []
      let mut left : List Nat := []
      for (vs, n) in out do
        if (goneOf vs).isSome then left := n :: left
        else
          let mut total := n
          for v in vs do
            total := total + (← escapes ctx depth v)
          ns := total :: ns
      let merged := if ns.isEmpty then [] else [((e :: es).map fun _ => AVal.unknown, ctx.fold ns)]
      pure (merged ++ (if left.isEmpty then [] else [([AVal.gone "*"], ctx.fold left)]))

partial def runExpr (ctx : ACtx) (depth : Nat) (b : Body) (env : List (String × AVal)) (e : ExprId) : A Alts :=
  match b.expr e with
  | .int _ | .mark _ | .type _ => pure [(.unknown, 0)]
  | .name q x => do
    tick
    -- Naming the binding is not yet a use; calling it, taking it apart, or
    -- letting it go where the count cannot follow is.
    match (if q.isNone then env.lookup x else none) with
    | some v => pure [(v, 0)]
    | none =>
      if let some c := ctx.ctorOf x then pure [(.data c [], 0)]
      else if (ctx.ops[x]?).isSome then pure [(.unknown, 0)]
      else if (ctx.bodyOf x).isSome then pure [(.fn x, 0)]
      else
        match ctx.aliases[x]? with
        | some value =>
          let (ab, ae) := Flat.ofExpr value
          runExpr ctx depth ab [] ae
        | none => pure [(.unknown, 0)]
  | .label _ => pure [(.unknown, 0)]
  | .tuple es => do
    let alts ← runList ctx depth b env es.toList
    pure (alts.map fun (vs, n) =>
      match goneOf vs with
      | some t => (.gone t, n)
      | none => (.data "" vs, n))
  | .proj e idx => do
    let alts ← runExpr ctx depth b env e
    pure (alts.map fun (v, n) =>
      match v with
      | .data _ args => (args.getD idx .unknown, n)
      | .tracked => (.unknown, n + 1)
      | .gone t => (.gone t, n)
      | .probe => (.probe, n)
      | _ => (.unknown, n))
  | .call id f args | .tailCall id f args => runCall ctx depth b env f args.toList id
  | .closure id clauses =>
    if id != 0 && ctx.now.contains id then applyClauses ctx depth b clauses env []
    else
      -- Counting where a value is handed on: a callable that captures it
      -- and is kept in a variable has it, and destroys it if it is let go
      -- without being called. (The variable is then counted as any value.)
      let captured := if ctx.owning && ctx.capturesOwned then
          let free := b.fvClauses clauses
          env.filter fun (y, v) => free.contains y && isTracked v
        else []
      let env := if captured.isEmpty then env
        else env.map fun (y, v) => if captured.any (·.1 == y) then (y, AVal.unknown) else (y, v)
      pure [(.clo b clauses ((activeMark, .data activeMark (ctx.active.map AVal.fn)) :: env),
        if captured.isEmpty then 0 else 1)]
  | .handle subject arms => do
    let subject ← runExpr ctx depth b env subject
    let mut completions : Array ClauseId := #[]
    let mut repeated := 0
    let mut terminal : Alts := []
    let mut handled : List String := []
    for arm in arms do
      let ⟨pats, body⟩ := b.clause arm
      match pats with
      | [.ctor name _ ps] =>
        match ctx.ops[name]? with
        | some resumptive =>
          handled := name :: handled
          let params := (ps.flatMap (binders ctx)).map (·, AVal.unknown)
          let alts ← runStmts ctx depth b (params ++ env) body.toList
          if resumptive then
            -- May run any number of times: one use there is already too many,
            -- and none there can be relied on.
            unless ctx.lower do
              for (v, n) in alts do
                -- (When it runs is not known either.)
                if ctx.probing && (holdsProbe v || v matches .gone _) then
                  terminal := terminal ++ [(.gone probeTarget, n)]
                else if n + (← escapes ctx depth v) > 0 then repeated := 2
          else terminal := terminal ++ alts
        | none => completions := completions.push arm
      | _ => completions := completions.push arm
    -- A path that left for an operation handled here goes on from here.
    let subject := subject.map fun (v, n) =>
      match v with
      | .gone t => if handled.contains t then (AVal.unknown, n) else (v, n)
      | _ => (v, n)
    let mut done : Alts := []
    for (v, n) in subject do
      if isGone v || completions.isEmpty then done := (v, n) :: done
      else
        let found ← applyClauses ctx depth b completions env [v]
        for (v', n') in found do
          done := (v', n + n') :: done
    -- How much of the subject ran before an arm that does not resume is not
    -- known: for the fewest uses, none of it.
    let before := if ctx.lower then 0 else maxUses subject
    let all := done ++ terminal.map fun (v, n) => (v, n + before)
    cap ctx depth (all.map fun (v, n) => (v, n + repeated))
  | .labelScope l body => do
    let alts ← runStmts ctx depth b env body.toList
    if ctx.lower then
      -- A path that left for this label goes on from here.
      pure (alts.map fun (v, n) =>
        match v with
        | .gone t => if t == "@" ++ l then (AVal.unknown, n) else (v, n)
        | _ => (v, n))
    -- (A block the front end makes, `%block`, is left through no label.)
    else if l == "%block" then pure alts
    else
      -- Leaving through the label gives a value the count does not follow.
      pure (alts ++ [(.unknown, maxUses alts)])
  | .ref _ _ | .refField _ _ _ _ _ => pure [(.unknown, 0)]
  | .fieldOf _ e _ => do
    let alts ← runExpr ctx depth b env e
    pure (alts.map fun (v, n) =>
      match v with
      | .tracked => (AVal.unknown, n + 1)
      | .gone t => (.gone t, n)
      | .probe => (.probe, n)
      | _ => (.unknown, n))
  -- Borrowing from a reference is no use of it.
  | .reborrow _ e => do
    let alts ← runExpr ctx depth b env e
    pure (alts.map fun (v, n) => if isGone v then (v, n) else (AVal.unknown, n))
  | .deref e => do
    let alts ← runExpr ctx depth b env e
    let (on, left) ← settle ctx depth alts
    pure ((match on with
      | some n => [(AVal.unknown, n)]
      | none => []) ++ left)

partial def runCall (ctx : ACtx) (depth : Nat) (b : Body) (env : List (String × AVal)) (f : ExprId)
    (args : List ExprId) (id : Nat) : A Alts := do
  tick
  let sure := ctx.lower && ctx.sure.contains id
  let alts ← runCallee ctx depth b env f args sure
  -- A call whose type says it comes back does, whatever was lost track of
  -- inside it.
  if sure then
    pure (alts.map fun (v, n) => if isGone v then (AVal.unknown, n) else (v, n))
  else pure alts

partial def runCallee (ctx : ACtx) (depth : Nat) (b : Body) (env : List (String × AVal)) (f : ExprId)
    (args : List ExprId) (sure : Bool) : A Alts := do
  let general : A Alts := do
    let mut out : Alts := []
    let found ← runExpr ctx depth b env f
    for (fv, n) in found do
      if isGone fv then out := (fv, n) :: out
      else
        let found ← runList ctx depth b env args
        for (vs, m) in found do
          match goneOf vs with
          | some t => out := (.gone t, n + m) :: out
          | none =>
            if ctx.handed && vs.any (fun v => match v with
                | .tracked => true
                | _ => false) then
              -- Given away: it is whoever takes it that has it now. (As
              -- often as it is given.)
              let given := (vs.filter fun v => match v with
                | .tracked => true
                | _ => false).length
              out := (.unknown, n + m + given) :: out
            else
            -- A call that comes back and is given nothing a use could come
            -- of need not be followed.
            if sure && !holdsTracked fv && !vs.any holdsTracked
                && !(ctx.probing && (holdsProbe fv || vs.any holdsProbe)) then
              out := (.unknown, n + m) :: out
            -- A function given nothing a use could come of, for the most
            -- uses along a path: followed so far, and where that is not far
            -- enough, taken as a call that cannot be followed is
            -- (`unfollowed`), not as the count given up.
            else if !ctx.lower && !ctx.probing && (match fv with | .fn _ => true | _ => false)
                && !vs.any holdsTracked && !vs.any holdsProbe then
              let st ← get
              let budget := min st.fuel 2000
              match (callValue ctx depth fv vs).run { st with fuel := budget } with
              | some (found, st') =>
                set { st' with fuel := st.fuel - (budget - st'.fuel) }
                for (v, k) in found do
                  out := (v, n + m + k) :: out
              | none =>
                set { st with fuel := st.fuel - budget }
                out := (.unknown, n + m) :: out
            else
              let found ← callValue ctx depth fv vs
              for (v, k) in found do
                out := (v, n + m + k) :: out
    cap ctx depth out
  -- The arguments go to something that is not followed; `after` says what
  -- becomes of the path once they have.
  let handedOn := fun (after : Nat → Alts) => (do
    let mut out : Alts := []
    let found ← runList ctx depth b env args
    for (vs, n) in found do
      match goneOf vs with
      | some t => out := (.gone t, n) :: out
      | none =>
        let mut k := n
        for v in vs do
          k := k + (← escapes ctx depth v)
        out := out ++ after k
    cap ctx depth out : A Alts)
  match b.expr f with
  | .label l =>
    -- Applying a label leaves for its scope.
    if ctx.lower then handedOn fun n => [(.gone ("@" ++ l), n)] else general
  -- A value written with its type is the value: nothing is called.
  | .mark .ascribe | .mark .inst | .mark .move =>
    match args with
    | value :: _ => runExpr ctx depth b env value
    | [] => pure [(.unknown, 0)]
  -- (Asking what a reference points to was built by only looks.)
  | .mark .ctorIs | .mark .shapes => if ctx.lower then handedOn fun n => [(.unknown, n)] else general
  | .name q x =>
    if q.isNone && (env.lookup x).isSome then general
    else if let some c := ctx.ctorOf x then
      let alts ← runList ctx depth b env args
      pure (alts.map fun (vs, n) =>
        match goneOf vs with
        | some t => (.gone t, n)
        | none => (.data c vs, n))
    else if x == "fixed_len" && (ctx.bodyOf x).isNone then
      -- Asking how long a `[T; N]` is only looks at it: it is still
      -- whoever's it was.
      let found ← runList ctx depth b env args
      pure (found.map fun (vs, n) =>
        match goneOf vs with
        | some t => (.gone t, n)
        | none => (.unknown, n))
    else if let some resumptive := ctx.ops[x]? then
      -- Performing an operation hands its payload to a handler.
      if ctx.lower then
        -- The handler need not resume: the path may end here. Unless the
        -- operation is declared `[1, 1]`: then it has to.
        if resumptive && ctx.exact.contains x then handedOn fun n => [(AVal.unknown, n)]
        else handedOn fun n => (if resumptive then [(AVal.unknown, n)] else []) ++ [(.gone x, n)]
      else
        let mut worst := 0
        let found ← runList ctx depth b env args
        for (vs, n) in found do
          let found ← unfollowed ctx depth vs
          for (_, k) in found do
            worst := max worst (n + k)
        pure [(.unknown, worst)]
    else if ctx.lower && ctx.quiet.contains x && (ctx.bodyOf x).isNone then
      handedOn fun n => [(.unknown, n)]
    else general
  | _ => general

partial def runStmts (ctx : ACtx) (depth : Nat) (b : Body) (env : List (String × AVal)) :
    List StmtId → A Alts
  | [] => pure [(.data "" [], 0)]
  | s :: rest =>
    match b.stmt s, rest with
    | .located _ _ s, rest => runStmts ctx depth b env (s :: rest)
    | .expr e, [] => runExpr ctx depth b env e
    | .expr e, rest => do
      -- The value is dropped, so the rest does not depend on which path was taken.
      let found ← runExpr ctx depth b env e
      -- (Where being let go is a use, as it is of a value with a `drop` to
      -- run, which the statement then runs: the value itself, let go here.)
      let letGo := if ctx.handed && !found.isEmpty && found.all (fun (v, _) => isTracked v) then 1 else 0
      let (on, left) ← settle ctx depth found (leaves := false)
      match on with
      | none => pure left
      | some first =>
        let alts ← runStmts ctx depth b env rest
        pure ((alts.map fun (v, n) => (v, n + first + letGo)) ++ left)
    | .let_ pat value, rest => do
      let mut out : Alts := []
      let owning := match pat, b.expr value with
        | .var _, .closure _ _ => true
        | .var _, .call _ m #[c, _] =>
          b.mark? m == some .ascribe && (match b.expr c with | .closure _ _ => true | _ => false)
        | _, _ => false
      let found ← runExpr { ctx with owning := owning } depth b env value
      for (v, n) in found do
        if isGone v then out := (v, n) :: out
        else
          if ctx.probing then
            match pat, v with
            | .var _, _ => pure ()
            | .wild, _ => pure ()
            | _, .probe => failure
            | _, _ => pure ()
          let (_, binds) := fit ctx pat v
          let bound := binds.map (·.1)
          let others := ((binders ctx pat).filter (!bound.contains ·)).map (·, AVal.unknown)
          let taken := takenApart ctx pat v
          -- (`let _ = x` lets `x` go, as `x;` does.)
          let taken := match pat with
            | .wild => if ctx.handed && isTracked v then taken + 1 else taken
            | _ => taken
          let found ← runStmts ctx depth b (binds ++ others ++ env) rest
          for (v', n') in found do
            out := (v', n + n' + taken) :: out
      cap ctx depth out
    | .letMut x value, rest => do
      -- The value goes into a cell, where the count does not follow it.
      let (on, left) ← settle ctx depth (← runExpr ctx depth b env value)
      match on with
      | none => pure left
      | some first =>
        let alts ← runStmts ctx depth b ((x, .unknown) :: env) rest
        pure ((alts.map fun (v, n) => (v, n + first)) ++ left)
    | .assign target value, rest => do
      let (on, left) ← settle ctx depth (← runExpr ctx depth b env value)
      match on with
      | none => pure left
      | some first =>
        let (inTarget, left') ← match b.expr target with
          | .deref e => settle ctx depth (← runExpr ctx depth b env e)
          | _ => pure (some 0, [])
        match inTarget with
        | none => pure (left ++ left'.map fun (v, n) => (v, n + first))
        | some inTarget =>
          let alts ← runStmts ctx depth b env rest
          pure ((alts.map fun (v, n) => (v, n + first + inTarget)) ++ left
            ++ left'.map fun (v, n) => (v, n + first))
    | .defer e, rest => do
      -- A cleanup runs however the rest is left.
      let mut ns : List Nat := []
      for (v, n) in ← runExpr ctx depth b env e do
        ns := (n + (← escapes ctx depth v)) :: ns
      let first := ctx.fold ns
      let alts ← runStmts ctx depth b env rest
      pure (alts.map fun (v, n) => (v, n + first))

end

/-- The most uses of `x` along any path through `body`, or with `ctx.lower` the
fewest, if the count finishes. `outer` are the other local names in scope,
about which nothing is known. -/
def pathUsesWith (ctx : ACtx) (outer : List String) (x : String) (b : Flat.Body) (body : List Flat.StmtId)
    (known : List (String × AVal) := []) : Option Nat × Array String :=
  let env := known ++ (x, AVal.tracked) :: outer.map (·, AVal.unknown)
  let count : A Nat := do
    let mut ns : List Nat := []
    let found ← runStmts ctx 8 b env body
    for (v, n) in found do
      -- What the body yields leaves the region being counted.
      ns := (n + (← escapes ctx 8 v)) :: ns
    pure (ctx.fold ns)
  match count.run { fuel := 200000 } with
  | some (n, s) => (some n, s.followed)
  -- (Not finished: what it would have read is not known.)
  | none => (none, #["*"])

/-- The most uses of `x` on any path through `body` up to a call of one of the
`probes`, if the count finishes: none if no use comes before such a call. A
path that leaves the body with something a probe may be called through ends
there too, since the call may follow. -/
def usesBeforeProbeWith (ctx : ACtx) (outer : List String) (x : String) (b : Flat.Body) (body : List Flat.StmtId)
    (known : List (String × AVal)) : Option Nat × Array String :=
  let ctx := { ctx with lower := false, probing := true }
  let env := known ++ (x, AVal.tracked) :: outer.map (·, AVal.unknown)
  let count : A Nat := do
    let mut worst := 0
    for (v, n) in ← runStmts ctx 8 b env body do
      match v with
      | .gone t => if t == probeTarget || t == "*" then worst := max worst n
      | _ =>
        if holdsProbe v then
          worst := max worst (n + (← escapes { ctx with lenient := true } 8 v))
    pure worst
  match count.run { fuel := 200000 } with
  | some (n, s) => (some n, s.followed)
  | none => (none, #["*"])

/-- `pathUsesWith`, what it followed noted (`St.followed`): what a group's
check read of other functions' bodies, which what is kept of it is keyed
by (`checkGroupKept`). -/
def pathUses (ctx : ACtx) (outer : List String) (x : String) (b : Flat.Body) (body : List Flat.StmtId)
    (known : List (String × AVal) := []) : M (Option Nat) := do
  let (r, f) := pathUsesWith ctx outer x b body known
  unless f.isEmpty do modify fun s => { s with followed := s.followed ++ f }
  pure r

def usesBeforeProbe (ctx : ACtx) (outer : List String) (x : String) (b : Flat.Body) (body : List Flat.StmtId)
    (known : List (String × AVal)) : M (Option Nat) := do
  let (r, f) := usesBeforeProbeWith ctx outer x b body known
  unless f.isEmpty do modify fun s => { s with followed := s.followed ++ f }
  pure r

open Flat in
/-- Does evaluating this run nothing at all? `quiet` names what only builds a
value. -/
partial def stillExpr (b : Body) (quiet : String → Bool) (e : ExprId) : Bool :=
  match b.expr e with
  | .int _ | .name _ _ | .label _ | .closure _ _ | .ref _ _ => true
  | .tuple es => es.all (stillExpr b quiet)
  | .call _ f args =>
    match b.expr f with
    | .name _ g => quiet g && args.all (stillExpr b quiet)
    | .mark .ctorIs | .mark .shapes => args.all (stillExpr b quiet)
    | _ => false
  | _ => false

def isName (b : Flat.Body) (x : String) (e : Flat.ExprId) : Bool := b.bare? e == some x

open Flat in
mutual

/-- Whether `x` is used by this expression before anything in it could fail to
come back: `some true` if so, `some false` if something that may not come back
runs first, `none` if neither happens. -/
partial def firstUse (b : Body) (quiet : String → Bool) (x : String) (e : ExprId) : Option Bool :=
  match b.expr e with
  | .tuple es => firstParts b quiet x true false es.toList
  | .call _ f args | .tailCall _ f args =>
    firstParts b quiet x (match b.expr f with
      | .name _ g => quiet g
      | .mark .ctorIs | .mark .shapes => true
      | _ => false) false (f :: args.toList)
  | .proj e _ => if isName b x e then some true else firstUse b quiet x e
  | .deref e => if isName b x e then none else firstUse b quiet x e
  | .handle _ _ => some false
  | .labelScope _ _ => some false
  | _ => none

/-- The parts of a tuple or call, in order. `x` among them is handed on once
all are computed, so nothing after it may fail to come back. `builds` says the
whole only builds a value; otherwise it is a call that may not come back. -/
partial def firstParts (b : Body) (quiet : String → Bool) (x : String) (builds pending : Bool) :
    List ExprId → Option Bool
  | [] => if pending then some true else if builds then none else some false
  | e :: rest =>
    if isName b x e then firstParts b quiet x builds true rest
    else if stillExpr b quiet e then firstParts b quiet x builds pending rest
    else
      match firstUse b quiet x e with
      | some true => if pending then some false else some true
      | some false => some false
      | none => if pending then some false else firstParts b quiet x builds pending rest

end

open Flat in
/-- Is `x` certainly used before anything in these statements could fail to
come back? Decided from their shape, in the order they are evaluated: a quick
yes that saves counting along paths. -/
partial def usedFirst (b : Body) (quiet : String → Bool) (x : String) : List StmtId → Bool
  | [] => false
  | s :: rest =>
    match b.stmt s, rest with
    | .located _ _ s, rest => usedFirst b quiet x (s :: rest)
    | .expr e, [] => isName b x e || firstUse b quiet x e == some true
    | .expr e, rest =>
      match firstUse b quiet x e with
      | some r => r
      | none => usedFirst b quiet x rest
    | .let_ pat value, rest =>
      if isName b x value then true
      else
        match firstUse b quiet x value with
        | some r => r
        | none => !(Elab.patVars pat).contains x && usedFirst b quiet x rest
    | .letMut y value, rest =>
      if isName b x value then true
      else
        match firstUse b quiet x value with
        | some r => r
        | none => y != x && usedFirst b quiet x rest
    | .assign _ value, rest =>
      if isName b x value then true
      else
        match firstUse b quiet x value with
        | some r => r
        | none => usedFirst b quiet x rest
    | .defer _, rest => usedFirst b quiet x rest

/-- One binding of `checkUses`: that its type allows how often it is used, with
`s` the state the bindings were checked from. -/
def checkUsesOf (code : Flat.Body) (pos : String) (body : List Flat.StmtId) (s : St) (ctx : ACtx)
    (names : List String) (x : String) (b : Binding) : M Unit := do
  let resumptive := fun (name : String) =>
    match s.ops.lookup name with
    | some sig => sig.result.isSome
    | none => false
  -- (A value clauses are given again, after one of them reached through a
  -- reference in it and was not for what it found: said as that.)
  let twice := fun (x : String) =>
    if x.startsWith "%again" then
      "a clause reaches through a reference inside the value, and where it is not for what it finds the clauses after it are given the value again"
    else s!"`{x}` is used more than once"
  let t := match b with
    | .val t _ => some t
    | .poly p => some p.ty
    | _ => none
  -- Parts of the name's value read, `x.f`. Where the name is used no other
  -- way, each part is a value of its own: used as often as that part is
  -- read, and the parts never read are what is let go.
  let mine : List (Ty × Nat × String × String) := match b with
    | .val _ bid => s.partReads.toList.filterMap fun (owner, _, subject, idx, part, at_) =>
        if owner == bid then some (subject, idx, part, at_) else none
    | _ => []
  -- (A field read by name before its type was known: which field it is.)
  let mine ← mine.mapM fun (subject, idx, part, at_) => do
    if idx == Syntax.partUnknown then
      match ← (try fieldIndex subject part catch _ => pure none) with
      | some found => pure (subject, found, part, at_)
      | none => pure (subject, idx, part, at_)
    else pure (subject, idx, part, at_)
  if let .val _ bid := b then
    unless mine.isEmpty do
      modify fun st => { st with partReads := st.partReads.filter fun (owner, _, _, _, _, _) => owner != bid }
  let apart := !mine.isEmpty && !body.any (code.usedWholeStmt x)
  -- Used whole too, where each part read is of a type that is copied, and
  -- no part is read once the whole has been given away: reading those
  -- parts takes nothing out of it, as Rust's reading of a `Copy` field
  -- does not, and they are not uses of it (`request.point == name` and
  -- then `push(&mut mine, request)`).
  let copiedParts ← if apart || mine.isEmpty then pure false else
    mine.allM fun (subject, idx, _, _) => do
      match ← (try fieldType subject idx catch _ => pure none) with
      | some ft =>
        let ft ← zonk ft
        modify fun st => { st with seen := {} }
        pure ((freeTys ft).isEmpty && (← borrowsOnlyStatic ft) && !hasParam ft
          && !(← tyOwnsOnce [] ft) && (← tyHasDrop [] ft).isNone)
      | none => pure false
  let looked : Flat.Body := if !copiedParts then code else
    (List.range code.exprs.size).foldl (fun (bb : Flat.Body) i =>
      match bb.exprs[i]! with
      | .fieldOf _ e _ | .proj e _ =>
        if bb.bare? e == some x then { bb with exprs := bb.exprs.set! i (.ref false x) } else bb
      | _ => bb) code
  let readAfter := (body.foldl (fun (seen, bad) s =>
    let (seen', bad') := looked.borrowAfterValueStmt x seen s
    (seen', bad || bad')) (false, false)).2
  let copiedParts := copiedParts && !readAfter
  let code := if copiedParts then looked else code
  -- A value with a `drop` to run, of which only parts that can be used
  -- any number of times are read: reading them takes nothing out of it.
  -- It stays whole, and is destroyed when its block is left, as a name
  -- that nothing uses is. (Not in its own `drop`, which is what lets go
  -- of it.)
  let mut kept := false
  if apart then
    if let (some t, .val _ bid) := (t, b) then
      if let .con n _ ← find t then
        if s.kimpls.has (.of "Drop") n
            && s.owner != Syntax.implFnName "Drop" n "drop" then
          let mut plain := true
          for (subject, idx, _, _) in mine do
            match ← (try fieldType subject idx catch _ => pure none) with
            | some ft =>
              let ft ← zonk ft
              modify fun st => { st with seen := {} }
              unless (freeTys ft).isEmpty && (← borrowsOnlyStatic ft) && !hasParam ft
                  && !(← tyOwnsOnce [] ft) && (← tyHasDrop [] ft).isNone do
                plain := false
            | none => plain := false
          if plain then
            if let some (line, col) := s.bindSites.lookup bid then
              kept := true
              modify fun st => { st with
                dropCands := st.dropCands.push
                  (⟨st.owner, line, col, (if st.letBinds.contains bid then .letBound x else .name x), false⟩, t, pos)
                aparts := st.aparts.filter fun (_, _, whose) => whose != some bid }
      -- (Of a type not known yet, as a callable's parameter may be: asked
      -- again once the function it is in has been read.)
      if let .var _ ← find t then
        if let some (line, col) := s.bindSites.lookup bid then
          let site : Elab.DropSite :=
            ⟨s.owner, line, col, (if s.letBinds.contains bid then .letBound x else .name x), false⟩
          let reads : List (Ty × Nat) := mine.map fun (subject, idx, _, _) => (subject, idx)
          modify fun st => { st with lateKeeps := st.lateKeeps.push (site, t, reads, pos) }
  if kept then return
  if apart then
    let (subject, firstAt) := match mine with
      | (subject, _, _, at_) :: _ => (subject, at_)
      | [] => (Ty.unit, pos)
    let taken := (mine.map fun (_, idx, _, _) => idx).eraseDups
    -- (The machine counts each read of a value that holds a resumption
    -- as a use of all of it.)
    if usesStmts code resumptive x body ≥ 2 then
      modify fun st => { st with takenApart := st.takenApart.push (subject, pos ++ s!"`{x}` is used more than once") }
    let others ← (try otherFields subject 0 catch _ => pure none)
    let count := match others with
      | some rest => rest.length + 1
      | none => 0
    let site := match b with
      | .val _ bid => s.bindSites.lookup bid
      | _ => none
    for i in List.range count do
      unless taken.contains i do
        if let some ft ← (try fieldType subject i catch _ => pure none) then
          modify fun st => { st with pos := firstAt }
          mustDrop ft "taking one field of a value lets go of the rest"
          -- What is let go is destroyed when the name's block is left,
          -- as a name nothing uses is; where the name has no such place,
          -- nothing would destroy it.
          match site with
          | some (line, col) =>
            modify fun st =>
              { st with dropCands := st.dropCands.push (⟨st.owner, line, col, .part x i, false⟩, ft, firstAt) }
          | none =>
            modify fun st => { st with leftBehind := st.leftBehind.push (ft, firstAt ++ "taking one field of a value lets go of the rest") }
          modify fun st => { st with pos := pos }
    let mut seenParts : List String := []
    for (_, idx, part, at_) in mine do
      unless seenParts.contains part do
        seenParts := part :: seenParts
        let (ob, only) := Flat.onlyPartStmts code x part body
        let ft := (← (try fieldType subject idx catch _ => pure none)).getD subject
        if usesStmts ob resumptive x only ≥ 2 then
          let ft ← zonk ft
          modify fun st => { st with seen := {} }
          let dropped := (← tyHasDrop [] ft).isSome
          let twice : Bool := match ← pathUses (if dropped then { ctx with handed := true } else ctx)
              (names.filter (· != x)) x ob only with
            | some n => decide (n ≥ 2)
            | none => true
          if twice then
            modify fun st => { st with pos := at_ }
            mustDup ft s!"`{x}.{part}` is used more than once"
            modify fun st => { st with pos := pos }
        if s.anyMust && !x.startsWith "%" then
          modify fun st =>
            { st with lowerChecks := st.lowerChecks.push (pos, x, ft, subject, names.filter (· != x), ob, only) }
  else if !copiedParts then
    -- Used as a whole too: each part read lets go of the rest of it.
    for (subject, idx, _, at_) in mine do
      modify fun st => { st with pos := at_ }
      match ← otherFields subject idx with
      | some rest =>
        for r in rest do
          mustDrop r "taking one field of a value lets go of the rest"
          modify fun st => { st with leftBehind := st.leftBehind.push (r, at_ ++ "taking one field of a value lets go of the rest") }
      | none => mustDrop subject "taking one field of a value lets go of the rest"
      modify fun st => { st with pos := pos }
  if apart then return
  if let some t := t then
    let mentions := usesStmts code resumptive x body
    if mentions ≥ 2 then
      let t ← zonk t
      modify fun st => { st with seen := {} }
      -- (A value with a `drop` to run is used where it is given away,
      -- whatever takes it does: giving it away twice would run it twice.)
      let dropped := (← tyHasDrop [] t).isSome
      let settled := (freeTys t).isEmpty && (freeCaps t).isEmpty && !hasParam t
        && !(← tyOwnsOnce [] t) && !dropped
      unless settled do
        match ← pathUses (if dropped then { ctx with handed := true } else ctx)
            (names.filter (· != x)) x code body with
        | some n => if n ≥ 2 then mustDup t (twice x)
        -- (The count gave up: said as that, not as a second use it did not
        -- find.)
        | none => mustDup t s!"`{x}` is used in more than one place, and the paths through the function are too many for the compiler to follow far enough to see that it is used at most once on each (give it to a function of its own where it is used, or say where it is taken with `replace`)"
    -- A value that has to be used: is it, however the body goes? Looked at
    -- once the function's types are known. A name the compiler made up
    -- stands for nothing the program wrote.
    if s.anyMust && !x.startsWith "%" then
      modify fun st =>
        { st with lowerChecks := st.lowerChecks.push (pos, x, t, t, names.filter (· != x), code, body) }

/-- Record, for each binding used more than once in `body`, that its type must
allow that. `outer` is the scope the bindings are added to. A binding whose
type is already known to allow it needs no count; one that fails the coarse
count is counted again along the paths the program can take. -/
def checkUses (code : Flat.Body) (pos : String) (outer : Scope) (binds : Scope) (body : List Flat.StmtId) : M Unit := do
  -- Report at the statement the bindings belong to, not the last one checked.
  modify fun st => { st with pos := pos }
  let s ← get
  -- What only computes: the machine's own operations and what builds a value.
  let ctx : ACtx :=
    { fns := s.runFns, declFns := s.declFns, ctors := s.runCtors, aliases := s.runAliases, ops := s.runOps,
      quiet := intrinsics, exact := s.runExact, now := s.runNow }
  let names := (binds ++ outer).map (·.1)
  for (x, b) in binds do
    checkUsesOf code pos body s ctx names x b

/-- A callable of `arity` arguments that uses the environment `%env` when it
is called. -/
def usesEnv (arity : Nat) : AVal :=
  let b := Flat.ofClauses [.mk (List.replicate arity Pattern.wild) [.expr (.proj (.name none "%env") 0)]]
  .clo b b.roots [("%env", AVal.tracked)]

/-- Does a value of this type hold a callable that can jump to a label? -/
partial def tyJumps (t : Ty) : M Bool := do
  match ← find t with
  | .var _ | .rigid _ => pure false
  | .con _ args | .tuple args => args.anyM tyJumps
  | .ref _ inner _ => tyJumps inner
  | .fn ps r _ _ cap => do
    if ← ps.anyM tyJumps then return true
    if ← tyJumps r then return true
    let some edges ← unseenEdges cap | return false
    for (_, what) in edges do
      match what with
      | .brand b => unless (← get).cells.any (·.1 == b) do return true
      | .ty t => if ← tyJumps t then return true
      | _ => pure ()
    return false

/-- Does a value of this type hold a borrow, of a variable or through one:
what its captures hold, followed through the types they hold. -/
partial def tyBorrows (t : Ty) (seen : List Nat := []) : M Bool := do
  let mut seen := seen
  for c in freeCaps (← zonk t) do
    let root ← findCap c
    if seen.contains root then continue
    seen := root :: seen
    for (_, what) in ← edgesFrom root do
      match what with
      | .loan _ => return true
      | .brand _ => return true
      | .touch _ _ => return true
      | .ty t' => if ← tyBorrows t' seen then return true
      | _ => pure ()
  pure false

/-- What must borrow nothing does not: a thread's callable (`F: 'static`). -/
def checkStatics (statics : Array (Ty × String)) : M Unit := do
  for (t, why) in statics do
    if ← tyBorrows t then throw why

/-- A callable that has to come back when called may hold no label. -/
def checkStays (stays : Array (Ty × String)) : M Unit := do
  for (t, why) in stays do
    modify fun s => { s with seen := {} }
    if ← tyJumps t then
      throw s!"{why}, but what it is given here can jump to a label and not come back"

/-- The edges whose source is the capture variable `c` itself, in the order
made: each by its number, with what it is and the name it is under. -/
def edgesOfSource (c : Nat) : M (List (Nat × Captured × Option (String × Nat))) := do
  let s ← get
  let mine := ((s.capOut.getD (← findCap c) #[]).toList.mergeSort (· ≤ ·)).eraseDups
  pure (mine.filterMap fun i => match s.capEdges.get? i with
    | some (src, what) => if src == c then some (i, what, (s.capEdgeNames.get? i).join) else none
    | none => none)


/-- A `let x` at `line:col` (or a parameter, at `0:0`) whose value one path
gives away and another does not: kept in a variable with a flag, set where it is given away, that
destroys it where its block ends if it is not (the elaborator's, from the
drop site `SiteName.given`, `Elab.flagged`), as Rust's drop flags do: it
stays the value it was checked as. -/
def flagPlace (owner : String) (line col : Nat) (x : String) (t : Ty) (pos : String)
    (b : Flat.Body) (body : List Flat.StmtId) : M Bool := do
  -- (A parameter, at no place: its variable starts where the clause's first
  -- statement is, `Elab.heldFirst`, and its flag is said there.)
  let at_ := if line != 0 then some (line, col) else
    match body.head?.map b.stmt with
    | some (.located l c _) => some (l, c)
    | _ => none
  let some (l, c) := at_ | return false
  modify fun st =>
    { st with dropCands := st.dropCands.push (⟨owner, l, c, .given x, false⟩, t, pos)
              flagged := (owner, pos) :: st.flagged }
  pure true
/-- With the types of a function known: note which of its calls certainly come
back, and look at each binding that may have to be used. `fnTy` is the
function's type.

A call comes back if its callee performs no operation and can jump to no
label. Effects not yet named are none at all unless something can supply
them: a callable the function was given, or one kept in a declared type. -/
def runLowerChecks (fnTy : Ty) : M Unit := do
  let s ← get
  modify fun st =>
    { st with calls := #[], lowerChecks := #[], abandoned := #[], envGroups := #[], envAfter := #[],
              envLent := #[] }
  unless s.anyMust || !s.envGroups.isEmpty || !s.envAfter.isEmpty || !s.envLent.isEmpty do return
  let mut sources : List Nat := []
  if let .fn ps _ _ _ _ ← zonk fnTy then
    sources := ps.flatMap freeRows
  -- A callable the function was given holds whatever its caller gave it: it
  -- comes back only if that holds no label.
  let mut given : List Nat := []
  if let .fn ps _ _ _ _ ← zonk fnTy then
    for c in ps.flatMap freeCaps do
      given := (← findCap c) :: given
  let mut sure := s.sure
  let mut conditional : List (Nat × Ty) := []
  for (id, callee, silent) in s.calls do
    let callee ← zonk callee
    if let .fn _ _ effs tail _ := callee then
      modify fun st => { st with seen := {} }
      -- (An effect all of whose operations are declared `[1, 1]` is always
      -- resumed: a callable that performs nothing else comes back.)
      let resumed := effs.all fun (e, _) =>
        let mine := s.ops.filter fun (_, sig) => sig.effect == e
        !mine.isEmpty && mine.all fun (_, sig) => sig.must && sig.result.isSome
      let silent := silent || (resumed && match tail with
        | none => true
        | some ρ => !sources.contains ρ)
      if silent && !(← tyJumps callee) then
        let mut theirs := false
        for c in freeCaps callee do
          if given.contains (← findCap c) then theirs := true
        if theirs then conditional := (id, callee) :: conditional
        else sure := sure.insert id
  modify fun st => { st with sure := sure }
  for (id, t, why) in s.abandoned do
    unless sure.contains id do
      modify fun st => { st with drops := st.drops.push (t, why) }
  let resumptive := fun (name : String) =>
    match s.ops.lookup name with
    | some sig => sig.result.isSome
    | none => false
  let ctx : ACtx :=
    { fns := s.runFns, declFns := s.declFns, ctors := s.runCtors, aliases := s.runAliases, ops := s.runOps,
      quiet := intrinsics, exact := s.runExact, lower := true, sure := sure }
  let quiet := fun (f : String) =>
    (ctx.ctorOf f).isSome || (intrinsics.contains f && (ctx.bodyOf f).isNone)
  let roots ← mustInfo
  -- What is found here is said first: it names the binding.
  let earlier := (← get).drops
  modify fun st => { st with drops := #[] }
  let mut relied := false
  -- Callables of which one is certainly called, sharing what they hold: that
  -- the others are then let go is no loss. Whoever gives them is asked that
  -- each holds what has to be used.
  let certain := (s.envGroups.toList.filter (·.2.2.1)).flatMap fun g => g.2.1.map (·.1)
  for (pos, x, t, whole, names, b, body) in s.lowerChecks do
    -- A variable that gives its value away: if some path does not use the
    -- value, the variable is given a cleanup that destroys it there.
    if let some (site, held, at_) := s.givenSites.lookup pos then
      unless usedFirst b quiet x body do
        let somewhere_not := match ← pathUses { ctx with handed := true } names x b body with
          | some n => n == 0
          | none => true
        if somewhere_not then
          modify fun st => { st with dropCands := st.dropCands.push (site, held, at_) }
    if certain.contains x then continue
    let t ← zonk t
    -- Only a type that has to be used, or one not yet known, needs the count.
    let free := !(freeTys t).isEmpty || !(freeCaps t).isEmpty || hasParam t
    modify fun st => { st with seen := {} }
    -- (A callable kept by `let` is general in what it captures, but what it
    -- holds is known: it has a `drop` to run if what it holds does.)
    let heldDrop ← match ← find t with
      | .fn _ _ _ _ cap => do
        modify fun st => { st with seen := {} }
        let held ← tyHasDrop [] t
        modify fun st => { st with seen := {} }
        -- (Or, in the program's own function, a value of a type it is
        -- generic in, which may have one.)
        let generic ← if s.ownItems && !libraryOwner s.owner then do
            let root ← findCap cap
            (← edgesFrom root).anyM fun (_, what) => do
              match what with
              | .ty heldTy =>
                if hasParam heldTy then
                  match ← find heldTy with
                  | .ref .. => pure false
                  | .fn .. => pure false
                  | _ => pure true
                else pure false
              | _ => pure false
          else pure false
        pure (held.isSome || generic)
      | _ => pure false
    -- A value of a type the function is generic in, which may have a `drop`
    -- to run, used on one path and not on another: kept in a variable too,
    -- which destroys it where it was not used. (Of the program's own
    -- functions: the library is checked once for every program.)
    -- (Not a reference or a callable, which have nothing to destroy of
    -- their own; nor the library's, checked for every program alike.)
    let ownValue ← match ← find t with
      | .ref .. => pure false
      | .fn .. => pure false
      | _ => pure true
    let library := libraryOwner s.owner
    -- (Not of a type parameter said to be copied, `E: Use<[0, *]>`, which
    -- has nothing to destroy.)
    -- (Nor of a type said to be used any number of times, `impl Use<[0, *]>
    -- for Ptr<T>`, a handle: copied, it has nothing of its own to destroy.)
    let copied ← match ← find t with
      | .rigid r =>
        let named := match r with
          | .param p _ => s.copyParams.contains p
          | .cond .. => false
        pure (named || (← usedAnyNumber r.spelled))
      | .con n [] => pure (n.startsWith "'" && s.copyParams.contains (((n.drop 1).takeWhile (· != '@')).toString) || (← usedAnyNumber n))
      | .con n _ => usedAnyNumber n
      | _ => pure false
    if free && !heldDrop && hasParam t && ownValue && s.ownItems && !library && !copied
        && (← tyMustUse roots [] t).isNone then
      unless s.flagged.contains (s.owner, pos) || usesStmts b resumptive x body == 0 || usedFirst b quiet x body do
        if (← pathUses { ctx with handed := true, capturesOwned := true } names x b body) == some 0 then
          let place := ((pos.splitOn ":").take 2).filterMap String.toNat?
          let (line, col) := match place with
            | [line, col] => (line, col)
            | _ => (0, 0)
          if ← flagPlace s.owner line col x whole pos b body then continue
          throwThe Elab.Said { msg := s!"{pos}`{x}` is used on one path and not on another, and its type may have a `drop` to run: where it is not used nothing would run it. Use it on every path, let it go there with a function that takes it, or keep it in a variable (`let mut {x}`), which is destroyed where it was not used" }
    unless (free && !heldDrop) || (← tyMustUse roots [] t).isSome do
      -- A value with a `drop` to run that is used on one path and not on
      -- another: where it is not, nothing would run its `drop`, since the
      -- paths are callables and it is theirs. (One no path uses stays in
      -- its variable, and is destroyed there.)
      modify fun st => { st with seen := {} }
      -- (A callable that holds a value of a type the function is generic in
      -- is asked the same, of that value.)
      let named ← tyHasDrop [] t
      let named := if named.isNone && heldDrop then some "%generic" else named
      if let some name := named then
        -- (A variable that gives its value away asks, when its block ends,
        -- whether it did: it may on some paths and not on others.)
        unless s.flagged.contains (s.owner, pos) || usesStmts b resumptive x body == 0
            || (!heldDrop && usedFirst b quiet x body) do
          -- (A callable is counted as what has to be used is: handed to a
          -- function, it is used only if that function uses it, since one
          -- that lets it go does not destroy it.)
          let count ← if heldDrop then pathUses { ctx with capturesOwned := true } names x b body
            else pathUses { ctx with handed := true, capturesOwned := true } names x b body
          if count == some 0 then
            if heldDrop && name == "%generic" then
              throw s!"{pos}`{x}` holds a value of a type the function is generic in, which may have a `drop` to run, and is not used on every path (a function it is given uses it only if it calls it or hands it on): where it is not used nothing would run the `drop`. Use it on every path, or give it up there with `cancel({x})`, which destroys what it holds"
            if heldDrop then
              throw s!"{pos}`{x}` holds a `{name}`, which has a `drop` to run, and is not used on every path (a function it is given uses it only if it calls it or hands it on): where it is not used nothing would run the `drop`. Use it on every path, or give it up there with `cancel({x})`, which destroys what it holds"
            -- (Said with which `let` it is: the program is read again with
            -- the value kept in a variable, which destroys it where no path
            -- used it.)
            let place := ((pos.splitOn ":").take 2).filterMap String.toNat?
            let owner := (← get).owner
            -- (No place: a parameter.)
            let (line, col) := match place with
              | [line, col] => (line, col)
              | _ => (0, 0)
            -- (One whose part with something to destroy is taken, `eat(p.a)`,
            -- has its flag set there too, `Elab.takenSite`.)
            if ← flagPlace owner line col x whole pos b body then continue
            throwThe Elab.Said { msg := s!"{pos}`{x}` is used on one path and not on another, and a `{name}` has a `drop` to run: where it is not used nothing would run it. Use it on every path, let it go there with a function that takes it, or keep it in a variable (`let mut {x}`), which is destroyed where it was not used" }
      continue
    -- (A value whose type has nothing to destroy, its type parameters each
    -- said to be copied, `A: Use<[0, *]>`: let go on a path that does not
    -- use it, nothing is lost.)
    if hasParam t then
      let params := paramNames t
      if !params.isEmpty && params.all (fun n => s.copyParams.contains (((n.drop 1).takeWhile (· != '@')).toString)) then
        modify fun st => { st with seen := {} }
        if (← tyHasDrop [] t).isNone && (← tyMustUse roots [] t).isNone then continue
    let mut unused := false
    if usesStmts b resumptive x body == 0 then unused := true
    else if usedFirst b quiet x body then unused := false
    else
      let counted := fun (c : ACtx) => (do
        match ← pathUses c names x b body with
        | some n => pure (n == 0)
        | none => pure true : M Bool)
      unused ← counted ctx
      -- Used on every path if the callables the function was given come
      -- back: then that is asked of whoever gives them.
      if unused && !conditional.isEmpty then
        unless ← counted { ctx with sure := conditional.foldl (fun set c => set.insert c.1) sure } do
          unused := false
          relied := true
    if unused then
      modify fun st => { st with pos := pos }
      mustDrop t s!"`{x}` is not used on every path"
  modify fun st => { st with drops := st.drops ++ earlier }
  -- Blocks of which one certainly runs: each has to hold what has to be used.
  modify fun st => { st with envHeld := #[] }
  for (pos, callee, caps) in s.envHeld do
    let mut held : List (List String) := []
    for cap in caps do
      let root ← findCap cap
      let mut names : List String := []
      for ((_, (src, what)), (_, name)) in s.capEdges.entries.zip s.capEdgeNames.entries do
        if (← findCap src) == root then
          if let .ty t := what then
            modify fun st => { st with seen := {} }
            if (← tyMustUse roots [] t).isSome then
              names := ((name.map (·.1)).getD "%unnamed") :: names
      held := held ++ [names]
    for names in held do
      for x in names do
        unless x != "%unnamed" && held.all (·.contains x) do
          let what := if x == "%unnamed" then "a value" else s!"`{x}`"
          throw s!"{pos}{what} has to be used, and one of the blocks given to `{callee}` holds it but not every one: only one of them runs"
  -- Callables that run in one environment, given whole: calling one uses it
  -- up. Each is taken to use the environment when called, and the uses are
  -- counted along every path, as for any value used once.
  for (env, members, must, names, b, body) in s.envGroups do
    let listed := ", ".intercalate (members.map fun (x, _) => s!"`{x}`")
    let known := members.map fun (x, arity) =>
      (x, usesEnv arity)
    let outer := names.filter fun n => !members.any (·.1 == n)
    match ← pathUses { ctx with lower := false } outer "%env" b body known with
    | some n =>
      if n ≥ 2 then
        throw s!"{listed} run in the environment `{env}`, which is used up by the first that is called: on some path more than one call is made"
    | none =>
      throw s!"{listed} run in the environment `{env}`, which is used up by the first that is called: it could not be shown that no path calls more than one"
    if must then
      match ← pathUses ctx outer "%env" b body known with
      | some n =>
        if n == 0 then
          throw s!"the environment `{env}` has to be used: on some path none of {listed} is called"
      | none =>
        throw s!"the environment `{env}` has to be used: it could not be shown that every path calls one of {listed}"
  -- An environment that is there only once a callable has run: nothing runs in
  -- it before. A path is followed up to the first call that leaves the
  -- environment, and no call of one that runs in it may be on it.
  for (env, producers, members, names, b, body) in s.envAfter do
    let known :=
      (producers.map fun (x, arity) =>
        let left := Flat.ofClauses [.mk (List.replicate arity Pattern.wild) [.expr (.name none "%left")]]
        (x, AVal.clo left left.roots [("%left", AVal.gone "%after")]))
      ++ members.map fun (x, arity) => (x, usesEnv arity)
    let outer := names.filter fun n => !known.any (·.1 == n)
    let listed := fun (xs : List (String × Nat)) => ", ".intercalate (xs.map fun (x, _) => s!"`{x}`")
    match ← pathUses { ctx with lower := false } outer "%env" b body known with
    | some 0 => pure ()
    | _ =>
      throw s!"{listed members} runs in the environment `{env}`, which is there only once {listed producers} has run: on some path it is called first"
  -- An environment given to one callable and lent to others: once it is given
  -- it is used up, so none it is lent to is called after. A path is followed
  -- up to each call of one it is lent to, and no call of one it is given to
  -- may be on it.
  for (env, owners, borrowers, names, b, body) in s.envLent do
    let known :=
      (owners.map fun (x, arity) => (x, usesEnv arity))
      ++ borrowers.map fun (x, _) => (x, AVal.probe)
    let outer := names.filter fun n => !known.any (·.1 == n)
    let listed := fun (xs : List (String × Nat)) => ", ".intercalate (xs.map fun (x, _) => s!"`{x}`")
    match ← usesBeforeProbe ctx outer "%env" b body known with
    | some 0 => pure ()
    | some _ =>
      throw s!"{listed borrowers} runs in the environment `{env}` lent to it, and {listed owners} is given `{env}` and uses it up: on some path {listed borrowers} is called after {listed owners}"
    | none =>
      throw s!"{listed borrowers} runs in the environment `{env}` lent to it, and {listed owners} is given `{env}` and uses it up: it could not be shown that {listed borrowers} is never called after {listed owners}"
  if relied then
    for (_, callee) in conditional do
      modify fun st => { st with stays := st.stays.push (callee,
        "a value that has to be used is held while a callable the function was given is called") }
  -- A block given a block that was not run. If only one block of the program
  -- so far can be that one, the second runs in its place: what the first held
  -- under a name the second also mentions is the second's to use, and is held
  -- once, by the first; the rest of what the first held is let go. Otherwise
  -- all of it is.
  modify fun st => { st with unrunGiven := #[] }
  for (id, cap, input, mentioned, why, own) in s.unrunGiven do
    let root ← findCap cap
    let mut owners : List (Nat × Nat) := []
    for (owner, c) in s.blockCaps do
      if owner != id && owner != 0 && s.envBlocks.contains owner && (← findCap c) == root && !owners.any (·.1 == owner) then
        owners := (owner, c) :: owners
    match owners with
    | [(owner, c)] =>
      let mut theirs : List (String × Nat) := []
      for (i, what, name) in ← edgesOfSource c do
        do
          if let .ty held := what then
            if let some n := name then theirs := n :: theirs
            -- (What a variable would have given a block that was not run
            -- is still the variable's: whether it is used on this path is
            -- seen where the variable's uses are counted.)
            let covered := s.givenEdges.contains i || match name with
              | some n => mentioned.contains n
              | none => false
            unless covered do
              modify fun st => { st with drops := st.drops.push (held,
                why ++ ", and the block it is given was not run and holds a value this one does not mention") }
      for (i, what, name) in ← edgesOfSource own do
        do
          if let .ty _ := what then
            if let some n := name then
              if theirs.contains n then
                modify fun st => { st with sharedEdges := st.sharedEdges.insert i }
      modify fun st => { st with assumedLinks := st.assumedLinks.push (id, owner, input, why) }
    | _ => modify fun st => { st with drops := st.drops.push (input, why) }

/-- Can this pattern fail to match? Decided from its shape alone. -/
partial def irrefutable : Pattern → M Bool
  | .wild => pure true
  | .int _ | .ctor _ _ _ | .marked _ _ => pure false
  | .tuple ps => ps.allM irrefutable
  | .var x => do
    if (← resolveCtor x none).isSome then return false
    return ((← get).aliases[x]?).isNone

end Glorious.Check

namespace Glorious.Check

/-- The counts of uses of the function just read (`usesLater`), made of its
body as read, every adjustment in it: once each, after it is read. -/
def countUsesNow : M Unit := do
  let later := (← get).usesLater
  modify fun s => { s with usesLater := #[] }
  for u in later do
    let b := (← get).body
    match u.kind with
    | .plain => checkUses b u.pos u.outer u.binds u.body
    | .lessParts x =>
      let (lb, less) := Syntax.Flat.lessPartsStmts b x u.body
      checkUses lb u.pos u.outer u.binds less
    | .clause c site =>
      let cs := Elab.firstOf (← get).coercions.toList
      if cs.isEmpty then checkUses b u.pos u.outer u.binds u.body
      else
        let (c, coerced) := (Elab.coerceClause cs (site.bind (cs[·]?)) c).run b
        checkUses coerced u.pos u.outer u.binds (coerced.clause c).body.toList

end Glorious.Check
