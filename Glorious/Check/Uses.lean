import Glorious.Check.Scopes

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
  /-- Those that are a resumption which has to be used. -/
  roots : List Nat := []
  /-- Those that are a resumption at all. What one mentions is the computation
  it suspended, not something it holds. -/
  resumptions : List Nat := []
  /-- Those of callables written in the program. -/
  blocks : List Nat := []
  /-- The types of what each captures. -/
  held : Array (Nat × Ty) := #[]
  /-- Of those, the ones that are a variable's value, which the variable
  destroys if the callable does not use it. -/
  flagged : Array (Nat × Ty) := #[]

def mustInfo : M MustInfo := do
  let s ← get
  let mut info : MustInfo := {}
  unless s.anyMust do return info
  for ((src, what), i) in s.capEdges.zipIdx do
    let root ← findCap src
    match what with
    | .must => unless info.roots.contains root do info := { info with roots := root :: info.roots }
    | .once =>
      unless info.resumptions.contains root do
        info := { info with resumptions := root :: info.resumptions }
    | .ty t =>
      unless s.sharedEdges.contains i do
        if s.givenEdges.contains i then info := { info with flagged := info.flagged.push (root, t) }
        else info := { info with held := info.held.push (root, t) }
    | _ => pure ()
  for (_, c) in s.blockCaps do
    let root ← findCap c
    unless info.blocks.contains root do info := { info with blocks := root :: info.blocks }
  pure info

/-- What in a type has to be used, if anything: said for the message. A
callable has to be called if it holds something that has to be used, or
something with a `drop` to run: nothing destroys what a callable holds, so
one that is let go without being called would take the value with it. -/
partial def tyMustUse (info : MustInfo) (visiting : List String) (t : Ty) :
    M (Option String) := do
  match ← find t with
  | .var _ => pure none
  | .tuple args => args.findSomeM? (tyMustUse info visiting)
  | .fn _ _ _ _ cap => do
    let root ← findCap cap
    if info.roots.contains root then
      return some "a resumption of an operation declared `[1, 1]`"
    if info.resumptions.contains root && !info.blocks.contains root then return none
    if (← get).seen.contains root then return none
    modify fun s => { s with seen := root :: s.seen }
    for (r, held) in info.held do
      if r == root then
        if let some what ← tyMustUse info visiting held then
          return some s!"a callable that holds {what}"
        if let some name ← tyHasDrop [] held then
          return some s!"a callable that holds a `{name}`, whose `drop` would then not run,"
    -- The value of a variable that gives it away: the variable's cleanup
    -- runs its `drop` where the callable did not use it, so only what has
    -- to be used makes the callable one that has to be called.
    for (r, held) in info.flagged do
      if r == root then
        if let some what ← tyMustUse info visiting held then
          return some s!"a callable that holds {what}"
    return none
  | .ref _ _ _ => pure none
  | .con name args => do
    if let some (must, _) := (← get).useDecls.lookup name then
      if must then return some s!"a `{bareName name}`"
    if let some w ← args.findSomeM? (tyMustUse info visiting) then return some w
    if visiting.contains name then return none
    match (← get).types.lookup name with
    | none => pure none
    | some decl =>
      decl.ctors.findSomeM? fun c => do
        match (← get).ctors.lookup c with
        | none => pure none
        | some sig =>
          (sig.fieldsAt args).findSomeM?
            (tyMustUse info (name :: visiting))

/-- Does a type mention a type parameter the function being checked wrote?
What such a type is, is known only where the function is used. -/
partial def hasParam : Ty → Bool
  | .con n [] => n.startsWith "'" && n.length > 1
  | .con _ args => args.any hasParam
  | .tuple args => args.any hasParam
  | .fn ps r _ _ _ => ps.any hasParam || hasParam r
  | .ref _ t _ => hasParam t
  | _ => false

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
  for (t, pos) in s.aparts do
    if let .con n _ ← find t then
      if s.kimpls.any (fun I => I.trait == "Drop" && I.head == n) then
        if let some here := s.modules.homes.lookup s.owner then
          let home := "::".intercalate ((n.splitOn "::").dropLast)
          unless here == home do
            throw s!"{pos}`{Syntax.lastSegment n}` has `Drop`, so only the module that declares it can take a field out of one: what `drop` does would not be done. Borrow the field, or ask the module for it"

def checkDrops (drops : Array (Ty × String)) : M Unit := do
  if drops.isEmpty then return
  let info ← mustInfo
  for (t, why) in drops do
    modify fun s => { s with seen := [] }
    if let some what ← tyMustUse info [] t then
      throw s!"{why}, but {what} has to be used"

def addUses (a b : Nat) : Nat := min 2 (a + b)

mutual

/-- How often an expression uses the binding `x`: 0, 1, or 2 for more.
`resumptive` says which operation names have arms that may run repeatedly. -/
partial def usesExpr (resumptive : String → Bool) (x : String) : Expr → Nat
  | .int _ => 0
  | .name q y => if q.isNone && y == x then 1 else 0
  | .label _ => 0
  | .call _ f args =>
    (args.map (usesExpr resumptive x)).foldl addUses (usesExpr resumptive x f)
  | .tailCall _ f args =>
    (args.map (usesExpr resumptive x)).foldl addUses (usesExpr resumptive x f)
  | .tuple args => (args.map (usesExpr resumptive x)).foldl addUses 0
  | .proj e _ => usesExpr resumptive x e
  | .closure _ clauses => (clauses.map (usesClause resumptive x)).foldl max 0
  | .handle subject arms =>
    let repeated := fun (arm : Clause) =>
      match arm with
      | .mk [.ctor name _ _] _ => resumptive name
      | _ => false
    let once := ((arms.filter (!repeated ·)).map (usesClause resumptive x)).foldl max 0
    let many := if (arms.filter repeated).any (usesClause resumptive x · > 0) then 2 else 0
    addUses (addUses (usesExpr resumptive x subject) once) many
  | .labelScope _ body => usesStmts resumptive x body
  | .ref _ _ => 0
  | .deref e => usesExpr resumptive x e
  | .reborrow _ e => usesExpr resumptive x e
  | .refField _ _ _ _ _ => 0
  | .fieldOf _ e _ => usesExpr resumptive x e

partial def usesClause (resumptive : String → Bool) (x : String) : Clause → Nat
  | .mk pats body =>
    if (pats.flatMap Elab.patVars).contains x then 0 else usesStmts resumptive x body

partial def usesStmts (resumptive : String → Bool) (x : String) : List Stmt → Nat
  | [] => 0
  | .expr e :: rest => addUses (usesExpr resumptive x e) (usesStmts resumptive x rest)
  | .let_ pat value :: rest =>
    addUses (usesExpr resumptive x value)
      (if (Elab.patVars pat).contains x then 0 else usesStmts resumptive x rest)
  | .letMut y value :: rest =>
    addUses (usesExpr resumptive x value) (if y == x then 0 else usesStmts resumptive x rest)
  | .assign target value :: rest =>
    let inTarget := match target with
      | .deref e => usesExpr resumptive x e
      | _ => 0
    addUses (addUses inTarget (usesExpr resumptive x value)) (usesStmts resumptive x rest)
  | .defer e :: rest => addUses (usesExpr resumptive x e) (usesStmts resumptive x rest)
  | .located _ _ s :: rest => usesStmts resumptive x (s :: rest)

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
  | clo (clauses : List Clause) (env : List (String × AVal))
  | fn (name : String)
  /-- No value: the path left for somewhere else, an operation's handler
  (named by the operation), a label's scope (`@name`), or somewhere unknown. -/
  | gone (target : String)
  /-- A callable that runs in an environment it is lent, or a value one may be
  in: calling it may be the call whose place on the path is asked about. -/
  | probe
  deriving Inhabited

structure ACtx where
  fns : List (String × List Clause)
  ctors : List String
  aliases : List (String × Expr)
  ops : List (String × Bool)
  /-- Count the fewest uses along any path instead of the most. Then a call
  that cannot be followed may also not come back, a callable that leaves the
  count may never be called, and a path that leaves ends with what it has. -/
  lower : Bool := false
  /-- Names whose calls only compute: they always come back. -/
  quiet : List String := []
  /-- The operations declared `[1, 1]`: whoever handles one resumes it, so
  performing it comes back. -/
  exact : List String := []
  /-- Count the binding as used where it is given to something, whatever
  that then does with it: whoever takes a value has it. -/
  handed : Bool := false
  /-- Calls, by identity, whose types say they come back. -/
  sure : List Nat := []
  /-- The count is of what comes before a call of a `probe`: a path ends at
  such a call, with the name below for where it left to, and a value one may
  be in cannot go where the count does not follow. -/
  probing : Bool := false
  /-- Where such a value goes is accounted for by whoever lets it go. -/
  lenient : Bool := false
  /-- The blocks that are run where they are written, by their numbers. -/
  now : List Nat := []
  /-- The functions being followed. One that calls itself is not followed
  again: what it is given goes where the count does not follow, which says
  of every later round what the first said. -/
  active : List String := []

/-- Where a path that ends at a call of a `probe` is said to leave to. -/
def probeTarget : String := "%probe"

def isGone : AVal → Bool
  | .gone _ => true
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

/-- A budget of steps; running out abandons the count. -/
abbrev A := StateT Nat Option

def tick : A Unit := do
  match ← get with
  | 0 => failure
  | n + 1 => set n

/-- The outcomes of a computation: its value and the uses so far, per path. -/
abbrev Alts := List (AVal × Nat)

partial def ACtx.ctorOf (ctx : ACtx) (name : String) : Option String :=
  if ctx.ctors.contains name then some name
  else
    match (ctx.aliases.lookup name).map Syntax.aliasValue with
    | some (.name _ y) => ctx.ctorOf y
    | _ => none

partial def constPat : Expr → Option Pattern
  | .int n => some (.int n)
  | .name q x => some (if q.isSome then .ctor x q [] else .var x)
  | .call _ (.name q x) args => do
    some (.ctor x q (← args.mapM constPat))
  | .tuple args => do
    some (.tuple (← args.mapM constPat))
  | _ => none

/-- The names a pattern binds, leaving out constructors and constants. -/
partial def binders (ctx : ACtx) : Pattern → List String
  | .wild => []
  | .int _ => []
  | .var x =>
    if (ctx.ctorOf x).isSome || (ctx.aliases.lookup x).isSome then [] else [x]
  | .ctor _ _ ps => ps.flatMap (binders ctx)
  | .tuple ps => ps.flatMap (binders ctx)

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
  | .int _, _ => (.maybe, [])
  | .var x, v =>
    match ctx.ctorOf x with
    | some c => fitData ctx c [] v
    | none =>
      match ctx.aliases.lookup x with
      | some e =>
        match constPat e with
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

/-- Can a use of the binding come of this value? -/
partial def holdsTracked : AVal → Bool
  | .tracked => true
  | .data _ args => args.any holdsTracked
  | .clo clauses env =>
    (clauses.flatMap (Elab.fvClause [])).eraseDups.any fun y =>
      match env.lookup y with
      | some v => holdsTracked v
      | none => false
  | _ => false

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

/-- May a call of a `probe` come of this value? -/
partial def holdsProbe : AVal → Bool
  | .probe => true
  | .data _ args => args.any holdsProbe
  | .clo clauses env =>
    (clauses.flatMap (Elab.fvClause [])).eraseDups.any fun y =>
      match env.lookup y with
      | some v => holdsProbe v
      | none => false
  | _ => false

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
  | .clo clauses env => do
    if ctx.probing && !ctx.lenient && holdsProbe (.clo clauses env) then failure
    let ctx := ctx.inside env
    -- For the fewest uses: a callable that mentions the binding has to be
    -- called, since the binding has to be used; one that does not, need not.
    if ctx.lower && !holdsTracked (.clo clauses env) then return 0
    tick
    let mut ns : List Nat := []
    for clause in clauses do
      match clause with
      | .mk pats body =>
        let params := (pats.flatMap (binders ctx)).map (·, AVal.unknown)
        let found ← runStmts ctx depth (params ++ env) body
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

partial def applyClauses (ctx : ACtx) (depth : Nat) (clauses : List Clause)
    (env : List (String × AVal)) (args : List AVal) : A Alts := do
  let mut out : Alts := []
  for clause in clauses do
    match clause with
    | .mk pats body =>
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
          let alts ← runStmts ctx depth (binds ++ env) body
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
  | .clo clauses env => applyClauses (ctx.inside env) depth clauses env args
  | .fn name =>
    match depth, ctx.fns.lookup name with
    | d + 1, some clauses =>
      if ctx.active.contains name then unfollowed ctx depth args
      else applyClauses { ctx with active := name :: ctx.active } d clauses [] args
    | _, _ => unfollowed ctx depth args
  | _ => unfollowed ctx depth args

/-- Evaluate expressions left to right, over every combination of paths. A
path that left on the way has only the value that says so. -/
partial def runList (ctx : ACtx) (depth : Nat) (env : List (String × AVal)) :
    List Expr → A (List (List AVal × Nat))
  | [] => pure [([], 0)]
  | e :: es => do
    let heads ← runExpr ctx depth env e
    let mut out : List (List AVal × Nat) := []
    for (v, n) in heads do
      if isGone v then out := ([v], n) :: out
    let on := heads.filter fun (v, _) => !isGone v
    unless on.isEmpty do
      let tails ← runList ctx depth env es
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

partial def runExpr (ctx : ACtx) (depth : Nat) (env : List (String × AVal)) : Expr → A Alts
  | .int _ => pure [(.unknown, 0)]
  | .name q x => do
    tick
    -- Naming the binding is not yet a use; calling it, taking it apart, or
    -- letting it go where the count cannot follow is.
    match (if q.isNone then env.lookup x else none) with
    | some v => pure [(v, 0)]
    | none =>
      if let some c := ctx.ctorOf x then pure [(.data c [], 0)]
      else if (ctx.ops.lookup x).isSome then pure [(.unknown, 0)]
      else if (ctx.fns.lookup x).isSome then pure [(.fn x, 0)]
      else
        match ctx.aliases.lookup x with
        | some e => runExpr ctx depth [] e
        | none => pure [(.unknown, 0)]
  | .label _ => pure [(.unknown, 0)]
  | .tuple es => do
    let alts ← runList ctx depth env es
    pure (alts.map fun (vs, n) =>
      match goneOf vs with
      | some t => (.gone t, n)
      | none => (.data "" vs, n))
  | .proj e idx => do
    let alts ← runExpr ctx depth env e
    pure (alts.map fun (v, n) =>
      match v with
      | .data _ args => (args.getD idx .unknown, n)
      | .tracked => (.unknown, n + 1)
      | .gone t => (.gone t, n)
      | .probe => (.probe, n)
      | _ => (.unknown, n))
  | .call id f args => runCall ctx depth env f args id
  | .tailCall id f args => runCall ctx depth env f args id
  | .closure id clauses =>
    if id != 0 && ctx.now.contains id then applyClauses ctx depth clauses env []
    else pure [(.clo clauses ((activeMark, .data activeMark (ctx.active.map AVal.fn)) :: env), 0)]
  | .handle subject arms => do
    let subject ← runExpr ctx depth env subject
    let mut completions : List Clause := []
    let mut repeated := 0
    let mut terminal : Alts := []
    let mut handled : List String := []
    for arm in arms do
      match arm with
      | .mk [.ctor name q ps] body =>
        match ctx.ops.lookup name with
        | some resumptive =>
          handled := name :: handled
          let params := (ps.flatMap (binders ctx)).map (·, AVal.unknown)
          let alts ← runStmts ctx depth (params ++ env) body
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
        | none => completions := completions ++ [.mk [.ctor name q ps] body]
      | other => completions := completions ++ [other]
    -- A path that left for an operation handled here goes on from here.
    let subject := subject.map fun (v, n) =>
      match v with
      | .gone t => if handled.contains t then (AVal.unknown, n) else (v, n)
      | _ => (v, n)
    let mut done : Alts := []
    for (v, n) in subject do
      if isGone v || completions.isEmpty then done := (v, n) :: done
      else
        let found ← applyClauses ctx depth completions env [v]
        for (v', n') in found do
          done := (v', n + n') :: done
    -- How much of the subject ran before an arm that does not resume is not
    -- known: for the fewest uses, none of it.
    let before := if ctx.lower then 0 else maxUses subject
    let all := done ++ terminal.map fun (v, n) => (v, n + before)
    cap ctx depth (all.map fun (v, n) => (v, n + repeated))
  | .labelScope l body => do
    let alts ← runStmts ctx depth env body
    if ctx.lower then
      -- A path that left for this label goes on from here.
      pure (alts.map fun (v, n) =>
        match v with
        | .gone t => if t == "@" ++ l then (AVal.unknown, n) else (v, n)
        | _ => (v, n))
    else
      -- Leaving through the label gives a value the count does not follow.
      pure (alts ++ [(.unknown, maxUses alts)])
  | .ref _ _ => pure [(.unknown, 0)]
  | .refField _ _ _ _ _ => pure [(.unknown, 0)]
  | .fieldOf _ e _ => do
    let alts ← runExpr ctx depth env e
    pure (alts.map fun (v, n) =>
      match v with
      | .tracked => (AVal.unknown, n + 1)
      | .gone t => (.gone t, n)
      | .probe => (.probe, n)
      | _ => (.unknown, n))
  -- Borrowing from a reference is no use of it.
  | .reborrow _ e => do
    let alts ← runExpr ctx depth env e
    pure (alts.map fun (v, n) => if isGone v then (v, n) else (AVal.unknown, n))
  | .deref e => do
    let alts ← runExpr ctx depth env e
    let (on, left) ← settle ctx depth alts
    pure ((match on with
      | some n => [(AVal.unknown, n)]
      | none => []) ++ left)

partial def runCall (ctx : ACtx) (depth : Nat) (env : List (String × AVal)) (f : Expr)
    (args : List Expr) (id : Nat) : A Alts := do
  tick
  let sure := ctx.lower && ctx.sure.contains id
  let alts ← runCallee ctx depth env f args sure
  -- A call whose type says it comes back does, whatever was lost track of
  -- inside it.
  if sure then
    pure (alts.map fun (v, n) => if isGone v then (AVal.unknown, n) else (v, n))
  else pure alts

partial def runCallee (ctx : ACtx) (depth : Nat) (env : List (String × AVal)) (f : Expr)
    (args : List Expr) (sure : Bool) : A Alts := do
  let general : A Alts := do
    let mut out : Alts := []
    let found ← runExpr ctx depth env f
    for (fv, n) in found do
      if isGone fv then out := (fv, n) :: out
      else
        let found ← runList ctx depth env args
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
            else
              let found ← callValue ctx depth fv vs
              for (v, k) in found do
                out := (v, n + m + k) :: out
    cap ctx depth out
  -- The arguments go to something that is not followed; `after` says what
  -- becomes of the path once they have.
  let handedOn := fun (after : Nat → Alts) => (do
    let mut out : Alts := []
    let found ← runList ctx depth env args
    for (vs, n) in found do
      match goneOf vs with
      | some t => out := (.gone t, n) :: out
      | none =>
        let mut k := n
        for v in vs do
          k := k + (← escapes ctx depth v)
        out := out ++ after k
    cap ctx depth out : A Alts)
  match f with
  | .label l =>
    -- Applying a label leaves for its scope.
    if ctx.lower then handedOn fun n => [(.gone ("@" ++ l), n)] else general
  | .name q x =>
    -- A value written with its type is the value: nothing is called.
    if q.isNone && (x == Syntax.ascribeMark || x == Syntax.instMark || x == Syntax.moveMark) then
      match args with
      | value :: _ => runExpr ctx depth env value
      | [] => pure [(.unknown, 0)]
    else if q.isNone && (env.lookup x).isSome then general
    else if let some c := ctx.ctorOf x then
      let alts ← runList ctx depth env args
      pure (alts.map fun (vs, n) =>
        match goneOf vs with
        | some t => (.gone t, n)
        | none => (.data c vs, n))
    else if x == "arr_len" && (ctx.fns.lookup x).isNone then
      -- Asking how long an array is only looks at it: the array is still
      -- whoever's it was.
      let found ← runList ctx depth env args
      pure (found.map fun (vs, n) =>
        match goneOf vs with
        | some t => (.gone t, n)
        | none => (.unknown, n))
    else if let some resumptive := ctx.ops.lookup x then
      -- Performing an operation hands its payload to a handler.
      if ctx.lower then
        -- The handler need not resume: the path may end here. Unless the
        -- operation is declared `[1, 1]`: then it has to.
        if resumptive && ctx.exact.contains x then handedOn fun n => [(AVal.unknown, n)]
        else handedOn fun n => (if resumptive then [(AVal.unknown, n)] else []) ++ [(.gone x, n)]
      else
        let mut worst := 0
        let found ← runList ctx depth env args
        for (vs, n) in found do
          let found ← unfollowed ctx depth vs
          for (_, k) in found do
            worst := max worst (n + k)
        pure [(.unknown, worst)]
    else if ctx.lower && ctx.quiet.contains x && (ctx.fns.lookup x).isNone then
      handedOn fun n => [(.unknown, n)]
    else general
  | _ => general

partial def runStmts (ctx : ACtx) (depth : Nat) (env : List (String × AVal)) :
    List Stmt → A Alts
  | [] => pure [(.data "" [], 0)]
  | .located _ _ s :: rest => runStmts ctx depth env (s :: rest)
  | [.expr e] => runExpr ctx depth env e
  | .expr e :: rest => do
    -- The value is dropped, so the rest does not depend on which path was taken.
    let (on, left) ← settle ctx depth (← runExpr ctx depth env e) (leaves := false)
    match on with
    | none => pure left
    | some first =>
      let alts ← runStmts ctx depth env rest
      pure ((alts.map fun (v, n) => (v, n + first)) ++ left)
  | .let_ pat value :: rest => do
    let mut out : Alts := []
    let found ← runExpr ctx depth env value
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
        let found ← runStmts ctx depth (binds ++ others ++ env) rest
        for (v', n') in found do
          out := (v', n + n' + taken) :: out
    cap ctx depth out
  | .letMut x value :: rest => do
    -- The value goes into a cell, where the count does not follow it.
    let (on, left) ← settle ctx depth (← runExpr ctx depth env value)
    match on with
    | none => pure left
    | some first =>
      let alts ← runStmts ctx depth ((x, .unknown) :: env) rest
      pure ((alts.map fun (v, n) => (v, n + first)) ++ left)
  | .assign target value :: rest => do
    let (on, left) ← settle ctx depth (← runExpr ctx depth env value)
    match on with
    | none => pure left
    | some first =>
      let (inTarget, left') ← match target with
        | .deref e => settle ctx depth (← runExpr ctx depth env e)
        | _ => pure (some 0, [])
      match inTarget with
      | none => pure (left ++ left'.map fun (v, n) => (v, n + first))
      | some inTarget =>
        let alts ← runStmts ctx depth env rest
        pure ((alts.map fun (v, n) => (v, n + first + inTarget)) ++ left
          ++ left'.map fun (v, n) => (v, n + first))
  | .defer e :: rest => do
    -- A cleanup runs however the rest is left.
    let mut ns : List Nat := []
    for (v, n) in ← runExpr ctx depth env e do
      ns := (n + (← escapes ctx depth v)) :: ns
    let first := ctx.fold ns
    let alts ← runStmts ctx depth env rest
    pure (alts.map fun (v, n) => (v, n + first))

end

/-- The most uses of `x` along any path through `body`, or with `ctx.lower` the
fewest, if the count finishes. `outer` are the other local names in scope,
about which nothing is known. -/
def pathUses (ctx : ACtx) (outer : List String) (x : String) (body : List Stmt)
    (known : List (String × AVal) := []) : Option Nat :=
  let env := known ++ (x, AVal.tracked) :: outer.map (·, AVal.unknown)
  let count : A Nat := do
    let mut ns : List Nat := []
    let found ← runStmts ctx 8 env body
    for (v, n) in found do
      -- What the body yields leaves the region being counted.
      ns := (n + (← escapes ctx 8 v)) :: ns
    pure (ctx.fold ns)
  (count.run 20000).map (·.1)

/-- The most uses of `x` on any path through `body` up to a call of one of the
`probes`, if the count finishes: none if no use comes before such a call. A
path that leaves the body with something a probe may be called through ends
there too, since the call may follow. -/
def usesBeforeProbe (ctx : ACtx) (outer : List String) (x : String) (body : List Stmt)
    (known : List (String × AVal)) : Option Nat :=
  let ctx := { ctx with lower := false, probing := true }
  let env := known ++ (x, AVal.tracked) :: outer.map (·, AVal.unknown)
  let count : A Nat := do
    let mut worst := 0
    for (v, n) in ← runStmts ctx 8 env body do
      match v with
      | .gone t => if t == probeTarget || t == "*" then worst := max worst n
      | _ =>
        if holdsProbe v then
          worst := max worst (n + (← escapes { ctx with lenient := true } 8 v))
    pure worst
  (count.run 20000).map (·.1)

/-- Does evaluating this run nothing at all? `quiet` names what only builds a
value. -/
partial def stillExpr (quiet : String → Bool) : Expr → Bool
  | .int _ => true
  | .name _ _ => true
  | .label _ => true
  | .closure _ _ => true
  | .ref _ _ => true
  | .tuple es => es.all (stillExpr quiet)
  | .call _ (.name _ f) args => quiet f && args.all (stillExpr quiet)
  | _ => false

def isName (x : String) : Expr → Bool
  | .name none y => y == x
  | _ => false

mutual

/-- Whether `x` is used by this expression before anything in it could fail to
come back: `some true` if so, `some false` if something that may not come back
runs first, `none` if neither happens. -/
partial def firstUse (quiet : String → Bool) (x : String) : Expr → Option Bool
  | .tuple es => firstParts quiet x true false es
  | .call _ f args =>
    firstParts quiet x (match f with
      | .name _ g => quiet g
      | _ => false) false (f :: args)
  | .tailCall _ f args =>
    firstParts quiet x (match f with
      | .name _ g => quiet g
      | _ => false) false (f :: args)
  | .proj e _ => if isName x e then some true else firstUse quiet x e
  | .deref e => if isName x e then none else firstUse quiet x e
  | .handle _ _ => some false
  | .labelScope _ _ => some false
  | _ => none

/-- The parts of a tuple or call, in order. `x` among them is handed on once
all are computed, so nothing after it may fail to come back. `builds` says the
whole only builds a value; otherwise it is a call that may not come back. -/
partial def firstParts (quiet : String → Bool) (x : String) (builds pending : Bool) :
    List Expr → Option Bool
  | [] => if pending then some true else if builds then none else some false
  | e :: rest =>
    if isName x e then firstParts quiet x builds true rest
    else if stillExpr quiet e then firstParts quiet x builds pending rest
    else
      match firstUse quiet x e with
      | some true => if pending then some false else some true
      | some false => some false
      | none => if pending then some false else firstParts quiet x builds pending rest

end

/-- Is `x` certainly used before anything in these statements could fail to
come back? Decided from their shape, in the order they are evaluated: a quick
yes that saves counting along paths. -/
partial def usedFirst (quiet : String → Bool) (x : String) : List Stmt → Bool
  | [] => false
  | .located _ _ s :: rest => usedFirst quiet x (s :: rest)
  | [.expr e] => isName x e || firstUse quiet x e == some true
  | .expr e :: rest =>
    match firstUse quiet x e with
    | some b => b
    | none => usedFirst quiet x rest
  | .let_ pat value :: rest =>
    if isName x value then true
    else
      match firstUse quiet x value with
      | some b => b
      | none => !(Elab.patVars pat).contains x && usedFirst quiet x rest
  | .letMut y value :: rest =>
    if isName x value then true
    else
      match firstUse quiet x value with
      | some b => b
      | none => y != x && usedFirst quiet x rest
  | .assign _ value :: rest =>
    if isName x value then true
    else
      match firstUse quiet x value with
      | some b => b
      | none => usedFirst quiet x rest
  | .defer _ :: rest => usedFirst quiet x rest

/-- Record, for each binding used more than once in `body`, that its type must
allow that. `outer` is the scope the bindings are added to. A binding whose
type is already known to allow it needs no count; one that fails the coarse
count is counted again along the paths the program can take. -/
def checkUses (pos : String) (outer : Scope) (binds : Scope) (body : List Stmt) : M Unit := do
  -- Report at the statement the bindings belong to, not the last one checked.
  modify fun st => { st with pos := pos }
  let s ← get
  let resumptive := fun (name : String) =>
    match s.ops.lookup name with
    | some sig => sig.result.isSome
    | none => false
  -- What only computes: the machine's own operations and what builds a value.
  let intrinsics := Elab.prims.map (·.1) ++ Elab.casts ++ Elab.hosts.map (·.1) ++ ["cancel", "replace", "swap", Syntax.foreignCall, Syntax.ctorIsMark, "%shapes", "%never"]
  let ctx : ACtx :=
    { fns := s.fnBodies, ctors := s.ctors.map (·.1), aliases := s.aliases,
      ops := s.ops.map fun (name, sig) => (name, sig.result.isSome), quiet := intrinsics,
      exact := s.ops.filterMap fun (name, sig) => if sig.must && sig.result.isSome then some name else none
      now := s.packs.toList.filterMap fun (id, names) =>
        if names == [Syntax.nowMark] then some id else none }
  let names := (binds ++ outer).map (·.1)
  for (x, b) in binds do
    let t := match b with
      | .val t _ => some t
      | .poly p => some p.ty
      | _ => none
    if let some t := t then
      let mentions := usesStmts resumptive x body
      if mentions ≥ 2 then
        let t ← zonk t
        modify fun st => { st with seen := [] }
        -- (A value with a `drop` to run is used where it is given away,
        -- whatever takes it does: giving it away twice would run it twice.)
        let dropped := (← tyHasDrop [] t).isSome
        let settled := (freeTys t).isEmpty && (freeCaps t).isEmpty && !hasParam t
          && !(← tyOwnsOnce [] t) && !dropped
        unless settled do
          match pathUses (if dropped then { ctx with handed := true } else ctx)
              (names.filter (· != x)) x body with
          | some n => if n ≥ 2 then mustDup t s!"`{x}` is used more than once"
          | none => mustDup t s!"`{x}` is used more than once"
      -- A value that has to be used: is it, however the body goes? Looked at
      -- once the function's types are known. A name the compiler made up
      -- stands for nothing the program wrote.
      if s.anyMust && !x.startsWith "%" then
        modify fun st =>
          { st with lowerChecks := st.lowerChecks.push (pos, x, t, names.filter (· != x), body) }

/-- Does a value of this type hold a callable that can jump to a label? -/
partial def tyJumps (t : Ty) : M Bool := do
  match ← find t with
  | .var _ => pure false
  | .con _ args => args.anyM tyJumps
  | .tuple args => args.anyM tyJumps
  | .ref _ inner _ => tyJumps inner
  | .fn ps r _ _ cap => do
    if ← ps.anyM tyJumps then return true
    if ← tyJumps r then return true
    let root ← findCap cap
    if (← get).seen.contains root then return false
    modify fun s => { s with seen := root :: s.seen }
    for (src, what) in (← get).capEdges do
      if (← findCap src) == root then
        match what with
        | .brand b => unless (← get).cells.any (·.1 == b) do return true
        | .ty t => if ← tyJumps t then return true
        | _ => pure ()
    return false

/-- A callable that has to come back when called may hold no label. -/
def checkStays (stays : Array (Ty × String)) : M Unit := do
  for (t, why) in stays do
    modify fun s => { s with seen := [] }
    if ← tyJumps t then
      throw s!"{why}, but what it is given here can jump to a label and not come back"

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
  for id in s.monoRows do
    sources := sources ++ (← zonkRow ⟨[], some id⟩).tail.toList
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
      modify fun st => { st with seen := [] }
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
        else sure := id :: sure
  modify fun st => { st with sure := sure }
  for (id, t, why) in s.abandoned do
    unless sure.contains id do
      modify fun st => { st with drops := st.drops.push (t, why) }
  let resumptive := fun (name : String) =>
    match s.ops.lookup name with
    | some sig => sig.result.isSome
    | none => false
  let intrinsics := Elab.prims.map (·.1) ++ Elab.casts ++ Elab.hosts.map (·.1) ++ ["cancel", "replace", "swap", Syntax.foreignCall, Syntax.ctorIsMark, "%shapes", "%never"]
  let ctx : ACtx :=
    { fns := s.fnBodies, ctors := s.ctors.map (·.1), aliases := s.aliases,
      ops := s.ops.map fun (name, sig) => (name, sig.result.isSome), quiet := intrinsics,
      exact := s.ops.filterMap fun (name, sig) => if sig.must && sig.result.isSome then some name else none,
      lower := true, sure := sure }
  let quiet := fun (f : String) =>
    (ctx.ctorOf f).isSome || (intrinsics.contains f && (ctx.fns.lookup f).isNone)
  let roots ← mustInfo
  -- What is found here is said first: it names the binding.
  let earlier := (← get).drops
  modify fun st => { st with drops := #[] }
  let mut relied := false
  -- Callables of which one is certainly called, sharing what they hold: that
  -- the others are then let go is no loss. Whoever gives them is asked that
  -- each holds what has to be used.
  let certain := (s.envGroups.toList.filter (·.2.2.1)).flatMap fun g => g.2.1.map (·.1)
  for (pos, x, t, names, body) in s.lowerChecks do
    if certain.contains x then continue
    let t ← zonk t
    -- Only a type that has to be used, or one not yet known, needs the count.
    let free := !(freeTys t).isEmpty || !(freeCaps t).isEmpty || hasParam t
    modify fun st => { st with seen := [] }
    unless free || (← tyMustUse roots [] t).isSome do
      -- A value with a `drop` to run that is used on one path and not on
      -- another: where it is not, nothing would run its `drop`, since the
      -- paths are callables and it is theirs. (One no path uses stays in
      -- its variable, and is destroyed there.)
      if let some name ← tyHasDrop [] t then
        -- (A variable that gives its value away asks, when its block ends,
        -- whether it did: it may on some paths and not on others.)
        unless s.flagged.contains pos || usesStmts resumptive x body == 0 || usedFirst quiet x body do
          if (pathUses { ctx with handed := true } names x body) == some 0 then
            throw s!"{pos}`{x}` is used on one path and not on another, and a `{name}` has a `drop` to run: where it is not used nothing would run it. Use it on every path, let it go there with a function that takes it, or keep it in a variable (`let mut {x}`), which is destroyed where it was not used"
      continue
    let mut unused := false
    if usesStmts resumptive x body == 0 then unused := true
    else if usedFirst quiet x body then unused := false
    else
      let counted := fun (c : ACtx) =>
        match pathUses c names x body with
        | some n => n == 0
        | none => true
      unused := counted ctx
      -- Used on every path if the callables the function was given come
      -- back: then that is asked of whoever gives them.
      if unused && !conditional.isEmpty then
        unless counted { ctx with sure := conditional.map (·.1) ++ sure } do
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
      for ((src, what), name) in s.capEdges.zip s.capEdgeNames do
        if (← findCap src) == root then
          if let .ty t := what then
            modify fun st => { st with seen := [] }
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
  for (env, members, must, names, body) in s.envGroups do
    let listed := ", ".intercalate (members.map fun (x, _) => s!"`{x}`")
    let known := members.map fun (x, arity) =>
      (x, AVal.clo [.mk (List.replicate arity Pattern.wild) [.expr (.proj (.name none "%env") 0)]]
        [("%env", AVal.tracked)])
    let outer := names.filter fun n => !members.any (·.1 == n)
    match pathUses { ctx with lower := false } outer "%env" body known with
    | some n =>
      if n ≥ 2 then
        throw s!"{listed} run in the environment `{env}`, which is used up by the first that is called: on some path more than one call is made"
    | none =>
      throw s!"{listed} run in the environment `{env}`, which is used up by the first that is called: it could not be shown that no path calls more than one"
    if must then
      match pathUses ctx outer "%env" body known with
      | some n =>
        if n == 0 then
          throw s!"the environment `{env}` has to be used: on some path none of {listed} is called"
      | none =>
        throw s!"the environment `{env}` has to be used: it could not be shown that every path calls one of {listed}"
  -- An environment that is there only once a callable has run: nothing runs in
  -- it before. A path is followed up to the first call that leaves the
  -- environment, and no call of one that runs in it may be on it.
  for (env, producers, members, names, body) in s.envAfter do
    let known :=
      (producers.map fun (x, arity) =>
        (x, AVal.clo [.mk (List.replicate arity Pattern.wild) [.expr (.name none "%left")]]
          [("%left", AVal.gone "%after")]))
      ++ members.map fun (x, arity) =>
        (x, AVal.clo [.mk (List.replicate arity Pattern.wild) [.expr (.proj (.name none "%env") 0)]]
          [("%env", AVal.tracked)])
    let outer := names.filter fun n => !known.any (·.1 == n)
    let listed := fun (xs : List (String × Nat)) => ", ".intercalate (xs.map fun (x, _) => s!"`{x}`")
    match pathUses { ctx with lower := false } outer "%env" body known with
    | some 0 => pure ()
    | _ =>
      throw s!"{listed members} runs in the environment `{env}`, which is there only once {listed producers} has run: on some path it is called first"
  -- An environment given to one callable and lent to others: once it is given
  -- it is used up, so none it is lent to is called after. A path is followed
  -- up to each call of one it is lent to, and no call of one it is given to
  -- may be on it.
  for (env, owners, borrowers, names, body) in s.envLent do
    let known :=
      (owners.map fun (x, arity) =>
        (x, AVal.clo [.mk (List.replicate arity Pattern.wild) [.expr (.proj (.name none "%env") 0)]]
          [("%env", AVal.tracked)]))
      ++ borrowers.map fun (x, _) => (x, AVal.probe)
    let outer := names.filter fun n => !known.any (·.1 == n)
    let listed := fun (xs : List (String × Nat)) => ", ".intercalate (xs.map fun (x, _) => s!"`{x}`")
    match usesBeforeProbe ctx outer "%env" body known with
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
      if owner != id && owner != 0 && (← findCap c) == root && !owners.any (·.1 == owner) then
        owners := (owner, c) :: owners
    match owners with
    | [(owner, c)] =>
      let mut theirs : List (String × Nat) := []
      for ((src, what), name) in s.capEdges.zip s.capEdgeNames do
        if src == c then
          if let .ty held := what then
            if let some n := name then theirs := n :: theirs
            let covered := match name with
              | some n => mentioned.contains n
              | none => false
            unless covered do
              modify fun st => { st with drops := st.drops.push (held,
                why ++ ", and the block it is given was not run and holds a value this one does not mention") }
      for (((src, what), name), i) in (s.capEdges.zip s.capEdgeNames).zipIdx do
        if src == own then
          if let .ty _ := what then
            if let some n := name then
              if theirs.contains n then
                modify fun st => { st with sharedEdges := i :: st.sharedEdges }
      modify fun st => { st with assumedLinks := st.assumedLinks.push (id, owner, input, why) }
    | _ => modify fun st => { st with drops := st.drops.push (input, why) }

/-- Can this pattern fail to match? Decided from its shape alone. -/
partial def irrefutable : Pattern → M Bool
  | .wild => pure true
  | .int _ => pure false
  | .tuple ps => ps.allM irrefutable
  | .var x => do
    if (← resolveCtor x none).isSome then return false
    return ((← get).aliases.lookup x).isNone
  | .ctor _ _ _ => pure false

end Glorious.Check
