module

public import Glorious.Infer.Solve

public section

namespace Glorious.Infer

open Syntax
open Glorious.Typing (Ty FnSig Hint Cert SigEntry DataInst OpInst)

/-! ## Reading off the result -/

/-- How regions are written in the types of one function: its cells' regions by
number, and those bound by the callable types being written, innermost first. -/
structure Pr where
  vars : List (Nat × Typing.Rgn) := []
  bound : List Nat := []

/-- A finished region. One nothing determined, or that the function has no
number for, is a region no cell has. -/
def zonkRg (pr : Pr) (ρ : Nat) : M Typing.Rgn := do
  unless (← get).regions do return .cell 0
  let r ← findRg ρ
  let one := fun (r : Nat) =>
    match pr.bound.idxOf? r with
    | some i => Typing.Rgn.bound i
    | none => (pr.vars.lookup r).getD (.cell 0)
  if pr.bound.contains r || (pr.vars.lookup r).isSome then return one r
  -- (One of several places: each of them, in the order of the regions that
  -- stand for them, which a function's signature and the code using it
  -- write alike.)
  let mut places : List Typing.Rgn := []
  for l in (← leavesOf r).mergeSort (· ≤ ·) do
    let x := one l
    unless places.contains x do places := places ++ [x]
  match places with
  | x :: rest => pure (rest.foldl Typing.Rgn.or x)
  | [] => pure (one r)

/-- What a callable touches, in a fixed order, so that equal sets are equal
lists: a region no cell has, then cells from the oldest, then bound regions;
and after each region, leave to write it if the callable may. -/
def zonkAcc (pr : Pr) (a : Nat) : M (List Typing.Rgn) := do
  unless (← get).regions do return []
  let sorted := (← accSet a).mergeSort (· ≤ ·)
  let written ← accWrSet a
  let mut unknown := false
  let mut unknownWr := false
  let mut frees : List (Typing.Rgn × Bool) := []
  let mut bounds : List (Typing.Rgn × Bool) := []
  for r in sorted do
    let w := written.contains r
    -- (a region a callable type binds is no cell, and is written as bound)
    if !(← isAtom r) && !pr.bound.contains r && (pr.vars.lookup r).isNone then
      unknown := true
      unknownWr := unknownWr || w
    else
      match ← zonkRg pr r with
      | .bound i =>
        match bounds.find? (·.1 == .bound i) with
        | some _ => bounds := bounds.map fun (x, v) => if x == .bound i then (x, v || w) else (x, v)
        | none => bounds := bounds ++ [(.bound i, w)]
      | .cell _ =>
        unknown := true
        unknownWr := unknownWr || w
      | x =>
        match frees.find? (·.1 == x) with
        | some _ => frees := frees.map fun (y, v) => if y == x then (y, v || w) else (y, v)
        | none => frees := frees ++ [(x, w)]
  -- Bound regions in the order they are bound, whatever stands for them here.
  let index := fun (x : Typing.Rgn × Bool) => match x.1 with
    | .bound i => i
    | _ => 0
  let ordered := bounds.mergeSort fun a b => index a ≤ index b
  let all := (if unknown then [(Typing.Rgn.cell 0, unknownWr)] else []) ++ frees ++ ordered
  pure (all.flatMap fun (x, w) => if w then [x, .wr x] else [x])

mutual

/-- A finished type. A type nothing determined is unit; an open row is closed. -/
partial def zonk (pr : Pr) (t : ITy) : M Ty := do
  match ← find t with
  | .var id => do
    let s ← get
    pure (if s.numeric.contains id then .int else if s.anyUnknown then .data anyName [] else .tuple [])
  | .param _ => pure (if (← get).anyUnknown then .data anyName [] else .tuple [])
  | .int => pure .int
  | .scalar b => pure (.scalar b)
  | .tuple fs => do pure (.tuple (← fs.mapM (zonk pr)))
  | .data n args => do pure (.data n (← args.mapM (zonk pr)))
  | .fn ps r ops tail cls env acc => do
    let once := match ← findCls cls with
      | .lit b => b
      | .var _ => false
    -- The callable a cell's scope runs binds the cell's region; one given
    -- references to cells of the caller's choosing binds theirs.
    let binders ← bindersOf acc
    let pr := { pr with bound := binders ++ pr.bound }
    let env ← match ← find env with
      | .tuple stated => do pure (some (← stated.mapM (zonk pr)))
      | _ => pure none
    pure (.fn binders.length (← ps.mapM (zonk pr)) (← zonk pr r)
      (← zonkRow pr ⟨ops, tail⟩) once env (← zonkAcc pr acc))
  | .ref ρ t => do pure (.ref (← zonkRg pr ρ) (← zonk pr t))
  | .never => pure .never

partial def zonkOps (pr : Pr) (ops : IOps) : M Typing.Row :=
  ops.mapM fun (op, targs) => do pure (op, ← targs.mapM (zonk pr))

/-- A finished row, in a fixed order so that equal rows are equal lists. -/
partial def zonkRow (pr : Pr) (r : IRow) : M Typing.Row := do
  let r ← flattenRow r
  let ops ← zonkOps pr r.ops
  let once := ops.foldl (fun acc e => if acc.any (·.1 == e.1) then acc else acc ++ [e]) []
  pure (once.mergeSort fun a b => a.1 ≤ b.1)

end

/-- The cells' regions a type mentions, other than those its callable types bind. -/
partial def atomsOf (t : ITy) (out : List Nat) : M (List Nat) := do
  match ← find t with
  | .var _ | .param _ | .int | .scalar _ => pure out
  | .tuple fs | .data _ fs => fs.foldlM (fun o f => atomsOf f o) out
  | t@(.fn _ _ _ _ _ _ acc) => do
    let mut inner ← (← partsOf t).foldlM (fun o f => atomsOf f o) []
    for r in ← accSet acc do
      if ((← isAtom r) || (← isRank r)) && !inner.contains r then inner := r :: inner
    let binders ← bindersOf acc
    pure (inner.foldl (fun o r => if binders.contains r || o.contains r then o else r :: o) out)
  | .ref ρ t => do
    -- (a region an enclosing callable's type binds is, to what is inside it,
    -- a region like a cell's: one it has to be told; and one of several
    -- places is each of them)
    let mut out := out
    for r in ← leavesOf ρ do
      if ((← isAtom r) || (← isRank r)) && !out.contains r then out := r :: out
    atomsOf t out
  | .never => pure out

/-- How one function writes its regions: in its signature, where a cell scope's
function binds the cell's region, and in its body, where that region is the one
after those fixed when a closure of the function is made. -/
structure Numbering where
  sig : Pr := {}
  body : Pr := {}
  crgns : Nat := 0
  rgns : Nat := 0
  /-- The cells' regions of the signature, in the order they are numbered. -/
  atoms : List Nat := []

def numbering (s : ISig) : M Numbering := do
  unless (← get).regions do return {}
  let owns ← bindersOf s.acc
  let whole := ITy.fn (s.caps ++ s.params) s.ret s.row.ops s.row.tail (.lit false) .never s.acc
  let atoms := ((← atomsOf whole []).filter fun r => !owns.contains r).mergeSort (· ≤ ·)
  let vars := atoms.zipIdx.map fun (r, j) => (r, Typing.Rgn.var j)
  -- In the body the regions the signature binds come after those fixed when
  -- a closure is made, in the order the signature binds them.
  let bodyVars := owns.zipIdx.map fun (b, i) => (b, Typing.Rgn.var (atoms.length + i))
  pure { sig := { vars, bound := owns }, body := { vars := bodyVars ++ vars }
         crgns := atoms.length, rgns := owns.length, atoms }

/-- A finished signature, its regions numbered as `nb` says. -/
def zonkSigWith (nb : Numbering) (s : ISig) : M FnSig := do
  pure ⟨← s.caps.mapM (zonk nb.sig), ← s.params.mapM (zonk nb.sig), ← zonk nb.sig s.ret,
    ← zonkRow nb.sig s.row, nb.crgns, nb.rgns, ← zonkAcc nb.sig s.acc⟩

/-- A use of a function: the signature it is used at, and the cells its
numbered regions and the region it binds are at this use. -/
structure Use where
  sig : FnSig
  atoms : List Nat := []
  own : Option Nat := none
  /-- The further regions the signature binds. -/
  more : List Nat := []

/-- The signature a function is used at where regions are written as `pr`
says, and the regions that use gives the function. -/
def demand (pr : Pr) (s : ISig) : M (Use × List Typing.Rgn) := do
  let nb ← numbering s
  let owns ← bindersOf s.acc
  pure (⟨← zonkSigWith nb s, nb.atoms, owns.head?, owns.drop 1⟩, ← nb.atoms.mapM (zonkRg pr))

/-- The callable a cell's scope runs gives back, performs with or captured
something whose type mentions the cell's region. A reference that outlives its
cell does this; so does a callable that was given the type of another that
uses the cell, though it does not use the cell itself. -/
def escapes (sig : FnSig) : Bool :=
  sig.rgns == 1 && !(sig.caps.all Ty.lc && sig.ret.lc && Typing.Row.lc sig.eff)

/-- A cell that holds something whose type mentions the cell's own region: a
callable that uses the variable it is kept in, say. Nothing outlives anything,
but the region rules have no type for it. -/
def holdsItself (sig : FnSig) : Bool :=
  sig.rgns == 1 &&
    match sig.params with
    | [.ref _ σ] => !σ.lc
    | _ => false

def zonkHint (pr : Pr) : IHint → M (List Hint)
  | .ty t => do pure [.ty (← zonk pr t)]
  | .clo t sig => do
    if (← get).regions then
      let (use, θ) ← demand pr sig
      -- The checker would turn these away; saying so here names the reason.
      -- (Not of a callable that binds a region for whoever calls it: what it
      -- gives may be of that region.)
      let ranked ← match use.own with
        | some b => do pure !(← isAtom b)
        | none => pure false
      if !ranked && escapes use.sig then
        throw "region: something whose type mentions a mutable variable leaves the variable's block"
      if !ranked && holdsItself use.sig then
        throw "region: a mutable variable holds something that uses the variable itself"
      pure [.clo (← zonk pr t) θ]
    else pure [.ty (← zonk pr t)]
  | .handler ρ H Φ sigs => do
    pure [.handler (← zonk pr ρ) (← zonkOps pr H) (← zonkAcc pr Φ)
      (← sigs.mapM fun s => do pure (← demand pr s).2)]
  | .result r b => do
    if (← zonk pr r) == .never then pure [.ty (← zonk pr b)] else pure []
  | .rgns acc actuals => do
    let binders ← bindersOf acc
    if binders.isEmpty then pure []
    else
      -- A call that chose nothing for a region the callable's type binds is
      -- one made before the type was known to bind it: a function's call of
      -- itself, at the regions it was itself called at.
      let chosen ← (actuals.zip binders).mapM fun (actual, binder) => do
        let r ← findRg actual
        if pr.bound.contains r || (pr.vars.lookup r).isSome then zonkRg pr actual
        else zonkRg pr binder
      pure [.rgns chosen]

def zonkHints (pr : Pr) (hs : Array IHint) : M (List Hint) := do
  pure (← hs.toList.mapM (zonkHint pr)).flatten

/-- The regions of a signature being read back: one for each it numbers, and
one for the region it binds. -/
structure RgEnv where
  vars : Array Nat := #[]
  own : Option Nat := none
  /-- The regions bound by the callable types being read, innermost first. -/
  bound : List Nat := []

partial def ofRg (env : RgEnv) : Typing.Rgn → M Nat
  | .var i =>
    match env.vars[i]? with
    | some r => pure r
    | none => freshRg
  | .bound k =>
    match env.bound[k]? with
    | some r => pure r
    | none =>
      match env.own with
      | some r => pure r
      | none => freshRg
  | .cell _ | .lab _ | .loan _ | .wr _ => freshRg
  | .or a b => do
    -- (One of several places: a region of its own, used as each.)
    let x ← ofRg env a
    let y ← ofRg env b
    let u ← freshRg
    modify fun s => { s with lows := s.lows.insert u [x, y] }
    pure u

def ofAcc (env : RgEnv) (acc : List Typing.Rgn) : M Nat := do
  let a ← freshAcc
  for r in acc do
    match r with
    | .wr x => accWr a (← ofRg env x)
    | _ => accRgn a (← ofRg env r)
  pure a

partial def ofTy (env : RgEnv) : Ty → M ITy
  | .int => pure .int
  | .scalar b => pure (.scalar b)
  | .tuple fs => do pure (.tuple (← fs.mapM (ofTy env)))
  -- (What nothing decided, in the types for lowering: still to be decided.)
  | .data n [] => if n == anyName then freshTy else pure (.data n [])
  | .data n args => do pure (.data n (← args.mapM (ofTy env)))
  | .fn n ps r eff once stated acc => do
    -- A callable type that binds a region has a region of its own.
    let (env, binders) ← if n ≥ 1 && (← get).ranked then do
        let bs ← (List.range n).mapM fun _ => freshRg
        for b in bs do
          markRank b
        pure ({ env with bound := bs ++ env.bound }, bs)
      else pure (env, [])
    let ops ← eff.mapM fun (op, targs) => do pure (op, ← targs.mapM (ofTy env))
    let stated ← match stated with
      | some ts => do pure (ITy.tuple (← ts.mapM (ofTy env)))
      | none => pure .never
    let a ← ofAcc env acc
    unless binders.isEmpty do
      modify fun s =>
        { s with accVer := s.accVer + 1, accs := s.accs.modify a fun x =>
            { x with binder := binders.head?, more := binders.drop 1 } }
    pure (.fn (← ps.mapM (ofTy env)) (← ofTy env r) ops none (.lit once) stated a)
  | .ref ρ t => do pure (.ref (← ofRg env ρ) (← ofTy env t))
  | .never => pure .never

/-- The signature of a use as one to unify with: its numbered regions are the
cells they are at that use. -/
def ofSig (use : Use) : M ISig := do
  let sig := use.sig
  let env : RgEnv :=
    { vars := use.atoms.toArray, own := use.own, bound := use.own.toList ++ use.more }
  let acc ← ofAcc env sig.acc
  if (← get).regions then
    modify fun s =>
      { s with accVer := s.accVer + 1, accs := s.accs.modify acc fun x => { x with binder := use.own, more := use.more } }
  let ops ← sig.eff.mapM fun (op, targs) => do pure (op, ← targs.mapM (ofTy env))
  pure ⟨← sig.caps.mapM (ofTy env), ← sig.params.mapM (ofTy env), ← ofTy env sig.ret,
    ⟨ops, none⟩, acc⟩

partial def showRgn : Typing.Rgn → String
  | .var i => s!"r{i}"
  | .bound k => s!"b{k}"
  | .cell a => s!"cell{a}"
  | .lab id => s!"lab{id}"
  | .loan b => s!"loan{b}"
  | .wr r => s!"wr({showRgn r})"
  | .or a b => s!"({showRgn a}|{showRgn b})"

partial def showCoreTy : Typing.Ty → String
  | .int => "int"
  | .scalar b => s!"scalar{b}"
  | .tuple fs => "(" ++ ", ".intercalate (fs.map showCoreTy) ++ ")"
  | .data n args => s!"#{n}<" ++ ", ".intercalate (args.map showCoreTy) ++ ">"
  | .fn n ps r eff once env acc =>
    s!"fn[{n}](" ++ ", ".intercalate (ps.map showCoreTy) ++ ") -> " ++ showCoreTy r
      ++ (if eff.isEmpty then "" else " / {" ++ ", ".intercalate (eff.map fun (op, ts) =>
        s!"op{op}<" ++ ", ".intercalate (ts.map showCoreTy) ++ ">") ++ "}")
      ++ (if once then " once" else "")
      ++ (match env with
        | some cs => " env(" ++ ", ".intercalate (cs.map showCoreTy) ++ ")"
        | none => "")
      ++ " touches [" ++ ", ".intercalate (acc.map showRgn) ++ "]"
  | .ref ρ t => s!"&{showRgn ρ} {showCoreTy t}"
  | .never => "!"


def showSig (sig : FnSig) : String :=
  s!"caps ({", ".intercalate (sig.caps.map showCoreTy)}) params ({", ".intercalate (sig.params.map showCoreTy)}) -> {showCoreTy sig.ret}; fixed {sig.crgns}, bound {sig.rgns}; touches [{", ".intercalate (sig.acc.map showRgn)}]"

/-! ## Signatures at the types a program uses -/

/-- Give `fn` the signature of a use, and with it every function of its group
and everything they refer to, at the types that follow. -/
partial def instantiate (fn : Nat) (use : Use) : M Unit := do
  let sig := use.sig
  if ((← get).emitted[fn]?.getD []).contains sig then return
  let key ← fnKey fn
  -- (Kept from an earlier compile: what it gave is given again, with the
  -- regions of each use made anew, one for each it had.)
  let byKey := (← get).byKey
  let kept := (((← get).memo.get? key).getD []).find? (·.1 == sig)
  if let some (_, r) := kept then
    let entries := r.entries.filterMap fun (k, g, hs) => (byKey.get? k).map (·, g, hs)
    let wanted := r.wanted.filterMap fun (k, g, atoms, own, more) =>
      (byKey.get? k).map (·, g, atoms, own, more)
    if entries.length == r.entries.length && wanted.length == r.wanted.length then
      for (f, ground, hints) in entries do
        unless ((← get).emitted[f]?.getD []).contains ground do
          modify fun s =>
            { s with
              emitted := let old := s.emitted.getD f []; s.emitted.insert f (ground :: old)
              entries := s.entries.push ⟨f, ground, hints⟩ }
      modify fun s => { s with made := s.made.push (key, sig, r) }
      for (g, gsig, atoms, own, more) in wanted do
        let mut fresh : Std.HashMap Nat Nat := {}
        for a in atoms ++ own.toList ++ more do
          unless fresh.contains a do fresh := fresh.insert a (← freshAtom)
        let at_ := fun (a : Nat) => fresh.getD a a
        instantiate g ⟨gsig, atoms.map at_, own.map at_, more.map at_⟩
      return
  let sch ← schemeOf ((← get).scc[fn]?.getD fn)
  -- (What is put back afterwards is taken out, and not the whole state:
  -- held, every array of it would be copied where this first changes it.)
  let outer ← modifyGet fun s =>
    ((s.incls, s.places, s.coerces, s.nevers, s.onces, s.shows, s.opens, s.calls),
     { s with incls := #[], places := #[], coerces := #[], nevers := #[], onces := #[], shows := #[]
              opens := #[], calls := #[] })
  startCopy
  let members ← sch.members.mapM fun m => do
    pure { m with
      sig := ← renSig (copyRen sch) m.sig
      hints := ← m.hints.mapM fun hs => hs.mapM (renHint (copyRen sch))
      refs := ← m.refs.mapM fun (g, s) => do pure (g, ← renSig (copyRen sch) s) }
  let (incls, places, coerces, nevers, onces, shows, opens, calls) ←
    copyAsks sch sch.incls sch.places sch.coerces sch.nevers sch.onces sch.shows
  modify fun s =>
    { s with
      incls := incls, places := places, coerces := coerces, nevers := nevers, onces := onces
      shows := shows, opens := opens, calls := calls }
  let givenUpOpen ← sch.givenUpOpen.mapM fun (kt, amb, self) => do
    pure (← renTy (copyRen sch) kt, ← renRow (copyRen sch) amb, ← copyAcc sch self)
  match members.find? (·.fn == fn) with
  | none => throw s!"certificate: function {fn} is missing from its group"
  | some m =>
    let want ← ofSig use
    unifyList m.sig.caps want.caps
    unifyList m.sig.params want.params
    unify m.sig.ret want.ret
    unifyRow m.sig.row want.row
    unifyAcc m.sig.acc want.acc
  -- (A callable given up whose type the use fixes touches what it does.)
  for (kt, amb, self) in givenUpOpen do
    match ← find kt with
    | .var _ => pure ()
    | kt => if ← bindsNone kt then givenUp kt amb self
  settleAll
  let mut wanted : List (Nat × Use) := []
  let mut gave : List (UInt64 × FnSig × List (List Hint)) := []
  for m in members do
    let nb ← numbering m.sig
    let ground ← zonkSigWith nb m.sig
    -- (For the typed lowering, which reads no regions, it may be.)
    if m.fn == fn && ground != sig && !(← get).anyUnknown then
      throw s!"region: function {fn} cannot be used with the regions it is given: wanted {showSig sig}, found {showSig ground}"
    unless ((← get).emitted[m.fn]?.getD []).contains ground do
      let hints ← try m.hints.toList.mapM (zonkHints nb.body)
        catch e => throw s!"{e} (in function {m.fn})"
      gave := gave ++ [(← fnKey m.fn, ground, hints)]
      modify fun s =>
        { s with
          emitted := let old := s.emitted.getD m.fn []; s.emitted.insert m.fn (ground :: old)
          entries := s.entries.push ⟨m.fn, ground, hints⟩ }
      for (g, gs) in m.refs do
        wanted := wanted ++ [(g, (← demand nb.body gs).1)]
  let (incls, places, coerces, nevers, onces, shows, opens, calls) := outer
  modify fun s =>
    { s with incls, places, coerces, nevers, onces, shows, opens, calls }
  let wantedKeys ← wanted.mapM fun (g, u) => do pure (← fnKey g, u.sig, u.atoms, u.own, u.more)
  modify fun s => { s with made := s.made.push (key, sig, ⟨gave, wantedKeys⟩) }
  for (g, gs) in wanted do
    instantiate g gs

/-- Every use of a declared type inside a type. -/
partial def dataUses : Ty → List (Nat × List Ty)
  | .int | .scalar _ | .never => []
  | .tuple fs => fs.flatMap dataUses
  | .data n args => (n, args) :: args.flatMap dataUses
  | .fn _ ps r eff _ env _ =>
    ps.flatMap dataUses ++ dataUses r ++ (eff.flatMap fun (_, targs) => targs.flatMap dataUses)
      ++ (env.getD []).flatMap dataUses
  | .ref _ t => dataUses t

/-- Every use of an operation inside a type. -/
partial def opUses : Ty → List (Nat × List Ty)
  | .int | .scalar _ => []
  | .tuple fs | .data _ fs => fs.flatMap opUses
  | .fn _ ps r eff _ env _ =>
    ps.flatMap opUses ++ opUses r ++ eff ++ (eff.flatMap fun (_, targs) => targs.flatMap opUses)
      ++ (env.getD []).flatMap opUses
  | .ref _ t => opUses t
  | .never => []

def hintTypes : Hint → List Ty
  | .ty t | .clo t _ => [t]
  | .handler ρ H _ _ => ρ :: H.flatMap (·.2)
  | .rgns _ => []

def hintOps : Hint → List (Nat × List Ty)
  | .ty _ | .clo _ _ => []
  | .handler _ H _ _ => H
  | .rgns _ => []

def canonRg (r : Typing.Rgn) : StateM Nat Typing.Rgn :=
  match r with
  -- Leave to write a region comes right after the region.
  | .wr x => do if x.free then pure (.wr (.var ((← get) - 1))) else pure r
  | _ =>
    if r.free then do
      let k ← get
      set (k + 1)
      pure (.var k)
    else pure r

/-- A type with each of its regions made a variable of its own, numbered in the
order `Ty.frees` lists them: the form a declared type is recorded at, which
serves the type at whatever regions it is used. -/
partial def canonTy : Ty → StateM Nat Ty
  | .int => pure .int
  | .scalar b => pure (.scalar b)
  | .tuple fs => do pure (.tuple (← fs.mapM canonTy))
  | .data n args => do pure (.data n (← args.mapM canonTy))
  | .fn n ps r eff once env acc => do
    let ps ← ps.mapM canonTy
    let r ← canonTy r
    let eff ← eff.mapM fun (op, ts) => do pure (op, ← ts.mapM canonTy)
    let env ← match env with
      | some ts => some <$> ts.mapM canonTy
      | none => pure none
    let acc ← acc.mapM canonRg
    pure (.fn n ps r eff once env acc)
  | .ref ρ t => do
    let ρ ← canonRg ρ
    pure (.ref ρ (← canonTy t))
  | .never => pure .never

/-- Type arguments as a declaration is recorded at, as types to substitute, and
how the regions they were given are written. -/
def canonArgs (args : List Ty) : M (List ITy × Pr) := do
  if (← get).regions then
    let (cargs, n) := (args.mapM canonTy).run 0
    let mut vars : Array Nat := #[]
    for _ in [0:n] do
      vars := vars.push (← freshAtom)
    let iargs ← cargs.mapM (ofTy { vars })
    pure (iargs, { vars := vars.toList.zipIdx.map fun (r, k) => (r, Typing.Rgn.var k) })
  else pure (← args.mapM (ofTy {}), {})

deriving instance Hashable for Glorious.Typing.Rgn, Glorious.Typing.Ty

/-- The declarations behind every declared type and operation these types use,
and behind those the declarations use in turn. A use is recorded by the shape
of its type arguments. -/
partial def declsFor (types : List Ty) (opsTodo : List (Nat × List Ty)) (datas : Array DataInst := #[])
    (ops : Array OpInst := #[]) (seen : Std.HashSet (Nat × List Ty) := {})
    (seenOps : Std.HashSet (Nat × List Ty) := {}) : M (List DataInst × List OpInst) := do
  if datas.size + ops.size ≥ 4000 then
    throw "certificate: too many uses of declared types and operations"
  match opsTodo with
  | (op, args) :: rest =>
    let shape := args.map Ty.shape
    if seenOps.contains (op, shape) then declsFor types rest datas ops seen seenOps
    else
      let d ← opDecl op
      let (iargs, pr) ← canonArgs args
      let payload ← d.payload.mapM fun t => zonk pr (subst iargs t)
      let result ← match d.result with
        | some t => some <$> zonk pr (subst iargs t)
        | none => pure none
      declsFor (payload ++ result.toList ++ types) rest datas (ops.push ⟨op, shape, payload, result⟩) seen
        (seenOps.insert (op, shape))
  | [] =>
    match types with
    | [] => pure (datas.toList, ops.toList)
    | t :: rest =>
      let newData := (dataUses t).filter fun (name, args) =>
        !seen.contains (name, args.map Ty.shape)
      match newData with
      | [] => declsFor rest (opUses t) datas ops seen seenOps
      | (name, args) :: _ =>
        let tags := (← get).types[name]?.getD []
        let (iargs, pr) ← canonArgs args
        let mut ctors : List (Nat × List Ty) := []
        for tag in tags do
          let d ← ctorDecl tag
          let fields ← d.fields.mapM fun f => zonk pr (subst iargs f)
          ctors := ctors ++ [(tag, fields)]
        let shape := args.map Ty.shape
        declsFor (ctors.flatMap (·.2) ++ types) opsTodo
          (datas.push ⟨name, shape, ctors, true⟩) ops (seen.insert (name, shape)) seenOps

/-! ## Declarations -/

/-- Read a declared type. A bare unknown name, or `_`, is a field whose type is
inferred: one type for the whole program. -/
partial def resolveType (typeNames params : List String) (locals : List (String × Nat)) :
    TypeExpr → M ITy
  | .name x args => do
    -- A callable for every lifetime: here, the callable.
    if x == Syntax.rankedMark then
      match args.getLast? with
      | some inner =>
        -- Where callables are taken to bind regions, it binds one for each
        -- lifetime written.
        if (← get).regions && (← get).ranked then
          let names := args.dropLast.filterMap fun
            | .name l [] => some l
            | _ => none
          let bound ← names.mapM fun _ => freshRg
          for b in bound do
            markRank b
          let t ← resolveType typeNames params (names.zip bound ++ locals) inner
          if let .fn _ _ _ _ _ _ acc := t then
            let a ← findAcc acc
            modify fun s =>
              { s with accVer := s.accVer + 1, accs := s.accs.modify a fun x =>
                  { x with binder := bound.head?, more := bound.drop 1 } }
          return t
        else return ← resolveType typeNames params locals inner
      | none => return ← freshTy
    match params.idxOf? x with
    | some i => pure (.param i)
    | none =>
      -- A lifetime that is no parameter of the declaration: a region of its own.
      if x.startsWith "'" then pure (.ref (← freshRg) (.tuple []))
      else if x == "Int" then pure .int
      else if Syntax.isScalar x then pure (.scalar (Syntax.scalarBits x))
      else if x == "Fixed" && args.length == 2 then
        match args with
        | [t, n] => pure (.data fixedName [← resolveType typeNames params locals t,
            ← lengthTy (resolveType typeNames params locals) n])
        | _ => freshTy
      else
        match typeNames.idxOf? x with
        | some id => do
          let given ← args.mapM (resolveType typeNames params locals)
          -- A lifetime the type takes that is not written is one of its own.
          let lifetimes := (← get).typeLifetimes[id]?.getD []
          let mut missing := lifetimes.length - given.length
          let mut rest := given
          let mut out : Array ITy := #[]
          for isLifetime in lifetimes do
            if isLifetime && missing > 0 then
              out := out.push (.ref (← freshRg) (.tuple []))
              missing := missing - 1
            else
              match rest with
              | a :: more =>
                out := out.push a
                rest := more
              | [] => out := out.push (← freshTy)
          pure (.data id (out.toList ++ rest))
        | none => freshTy
  | .tuple args => do pure (.tuple (← args.mapM (resolveType typeNames params locals)))
  | .fn ps r => do
    let row ← freshRow
    pure (.func (← ps.mapM (resolveType typeNames params locals)) (← resolveType typeNames params locals r) row
      (← freshCls) (← freshTy) (← freshAcc))
  | .ref _ t life => do
    -- A reference for a lifetime the declaration takes points where that
    -- argument says.
    let region ← match life.bind (fun l => locals.lookup l) with
      | some r => pure r
      | none =>
        match life.bind params.idxOf? with
        | some j => pure (lifetimeBase + j)
        | none => freshRg
    pure (.ref region (← resolveType typeNames params locals t))
  | .never => freshTy
  | .hole => freshTy
  -- What a callable performs is found again for Core, not read.
  | .performs r _ => resolveType typeNames params locals r

def declare (items : List Item) (g : Elab.Globals) : M Unit := do
  let typeNames := items.filterMap fun
    | .enum name _ _ => some name
    | .struct name _ _ => some name
    | _ => none
  let effectNames := items.filterMap fun
    | .effect name _ _ => some name
    | _ => none
  let setAt {α : Type} (arr : Array (Option α)) (i : Nat) (x : α) : Array (Option α) :=
    (if arr.size ≤ i then arr ++ Array.replicate (i + 1 - arr.size) none else arr).set! i (some x)
  let lifetimesOf := fun (params : List String) => params.map (·.startsWith "'")
  let typeLifetimes := items.filterMap fun
    | .enum _ params _ => some (lifetimesOf params)
    | .struct _ params _ => some (lifetimesOf params)
    | _ => none
  modify fun s =>
    { s with types := Array.replicate typeNames.length [], typeLifetimes := typeLifetimes.toArray, typeNames }
  -- What each function says of its parameters.
  let mut declared : Std.HashMap Nat (List String × List (Option TypeExpr) × Option TypeExpr) := {}
  -- (A type parameter said to be a callable is a callable's type, which
  -- says nothing here.)
  let callables : Std.HashMap String (List String) := items.foldl (fun m item =>
    match item with
    | .bounds name bs => m.insert name (bs.filterMap fun b =>
        if ["Fn", "RunsIn", "Label"].contains b.trait then some b.subject else none)
    | _ => m) {}
  for item in items do
    if let .fn name ps annots ret _ := item then
      if let some f := g.fns[name]? then
        let said := callables.getD name []
        let unsaid := fun (a : Option TypeExpr) => match a with
          | some (.name x []) => if said.contains x then none else some (TypeExpr.name x [])
          | a => a
        let annots := annots.map unsaid
        let ret := unsaid ret
        if annots.any Option.isSome || ret.isSome then declared := declared.insert f (Syntax.genericParams ps, annots, ret)
  modify fun s => { s with declared }
  -- (A struct is a type of one constructor, of its name.)
  let ctor := fun (name : String) (params : List String) (c : String) (fields : List TypeExpr) => do
    let owner := (typeNames.idxOf? name).getD 0
    match g.ctors[c]? with
    | some info =>
      let fields ← fields.mapM (resolveType typeNames params [])
      modify fun s =>
        { s with
          ctors := setAt s.ctors info.tag ⟨owner, params.length, fields, lifetimesOf params⟩
          types := s.types.modify owner (· ++ [info.tag]) }
    | none => throw s!"constructor `{c}` was not collected"
  for item in items do
    match item with
    | .enum name params ctors => for (c, fields) in ctors do ctor name params c fields
    | .struct name params fields => ctor name params name fields
    | .effect name params ops =>
      let effect := (effectNames.idxOf? name).getD 0
      for op in ops do
        match g.ops.lookup op.name with
        | some info =>
          let payload ← op.payload.mapM (resolveType typeNames params [])
          let result ← if op.terminal then pure none
            else some <$> resolveType typeNames params [] (op.result.getD .hole)
          modify fun s =>
            { s with ops := setAt s.ops info.id ⟨effect, params.length, payload, result, lifetimesOf params⟩ }
        | none => throw s!"operation `{op.name}` was not collected"
    | _ => pure ()

end Glorious.Infer
