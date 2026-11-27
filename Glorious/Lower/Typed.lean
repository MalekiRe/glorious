module

public import Glorious.Lower.Layout
public import Glorious.Trace

/-!
# The typed lowering

A program whose types (`Typer`) type it, with each cell made a cell of
memory and each memory operation one of an address, of the layout of the
type the reference is to (`Tm.cellL`, `MemOp.loadL` and the rest). Each
local's type is found from the hints, the signatures and the types' data and
operations.

A function is lowered at each of its signatures; until each is a copy of its
own, the lowerings must be the same, and a program whose are not, or that
reaches into something not yet bytes (an array's element, a field of a value
the machine holds), is not lowered.
-/

@[expose] public section

namespace Glorious.Lower

open Core

/-- Whether how a type is laid out has in it what nothing decided
(`anyName`): where it is laid out in place, not behind a reference, in what
the machine holds, or in a type parameter no field has. -/
partial def undecided (C : Types) : Ty → L Bool
  | .tuple fs => fs.anyM (undecided C)
  | .data name args => do
    if name == anyName then return true
    -- (A `[T; 0]`, a type parameter only named, is no bytes whatever `T` is.)
    if name == fixedName then
      return ← match args with
        | [t, .data len []] => if len != lenBase then undecided C t else pure false
        | _ => (args.take 1).anyM (undecided C)
    if ← holdsM C name args then return false
    match findData C.datas name args with
    | some ctors => ctors.anyM fun (_, fs) => fs.anyM (undecided C)
    | none => pure false
  | _ => pure false

/-- The types of the locals where the lowering is, oldest first: as the
checker's `TEnv`, an array, each found and each added at once. -/
abbrev Env := Array Ty
def aTy (Γ : Env) : Atom → Option Ty
  | .var i => Γ[i]?
  | .int _ => some .int
def asTy (Γ : Env) (as : List Atom) : Option (List Ty) := as.mapM (aTy Γ)

/-- What is there, or why not. -/
def need {α : Type} (o : Option α) (why : String) : L α :=
  match o with
  | some a => pure a
  | none => throw why

/-- The memory operation `op` of an address, laid out as what the reference
`args`' first is to; not if what it reaches into is not bytes. -/
def laidOp (C : Types) (Γ : Env) (op : MemOp) (args : List Atom) : L MemOp := do
  -- (Those by address are as they are.)
  if [.alloc, .free, .readBits, .writeBits, .copy, .sizeOf, .alignOf, .deref, .staticAt, .addressOf].contains op then return op
  let some (.ref σ) := args.head?.bind (aTy Γ) | throw "a memory operation not of a reference"
  -- (What nothing decided may be laid out otherwise where it is decided.)
  if ← undecided C σ then throw "a reference to what nothing decided the type of"
  let l := (← layOf C σ).lay
  match op with
  | .load => pure (.loadL l)
  | .store => pure (.storeL l)
  | .swap => pure (.swapL l)
  | .tag =>
    -- The constructor of something within: every step is to a field there.
    let rec steps : Lay → List Atom → Bool
      | _, [] | .held, _ => true
      | .fields _ fs, .int i :: rest => match fs[i.toNat]? with
        | some (_, l) => 0 ≤ i && steps l rest
        | none => false
      | .tagged cs, .int i :: rest => cs.all fun (_, fs) => match fs[i.toNat]? with
        | some (_, l) => 0 ≤ i && steps l rest
        | none => true
      | _, _ => false
    if steps l args.tail then pure (.tagL l) else throw "a constructor asked of a place not known"
  | .focus => pure (.focusL l)
  | _ => pure op

/-- Each function's uses as the lowering first writes them: at the `i`th
of `fn`'s signatures `base[fn] + i`, and at none of them `total + fn`; which
function each is comes once the signatures are split into kinds. -/
structure Uses where
  base : Array Nat
  total : Nat

/-- Whether a computation uses a function `p` says. -/
def _root_.Glorious.Core.Tm.anyFn (p : Nat → Bool) : Tm → Bool
  | .let_ (.closure fn _) b | .let_ (.rebind _ fn) b => p fn || b.anyFn p
  | .handle ret ops _ _ b => p ret || ops.any (p ·.2) || b.anyFn p
  | .handleTail ret ops _ _ => p ret || ops.any (p ·.2)
  | .let_ _ b | .call _ _ b | .perform _ _ b | .label _ b | .guard _ _ b | .cancel _ b
  | .cell _ _ b | .cellL _ _ _ b | .lend _ _ _ _ _ b | .mem _ _ b | .host _ _ b => b.anyFn p
  | _ => false

/-- Which of `fn`'s signatures a use of it is at: the first whose captures are
`Cs`, whose parameters begin with `Ps` and whose result is `ρ` (where
given). -/
def sigAt (C : Types) (fn : Nat) (Cs : List Ty) (Ps : List Ty) (ρ : Option Ty) : Option Nat :=
  (C.sigsOf fn).findIdx? fun e =>
    Cs == e.sig.caps && Ps == e.sig.params.take Ps.length && ρ.all (· == e.sig.ret)

/-- A use of a function as a function's lowering finds it: at the signature
its captures, parameters and result say (`sigAt`); or at none.
Which function that is, is worked out once every function is lowered
(`Ask.target`): a lowering asks, and is kept with what it asked
(`TypedKept`). -/
inductive Ask where
  | at (fn : Nat) (Cs Ps : List Ty) (ρ : Option Ty)
  | whole (fn : Nat)

def Ask.mapFn (f : Nat → Nat) : Ask → Ask
  | .at fn Cs Ps ρ => .at (f fn) Cs Ps ρ
  | .whole fn => .whole (f fn)

/-- The use as the lowering first writes it (`Uses`). -/
def Ask.target (C : Types) (U : Uses) : Ask → Nat
  | .at fn Cs Ps ρ =>
    match sigAt C fn Cs Ps ρ with
    | some i => U.base[fn]!+ i
    | none => U.total + fn
  | .whole fn => U.total + fn

/-- A function's lowering, with the uses it asked for, each named in it by
its place among them. -/
abbrev LT := StateT (Array Ask) L

def ask (a : Ask) : LT Nat := modifyGet fun as => (as.size, as.push a)

/-- The functions of a handler, each the one it is where it is lowered as more
than one: the one for a result at the thunk's result, each arm at its
operation's payload. -/
def handlerFns (C : Types) (Γ : Env) (ret : Nat) (ops : List (Nat × Nat))
    (captures : List Atom) (thunk : Atom) (ρ : Option Ty) (H : Row) :
    LT (Nat × List (Nat × Nat)) := do
  let Cs ← need (asTy Γ captures) "a handler's captures have no type"
  let σ := match aTy Γ thunk with
    | some (.fn _ σ ..) => [σ]
    | _ => []
  let ret ← ask (.at ret Cs σ ρ)
  let ops ← (ops.zip H).mapM fun ((op, arm), (_, targs)) => do
    let Ps := match findOp C.ops op targs with
      | some (Ps, _) => Ps
      | none => []
    pure (op, ← ask (.at arm Cs Ps ρ))
  pure (ret, ops)

/-- The computation lowered: `ε` the operations it may perform, the hints
the types have for it; each use of a function asked (`Ask`). -/
partial def lowerTm (C : Types) (ε : Row) : Env → Tm → List Hint → LT Tm
  | _, .ret a, _ => pure (.ret a)
  | Γ, .let_ rhs body, .ty σ :: hs => do
    let rhs ← match rhs, σ with
      | .closure fn captures, .fn Ps ρ .. => do
        let Cs ← need (asTy Γ captures) "a closure of what has no type"
        pure (.closure (← ask (.at fn Cs Ps (some ρ))) captures)
      -- (Made with what `a` was made with: its type says so.)
      | .rebind a fn, .fn Ps ρ _ _ (some Cs) => do pure (.rebind a (← ask (.at fn Cs Ps (some ρ))))
      | .rebind a fn, _ => do pure (.rebind a (← ask (.whole fn)))
      | _, _ => pure rhs
    pure (.let_ rhs (← lowerTm C ε (Γ.push σ) body hs))
  | _, .let_ _ _, _ => throw "a `let` without its type"
  | Γ, .call f args body, hs => do
    let some (.fn _ σ ..) := aTy Γ f | throw "a call of what is not callable"
    if σ == .never then
      let .ty σ' :: hs := hs | throw "a call that does not return without its type"
      pure (.call f args (← lowerTm C ε (Γ.push (σ')) body hs))
    else pure (.call f args (← lowerTm C ε (Γ.push σ) body hs))
  | _, .tail f args, _ => pure (.tail f args)
  | Γ, .handle ret ops captures thunk body, hs => do
    let .handler ρ H :: hs := hs | throw "a handler without its type"
    let (ret, ops) ← handlerFns C Γ ret ops captures thunk ρ H
    pure (.handle ret ops captures thunk (← lowerTm C ε (Γ.push (ρ)) body hs))
  | Γ, .handleTail ret ops captures thunk, hs => do
    let .handler _ H :: _ := hs | throw "a handler without its type"
    -- (What it yields is what the activation does: not known here.)
    let (ret, ops) ← handlerFns C Γ ret ops captures thunk none H
    pure (.handleTail ret ops captures thunk)
  | _, .raise op args, _ => pure (.raise op args)
  | Γ, .perform op args body, hs => do
    let targs ← need (ε.lookup op) "an operation performed where it may not be"
    let some (_, some σ) := findOp C.ops op targs | throw "an operation without its type"
    pure (.perform op args (← lowerTm C ε (Γ.push σ) body hs))
  | Γ, .label thunk body, hs => do
    let some (.fn _ σ ..) := aTy Γ thunk | throw "a label's scope not callable"
    pure (.label thunk (← lowerTm C ε (Γ.push σ) body hs))
  | _, .labelTail thunk, _ => pure (.labelTail thunk)
  | Γ, .guard cleanup thunk body, hs => do
    let some (.fn _ σ ..) := aTy Γ thunk | throw "a guard's scope not callable"
    pure (.guard cleanup thunk (← lowerTm C ε (Γ.push σ) body hs))
  | _, .guardTail cleanup thunk, _ => pure (.guardTail cleanup thunk)
  | Γ, .cancel k body, hs => do pure (.cancel k (← lowerTm C ε (Γ.push (.unit)) body hs))
  | Γ, .cell init thunk body, hs => do
    let σ ← need (aTy Γ init) "a cell of what has no type"
    let some (.fn _ ρ ..) := aTy Γ thunk | throw "a cell's scope not callable"
    pure (.cellL (← layOf C σ) init thunk (← lowerTm C ε (Γ.push (ρ)) body hs))
  | Γ, .cellTail init thunk, _ => do
    pure (.cellTailL (← layOf C (← need (aTy Γ init) "a cell of what has no type")) init thunk)
  | _, .cellL .., _ | _, .cellTailL .., _ => throw "lowered already"
  | Γ, .lend uniq r thunk pre post body, hs => do
    let some (.fn _ ρ ..) := aTy Γ thunk | throw "a borrow's scope not callable"
    pure (.lend uniq r thunk pre post (← lowerTm C ε (Γ.push (ρ)) body hs))
  -- (What a type takes, a number now.)
  | Γ, .mem op [a] body, hs =>
    if op == .sizeOf || op == .alignOf then do
      let some t := (match aTy Γ a with
        | some (.ref t) | some (.data _ (t :: _)) => some t
        | _ => none) | throw "the size of what is not a pointer's or a reference's"
      let l ← layOf C t
      pure (.let_ (.atom (.int (if op == .sizeOf then l.size else l.align)))
        (← lowerTm C ε (Γ.push (.scalar (-64))) body hs))
    else lowerMem C ε Γ op [a] body hs
  -- (A raw pointer's target, its address.)
  | Γ, .mem .deref [base, a, _] body, hs => do
    let some (.data _ (t :: _)) := aTy Γ base | throw "what a pointer of no type points to"
    pure (.let_ (.atom a) (← lowerTm C ε (Γ.push (.ref t)) body hs))
  | Γ, .mem op args body, hs => lowerMem C ε Γ op args body hs
  | Γ, .host id args body, hs => do
    match id, hs with
    | 0, hs => pure (.host id args (← lowerTm C ε (Γ.push (.unit)) body hs))
    | 1, hs => pure (.host id args (← lowerTm C ε (Γ.push (.tuple [.int, .int])) body hs))
    | _, .ty σ :: hs => pure (.host id args (← lowerTm C ε (Γ.push σ) body hs))
    | _, _ => throw "a host operation without its type"
where
  /-- A memory operation lowered: of the layout of what its reference is to. -/
  lowerMem (C : Types) (ε : Row) (Γ : Env) (op : MemOp) (args : List Atom) (body : Tm)
      (hs : List Hint) : LT Tm := do
    let σ ← match op, args.head?.bind (aTy Γ) with
      | .load, some (.ref σ) | .swap, some (.ref σ) => pure σ
      | .store, _ | .free, _ | .writeBits, _ | .copy, _ => pure .unit
      | .tag, _ | .readBits, _ => pure .int
      | .alloc, _ | .staticAt, _ => pure (.scalar (-64))
      | .addressOf, _ => match args with
        | [r, .int tag] => match aTy Γ r with
          | some (.ref σ) => do
            let ptr ← need (C.datas.find? fun d => d.ctors.any (·.1 == tag.toNat)) "a pointer type not known"
            pure (.data ptr.name [← need (fixedElem σ) "the address of what is not a `[T; N]`"])
          | _ => throw "the address of what is not a reference"
        | _ => throw "an address without its pointer's constructor"
      | .focus, some (.ref σ) =>
        match args with
        | [_, ix] => do
          let at_ := match ix with
            | .int (.ofNat i) => (placeTy C σ [i]).orElse fun _ => fixedElem σ
            | _ => if aTy Γ ix == some .int then fixedElem σ else none
          pure (.ref (← need at_ "a field not known"))
        | [_, _, .int (-1)] => do pure (.ref (← need (fixedElem σ) "a place in what is not a `[T; N]`"))
        | [_, .int (.ofNat i), .int (.ofNat built)] => do
          pure (.ref (← need ((ctorFieldsOf C built σ).bind (·[i]?)) "a field not known"))
        | _ => throw "a field not known"
      | _, _ => throw "a memory operation not of a reference"
    pure (.mem (← laidOp C Γ op args) args (← lowerTm C ε (Γ.push σ) body hs))

/-- A function's clauses lowered at a signature, with their hints there. -/
def lowerClauses (C : Types) (e : SigEntry) (cs : List Clause) : LT (List Clause) :=
  let sig := e.sig
  (cs.zip e.hints).mapM fun (c, hs) => do
    let Bs ← need (patsTys C c.pats sig.params) "patterns not of their types"
    pure { c with body := ← lowerTm C sig.eff (sig.params ++ sig.caps ++ Bs).toArray c.body hs }

/-- Which function each of a function's signatures is lowered as: itself, or a
copy of it (`ids`, by function and by the place of the signature in
`Types.sigsOf`). -/
structure Targets where
  ids : Array (Array Nat) := #[]

/-- Whether a function is lowered as more than one. -/
def Targets.several (T : Targets) (fn : Nat) : Bool :=
  match T.ids[fn]? with
  | some ids => ids.any (· != fn)
  | none => false

/-- The function a use of `fn` at its signature `i` is. -/
def Targets.at (T : Targets) (fn i : Nat) : Nat := ((T.ids[fn]?).bind (·[i]?)).getD fn

/-- What a function is at each of its signatures, for a split of them into
kinds (`kinds`, by function and signature): the functions each kind is, the
first itself and each other a copy of it, put after the program's. -/
def targetsOf (n : Nat) (kinds : Array (List Nat)) : Targets × List Nat := Id.run do
  let mut next := n
  let mut copies : List Nat := []
  let mut ids : Array (Array Nat) := #[]
  for (ks, fn) in kinds.toList.zipIdx do
    let mut of : Array Nat := #[]
    let mut row : Array Nat := #[]
    for k in ks do
      while of.size ≤ k do
        if of.isEmpty then of := of.push fn
        else
          of := of.push next
          copies := copies ++ [fn]
          next := next + 1
      row := row.push (of[k]?.getD fn)
    ids := ids.push row
  pure (⟨ids⟩, copies)

/-- A function lowered at a signature, kept for a later compile: its clauses,
each block of bytes in them by its bytes, and the uses it asked, each
function by `Program.sids`. -/
structure TypedKept where
  clauses : List Clause
  asks : Array Ask

/-- What each function's lowering at a signature made, by a key of what it
is made of, the signature and its hints, and the types'. -/
abbrev TypedMemo := Std.HashMap UInt64 TypedKept

/-- The program lowered, if its types type all of it; or why not. A
function is copied for each kind of layout its signatures need, each use of
it made of the copy for its signature; one with no signature is never
called, and stays as it is. What each copy is a copy of comes with it; and
what was lowered, for the next compile, which takes what `kept` has (none:
nothing is kept, and nothing keyed). -/
def lowered (C : Types) (p : Program) (kept : Option TypedMemo := none) : L (Program × List Nat × TypedMemo) := do
  let C := C.withIndex
  let sigs := (List.range p.fns.size).toArray.map C.sigsOf
  let base := sigs.foldl (fun (acc : Array Nat × Nat) es => (acc.1.push acc.2, acc.2 + es.length)) (#[], 0)
  let U : Uses := ⟨base.1, base.2⟩
  -- (Whose signature each use at one is.)
  let owner := (sigs.toList.zipIdx.flatMap fun (es, fn) => es.zipIdx.map fun (_, i) => (fn, i)).toArray
  -- (A function's lowering is kept by what it is made of as another
  -- compile knows it, `Program.keyed`, and what every one is lowered with:
  -- the declared types and operations the types use.)
  let sids := p.sids
  let bySid : Std.HashMap UInt64 Nat := sids.zipIdx.foldl (fun m (k, f) => m.insert k f) {}
  let staticAt : Std.HashMap Int Int := p.statics.zipIdx.foldl (fun m (bytes, i) =>
    m.insert (hash (some bytes)).toNat i) {}
  let statics := p.statics.toArray
  let bytesOf := fun (i : Int) => ((hash (statics[i.toNat]?)).toNat : Int)
  let global := hash (C.datas.foldl (fun h d => h + hash d) (0 : UInt64), C.ops.foldl (fun h o => h + hash o) (0 : UInt64))
  let mut lowers : Array (List (List Clause)) := #[]
  let mut made : TypedMemo := {}
  for ((F, es), fn) in (p.fns.toList.zip sigs.toList).zipIdx do
    let mut atSigs : Array (List Clause) := #[]
    -- (What it is made of, hashed once for all its signatures.)
    let madeOf := if es.isEmpty || kept.isNone then 0 else hash (F.clauses.map fun c => { c with body := p.keyed sids c.body })
    for e in es do
      let key := if kept.isNone then 0 else mixHash global (mixHash madeOf (hash (e.sig, e.hints)))
      let (cs, asks) ← match kept.bind (·[key]?) with
        | some k =>
          -- (Kept as it was, the same object: written again, it points into
          -- what was read.)
          made := made.insert key k
          pure (k.clauses.map (fun c => { c with body := c.body.mapStatics fun h => staticAt.getD h h }),
            k.asks.map (·.mapFn fun s => bySid.getD s.toUInt64 s))
        | none => do
          let (cs, asks) ← tryCatch ((lowerClauses C e F.clauses).run #[]) fun err => throw s!"{err} (in function {fn})"
          if kept.isSome then made := made.insert key ⟨cs.map (fun c => { c with body := c.body.mapStatics bytesOf }),
            asks.map (·.mapFn fun g => ((sids[g]?).getD (hash g)).toNat)⟩
          pure (cs, asks)
      atSigs := atSigs.push (cs.map fun c => { c with body := c.body.mapFns fun k => (asks[k]?).map (·.target C U) |>.getD k })
    lowers := lowers.push atSigs.toList
  let all := lowers.toList
  let (main, asks) ← (lowerTm C [] #[] p.main C.mainHints).run #[]
  let main := main.mapFns fun k => (asks[k]?).map (·.target C U) |>.getD k
  -- The signatures of a function split into kinds, one at first: a kind is
  -- split where its signatures are lowered otherwise, each use taken as of
  -- the kind its signature is, until none is.
  let width := sigs.foldl (fun m es => max m es.length) 0 + 1
  let rec settle (fuel : Nat) (kinds : Array (List Nat)) : L (Array (List Nat)) := do
    let kindOf := fun (u : Nat) => match owner[u]? with
      | some (fn, i) => fn * width + 1 + (((kinds[fn]?).bind (·[i]?)).getD 0)
      | none => (u - U.total) * width
    let kinds' := (kinds.toList.zip all).toArray.map fun (ks, ls) =>
      -- (One signature is one kind: nothing to tell apart.)
      if ls.length ≤ 1 then ks.map fun _ => 0 else
      let keys := ks.zip (ls.map (·.map fun c => { c with body := c.body.mapFns kindOf }))
      let firsts := keys.foldl (fun (acc : List (Nat × List Clause)) k =>
        if acc.contains k then acc else acc ++ [k]) []
      keys.map fun k => firsts.idxOf k
    match fuel with
    | 0 => throw "the functions' copies do not settle"
    | fuel + 1 => if kinds' == kinds then pure kinds else settle fuel kinds'
  let kinds ← settle 64 (sigs.map fun es => es.map fun _ => 0)
  let (T, copies) := targetsOf p.fns.size kinds
  -- (A use at none of its signatures, of a function lowered as more than one.)
  let unknown := fun (u : Nat) => U.total ≤ u && T.several (u - U.total)
  let used := main :: all.flatMap (·.flatMap (·.map (·.body)))
  if let some u := (used.findSome? fun t => if t.anyFn unknown then some t else none) then
    let fn := (List.range p.fns.size).find? (fun fn => u.anyFn (· == U.total + fn) && T.several fn)
    throw s!"a use of function {fn.getD 0} at none of its signatures"
  let resolve := fun (u : Nat) => match owner[u]? with
    | some (fn, i) => T.at fn i
    | none => u - U.total
  let all := (all.map (·.map (·.map fun c => { c with body := c.body.mapFns resolve }))).toArray
  -- Each function, and each copy, as its first signature of its kind is.
  let lowerOf := fun (id : Nat) (fn : Nat) =>
    match ((T.ids[fn]?).getD #[]).toList.idxOf? id with
    | some i => ((all[fn]?).bind (·[i]?)).getD ((p.fns[fn]?).map (·.clauses) |>.getD [])
    | none => (p.fns[fn]?).map (·.clauses) |>.getD []
  let fns := (p.fns.toList.zipIdx.map fun (F, fn) => { F with clauses := lowerOf fn fn })
    ++ (copies.zipIdx.map fun (fn, k) => ({ clauses := lowerOf (p.fns.size + k) fn } : Fn))
  -- How a closure of each is destroyed: by the copy of its destroyer at the
  -- signature that destroys one at its own.
  let drops := p.drops.flatMap fun (f, d) =>
    let es := (sigs[f]?).getD []
    let ids := (T.ids[f]?).getD #[]
    let ofF := (ids.toList.zip es).foldl (fun (acc : List (Nat × SigEntry)) (id, e) =>
      if acc.any (·.1 == id) then acc else acc ++ [(id, e)]) []
    if ofF.isEmpty then [(f, d)]
    else ofF.map fun (id, e) =>
      let j := ((sigs[d]?).getD []).findIdx? (·.sig == dropSig e.sig)
      (id, (j.map (T.at d)).getD d)
  let names := p.names ++ (copies.map fun fn => (p.names[fn]?).getD "").toArray
  pure ({ p with fns := fns.toArray, main := main.mapFns resolve, drops, names }, copies, made)

/-- The program lowered, if it can be (`lowered`). -/
def program (C : Types) (p : Program) (kept : Option TypedMemo := none) : Option (Program × List Nat × TypedMemo) :=
  match (lowered C p kept).run' {} with
  | .ok r => some r
  | .error e => if Trace.enabled then dbgTrace s!"not lowered: {e}" fun _ => none else none

end Glorious.Lower
