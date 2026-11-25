module

public import Glorious.Lower.Layout

/-!
# The typed lowering

A program whose certificate types it, with each cell made a cell of memory
and each memory operation one of an address, of the layout of the type the
reference is to (`Tm.cellL`, `MemOp.loadL` and the rest). The types are
found as the checker finds them (`Typing.checkTm`): each local's from the
hints, the signatures and the certificate's data and operations.

A function is lowered at each of its signatures; until each is a copy of its
own, the lowerings must be the same, and a program whose are not, or that
reaches into something not yet bytes (an array's element, a field of a value
the machine holds), is not lowered.
-/

@[expose] public section

namespace Glorious.Lower

open Typing Core

/-- Whether how a type is laid out has in it what nothing decided
(`anyName`): where it is laid out in place, not behind a reference, in what
the machine holds, or in a type parameter no field has. -/
partial def undecided (C : Cert) : Ty → L Bool
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
def laidOp (C : Cert) (Γ : Env) (op : MemOp) (args : List Atom) : L MemOp := do
  -- (Those by address are as they are.)
  if [.alloc, .free, .readBits, .writeBits, .copy, .sizeOf, .alignOf, .deref, .staticAt, .addressOf].contains op then return op
  let some (.ref _ σ) := args.head?.bind (aTy Γ) | throw "a memory operation not of a reference"
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

/-- The functions a computation uses, each made `f` of itself. -/
def _root_.Glorious.Core.Tm.mapFns (f : Nat → Nat) : Tm → Tm
  | .let_ (.closure fn cs) b => .let_ (.closure (f fn) cs) (b.mapFns f)
  | .let_ (.rebind a fn) b => .let_ (.rebind a (f fn)) (b.mapFns f)
  | .let_ r b => .let_ r (b.mapFns f)
  | .handle ret ops cs t b => .handle (f ret) (ops.map fun (o, g) => (o, f g)) cs t (b.mapFns f)
  | .handleTail ret ops cs t => .handleTail (f ret) (ops.map fun (o, g) => (o, f g)) cs t
  | .call g as b => .call g as (b.mapFns f)
  | .perform o as b => .perform o as (b.mapFns f)
  | .label t b => .label t (b.mapFns f)
  | .guard c t b => .guard c t (b.mapFns f)
  | .cancel k b => .cancel k (b.mapFns f)
  | .cell i t b => .cell i t (b.mapFns f)
  | .cellL l i t b => .cellL l i t (b.mapFns f)
  | .lend u r t pre post b => .lend u r t pre post (b.mapFns f)
  | .mem op as b => .mem op as (b.mapFns f)
  | .host id as b => .host id as (b.mapFns f)
  | t => t

/-- Whether a computation uses a function `p` says. -/
def _root_.Glorious.Core.Tm.anyFn (p : Nat → Bool) : Tm → Bool
  | .let_ (.closure fn _) b | .let_ (.rebind _ fn) b => p fn || b.anyFn p
  | .handle ret ops _ _ b => p ret || ops.any (p ·.2) || b.anyFn p
  | .handleTail ret ops _ _ => p ret || ops.any (p ·.2)
  | .let_ _ b | .call _ _ b | .perform _ _ b | .label _ b | .guard _ _ b | .cancel _ b
  | .cell _ _ b | .cellL _ _ _ b | .lend _ _ _ _ _ b | .mem _ _ b | .host _ _ b => b.anyFn p
  | _ => false

/-- Which of `fn`'s signatures a use of it is at: the first whose captures are
`Cs`, whose parameters begin with `Ps` and whose result is `ρ` (where given),
made with the regions `θ`. -/
def sigAt (C : Cert) (fn : Nat) (θ : List Rgn) (Cs : List Ty) (Ps : List Ty) (ρ : Option Ty) : Option Nat :=
  (C.sigsOf fn).findIdx? fun e =>
    θ.length == e.sig.crgns && Cs == e.sig.caps.map (Ty.inst θ)
      && Ps == (e.sig.params.take Ps.length).map (Ty.inst θ) && ρ.all (· == e.sig.ret.inst θ)

/-- A use of `fn`, as the lowering first writes it (`Uses`). -/
def retarget (C : Cert) (U : Uses) (fn : Nat) (θ : List Rgn) (Cs Ps : List Ty) (ρ : Option Ty) : Nat :=
  match sigAt C fn θ Cs Ps ρ with
  | some i => U.base[fn]!+ i
  | none => U.total + fn

/-- The functions of a handler, each the one it is where it is lowered as more
than one: the one for a result at the thunk's result, each arm at its
operation's payload. -/
def handlerFns (C : Cert) (U : Uses) (Γ : Env) (ret : Nat) (ops : List (Nat × Nat))
    (captures : List Atom) (thunk : Atom) (ρ : Option Ty) (H : Row) (θs : List (List Rgn)) :
    L (Nat × List (Nat × Nat)) := do
  let Cs ← need (asTy Γ captures) "a handler's captures have no type"
  let σ := match aTy Γ thunk with
    | some (.fn _ _ σ ..) => [σ]
    | _ => []
  let ret := retarget C U ret (θs.headD []) Cs σ ρ
  let ops ← (ops.zip (H.zip (θs.drop 1))).mapM fun ((op, arm), ((_, targs), θ)) => do
    let Ps := match findOp C.ops op targs with
      | some (Ps, _) => Ps
      | none => []
    pure (op, retarget C U arm θ Cs Ps ρ)
  pure (ret, ops)

/-- The computation lowered: `ε` the operations it may perform, the hints
the certificate has for it; each use of a function lowered as more than one,
of the one it is (`T`). -/
partial def lowerTm (C : Cert) (U : Uses) (ε : Row) : Env → Tm → List Hint → L Tm
  | _, .ret a, _ => pure (.ret a)
  | Γ, .let_ rhs body, h :: hs => do
    let (σ, θ) ← need h.bind? "a `let` without its type"
    let rhs ← match rhs, σ with
      | .closure fn captures, .fn _ Ps ρ .. => do
        let Cs ← need (asTy Γ captures) "a closure of what has no type"
        pure (.closure (retarget C U fn θ Cs Ps (some ρ)) captures)
      | .rebind a fn, .fn _ Ps ρ .. =>
        match aTy Γ a with
        | some (.fn _ _ _ _ _ (some Cs) _) => do pure (.rebind a (retarget C U fn θ Cs Ps (some ρ)))
        | _ => pure (.rebind a (U.total + fn))
      | _, _ => pure rhs
    pure (.let_ rhs (← lowerTm C U ε (Γ.push σ) body hs))
  | _, .let_ _ _, [] => throw "a `let` without its type"
  | Γ, .call f args body, hs => do
    let some (.fn n _ σ ..) := aTy Γ f | throw "a call of what is not callable"
    let (rs, hs) ← need (takeRgns n hs) "a call without its regions"
    if σ = .never then
      let .ty σ' :: hs := hs | throw "a call that does not return without its type"
      pure (.call f args (← lowerTm C U ε (Γ.push (σ')) body hs))
    else pure (.call f args (← lowerTm C U ε (Γ.push (σ.open rs)) body hs))
  | _, .tail f args, _ => pure (.tail f args)
  | Γ, .handle ret ops captures thunk body, hs => do
    let .handler ρ H _ θs :: hs := hs | throw "a handler without its type"
    let (ret, ops) ← handlerFns C U Γ ret ops captures thunk ρ H θs
    pure (.handle ret ops captures thunk (← lowerTm C U ε (Γ.push (ρ)) body hs))
  | Γ, .handleTail ret ops captures thunk, hs => do
    let .handler _ H _ θs :: _ := hs | throw "a handler without its type"
    -- (What it yields is what the activation does: not known here.)
    let (ret, ops) ← handlerFns C U Γ ret ops captures thunk none H θs
    pure (.handleTail ret ops captures thunk)
  | _, .raise op args, _ => pure (.raise op args)
  | Γ, .perform op args body, hs => do
    let targs ← need (ε.lookup op) "an operation performed where it may not be"
    let some (_, some σ) := findOp C.ops op targs | throw "an operation without its type"
    pure (.perform op args (← lowerTm C U ε (Γ.push σ) body hs))
  | Γ, .label thunk body, hs => do
    let some (.fn _ _ σ ..) := aTy Γ thunk | throw "a label's scope not callable"
    pure (.label thunk (← lowerTm C U ε (Γ.push σ) body hs))
  | _, .labelTail thunk, _ => pure (.labelTail thunk)
  | Γ, .guard cleanup thunk body, hs => do
    let some (.fn _ _ σ ..) := aTy Γ thunk | throw "a guard's scope not callable"
    pure (.guard cleanup thunk (← lowerTm C U ε (Γ.push σ) body hs))
  | _, .guardTail cleanup thunk, _ => pure (.guardTail cleanup thunk)
  | Γ, .cancel k body, hs => do pure (.cancel k (← lowerTm C U ε (Γ.push (.unit)) body hs))
  | Γ, .cell init thunk body, hs => do
    let σ ← need (aTy Γ init) "a cell of what has no type"
    let some (.fn _ _ ρ ..) := aTy Γ thunk | throw "a cell's scope not callable"
    pure (.cellL (← layOf C σ) init thunk (← lowerTm C U ε (Γ.push (ρ)) body hs))
  | Γ, .cellTail init thunk, _ => do
    pure (.cellTailL (← layOf C (← need (aTy Γ init) "a cell of what has no type")) init thunk)
  | _, .cellL .., _ | _, .cellTailL .., _ => throw "lowered already"
  | Γ, .lend uniq r thunk pre post body, hs => do
    let some (.fn _ _ ρ ..) := aTy Γ thunk | throw "a borrow's scope not callable"
    pure (.lend uniq r thunk pre post (← lowerTm C U ε (Γ.push (ρ)) body hs))
  -- (What a type takes, a number now.)
  | Γ, .mem op [a] body, hs =>
    if op == .sizeOf || op == .alignOf then do
      let some t := (match aTy Γ a with
        | some (.ref _ t) | some (.data _ (t :: _)) => some t
        | _ => none) | throw "the size of what is not a pointer's or a reference's"
      let l ← layOf C t
      pure (.let_ (.atom (.int (if op == .sizeOf then l.size else l.align)))
        (← lowerTm C U ε (Γ.push (.scalar (-64))) body hs))
    else lowerMem C U ε Γ op [a] body hs
  -- (A raw pointer's target, its address.)
  | Γ, .mem .deref [base, a, _] body, hs => do
    let some (.data _ (t :: _)) := aTy Γ base | throw "what a pointer of no type points to"
    pure (.let_ (.atom a) (← lowerTm C U ε (Γ.push (.ref (.cell 0) t)) body hs))
  | Γ, .mem op args body, hs => lowerMem C U ε Γ op args body hs
  | Γ, .host id args body, hs => do
    match id, hs with
    | 0, hs => pure (.host id args (← lowerTm C U ε (Γ.push (.unit)) body hs))
    | 1, hs => pure (.host id args (← lowerTm C U ε (Γ.push (.tuple [.int, .int])) body hs))
    | _, .ty σ :: hs => pure (.host id args (← lowerTm C U ε (Γ.push σ) body hs))
    | _, _ => throw "a host operation without its type"
where
  /-- A memory operation lowered: of the layout of what its reference is to. -/
  lowerMem (C : Cert) (U : Uses) (ε : Row) (Γ : Env) (op : MemOp) (args : List Atom) (body : Tm)
      (hs : List Hint) : L Tm := do
    let σ ← match op, args.head?.bind (aTy Γ) with
      | .load, some (.ref _ σ) | .swap, some (.ref _ σ) => pure σ
      | .store, _ | .free, _ | .writeBits, _ | .copy, _ => pure .unit
      | .tag, _ | .readBits, _ => pure .int
      | .alloc, _ | .staticAt, _ => pure (.scalar (-64))
      | .addressOf, _ => match args with
        | [r, .int tag] => match aTy Γ r with
          | some (.ref _ σ) => do
            let ptr ← need (C.datas.find? fun d => d.ctors.any (·.1 == tag.toNat)) "a pointer type not known"
            pure (.data ptr.name [← need (fixedElem σ) "the address of what is not a `[T; N]`"])
          | _ => throw "the address of what is not a reference"
        | _ => throw "an address without its pointer's constructor"
      | .focus, some (.ref r σ) =>
        match args with
        | [_, ix] => do
          let at_ := match ix with
            | .int (.ofNat i) => (placeTy C σ [i]).orElse fun _ => fixedElem σ
            | _ => if aTy Γ ix == some .int then fixedElem σ else none
          pure (.ref r (← need at_ "a field not known"))
        | [_, _, .int (-1)] => do pure (.ref r (← need (fixedElem σ) "a place in what is not a `[T; N]`"))
        | [_, .int (.ofNat i), .int (.ofNat built)] => do
          pure (.ref r (← need ((ctorFieldsOf C built σ).bind (·[i]?)) "a field not known"))
        | _ => throw "a field not known"
      | _, _ => throw "a memory operation not of a reference"
    pure (.mem (← laidOp C Γ op args) args (← lowerTm C U ε (Γ.push σ) body hs))

/-- A function's clauses lowered at a signature, with their hints there. -/
def lowerClauses (C : Cert) (U : Uses) (e : SigEntry) (cs : List Clause) : L (List Clause) :=
  let sig := e.sig
  let params := sig.params.map (Ty.open sig.vars)
  (cs.zip e.hints).mapM fun (c, hs) => do
    let Bs ← need (patsTys C c.pats params) "patterns not of their types"
    pure { c with body := ← lowerTm C U (sig.eff.open sig.vars) (params ++ sig.caps ++ Bs).toArray c.body hs }

/-- Which function each of a function's signatures is lowered as: itself, or a
copy of it (`ids`, by function and by the place of the signature in
`Cert.sigsOf`). -/
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

/-- The program lowered, if its certificate types all of it; or why not. A
function is copied for each kind of layout its signatures need, each use of
it made of the copy for its signature; one with no signature is never
called, and stays as it is. What each copy is a copy of comes with it. -/
def lowered (C : Cert) (p : Program) : L (Program × List Nat) := do
  let C := C.withIndex
  let sigs := (List.range p.fns.size).toArray.map C.sigsOf
  let base := sigs.foldl (fun (acc : Array Nat × Nat) es => (acc.1.push acc.2, acc.2 + es.length)) (#[], 0)
  let U : Uses := ⟨base.1, base.2⟩
  -- (Whose signature each use at one is.)
  let owner := (sigs.toList.zipIdx.flatMap fun (es, fn) => es.zipIdx.map fun (_, i) => (fn, i)).toArray
  let all ← (p.fns.toList.zip sigs.toList).zipIdx.mapM fun ((F, es), fn) => es.mapM fun e =>
    tryCatch (lowerClauses C U e F.clauses) fun err => throw s!"{err} (in function {fn})"
  let main ← lowerTm C U [] #[] p.main C.mainHints
  -- The signatures of a function split into kinds, one at first: a kind is
  -- split where its signatures are lowered otherwise, each use taken as of
  -- the kind its signature is, until none is.
  let width := sigs.foldl (fun m es => max m es.length) 0 + 1
  let rec settle (fuel : Nat) (kinds : Array (List Nat)) : L (Array (List Nat)) := do
    let kindOf := fun (u : Nat) => match owner[u]? with
      | some (fn, i) => fn * width + 1 + (((kinds[fn]?).bind (·[i]?)).getD 0)
      | none => (u - U.total) * width
    let kinds' := (kinds.toList.zip all).toArray.map fun (ks, ls) =>
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
  let all := all.map (·.map (·.map fun c => { c with body := c.body.mapFns resolve }))
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
  pure ({ p with fns := fns.toArray, main := main.mapFns resolve, drops, names }, copies)

/-- The program lowered, if it can be (`lowered`). -/
def program (C : Cert) (p : Program) : Option (Program × List Nat) := ((lowered C p).run' {}).toOption

end Glorious.Lower
