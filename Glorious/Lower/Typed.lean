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

/-- Why a program is not lowered, or what it is lowered to. -/
abbrev L := Except String

/-- What is there, or why not. -/
def need {α : Type} (o : Option α) (why : String) : L α :=
  match o with
  | some a => pure a
  | none => throw why

/-- The memory operation `op` of an address, laid out as what the reference
`args`' first is to; not if what it reaches into is not bytes. -/
def laidOp (C : Cert) (Γ : TEnv) (op : MemOp) (args : List Atom) : L MemOp := do
  let some (.ref _ σ) := args.head?.bind (atomTy Γ) | throw "a memory operation not of a reference"
  let l := (layOf C [] σ).lay
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

/-- The computation lowered: `ε` the operations it may perform, the hints
the certificate has for it. -/
partial def lowerTm (C : Cert) (ε : Row) : TEnv → Tm → List Hint → L Tm
  | _, .ret a, _ => pure (.ret a)
  | Γ, .let_ rhs body, h :: hs => do
    let (σ, _) ← need h.bind? "a `let` without its type"
    pure (.let_ rhs (← lowerTm C ε (Γ ++ [σ]) body hs))
  | _, .let_ _ _, [] => throw "a `let` without its type"
  | Γ, .call f args body, hs => do
    let some (.fn n _ σ ..) := atomTy Γ f | throw "a call of what is not callable"
    let (rs, hs) ← need (takeRgns n hs) "a call without its regions"
    if σ = .never then
      let .ty σ' :: hs := hs | throw "a call that does not return without its type"
      pure (.call f args (← lowerTm C ε (Γ ++ [σ']) body hs))
    else pure (.call f args (← lowerTm C ε (Γ ++ [σ.open rs]) body hs))
  | _, .tail f args, _ => pure (.tail f args)
  | Γ, .handle ret ops captures thunk body, hs => do
    let .handler ρ .. :: hs := hs | throw "a handler without its type"
    pure (.handle ret ops captures thunk (← lowerTm C ε (Γ ++ [ρ]) body hs))
  | _, .handleTail ret ops captures thunk, _ => pure (.handleTail ret ops captures thunk)
  | _, .raise op args, _ => pure (.raise op args)
  | Γ, .perform op args body, hs => do
    let targs ← need (ε.lookup op) "an operation performed where it may not be"
    let some (_, some σ) := findOp C.ops op targs | throw "an operation without its type"
    pure (.perform op args (← lowerTm C ε (Γ ++ [σ]) body hs))
  | Γ, .label thunk body, hs => do
    let some (.fn _ _ σ ..) := atomTy Γ thunk | throw "a label's scope not callable"
    pure (.label thunk (← lowerTm C ε (Γ ++ [σ]) body hs))
  | _, .labelTail thunk, _ => pure (.labelTail thunk)
  | Γ, .guard cleanup thunk body, hs => do
    let some (.fn _ _ σ ..) := atomTy Γ thunk | throw "a guard's scope not callable"
    pure (.guard cleanup thunk (← lowerTm C ε (Γ ++ [σ]) body hs))
  | _, .guardTail cleanup thunk, _ => pure (.guardTail cleanup thunk)
  | Γ, .cancel k body, hs => do pure (.cancel k (← lowerTm C ε (Γ ++ [.unit]) body hs))
  | Γ, .cell init thunk body, hs => do
    let σ ← need (atomTy Γ init) "a cell of what has no type"
    let some (.fn _ _ ρ ..) := atomTy Γ thunk | throw "a cell's scope not callable"
    pure (.cellL (layOf C [] σ) init thunk (← lowerTm C ε (Γ ++ [ρ]) body hs))
  | Γ, .cellTail init thunk, _ => do
    pure (.cellTailL (layOf C [] (← need (atomTy Γ init) "a cell of what has no type")) init thunk)
  | _, .cellL .., _ | _, .cellTailL .., _ => throw "lowered already"
  | Γ, .lend uniq r thunk pre post body, hs => do
    let some (.fn _ _ ρ ..) := atomTy Γ thunk | throw "a borrow's scope not callable"
    pure (.lend uniq r thunk pre post (← lowerTm C ε (Γ ++ [ρ]) body hs))
  | Γ, .mem op args body, hs => do
    let σ ← match op, args.head?.bind (atomTy Γ) with
      | .load, some (.ref _ σ) | .swap, some (.ref _ σ) => pure σ
      | .store, _ | .free, _ | .writeBits, _ | .copy, _ => pure .unit
      | .tag, _ | .readBits, _ => pure .int
      | .alloc, _ => pure (.scalar (-64))
      | .focus, some (.ref r σ) =>
        match args with
        | [_, ix] => do pure (.ref r (← need (focusTy C Γ σ ix) "a field not known"))
        | [_, .int (.ofNat i), .int (.ofNat built)] => do
          pure (.ref r (← need ((ctorFieldsOf C built σ).bind (·[i]?)) "a field not known"))
        | _ => throw "a field not known"
      | _, _ => throw "a memory operation not of a reference"
    pure (.mem (← laidOp C Γ op args) args (← lowerTm C ε (Γ ++ [σ]) body hs))
  | Γ, .host id args body, hs => do
    match id, hs with
    | 0, hs => pure (.host id args (← lowerTm C ε (Γ ++ [.unit]) body hs))
    | 1, hs => pure (.host id args (← lowerTm C ε (Γ ++ [.tuple [.int, .int]]) body hs))
    | _, .ty σ :: hs => pure (.host id args (← lowerTm C ε (Γ ++ [σ]) body hs))
    | _, _ => throw "a host operation without its type"

/-- A function's clauses lowered at a signature, with their hints there. -/
def lowerClauses (C : Cert) (e : SigEntry) (cs : List Clause) : L (List Clause) :=
  let sig := e.sig
  let params := sig.params.map (Ty.open sig.vars)
  (cs.zip e.hints).mapM fun (c, hs) => do
    let Bs ← need (patsTys C c.pats params) "patterns not of their types"
    pure { c with body := ← lowerTm C (sig.eff.open sig.vars) (params ++ sig.caps ++ Bs) c.body hs }

/-- The program lowered, if its certificate types all of it the same way at
each of a function's signatures; or why not. A function with none is never
called, and stays as it is. -/
def lowered (C : Cert) (p : Program) : L Program := do
  let C := C.withIndex
  let fns ← p.fns.toList.zipIdx.mapM fun (F, fn) => do
    match C.sigsOf fn with
    | [] => pure F
    | e :: rest =>
      let clauses ← lowerClauses C e F.clauses
      for e' in rest do
        if (lowerClauses C e' F.clauses).toOption != some clauses then
          throw s!"function {fn} is laid out otherwise at another of its signatures"
      pure { F with clauses }
  pure { p with fns := fns.toArray, main := ← lowerTm C [] [] p.main C.mainHints }

/-- The program lowered, if it can be (`lowered`). -/
def program (C : Cert) (p : Program) : Option Program := (lowered C p).toOption

end Glorious.Lower
