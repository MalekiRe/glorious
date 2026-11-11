import Glorious.Typing.Subst

/-!
# Types for machine states

What it means for a running Core machine to be well typed: its values, its
stack, and the continuations and memory cells in its store. `Typed` is the
invariant the safety theorem carries from step to step; `Fault` lists the ways
a typed state can still fail to step.

At run time a region is a cell: every type here is one in which the region
variables of the functions running have been replaced by the cells they stand
for.
-/

namespace Glorious.Typing

open Core

/-- The types of what the store holds, and of the scopes on the stack. Entries
are only ever added. -/
structure StoreTy where
  /-- A resumption: the type it is resumed with, the type its computation
  finally yields, the operations that computation needs where it resumes, and
  the regions it needs there. -/
  conts : Nat → Option (Ty × Ty × Row × List Rgn)
  /-- A label scope: the type the scope yields. -/
  labels : Nat → Option Ty
  /-- A handler: the type it yields, the operations it needs below it, and the
  regions it and the computation it handles may touch. -/
  handlers : Nat → Option (Ty × Row × List Rgn)
  /-- A memory cell: the type of its contents. -/
  cells : Nat → Option Ty

/-- `S'` knows everything `S` knows. -/
structure StoreTy.Le (S S' : StoreTy) : Prop where
  conts : ∀ id x, S.conts id = some x → S'.conts id = some x
  labels : ∀ id x, S.labels id = some x → S'.labels id = some x
  handlers : ∀ id x, S.handlers id = some x → S'.handlers id = some x
  cells : ∀ id x, S.cells id = some x → S'.cells id = some x

mutual

/-- A value has a type. A label can be used at any result type and among any
operations, because applying it never returns. -/
inductive HasVal (Δ : Ctx) (S : StoreTy) : Value → Ty → Prop where
  | int {n : Int} : HasVal Δ S (.int n) .int
  | data {tag : Nat} {fields : List Value} {T : Ty} {Fs : List Ty} :
      CtorOf Δ tag T Fs → HasVals Δ S fields Fs → HasVal Δ S (.data tag fields) T
  /-- A closure was made with regions for those its function leaves open. One
  that may be called many times captured only duplicable values. Only a
  function has an environment a type can state: a resumption and a label do
  not. -/
  | clo {fn : Nat} {captures : List Value} {sig : FnSig} {θ : List Rgn} {once : Bool}
      {env : Option (List Ty)} {τ : Ty} :
      Δ.fnSig fn sig → θ.length = sig.crgns → HasVals Δ S captures (sig.caps.map (Ty.inst θ)) →
      (once = false → ∀ c, c ∈ sig.caps → Δ.dup c) →
      (∀ Cs, env = some Cs → Cs = sig.caps.map (Ty.inst θ)) → τ = sig.ty θ once env →
      HasVal Δ S (.clo fn captures) τ
  /-- A resumption may be called once. -/
  | cont {id : Nat} {o ρ : Ty} {ε : Row} {Φ : List Rgn} :
      S.conts id = some (o, ρ, ε, Φ) → HasVal Δ S (.cont id) (.fn 0 [o] ρ ε true none Φ)
  /-- Under the region rules a label's type says that applying it touches the
  region of its scope. -/
  | label {id : Nat} {σ ρ : Ty} {ε : Row} {once : Bool} {acc : List Rgn} :
      S.labels id = some σ → (Δ.regions → .lab id ∈ acc) →
      HasVal Δ S (.label id) (.fn 0 [σ] ρ ε once none acc)
  /-- Under the region rules a reference's region is the cell it points to. -/
  | ref {a : Nat} {r : Rgn} {τ : Ty} :
      S.cells a = some τ → (Δ.regions → r = .cell a) → HasVal Δ S (.ref a) (.ref r τ)

inductive HasVals (Δ : Ctx) (S : StoreTy) : List Value → List Ty → Prop where
  | nil : HasVals Δ S [] []
  | cons {v : Value} {vs : List Value} {τ : Ty} {τs : List Ty} :
      HasVal Δ S v τ → HasVals Δ S vs τs → HasVals Δ S (v :: vs) (τ :: τs)

end

/-- An installed handler: its captured values fit the functions that serve it. -/
def HandlerRt (Δ : Ctx) (S : StoreTy) (h : Handler) (σ ρ : Ty) (H ε : Row) (Φ : List Rgn) :
    Prop :=
  ∃ Cs, HasVals Δ S h.caps Cs ∧ HandlerOk Δ Cs h.ret h.ops σ ρ H ε Φ

/-- An exit fits its target: a label scope is left with a value of the type the
scope yields, and a handler is left for one of its functions, which yields what
the handler yields and needs no more than the handler does. -/
inductive ExitOk (Δ : Ctx) (S : StoreTy) : Target → After → Prop where
  | label {id : Nat} {v : Value} {σ : Ty} :
      S.labels id = some σ → HasVal Δ S v σ → ExitOk Δ S (.label id) (.yield v)
  | handler {id fn : Nat} {captures args : List Value} {Cs Ps : List Ty} {ρ : Ty} {ε₀ : Row}
      {Φ : List Rgn} :
      S.handlers id = some (ρ, ε₀, Φ) → Enters Δ fn Cs Ps ρ ε₀ Φ →
      HasVals Δ S captures Cs → HasVals Δ S args Ps →
      ExitOk Δ S (.handler id) (.invoke fn captures args)

/-- A stack accepts a result of type `τ`, serves the operations in `ε` to the
code running on top of it, and grants that code the regions in `ϕ`: the cells
of scopes on the stack that the code may touch. -/
inductive StackOk (Δ : Ctx) (S : StoreTy) : List Frame → Ty → Row → List Rgn → Prop where
  /-- The bottom of the stack takes the program's result, serves nothing and
  grants nothing. -/
  | nil {τ : Ty} : StackOk Δ S [] τ [] []
  | call {env : Env} {body : Tm} {st : List Frame} {Γ : TEnv} {σ τ : Ty} {εb ε : Row}
      {ϕb ϕ : List Rgn} :
      HasVals Δ S env Γ → HasTm Δ ϕb (Γ ++ [σ]) body τ εb → Row.le εb ε → Sub ϕb ϕ →
      StackOk Δ S st τ ε ϕ → StackOk Δ S (.call env body :: st) σ ε ϕ
  /-- A handler serves its own operations and, of what is below it, only what
  it was installed among: so the frames above it stay well typed when they are
  captured and later put back on a different stack. For the same reason it
  grants only the regions it was installed with. -/
  | handler {id : Nat} {h : Handler} {st : List Frame} {σ ρ : Ty} {H ε₀ ε : Row}
      {Φ ϕ : List Rgn} :
      S.handlers id = some (ρ, ε₀, Φ) → HandlerRt Δ S h σ ρ H ε₀ Φ → Row.le ε₀ ε → Sub Φ ϕ →
      StackOk Δ S st ρ ε ϕ → StackOk Δ S (.handler id h :: st) σ (H ++ ε₀) Φ
  /-- The scope of a label passes its result on, and grants its own region:
  what lets the code above apply the label. -/
  | label {id : Nat} {st : List Frame} {τ : Ty} {ε : Row} {ϕ : List Rgn} :
      S.labels id = some τ → StackOk Δ S st τ ε ϕ →
      StackOk Δ S (.label id :: st) τ ε (.lab id :: ϕ)
  | guard {fn : Nat} {captures : List Value} {st : List Frame} {Cs : List Ty} {σc τ : Ty}
      {ε : Row} {ϕ : List Rgn} :
      Enters Δ fn Cs [] σc [] ϕ → HasVals Δ S captures Cs → StackOk Δ S st τ ε ϕ →
      StackOk Δ S (.guard fn captures :: st) τ ε ϕ
  /-- The scope of a cell passes its result on, and grants its cell. -/
  | cell {a : Nat} {st : List Frame} {τ : Ty} {ε : Row} {ϕ : List Rgn} :
      StackOk Δ S st τ ε ϕ → StackOk Δ S (.cell a :: st) τ ε (.cell a :: ϕ)
  /-- A pending result takes anything, since it discards it. -/
  | yield {w : Value} {st : List Frame} {σ τ : Ty} {ε : Row} {ϕ : List Rgn} :
      HasVal Δ S w σ → StackOk Δ S st σ ε ϕ → StackOk Δ S (.yield w :: st) τ ε ϕ
  /-- An exit in progress takes anything, and serves nothing: the cleanup
  running above it performs no operations, so it can never be captured. -/
  | exit {target : Target} {after : After} {st : List Frame} {σ τ : Ty} {ε : Row}
      {ϕ : List Rgn} :
      ExitOk Δ S target after → (∃ fr, fr ∈ st ∧ fr.isTarget target = true) →
      StackOk Δ S st σ ε ϕ → StackOk Δ S (.exit target after :: st) τ [] ϕ
  /-- Any stack takes the result of a call that does not return: none arrives. -/
  | never {st : List Frame} {σ : Ty} {ε : Row} {ϕ : List Rgn} :
      StackOk Δ S st σ ε ϕ → StackOk Δ S st .never ε ϕ

/-- Captured frames that take a value of type `o`: put back on any later stack
that takes `ρ`, serves at least `ε₀` and grants at least `Φ`, they make a
well-typed stack. -/
def ContOk (Δ : Ctx) (S : StoreTy) (seg : List Frame) (o ρ : Ty) (ε₀ : Row) (Φ : List Rgn) :
    Prop :=
  ∀ S', S.Le S' → ∀ st ε' ϕ', StackOk Δ S' st ρ ε' ϕ' → Row.le ε₀ ε' → Sub Φ ϕ' →
    ∃ ε'' ϕ'', StackOk Δ S' (seg ++ st) o ε'' ϕ''

/-- The store holds what its typing says, and nothing in the typing refers to
an identity that has not been given out yet. A used resumption and a freed cell
keep their types. -/
structure StoreOk (Δ : Ctx) (S : StoreTy) (store : Store Frame) : Prop where
  conts : ∀ id o ρ ε₀ Φ, S.conts id = some (o, ρ, ε₀, Φ) →
    id < store.conts.length
      ∧ ∀ seg, store.conts[id]? = some (some seg) → ContOk Δ S seg o ρ ε₀ Φ
  labels : ∀ id τ, S.labels id = some τ → id < store.labels
  handlers : ∀ id x, S.handlers id = some x → id < store.labels
  cells : ∀ a τ, S.cells a = some τ →
    a < store.cells.length ∧ ∀ v, store.cells[a]? = some (some v) → HasVal Δ S v τ

/-- A machine state is well typed under a store typing. Its code may touch
regions the stack grants. -/
inductive TypedAt (Δ : Ctx) (S : StoreTy) : State → Prop where
  | mk {tm : Tm} {env : Env} {stack : List Frame} {store : Store Frame} {Γ : TEnv} {τ : Ty}
      {ε ε' : Row} {ϕ ϕ' : List Rgn} :
      HasVals Δ S env Γ → HasTm Δ ϕ Γ tm τ ε → Row.le ε ε' → Sub ϕ ϕ' →
      StackOk Δ S stack τ ε' ϕ' → StoreOk Δ S store → TypedAt Δ S ⟨tm, env, stack, store⟩

/-- A machine state is well typed. -/
def Typed (Δ : Ctx) (s : State) : Prop := ∃ S, TypedAt Δ S s

/-- A program is well typed: what the context says of a type does not depend on
the regions in it; every signature the context gives a function is one its
clauses are typed at; those clauses cover every list of arguments of the
signature's parameter types, whatever regions it is entered with; and the main
computation performs no operations and touches no region it did not make. That
the clauses cover the arguments is assumed here, not derived from the patterns. -/
structure ProgramOk (Δ : Ctx) (p : Program) : Prop where
  stable : Δ.Stable
  fns : ∀ fn sig, Δ.fnSig fn sig → sig.wf = true ∧ ∃ F, p.fns[fn]? = some F ∧ FnTyped Δ sig F
    ∧ ∀ S vs θ, HasVals Δ S vs ((sig.params.map (Ty.open sig.vars)).map (Ty.inst θ)) →
        selectClause F.clauses vs ≠ none
  main : ∃ τ, HasTm Δ [] [] p.main τ []

/-- The callable a computation applies or gives up, if it does so. -/
def calleeAtom : Tm → Option Atom
  | .call f _ _ => some f
  | .tail f _ => some f
  | .label thunk _ => some thunk
  | .labelTail thunk => some thunk
  | .cancel k _ => some k
  | .cell _ thunk _ => some thunk
  | .cellTail _ thunk => some thunk
  | .ret _ => none
  | .let_ _ _ => none
  | .handle _ _ _ _ _ => none
  | .handleTail _ _ _ _ => none
  | .raise _ _ => none
  | .perform _ _ _ => none
  | .guard _ _ _ => none
  | .guardTail _ _ => none
  | .mem _ _ _ => none
  | .host _ _ _ => none

/-- The ways a well-typed state can fail to step. Types do not rule these out;
the checks on how often a resumption is used and on how long labels and cells
live are meant to. -/
inductive Fault : State → Prop where
  /-- The result of an arithmetic intrinsic does not fit in 64 bits. -/
  | overflow {p : Prim} {args : List Atom} {body : Tm} {env : Env} {stack : List Frame}
      {store : Store Frame} {m n : Int} :
      evalAtoms env args = some [.int m, .int n] → p.eval [.int m, .int n] = none →
      Fault ⟨.let_ (.prim p args) body, env, stack, store⟩
  /-- A memory cell is used after it was freed. -/
  | freed {op : MemOp} {args : List Atom} {body : Tm} {env : Env} {stack : List Frame}
      {store : Store Frame} {a : Nat} {vs : List Value} :
      evalAtoms env args = some (.ref a :: vs) → store.cells[a]? = some none →
      Fault ⟨.mem op args body, env, stack, store⟩
  /-- A resumption is resumed or cancelled after it was already used. -/
  | resumed {s : State} {f : Atom} {id : Nat} :
      calleeAtom s.tm = some f → f.eval s.env = some (.cont id) →
      s.store.conts[id]? = some none → Fault s
  /-- A label is applied after its scope has ended. -/
  | dead {s : State} {f : Atom} {id : Nat} :
      calleeAtom s.tm = some f → f.eval s.env = some (.label id) →
      findLabel Frame.asLabel id s.stack = none → Fault s

end Glorious.Typing
