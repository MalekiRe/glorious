import Glorious.Typing.Static

/-!
# Types for machine states

What it means for a running Core machine to be well typed: its values, its
stack, and the continuations and memory cells in its store. `Typed` is the
invariant the safety theorem carries from step to step; `Fault` lists the ways
a typed state can still fail to step.
-/

namespace Glorious.Typing

open Core

/-- The types of what the store holds, and of the scopes on the stack. Entries
are only ever added. -/
structure StoreTy where
  /-- A resumption: the type it is resumed with, the type its computation
  finally yields, and the operations that computation needs where it resumes. -/
  conts : Nat → Option (Ty × Ty × Row)
  /-- A label scope: the type the scope yields. -/
  labels : Nat → Option Ty
  /-- A handler: the type it yields, and the operations it needs below it. -/
  handlers : Nat → Option (Ty × Row)
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
  | clo {fn : Nat} {captures : List Value} {sig : FnSig} :
      Δ.fnSig fn sig → HasVals Δ S captures sig.caps →
      HasVal Δ S (.clo fn captures) (.fn sig.params sig.ret sig.eff)
  | cont {id : Nat} {o ρ : Ty} {ε : Row} :
      S.conts id = some (o, ρ, ε) → HasVal Δ S (.cont id) (.fn [o] ρ ε)
  | label {id : Nat} {σ ρ : Ty} {ε : Row} :
      S.labels id = some σ → HasVal Δ S (.label id) (.fn [σ] ρ ε)
  | ref {a : Nat} {τ : Ty} : S.cells a = some τ → HasVal Δ S (.ref a) (.ref τ)

inductive HasVals (Δ : Ctx) (S : StoreTy) : List Value → List Ty → Prop where
  | nil : HasVals Δ S [] []
  | cons {v : Value} {vs : List Value} {τ : Ty} {τs : List Ty} :
      HasVal Δ S v τ → HasVals Δ S vs τs → HasVals Δ S (v :: vs) (τ :: τs)

end

/-- An installed handler: its captured values fit the functions that serve it. -/
def HandlerRt (Δ : Ctx) (S : StoreTy) (h : Handler) (σ ρ : Ty) (H ε : Row) : Prop :=
  ∃ Cs, HasVals Δ S h.caps Cs ∧ HandlerOk Δ Cs h.ret h.ops σ ρ H ε

/-- An exit fits its target: a label scope is left with a value of the type the
scope yields, and a handler is left for one of its functions, which yields what
the handler yields and needs no more than the handler does. -/
inductive ExitOk (Δ : Ctx) (S : StoreTy) : Target → After → Prop where
  | label {id : Nat} {v : Value} {σ : Ty} :
      S.labels id = some σ → HasVal Δ S v σ → ExitOk Δ S (.label id) (.yield v)
  | handler {id fn : Nat} {captures args : List Value} {sig : FnSig} {ε₀ : Row} :
      S.handlers id = some (sig.ret, ε₀) → Δ.fnSig fn sig → Row.le sig.eff ε₀ →
      HasVals Δ S captures sig.caps → HasVals Δ S args sig.params →
      ExitOk Δ S (.handler id) (.invoke fn captures args)

/-- A stack accepts a result of type `τ`, and serves the operations in `ε` to
the code running on top of it. -/
inductive StackOk (Δ : Ctx) (S : StoreTy) : List Frame → Ty → Row → Prop where
  /-- The bottom of the stack takes the program's result and serves nothing. -/
  | nil {τ : Ty} : StackOk Δ S [] τ []
  | call {env : Env} {body : Tm} {st : List Frame} {Γ : TEnv} {σ τ : Ty} {εb ε : Row} :
      HasVals Δ S env Γ → HasTm Δ (Γ ++ [σ]) body τ εb → Row.le εb ε → StackOk Δ S st τ ε →
      StackOk Δ S (.call env body :: st) σ ε
  /-- A handler serves its own operations and, of what is below it, only what
  it was installed among: so the frames above it stay well typed when they are
  captured and later put back on a different stack. -/
  | handler {id : Nat} {h : Handler} {st : List Frame} {σ ρ : Ty} {H ε₀ ε : Row} :
      S.handlers id = some (ρ, ε₀) → HandlerRt Δ S h σ ρ H ε₀ → Row.le ε₀ ε →
      StackOk Δ S st ρ ε → StackOk Δ S (.handler id h :: st) σ (H ++ ε₀)
  | label {id : Nat} {st : List Frame} {τ : Ty} {ε : Row} :
      S.labels id = some τ → StackOk Δ S st τ ε → StackOk Δ S (.label id :: st) τ ε
  | guard {fn : Nat} {captures : List Value} {st : List Frame} {Cs : List Ty} {σc τ : Ty}
      {ε : Row} :
      Δ.fnSig fn ⟨Cs, [], σc, []⟩ → HasVals Δ S captures Cs → StackOk Δ S st τ ε →
      StackOk Δ S (.guard fn captures :: st) τ ε
  /-- A pending result takes anything, since it discards it. -/
  | yield {w : Value} {st : List Frame} {σ τ : Ty} {ε : Row} :
      HasVal Δ S w σ → StackOk Δ S st σ ε → StackOk Δ S (.yield w :: st) τ ε
  /-- An exit in progress takes anything, and serves nothing: the cleanup
  running above it performs no operations, so it can never be captured. -/
  | exit {target : Target} {after : After} {st : List Frame} {σ τ : Ty} {ε : Row} :
      ExitOk Δ S target after → (∃ fr, fr ∈ st ∧ fr.isTarget target = true) →
      StackOk Δ S st σ ε → StackOk Δ S (.exit target after :: st) τ []

/-- Captured frames that take a value of type `o`: put back on any later stack
that takes `ρ` and serves at least `ε₀`, they make a well-typed stack. -/
def ContOk (Δ : Ctx) (S : StoreTy) (seg : List Frame) (o ρ : Ty) (ε₀ : Row) : Prop :=
  ∀ S', S.Le S' → ∀ st ε', StackOk Δ S' st ρ ε' → Row.le ε₀ ε' →
    ∃ ε'', StackOk Δ S' (seg ++ st) o ε''

/-- The store holds what its typing says, and nothing in the typing refers to
an identity that has not been given out yet. A used resumption and a freed cell
keep their types. -/
structure StoreOk (Δ : Ctx) (S : StoreTy) (store : Store Frame) : Prop where
  conts : ∀ id o ρ ε₀, S.conts id = some (o, ρ, ε₀) →
    id < store.conts.length ∧ ∀ seg, store.conts[id]? = some (some seg) → ContOk Δ S seg o ρ ε₀
  labels : ∀ id τ, S.labels id = some τ → id < store.labels
  handlers : ∀ id x, S.handlers id = some x → id < store.labels
  cells : ∀ a τ, S.cells a = some τ →
    a < store.cells.length ∧ ∀ v, store.cells[a]? = some (some v) → HasVal Δ S v τ

/-- A machine state is well typed under a store typing. -/
inductive TypedAt (Δ : Ctx) (S : StoreTy) : State → Prop where
  | mk {tm : Tm} {env : Env} {stack : List Frame} {store : Store Frame} {Γ : TEnv} {τ : Ty}
      {ε ε' : Row} :
      HasVals Δ S env Γ → HasTm Δ Γ tm τ ε → Row.le ε ε' → StackOk Δ S stack τ ε' →
      StoreOk Δ S store → TypedAt Δ S ⟨tm, env, stack, store⟩

/-- A machine state is well typed. -/
def Typed (Δ : Ctx) (s : State) : Prop := ∃ S, TypedAt Δ S s

/-- A program is well typed: every signature the context gives a function is
one its clauses are typed at, those clauses cover every list of arguments of
the signature's parameter types, and the main computation performs no
operations. That the clauses cover the arguments is assumed here, not derived
from the patterns. -/
structure ProgramOk (Δ : Ctx) (p : Program) : Prop where
  fns : ∀ fn sig, Δ.fnSig fn sig → ∃ F, p.fns[fn]? = some F ∧ FnTyped Δ sig F
    ∧ ∀ S vs, HasVals Δ S vs sig.params → selectClause F.clauses vs ≠ none
  main : ∃ τ, HasTm Δ [] p.main τ []

/-- The callable a computation applies or gives up, if it does so. -/
def calleeAtom : Tm → Option Atom
  | .call f _ _ => some f
  | .tail f _ => some f
  | .label thunk _ => some thunk
  | .labelTail thunk => some thunk
  | .cancel k _ => some k
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
