module

public import Glorious.Typing.Subst

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

@[expose] public section

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
  /-- A borrow: the address of the cell it is a borrow of. -/
  loans : Nat → Option Nat

/-- `S'` knows everything `S` knows. -/
structure StoreTy.Le (S S' : StoreTy) : Prop where
  conts : ∀ id x, S.conts id = some x → S'.conts id = some x
  labels : ∀ id x, S.labels id = some x → S'.labels id = some x
  handlers : ∀ id x, S.handlers id = some x → S'.handlers id = some x
  cells : ∀ id x, S.cells id = some x → S'.cells id = some x
  loans : ∀ id x, S.loans id = some x → S'.loans id = some x

/-- A place of the region is of the cell at `a`: the cell's own, or that of a
borrow of it. -/
def OnCell (S : StoreTy) (r : Rgn) (a : Nat) : Prop :=
  ∃ x, x ∈ r.parts ∧ (x = .cell a ∨ ∃ b, x = .loan b ∧ S.loans b = some a)

/-- The reference to the cell at `a` that is borrow `b` is of a place of the
region `r`: the cell's own reference is of the cell's region, and a borrow's
of the borrow's. -/
def Tagged (S : StoreTy) (r : Rgn) (a b : Nat) : Prop :=
  ∃ x, x ∈ r.parts ∧ ((x = .cell a ∧ b = 0) ∨ (x = .loan b ∧ S.loans b = some a))

theorem Tagged.onCell {S : StoreTy} {r : Rgn} {a b : Nat} (h : Tagged S r a b) : OnCell S r a := by
  obtain ⟨x, hx, ⟨h, _⟩ | ⟨h, hl⟩⟩ := h
  · exact ⟨x, hx, .inl h⟩
  · exact ⟨x, hx, .inr ⟨b, h, hl⟩⟩

theorem OnCell.mono {S S' : StoreTy} (hle : S.Le S') {r : Rgn} {a : Nat} (h : OnCell S r a) :
    OnCell S' r a := by
  obtain ⟨x, hx, h | ⟨b, h, hl⟩⟩ := h
  · exact ⟨x, hx, .inl h⟩
  · exact ⟨x, hx, .inr ⟨b, h, hle.loans _ _ hl⟩⟩

theorem Tagged.mono {S S' : StoreTy} (hle : S.Le S') {r : Rgn} {a b : Nat} (h : Tagged S r a b) :
    Tagged S' r a b := by
  obtain ⟨x, hx, h | ⟨h, hl⟩⟩ := h
  · exact ⟨x, hx, .inl h⟩
  · exact ⟨x, hx, .inr ⟨h, hle.loans _ _ hl⟩⟩

theorem OnCell.cell {S : StoreTy} {a : Nat} : OnCell S (.cell a) a :=
  ⟨.cell a, List.mem_singleton_self _, .inl rfl⟩

theorem OnCell.loan {S : StoreTy} {a b : Nat} (hl : S.loans b = some a) : OnCell S (.loan b) a :=
  ⟨.loan b, List.mem_singleton_self _, .inr ⟨b, rfl, hl⟩⟩

theorem Tagged.cell {S : StoreTy} {a : Nat} : Tagged S (.cell a) a 0 :=
  ⟨.cell a, List.mem_singleton_self _, .inl ⟨rfl, rfl⟩⟩

theorem Tagged.loan {S : StoreTy} {a b : Nat} (hl : S.loans b = some a) : Tagged S (.loan b) a b :=
  ⟨.loan b, List.mem_singleton_self _, .inr ⟨rfl, hl⟩⟩

/-- A region of more places is of whatever cell the first is. -/
theorem OnCell.widen {S : StoreTy} {r r' : Rgn} {a : Nat} (h : OnCell S r a)
    (hp : ∀ x, x ∈ r.parts → x ∈ r'.parts) : OnCell S r' a := by
  obtain ⟨x, hx, h⟩ := h
  exact ⟨x, hp x hx, h⟩

theorem Tagged.widen {S : StoreTy} {r r' : Rgn} {a b : Nat} (h : Tagged S r a b)
    (hp : ∀ x, x ∈ r.parts → x ∈ r'.parts) : Tagged S r' a b := by
  obtain ⟨x, hx, h⟩ := h
  exact ⟨x, hp x hx, h⟩

/-- What the code above a borrow's scope may touch: the borrow, to write too if
it is one for writing, and whatever the code below may, except that it may not
write a place of what was lent, nor read one if it was lent for writing. -/
def lent (uniq : Bool) (ρ : Rgn) (b : Nat) (ϕ : List Rgn) : List Rgn :=
  .loan b :: ((if uniq then [.wr (.loan b)] else [])
    ++ (Rgn.flat ϕ).filter fun x =>
      !((Rgn.wr ρ).parts.contains x) && (!uniq || !(ρ.parts.contains x)) && x != .loan b
        && x != .wr (.loan b))

/-- What a borrow's scope grants is made of places and permissions alone. -/
theorem flat_lent (uniq : Bool) (ρ : Rgn) (b : Nat) (ϕ : List Rgn) :
    Rgn.flat (lent uniq ρ b ϕ) = lent uniq ρ b ϕ := by
  refine Rgn.flat_of_atoms fun x hx => ?_
  simp only [lent, List.mem_cons, List.mem_append] at hx
  rcases hx with rfl | hx | hx
  · rfl
  · cases uniq <;> simp at hx
    subst hx
    rfl
  · exact Rgn.atom_of_mem_flat (List.mem_filter.mp hx).1

/-- The region is of something the store typing knows. -/
def Known (S : StoreTy) : Rgn → Prop
  | .cell a => ∃ τ, S.cells a = some τ
  | .lab id => ∃ τ, S.labels id = some τ
  | .loan b => ∃ a, S.loans b = some a
  | .wr r => Known S r
  | .or a b => Known S a ∧ Known S b
  | .var _ => False
  | .bound _ => False

theorem Known.mono {S S' : StoreTy} (hle : S.Le S') {r : Rgn} (h : Known S r) : Known S' r := by
  induction r with
  | var i => exact h
  | bound k => exact h
  | cell a => exact h.imp fun τ h => hle.cells _ _ h
  | lab id => exact h.imp fun τ h => hle.labels _ _ h
  | loan b => exact h.imp fun a h => hle.loans _ _ h
  | wr r ih => exact ih h
  | or a b iha ihb => exact ⟨iha h.1, ihb h.2⟩

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
  /-- Under the region rules a reference's region is of the cell it points to;
  under the rules for borrows it is the region of the borrow the reference is.
  What it is a reference to is the part of what the cell holds that its path
  leads to. -/
  | ref {a b : Nat} {r : Rgn} {τ₀ τ : Ty} {path : List PathStep} :
      S.cells a = some τ₀ → PartOk Δ τ₀ path τ → (Δ.regions → OnCell S r a) →
      (Δ.regions → Δ.loans → Tagged S r a b) →
      HasVal Δ S (.ref a b path) (.ref r τ)

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
  /-- The scope of a cell passes its result on, and grants its cell, to read
  and to write. -/
  | cell {a : Nat} {st : List Frame} {σ τ : Ty} {ε : Row} {ϕ : List Rgn} :
      S.cells a = some σ → StackOk Δ S st τ ε ϕ →
      StackOk Δ S (.cell a :: st) τ ε (.cell a :: .wr (.cell a) :: ϕ)
  /-- The scope of a borrow passes its result on. It grants the borrow, and
  takes away what was lent: `ρ`, which the code below could touch. It serves
  nothing, so it is never among the frames a resumption captures. -/
  | lend {uniq : Bool} {a b : Nat} {st : List Frame} {τ : Ty} {ε : Row} {ϕ : List Rgn}
      {ρ : Rgn} :
      S.loans b = some a → 0 < b → OnCell S ρ a → Grants ϕ ρ → (uniq = true → Grants ϕ (.wr ρ)) →
      StackOk Δ S st τ ε ϕ → StackOk Δ S (.lend uniq a b :: st) τ [] (lent uniq ρ b ϕ)
  /-- Without the rules for borrows it takes nothing away. -/
  | lendLoose {uniq : Bool} {a b : Nat} {st : List Frame} {τ : Ty} {ε : Row} {ϕ : List Rgn} :
      ¬ (Δ.regions ∧ Δ.loans) → S.loans b = some a → (Δ.regions → ∃ ρ, OnCell S ρ a ∧ Grants ϕ ρ) →
      StackOk Δ S st τ ε ϕ →
      StackOk Δ S (.lend uniq a b :: st) τ ε (.loan b :: .wr (.loan b) :: ϕ)
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
  loans : ∀ b a, S.loans b = some a → b ≤ store.labels
  /-- Under the rules for borrows no resumption captured the scope of one. -/
  quiet : Δ.regions ∧ Δ.loans → ∀ (id : Nat) (seg : List Frame),
    store.conts[id]? = some (some seg) → ∀ uniq a b, Frame.lend uniq a b ∉ seg

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
  /-- A function whose closures say how they are destroyed: whatever signature
  it has, the function that destroys one is entered with no captures and with
  the closure's captures as its arguments, at the regions the closure was made
  with, and gives unit, performing nothing and touching nothing. -/
  drops : ∀ fn d sig, p.drops.lookup fn = some d → Δ.fnSig fn sig →
    ∃ sigd, Δ.fnSig d sigd ∧ sigd.caps = [] ∧ sigd.params = sig.caps ∧ sigd.ret = .unit
      ∧ sigd.eff = [] ∧ sigd.crgns = sig.crgns ∧ sigd.rgns = 0 ∧ sigd.acc = []

/-- The callable a computation applies or gives up, if it does so. -/
def calleeAtom : Tm → Option Atom
  | .call f _ _ => some f
  | .tail f _ => some f
  | .label thunk _ => some thunk
  | .labelTail thunk => some thunk
  | .cancel k _ => some k
  | .cell _ thunk _ => some thunk
  | .lend _ _ thunk _ _ _ => some thunk
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
  /-- An intrinsic has no result: arithmetic whose result does not fit, a
  division by zero, an array read at a place that is not there. -/
  | overflow {p : Prim} {args : List Atom} {body : Tm} {env : Env} {stack : List Frame}
      {store : Store Frame} {vs : List Value} :
      evalAtoms env args = some vs → p.eval vs = none →
      Fault ⟨.let_ (.prim p args) body, env, stack, store⟩
  /-- A memory cell is used after it was freed. -/
  | freed {op : MemOp} {args : List Atom} {body : Tm} {env : Env} {stack : List Frame}
      {store : Store Frame} {a b : Nat} {path : List PathStep} {vs : List Value} :
      evalAtoms env args = some (.ref a b path :: vs) → store.cells[a]? = some none →
      Fault ⟨.mem op args body, env, stack, store⟩
  /-- A reference is to a part of a value that is not there: a place past the
  end of an array. -/
  | absent {op : MemOp} {args : List Atom} {body : Tm} {env : Env} {stack : List Frame}
      {store : Store Frame} {a b : Nat} {path : List PathStep} {vs : List Value} {v : Value} :
      evalAtoms env args = some (.ref a b path :: vs) → store.cells[a]? = some (some v) →
      v.part path = none → Fault ⟨.mem op args body, env, stack, store⟩
  /-- A reference is asked for to a place below zero. -/
  | below {args : List Atom} {body : Tm} {env : Env} {stack : List Frame}
      {store : Store Frame} {a b : Nat} {path : List PathStep} {i : Int} :
      evalAtoms env args = some [.ref a b path, .int i] → i < 0 →
      Fault ⟨.mem .focus args body, env, stack, store⟩
  /-- A resumption is resumed or cancelled after it was already used. -/
  | resumed {s : State} {f : Atom} {id : Nat} :
      calleeAtom s.tm = some f → f.eval s.env = some (.cont id) →
      s.store.conts[id]? = some none → Fault s
  /-- A label is applied after its scope has ended. -/
  | dead {s : State} {f : Atom} {id : Nat} :
      calleeAtom s.tm = some f → f.eval s.env = some (.label id) →
      findLabel Frame.asLabel id s.stack = none → Fault s

end Glorious.Typing
