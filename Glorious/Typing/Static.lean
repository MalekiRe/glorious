import Glorious.Core.Semantics

/-!
# Types for Core

A type system for the kernel language, as the statement a safety proof is made
about. Types are monomorphic. A function that the surface language uses at
several types simply has several signatures here, and must be well typed at
each: polymorphism is a finite set of instances, as it is for any whole program
without polymorphic recursion.

A callable's type carries the operations it may perform. An operation is named,
with the type arguments its effect is used at; what it takes and gives back is
looked up in the program's declarations, so that an operation's payload can be
a callable that performs the same operation. A row lists operations nearest
handler first, so that looking an operation up in a row finds the same handler
the machine finds on the stack.

Ownership is part of the typing. A callable's type says whether it may be
called once only; a resumption may, and so may a function that captured
something that cannot be duplicated. A value whose type the context does not
call duplicable can be moved once: the rules below require that a local moved
by one step of a computation is not moved twice by it and is not mentioned by
the steps after it.
-/

namespace Glorious.Typing

open Core

inductive Ty where
  | int
  | tuple (fields : List Ty)
  /-- A declared data type applied to its arguments. -/
  | data (name : Nat) (args : List Ty)
  /-- A callable: a function, a resumption or a label. `eff` lists the operations
  it may perform, each with the type arguments of its effect. `once` says that
  it may be called at most once. -/
  | fn (params : List Ty) (ret : Ty) (eff : List (Nat × List Ty)) (once : Bool)
  | ref (t : Ty)
  /-- The result of a call that does not return. No value has this type. -/
  | never

/-- The type of an operation: its payload, and what it is resumed with if it
can be resumed at all. -/
abbrev OpTy := List Ty × Option Ty

/-- The operations available somewhere, nearest handler first, each with the
type arguments of its effect. -/
abbrev Row := List (Nat × List Ty)

def Ty.unit : Ty := .tuple []

/-- Everything `a` offers, `b` offers at the same type: code written for `a`
can run where `b` is available. -/
def Row.le (a b : Row) : Prop :=
  ∀ op sig, a.lookup op = some sig → b.lookup op = some sig

/-- One way a function can be used: the types of what it captured, of its
parameters and of its result, and the operations it may perform. -/
structure FnSig where
  caps : List Ty
  params : List Ty
  ret : Ty
  eff : Row

/-- What a program declares: the signatures of its functions, the fields of its
data constructors and the types of its operations. -/
structure Ctx where
  fnSig : Nat → FnSig → Prop
  /-- The type of operation `op` when its effect is used at `args`. -/
  opSig : (op : Nat) → (args : List Ty) → Option OpTy
  /-- The types whose values may be used any number of times. A context that
  calls every type duplicable imposes no ownership discipline. -/
  dup : Ty → Prop
  /-- The field types of constructor `tag` when it builds a value of declared
  type `name` applied to `args`. -/
  ctorFields : (tag name : Nat) → (args : List Ty) → Option (List Ty)

/-- Constructor `tag` builds a value of type `T` from fields of types `Fs`. Tag
zero is the tuple; every other tag belongs to a declared type. -/
def CtorOf (Δ : Ctx) (tag : Nat) (T : Ty) (Fs : List Ty) : Prop :=
  (tag = 0 ∧ T = .tuple Fs)
    ∨ (tag ≠ 0 ∧ ∃ name args, T = .data name args ∧ Δ.ctorFields tag name args = some Fs)

theorem CtorOf.unique {Δ : Ctx} {tag : Nat} {T : Ty} {Fs Fs' : List Ty}
    (h : CtorOf Δ tag T Fs) (h' : CtorOf Δ tag T Fs') : Fs = Fs' := by
  rcases h with ⟨h0, hT⟩ | ⟨h0, name, args, hT, hF⟩
  · rcases h' with ⟨_, hT'⟩ | ⟨h0', _⟩
    · rw [hT] at hT'
      exact Ty.tuple.inj hT'
    · exact absurd h0 h0'
  · rcases h' with ⟨h0', _⟩ | ⟨_, name', args', hT', hF'⟩
    · exact absurd h0' h0
    · rw [hT] at hT'
      obtain ⟨rfl, rfl⟩ := Ty.data.inj hT'
      rw [hF] at hF'
      exact Option.some.inj hF'

/-- Two lists related item by item. -/
inductive All₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : All₂ R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      R a b → All₂ R as bs → All₂ R (a :: as) (b :: bs)

/-- The types of the locals of an activation, oldest first. -/
abbrev TEnv := List Ty

inductive HasAtom (Γ : TEnv) : Atom → Ty → Prop where
  | var {i : Nat} {τ : Ty} : Γ[i]? = some τ → HasAtom Γ (.var i) τ
  | int {n : Int} : HasAtom Γ (.int n) .int

abbrev HasAtoms (Γ : TEnv) : List Atom → List Ty → Prop := All₂ (HasAtom Γ)

/-- The type found by following a field path from a type. A field can be read
without a test from a tuple, and from a declared type all of whose constructors
have the same fields. -/
inductive PlaceOk (Δ : Ctx) : Ty → List Nat → Ty → Prop where
  | here {τ : Ty} : PlaceOk Δ τ [] τ
  | tuple {Fs : List Ty} {i : Nat} {path : List Nat} {σ τ : Ty} :
      Fs[i]? = some σ → PlaceOk Δ σ path τ → PlaceOk Δ (.tuple Fs) (i :: path) τ
  | field {name : Nat} {args Fs : List Ty} {i : Nat} {path : List Nat} {σ τ : Ty} :
      (∀ tag Fs', CtorOf Δ tag (.data name args) Fs' → Fs' = Fs) → Fs[i]? = some σ →
      PlaceOk Δ σ path τ → PlaceOk Δ (.data name args) (i :: path) τ

/-! ## The locals a computation mentions -/

def atomVars : List Atom → List Nat
  | [] => []
  | .var i :: as => i :: atomVars as
  | .int _ :: as => atomVars as

/-- Every local a control-free computation mentions. -/
def rhsVars : Rhs → List Nat
  | .atom a => atomVars [a]
  | .prim _ args => atomVars args
  | .construct _ args => atomVars args
  | .place pl => [pl.var]
  | .closure _ captures => atomVars captures

/-- The locals whose values a control-free computation moves into its result.
Arithmetic and reading a field copy; they move nothing. -/
def rhsMoves : Rhs → List Nat
  | .atom a => atomVars [a]
  | .prim _ _ => []
  | .construct _ args => atomVars args
  | .place _ => []
  | .closure _ captures => atomVars captures

/-- Every local a computation mentions, now or later. A local it does not
mention is dead: whatever it holds will not be used again. -/
def fv : Tm → List Nat
  | .ret a => atomVars [a]
  | .let_ rhs body => rhsVars rhs ++ fv body
  | .call f args body => atomVars (f :: args) ++ fv body
  | .tail f args => atomVars (f :: args)
  | .handle _ _ captures thunk body => atomVars [thunk] ++ (atomVars captures ++ fv body)
  | .handleTail _ _ captures thunk => atomVars (thunk :: captures)
  | .raise _ args => atomVars args
  | .perform _ args body => atomVars args ++ fv body
  | .label thunk body => atomVars [thunk] ++ fv body
  | .labelTail thunk => atomVars [thunk]
  | .guard cleanup thunk body => atomVars [cleanup, thunk] ++ fv body
  | .guardTail cleanup thunk => atomVars [cleanup, thunk]
  | .cancel k body => atomVars [k] ++ fv body
  | .mem _ args body => atomVars args ++ fv body
  | .host _ args body => atomVars args ++ fv body

/-- How often a local occurs in a list of locals. -/
def cnt (i : Nat) : List Nat → Nat
  | [] => 0
  | a :: as => (if a = i then 1 else 0) + cnt i as

/-- The locals in `moved` are moved by a step and those in `rest` are mentioned
after it. A local whose type is not duplicable is moved at most once and is not
mentioned afterwards. -/
def Linear (Δ : Ctx) (Γ : TEnv) (moved rest : List Nat) : Prop :=
  ∀ i τ, Γ[i]? = some τ → ¬ Δ.dup τ → cnt i moved ≤ 1 ∧ (i ∈ moved → i ∉ rest)

def isWild : Pat → Bool
  | .wild => true
  | .bind => false
  | .int _ => false
  | .ctor _ _ => false

inductive HasRhs (Δ : Ctx) (Γ : TEnv) : Rhs → Ty → Prop where
  | atom {a : Atom} {τ : Ty} : HasAtom Γ a τ → HasRhs Δ Γ (.atom a) τ
  | prim {p : Prim} {a b : Atom} :
      HasAtom Γ a .int → HasAtom Γ b .int → HasRhs Δ Γ (.prim p [a, b]) .int
  | construct {tag : Nat} {args : List Atom} {T : Ty} {Fs : List Ty} :
      CtorOf Δ tag T Fs → HasAtoms Γ args Fs → HasRhs Δ Γ (.construct tag args) T
  /-- Reading a field copies it, so the field must be duplicable. -/
  | place {pl : Place} {σ τ : Ty} :
      Γ[pl.var]? = some σ → PlaceOk Δ σ pl.path τ → Δ.dup τ → HasRhs Δ Γ (.place pl) τ
  /-- A function that captured something that cannot be duplicated can itself
  be called only once. -/
  | closure {fn : Nat} {captures : List Atom} {sig : FnSig} {once : Bool} :
      Δ.fnSig fn sig → HasAtoms Γ captures sig.caps →
      (once = false → ∀ c, c ∈ sig.caps → Δ.dup c) →
      HasRhs Δ Γ (.closure fn captures) (.fn sig.params sig.ret sig.eff once)

mutual

/-- A pattern against a type, and the types of what it binds, in binder order. -/
inductive PatOk (Δ : Ctx) : Pat → Ty → List Ty → Prop where
  | wild {τ : Ty} : PatOk Δ .wild τ []
  | bind {τ : Ty} : PatOk Δ .bind τ [τ]
  | int {n : Int} : PatOk Δ (.int n) .int []
  | ctor {tag : Nat} {ps : List Pat} {T : Ty} {Fs Bs : List Ty} :
      CtorOf Δ tag T Fs → PatsOk Δ ps Fs Bs → PatOk Δ (.ctor tag ps) T Bs

inductive PatsOk (Δ : Ctx) : List Pat → List Ty → List Ty → Prop where
  | nil : PatsOk Δ [] [] []
  | cons {p : Pat} {ps : List Pat} {τ : Ty} {τs B Bs : List Ty} :
      PatOk Δ p τ B → PatsOk Δ ps τs Bs → PatsOk Δ (p :: ps) (τ :: τs) (B ++ Bs)

end

/-- The functions serving a handler's operations, against the type each
operation is declared to have. A resumptive operation's function also receives
the resumption, which can be called once, resumes with the operation's result
type and yields what the handler yields, where the handler was installed. -/
inductive ArmsOk (Δ : Ctx) (Cs : List Ty) (ρ : Ty) (ε : Row) : List (Nat × Nat) → Row → Prop where
  | nil : ArmsOk Δ Cs ρ ε [] []
  | terminal {op arm : Nat} {targs Ps : List Ty} {εa : Row} {ops : List (Nat × Nat)} {H : Row} :
      Δ.opSig op targs = some (Ps, none) → Δ.fnSig arm ⟨Cs, Ps, ρ, εa⟩ → Row.le εa ε →
      ArmsOk Δ Cs ρ ε ops H → ArmsOk Δ Cs ρ ε ((op, arm) :: ops) ((op, targs) :: H)
  | resumptive {op arm : Nat} {targs Ps : List Ty} {o : Ty} {εa : Row}
      {ops : List (Nat × Nat)} {H : Row} :
      Δ.opSig op targs = some (Ps, some o) →
      Δ.fnSig arm ⟨Cs, Ps ++ [.fn [o] ρ ε true], ρ, εa⟩ →
      Row.le εa ε → ArmsOk Δ Cs ρ ε ops H →
      ArmsOk Δ Cs ρ ε ((op, arm) :: ops) ((op, targs) :: H)

/-- A handler whose functions share captures of types `Cs`. It handles a
computation yielding `σ`, itself yields `ρ`, gives the operations in `H` their
types, and runs where `ε` is available. Its functions can run many times with
the same captures, so the captures are duplicable. -/
structure HandlerOk (Δ : Ctx) (Cs : List Ty) (ret : Nat) (ops : List (Nat × Nat))
    (σ ρ : Ty) (H ε : Row) : Prop where
  ret : ∃ εr, Δ.fnSig ret ⟨Cs, [σ], ρ, εr⟩ ∧ Row.le εr ε
  arms : ArmsOk Δ Cs ρ ε ops H
  dup : ∀ c, c ∈ Cs → Δ.dup c

/-- A computation in an activation whose locals have types `Γ`: it gives the
activation a result of type `τ` and may perform the operations in `ε`. -/
inductive HasTm (Δ : Ctx) : TEnv → Tm → Ty → Row → Prop where
  | ret {Γ : TEnv} {a : Atom} {τ : Ty} {ε : Row} : HasAtom Γ a τ → HasTm Δ Γ (.ret a) τ ε
  | let_ {Γ : TEnv} {rhs : Rhs} {body : Tm} {σ τ : Ty} {ε : Row} :
      HasRhs Δ Γ rhs σ → Linear Δ Γ (rhsMoves rhs) (fv body) →
      HasTm Δ (Γ ++ [σ]) body τ ε → HasTm Δ Γ (.let_ rhs body) τ ε
  | call {Γ : TEnv} {f : Atom} {args : List Atom} {body : Tm} {Ps : List Ty} {σ τ : Ty}
      {ε' ε : Row} {once : Bool} :
      HasAtom Γ f (.fn Ps σ ε' once) → HasAtoms Γ args Ps → Row.le ε' ε →
      Linear Δ Γ (atomVars (f :: args)) (fv body) →
      HasTm Δ (Γ ++ [σ]) body τ ε → HasTm Δ Γ (.call f args body) τ ε
  | tail {Γ : TEnv} {f : Atom} {args : List Atom} {Ps : List Ty} {τ : Ty} {ε' ε : Row}
      {once : Bool} :
      HasAtom Γ f (.fn Ps τ ε' once) → HasAtoms Γ args Ps → Row.le ε' ε →
      Linear Δ Γ (atomVars (f :: args)) [] → HasTm Δ Γ (.tail f args) τ ε
  /-- A call that does not return can stand where a result of any type is
  expected, and the code after it can take its result to be of any type. This is
  what lets one label be applied in places that expect different types. -/
  | callNever {Γ : TEnv} {f : Atom} {args : List Atom} {body : Tm} {Ps : List Ty} {σ τ : Ty}
      {ε' ε : Row} {once : Bool} :
      HasAtom Γ f (.fn Ps .never ε' once) → HasAtoms Γ args Ps → Row.le ε' ε →
      Linear Δ Γ (atomVars (f :: args)) (fv body) →
      HasTm Δ (Γ ++ [σ]) body τ ε → HasTm Δ Γ (.call f args body) τ ε
  | tailNever {Γ : TEnv} {f : Atom} {args : List Atom} {Ps : List Ty} {τ : Ty} {ε' ε : Row}
      {once : Bool} :
      HasAtom Γ f (.fn Ps .never ε' once) → HasAtoms Γ args Ps → Row.le ε' ε →
      Linear Δ Γ (atomVars (f :: args)) [] → HasTm Δ Γ (.tail f args) τ ε
  | handle {Γ : TEnv} {ret : Nat} {ops : List (Nat × Nat)} {captures : List Atom}
      {thunk : Atom} {body : Tm} {Cs : List Ty} {σ ρ τ : Ty} {εt H ε : Row} {once : Bool} :
      HasAtom Γ thunk (.fn [] σ εt once) → HasAtoms Γ captures Cs →
      HandlerOk Δ Cs ret ops σ ρ H ε → Row.le εt (H ++ ε) →
      Linear Δ Γ (atomVars [thunk]) (fv body) →
      HasTm Δ (Γ ++ [ρ]) body τ ε → HasTm Δ Γ (.handle ret ops captures thunk body) τ ε
  | handleTail {Γ : TEnv} {ret : Nat} {ops : List (Nat × Nat)} {captures : List Atom}
      {thunk : Atom} {Cs : List Ty} {σ τ : Ty} {εt H ε : Row} {once : Bool} :
      HasAtom Γ thunk (.fn [] σ εt once) → HasAtoms Γ captures Cs →
      HandlerOk Δ Cs ret ops σ τ H ε → Row.le εt (H ++ ε) →
      HasTm Δ Γ (.handleTail ret ops captures thunk) τ ε
  | raise {Γ : TEnv} {op : Nat} {args : List Atom} {targs Ps : List Ty} {τ : Ty} {ε : Row} :
      ε.lookup op = some targs → Δ.opSig op targs = some (Ps, none) → HasAtoms Γ args Ps →
      Linear Δ Γ (atomVars args) [] → HasTm Δ Γ (.raise op args) τ ε
  | perform {Γ : TEnv} {op : Nat} {args : List Atom} {body : Tm} {targs Ps : List Ty}
      {σ τ : Ty} {ε : Row} :
      ε.lookup op = some targs → Δ.opSig op targs = some (Ps, some σ) → HasAtoms Γ args Ps →
      Linear Δ Γ (atomVars args) (fv body) →
      HasTm Δ (Γ ++ [σ]) body τ ε → HasTm Δ Γ (.perform op args body) τ ε
  | label {Γ : TEnv} {thunk : Atom} {body : Tm} {σ ρ τ : Ty} {εl εt ε : Row}
      {once once' : Bool} :
      HasAtom Γ thunk (.fn [.fn [σ] ρ εl once'] σ εt once) → Row.le εt ε →
      Linear Δ Γ (atomVars [thunk]) (fv body) →
      HasTm Δ (Γ ++ [σ]) body τ ε → HasTm Δ Γ (.label thunk body) τ ε
  | labelTail {Γ : TEnv} {thunk : Atom} {ρ τ : Ty} {εl εt ε : Row} {once once' : Bool} :
      HasAtom Γ thunk (.fn [.fn [τ] ρ εl once'] τ εt once) → Row.le εt ε →
      HasTm Δ Γ (.labelTail thunk) τ ε
  /-- A cleanup performs no operations. -/
  | guard {Γ : TEnv} {cleanup thunk : Atom} {body : Tm} {σc σ τ : Ty} {εt ε : Row}
      {once once' : Bool} :
      HasAtom Γ cleanup (.fn [] σc [] once') → HasAtom Γ thunk (.fn [] σ εt once) →
      Row.le εt ε → Linear Δ Γ (atomVars [cleanup, thunk]) (fv body) →
      HasTm Δ (Γ ++ [σ]) body τ ε → HasTm Δ Γ (.guard cleanup thunk body) τ ε
  | guardTail {Γ : TEnv} {cleanup thunk : Atom} {σc τ : Ty} {εt ε : Row} {once once' : Bool} :
      HasAtom Γ cleanup (.fn [] σc [] once') → HasAtom Γ thunk (.fn [] τ εt once) →
      Row.le εt ε → Linear Δ Γ (atomVars [cleanup, thunk]) [] →
      HasTm Δ Γ (.guardTail cleanup thunk) τ ε
  /-- Giving up a callable may run the cleanups of what it captured, among
  whatever that could still perform. -/
  | cancel {Γ : TEnv} {k : Atom} {body : Tm} {σ ρ τ : Ty} {ε' ε : Row} {once : Bool} :
      HasAtom Γ k (.fn [σ] ρ ε' once) → Row.le ε' ε → Linear Δ Γ (atomVars [k]) (fv body) →
      HasTm Δ (Γ ++ [.unit]) body τ ε → HasTm Δ Γ (.cancel k body) τ ε
  | alloc {Γ : TEnv} {a : Atom} {body : Tm} {σ τ : Ty} {ε : Row} :
      HasAtom Γ a σ → Linear Δ Γ (atomVars [a]) (fv body) →
      HasTm Δ (Γ ++ [.ref σ]) body τ ε → HasTm Δ Γ (.mem .alloc [a] body) τ ε
  /-- Reading a cell copies its value, so the value must be duplicable. A value
  that is not is taken out with `swap`. -/
  | load {Γ : TEnv} {a : Atom} {body : Tm} {σ τ : Ty} {ε : Row} :
      HasAtom Γ a (.ref σ) → Δ.dup σ → HasTm Δ (Γ ++ [σ]) body τ ε →
      HasTm Δ Γ (.mem .load [a] body) τ ε
  | store {Γ : TEnv} {a b : Atom} {body : Tm} {σ τ : Ty} {ε : Row} :
      HasAtom Γ a (.ref σ) → HasAtom Γ b σ → Linear Δ Γ (atomVars [b]) (fv body) →
      HasTm Δ (Γ ++ [.unit]) body τ ε → HasTm Δ Γ (.mem .store [a, b] body) τ ε
  | swap {Γ : TEnv} {a b : Atom} {body : Tm} {σ τ : Ty} {ε : Row} :
      HasAtom Γ a (.ref σ) → HasAtom Γ b σ → Linear Δ Γ (atomVars [b]) (fv body) →
      HasTm Δ (Γ ++ [σ]) body τ ε → HasTm Δ Γ (.mem .swap [a, b] body) τ ε
  | free {Γ : TEnv} {a : Atom} {body : Tm} {σ τ : Ty} {ε : Row} :
      HasAtom Γ a (.ref σ) → HasTm Δ (Γ ++ [.unit]) body τ ε →
      HasTm Δ Γ (.mem .free [a] body) τ ε
  | write {Γ : TEnv} {a : Atom} {body : Tm} {σ τ : Ty} {ε : Row} :
      HasAtom Γ a σ → HasTm Δ (Γ ++ [.unit]) body τ ε → HasTm Δ Γ (.host 0 [a] body) τ ε
  | read {Γ : TEnv} {body : Tm} {τ : Ty} {ε : Row} :
      HasTm Δ (Γ ++ [.tuple [.int, .int]]) body τ ε → HasTm Δ Γ (.host 1 [] body) τ ε

/-- A clause at a signature: its patterns fit the parameters, and its body is
typed in `arguments ++ captures ++ pattern bindings`. An argument a pattern
takes apart is used through what the pattern binds, not as a whole as well. -/
def ClauseOk (Δ : Ctx) (sig : FnSig) (c : Clause) : Prop :=
  (∃ Bs, PatsOk Δ c.pats sig.params Bs ∧
    HasTm Δ (sig.params ++ sig.caps ++ Bs) c.body sig.ret sig.eff)
  ∧ ∀ i p, c.pats[i]? = some p → isWild p = false → i ∉ fv c.body

/-- Every clause of a function is typed at a signature. -/
def FnTyped (Δ : Ctx) (sig : FnSig) (F : Fn) : Prop :=
  ∀ c, c ∈ F.clauses → ClauseOk Δ sig c

end Glorious.Typing
