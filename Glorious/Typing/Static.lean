import Glorious.Typing.Types

/-!
# Typing Core

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

A function's type may also state its environment: the types of what it
captured. Another function written against the same environment can then be
given it, in place of the first. That is how two bodies of which one runs share
what they capture.

Ownership is part of the typing. A callable's type says whether it may be
called once only; a resumption may, and so may a function that captured
something that cannot be duplicated. A value whose type the context does not
call duplicable can be moved once: the rules below require that a local moved
by one step of a computation is not moved twice by it and is not mentioned by
the steps after it.

Regions are part of the typing too. A computation is typed with the regions it
may touch; reading or writing through a reference needs the reference's region
among them, and so does calling a callable for each region it may touch. A
function is polymorphic in regions, though in nothing else: some are fixed when
a closure of it is made, the others chosen at each call. The scope of a cell
gives the callable it runs a region no type outside the scope can mention.
-/

namespace Glorious.Typing

open Core

/-- One way a function can be used: the types of what it captured, of its
parameters and of its result, the operations it may perform and the regions it
may touch. Its types mention `crgns` region variables, fixed when a closure of
it is made, and bind `rgns` regions, chosen at each call. -/
structure FnSig where
  caps : List Ty
  params : List Ty
  ret : Ty
  eff : Row
  crgns : Nat
  rgns : Nat
  acc : List Rgn

/-- The variables a signature's call regions are in the function's body. -/
def FnSig.vars (sig : FnSig) : List Rgn := Rgn.callVars sig.crgns sig.rgns

/-- The type of a closure of a function at a signature, made with the regions `θ`. -/
def FnSig.ty (sig : FnSig) (θ : List Rgn) (once : Bool) (env : Option (List Ty)) : Ty :=
  .fn sig.rgns (sig.params.map (Ty.inst θ)) (sig.ret.inst θ) (sig.eff.inst θ) once env
    (sig.acc.map (Rgn.inst θ))

/-- Whoever may write a region may read it. -/
def closed (l : List Rgn) : Bool :=
  l.all fun x =>
    match x with
    | .wr r => l.contains r
    | _ => true

theorem closed_mem {l : List Rgn} (h : closed l = true) {r : Rgn} (hr : .wr r ∈ l) : r ∈ l := by
  have := List.all_eq_true.mp h _ hr
  simpa using this

/-- A signature mentions no region variable but those fixed when a closure is
made, and its function may read what it may write. -/
def FnSig.wf (sig : FnSig) : Bool :=
  sig.caps.all (Ty.within sig.crgns) && sig.params.all (Ty.within sig.crgns)
    && sig.ret.within sig.crgns && sig.eff.within sig.crgns && sig.acc.all (Rgn.within sig.crgns)
    && closed sig.acc

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
  /-- Whether the region rules are to hold. Without them a reference's region
  means nothing and nothing is shown about how long a cell is used. -/
  regions : Prop
  /-- Whether the rules for borrows are to hold. Without them a lent reference
  is the reference it was lent from, and nothing is shown about who uses a cell
  while it is lent. -/
  loans : Prop

/-- What a context says of a type does not depend on which regions stand for
its region variables. -/
structure Ctx.Stable (Δ : Ctx) : Prop where
  dup : ∀ τ θ, Δ.dup (Ty.inst θ τ) ↔ Δ.dup τ
  ctor : ∀ tag name args θ, Δ.ctorFields tag name (args.map (Ty.inst θ))
    = (Δ.ctorFields tag name args).map (·.map (Ty.inst θ))
  op : ∀ op targs θ, Δ.opSig op (targs.map (Ty.inst θ))
    = (Δ.opSig op targs).map fun x => (x.1.map (Ty.inst θ), x.2.map (Ty.inst θ))

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

/-- Every region of `a` is one of `b`. -/
def Sub (a b : List Rgn) : Prop := ∀ r, r ∈ a → r ∈ b

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
  | .rebind a _ => atomVars [a]

/-- The locals whose values a control-free computation moves into its result.
Arithmetic and reading a field copy; they move nothing. -/
def rhsMoves : Rhs → List Nat
  | .atom a => atomVars [a]
  | .prim _ _ => []
  | .construct _ args => atomVars args
  | .place _ => []
  | .closure _ captures => atomVars captures
  | .rebind a _ => atomVars [a]

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
  | .cell init thunk body => atomVars [init, thunk] ++ fv body
  | .cellTail init thunk => atomVars [init, thunk]
  | .lend _ r thunk pre post body => atomVars (r :: thunk :: pre ++ post) ++ fv body
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

/-- Every field of a value of type `T`, whichever constructor built it, has
type `τ`: such a value can be read at a place found when the program runs. -/
def Uniform (Δ : Ctx) (T τ : Ty) : Prop :=
  ∀ tag Fs, CtorOf Δ tag T Fs → ∀ σ, σ ∈ Fs → σ = τ

/-- After each constructor of `T` comes one that takes a `τ` more. -/
def Grows (Δ : Ctx) (T τ : Ty) : Prop :=
  ∀ tag Fs, CtorOf Δ tag T Fs → CtorOf Δ (tag + 1) T (Fs ++ [τ])

/-- Before each constructor of `T` that takes anything comes one that takes
all but the last. -/
def Shrinks (Δ : Ctx) (T : Ty) : Prop :=
  ∀ tag Fs, CtorOf Δ tag T Fs → Fs ≠ [] → CtorOf Δ (tag - 1) T Fs.dropLast

inductive HasRhs (Δ : Ctx) (Γ : TEnv) : Rhs → Ty → Prop where
  | atom {a : Atom} {τ : Ty} : HasAtom Γ a τ → HasRhs Δ Γ (.atom a) τ
  | prim {p : Prim} {a b : Atom} :
      HasAtom Γ a .int → HasAtom Γ b .int → HasRhs Δ Γ (.prim p [a, b]) .int
  /-- An array is read at a place: a copy of the field, so it is duplicable. -/
  | arrGet {a i : Atom} {T τ : Ty} :
      HasAtom Γ a T → HasAtom Γ i .int → Uniform Δ T τ → Δ.dup τ →
      HasRhs Δ Γ (.prim .arrGet [a, i]) τ
  /-- The array with another value at a place. The array is copied, so it is
  duplicable; and so, being of fields of that type, is the value. -/
  | arrSet {a i v : Atom} {T τ : Ty} :
      HasAtom Γ a T → HasAtom Γ i .int → HasAtom Γ v τ → Uniform Δ T τ → Δ.dup T →
      HasRhs Δ Γ (.prim .arrSet [a, i, v]) T
  | arrLen {a b : Atom} {T σ : Ty} :
      HasAtom Γ a T → HasAtom Γ b σ → HasRhs Δ Γ (.prim .arrLen [a, b]) .int
  | arrPush {a v : Atom} {T τ : Ty} :
      HasAtom Γ a T → HasAtom Γ v τ → Grows Δ T τ → Δ.dup T →
      HasRhs Δ Γ (.prim .arrPush [a, v]) T
  /-- The array without its last element, and the last. -/
  | arrPop {a b : Atom} {T τ σ : Ty} :
      HasAtom Γ a T → HasAtom Γ b σ → Uniform Δ T τ → Shrinks Δ T → Δ.dup (.tuple [T, τ]) →
      HasRhs Δ Γ (.prim .arrPop [a, b]) (.tuple [T, τ])
  | construct {tag : Nat} {args : List Atom} {T : Ty} {Fs : List Ty} :
      CtorOf Δ tag T Fs → HasAtoms Γ args Fs → HasRhs Δ Γ (.construct tag args) T
  /-- Reading a field copies it, so the field must be duplicable. -/
  | place {pl : Place} {σ τ : Ty} :
      Γ[pl.var]? = some σ → PlaceOk Δ σ pl.path τ → Δ.dup τ → HasRhs Δ Γ (.place pl) τ
  /-- A closure is made with regions for those its signature leaves open. A
  function that captured something that cannot be duplicated can itself be
  called only once. -/
  | closure {fn : Nat} {captures : List Atom} {sig : FnSig} {θ : List Rgn} {once : Bool}
      {env : Option (List Ty)} :
      Δ.fnSig fn sig → θ.length = sig.crgns → HasAtoms Γ captures (sig.caps.map (Ty.inst θ)) →
      (once = false → ∀ c, c ∈ sig.caps → Δ.dup c) →
      (∀ Cs, env = some Cs → Cs = sig.caps.map (Ty.inst θ)) →
      HasRhs Δ Γ (.closure fn captures) (sig.ty θ once env)
  /-- A function whose environment is known gives it to another function
  written against the same environment. The first function is given up without
  being called, so what it captured is still owned once. -/
  | rebind {a : Atom} {fn : Nat} {sig : FnSig} {θ : List Rgn} {n : Nat} {Ps : List Ty} {σ : Ty}
      {ε : Row} {acc : List Rgn} {once once' : Bool} {env : Option (List Ty)} :
      HasAtom Γ a (.fn n Ps σ ε once' (some (sig.caps.map (Ty.inst θ))) acc) → Δ.fnSig fn sig →
      θ.length = sig.crgns → (once = false → ∀ c, c ∈ sig.caps → Δ.dup c) →
      (∀ Cs, env = some Cs → Cs = sig.caps.map (Ty.inst θ)) →
      HasRhs Δ Γ (.rebind a fn) (sig.ty θ once env)

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

/-- Function `fn`, with captures of types `Cs`, can be entered with arguments
of types `Ps` and no regions of its own to choose: it gives a `ρ`, performs
within `ε` and touches within `Φ`. This is how a handler's functions and a
cleanup are entered. -/
def Enters (Δ : Ctx) (fn : Nat) (Cs Ps : List Ty) (ρ : Ty) (ε : Row) (Φ : List Rgn) : Prop :=
  ∃ sig θ, Δ.fnSig fn sig ∧ θ.length = sig.crgns ∧ sig.rgns = 0
    ∧ Cs = sig.caps.map (Ty.inst θ) ∧ Ps = sig.params.map (Ty.inst θ) ∧ ρ = sig.ret.inst θ
    ∧ Row.le (sig.eff.inst θ) ε ∧ Sub (sig.acc.map (Rgn.inst θ)) Φ
    ∧ (Δ.loans → (sig.acc.map (Rgn.inst θ)).Nodup)

/-- The functions serving a handler's operations, against the type each
operation is declared to have. A resumptive operation's function also receives
the resumption, which can be called once, resumes with the operation's result
type and yields what the handler yields, where the handler was installed. The
resumption touches what the handled computation and the handler may. -/
inductive ArmsOk (Δ : Ctx) (Cs : List Ty) (ρ : Ty) (ε : Row) (Φ : List Rgn) :
    List (Nat × Nat) → Row → Prop where
  | nil : ArmsOk Δ Cs ρ ε Φ [] []
  | terminal {op arm : Nat} {targs Ps : List Ty} {ops : List (Nat × Nat)} {H : Row} :
      Δ.opSig op targs = some (Ps, none) → Enters Δ arm Cs Ps ρ ε Φ →
      ArmsOk Δ Cs ρ ε Φ ops H → ArmsOk Δ Cs ρ ε Φ ((op, arm) :: ops) ((op, targs) :: H)
  | resumptive {op arm : Nat} {targs Ps : List Ty} {o : Ty} {ops : List (Nat × Nat)} {H : Row} :
      Δ.opSig op targs = some (Ps, some o) →
      Enters Δ arm Cs (Ps ++ [.fn 0 [o] ρ ε true none Φ]) ρ ε Φ →
      ArmsOk Δ Cs ρ ε Φ ops H → ArmsOk Δ Cs ρ ε Φ ((op, arm) :: ops) ((op, targs) :: H)

/-- A handler whose functions share captures of types `Cs`. It handles a
computation yielding `σ`, itself yields `ρ`, gives the operations in `H` their
types, runs where `ε` is available and touches within `Φ`. Its functions can
run many times with the same captures, so the captures are duplicable. -/
structure HandlerOk (Δ : Ctx) (Cs : List Ty) (ret : Nat) (ops : List (Nat × Nat))
    (σ ρ : Ty) (H ε : Row) (Φ : List Rgn) : Prop where
  ret : Enters Δ ret Cs [σ] ρ ε Φ
  arms : ArmsOk Δ Cs ρ ε Φ ops H
  dup : ∀ c, c ∈ Cs → Δ.dup c

/-! ## What each form needs

The conditions on a form of computation, apart from what it needs of the
ownership rules, are gathered under names: a proof that uses one condition
says which, and is untouched when another is added. Each says which rules it
belongs to: the typing, the region rules, or the rules for borrows. -/

/-- A call chooses the regions the callable binds, and needs every region the
callable may touch. -/
structure CallOk (Δ : Ctx) (ϕ : List Rgn) (Γ : TEnv) (f : Atom) (args : List Atom) (n : Nat)
    (rs : List Rgn) (Ps : List Ty) (σ : Ty) (ε' ε : Row) (once : Bool) (env : Option (List Ty))
    (acc : List Rgn) : Prop where
  callee : HasAtom Γ f (.fn n Ps σ ε' once env acc)
  len : rs.length = n
  argsOk : HasAtoms Γ args (Ps.map (Ty.open rs))
  row : Row.le (ε'.open rs) ε
  /-- Regions: the code may touch what the callable does. -/
  touches : Sub (acc.map (Rgn.openAt 0 rs)) ϕ
  /-- Borrows: the regions the callable touches are different regions here. -/
  apart : Δ.loans → (acc.map (Rgn.openAt 0 rs)).Nodup

/-- The handled computation and the handler's functions touch within `Φ`,
which the code installing the handler may touch. -/
structure InstallOk (Δ : Ctx) (ϕ : List Rgn) (Γ : TEnv) (ret : Nat) (ops : List (Nat × Nat))
    (captures : List Atom) (thunk : Atom) (Cs : List Ty) (σ ρ : Ty) (εt H ε : Row) (once : Bool)
    (env : Option (List Ty)) (acc Φ : List Rgn) : Prop where
  thunk : HasAtom Γ thunk (.fn 0 [] σ εt once env acc)
  caps : HasAtoms Γ captures Cs
  handler : HandlerOk Δ Cs ret ops σ ρ H ε Φ
  row : Row.le εt (H ++ ε)
  /-- Regions. -/
  touches : Sub acc Φ
  within : Sub Φ ϕ
  /-- Borrows. -/
  apart : Δ.loans → acc.Nodup

/-- A label lives for the scope it is made for. The callable run in that
scope is given the label. Under the region rules the callable is polymorphic
in the scope's region, which the label's type says applying it touches, and
neither what the scope gives nor what it performs mentions that region: so
nothing typed outside the scope can apply the label. -/
structure LabelOk (Δ : Ctx) (ϕ : List Rgn) (Γ : TEnv) (thunk : Atom) (n : Nat) (σ ρ : Ty)
    (εl εt ε : Row) (once once' : Bool) (env : Option (List Ty)) (accl acc : List Rgn) :
    Prop where
  thunk : HasAtom Γ thunk (.fn n [.fn 0 [σ] ρ εl once' none accl] σ εt once env acc)
  lcGiven : σ.lc = true
  lcRow : εt.lc = true
  arity : n = 0 ∨ n = 1
  /-- Regions. -/
  region : Δ.regions → n = 1 ∧ .bound 0 ∈ accl
  touches : ∀ x, x ∈ acc → (n = 1 ∧ x = .bound 0) ∨ (x.free = true ∧ x ∈ ϕ)
  /-- Borrows. -/
  apart : Δ.loans → acc.Nodup
  row : Row.le εt ε

/-- A cleanup performs no operations. -/
structure GuardOk (Δ : Ctx) (ϕ : List Rgn) (Γ : TEnv) (cleanup thunk : Atom) (σc σ : Ty)
    (εt ε : Row) (once once' : Bool) (env env' : Option (List Ty)) (accc acc : List Rgn) :
    Prop where
  cleanup : HasAtom Γ cleanup (.fn 0 [] σc [] once' env' accc)
  thunk : HasAtom Γ thunk (.fn 0 [] σ εt once env acc)
  row : Row.le εt ε
  /-- Regions. -/
  cleanupTouches : Sub accc ϕ
  touches : Sub acc ϕ
  /-- Borrows. -/
  apart : Δ.loans → accc.Nodup ∧ acc.Nodup

/-- A cell lives for the scope it is made for. The callable run in that scope
is given a reference to the cell, which holds `init` to begin with. Under the
region rules the callable is polymorphic in the cell's region, and neither
what it gives back, nor what it performs, nor what the cell holds mentions
that region: so nothing typed outside the scope can. The callable may read
and write the cell. -/
structure CellOk (Δ : Ctx) (ϕ : List Rgn) (Γ : TEnv) (init thunk : Atom) (n : Nat) (r : Rgn)
    (σ ρ : Ty) (εt ε : Row) (once : Bool) (env : Option (List Ty)) (acc : List Rgn) : Prop where
  init : HasAtom Γ init σ
  thunk : HasAtom Γ thunk (.fn n [.ref r σ] ρ εt once env acc)
  lcHeld : σ.lc = true
  lcGiven : ρ.lc = true
  lcRow : εt.lc = true
  arity : n = 0 ∨ (n = 1 ∧ r = .bound 0)
  /-- Regions. -/
  region : Δ.regions → n = 1 ∧ r = .bound 0
  touches : ∀ x, x ∈ acc →
    (n = 1 ∧ (x = .bound 0 ∨ x = .wr (.bound 0))) ∨ (x.free = true ∧ x ∈ ϕ)
  /-- Borrows. -/
  apart : Δ.loans → acc.Nodup
  row : Row.le εt ε

/-- Lending a reference calls a callable with a reference to the same cell,
among the arguments `pre` and `post`, for the scope. Under the rules for
borrows the callable is polymorphic in the region of the borrow, which no other
argument's type mentions, and the callable may not, meanwhile, write what was
lent, nor read it if it was lent for writing: it has the borrow instead. Lending
for writing needs leave to write. And the callable performs no operation it
does not handle itself: so the scope is never among the frames a resumption
captures, and no handler runs while the borrow is set aside. -/
structure LendOk (Δ : Ctx) (ϕ : List Rgn) (Γ : TEnv) (uniq : Bool) (r thunk : Atom)
    (pre post : List Atom) (n : Nat) (ρ κ : Rgn) (σ ρt : Ty) (Pre Post : List Ty) (εt ε : Row)
    (once : Bool) (env : Option (List Ty)) (acc : List Rgn) : Prop where
  ref : HasAtom Γ r (.ref ρ σ)
  thunk : HasAtom Γ thunk (.fn n (Pre ++ .ref κ σ :: Post) ρt εt once env acc)
  before : HasAtoms Γ pre Pre
  after : HasAtoms Γ post Post
  lcArgs : ∀ t, t ∈ Pre ++ Post → t.lc = true
  lcHeld : σ.lc = true
  lcGiven : ρt.lc = true
  lcRow : εt.lc = true
  arity : (n = 0 ∧ κ = ρ) ∨ (n = 1 ∧ κ = .bound 0)
  /-- Regions. -/
  region : Δ.regions → ρ ∈ ϕ
  /-- Borrows. -/
  loan : Δ.loans → n = 1 ∧ ρ ∈ ϕ ∧ (uniq = true → .wr ρ ∈ ϕ) ∧ acc.Nodup ∧ εt = []
  touches : ∀ x, x ∈ acc → (n = 1 ∧ (x = .bound 0 ∨ (uniq = true ∧ x = .wr (.bound 0))))
    ∨ (x.free = true ∧ x ∈ ϕ ∧ (Δ.loans → x ≠ .wr ρ ∧ (uniq = true → x ≠ ρ)))
  row : Row.le εt ε

/-- Writing a cell. Under the region rules it needs the cell's region; under
the rules for borrows, leave to write it. -/
structure WriteOk (Δ : Ctx) (ϕ : List Rgn) (Γ : TEnv) (a b : Atom) (r : Rgn) (σ : Ty) :
    Prop where
  ref : HasAtom Γ a (.ref r σ)
  /-- Regions. -/
  region : Δ.regions → r ∈ ϕ
  /-- Borrows. -/
  write : Δ.loans → .wr r ∈ ϕ
  value : HasAtom Γ b σ

/-- A computation in an activation whose locals have types `Γ`: it gives the
activation a result of type `τ`, may perform the operations in `ε`, and may
touch the regions in `ϕ`. What a form needs of the ownership rules is said
beside it: the locals it moves are moved once, and not mentioned afterwards. -/
inductive HasTm (Δ : Ctx) (ϕ : List Rgn) : TEnv → Tm → Ty → Row → Prop where
  | ret {Γ : TEnv} {a : Atom} {τ : Ty} {ε : Row} : HasAtom Γ a τ → HasTm Δ ϕ Γ (.ret a) τ ε
  | let_ {Γ : TEnv} {rhs : Rhs} {body : Tm} {σ τ : Ty} {ε : Row} :
      HasRhs Δ Γ rhs σ → Linear Δ Γ (rhsMoves rhs) (fv body) →
      HasTm Δ ϕ (Γ ++ [σ]) body τ ε → HasTm Δ ϕ Γ (.let_ rhs body) τ ε
  | call {Γ : TEnv} {f : Atom} {args : List Atom} {body : Tm} {n : Nat} {rs : List Rgn}
      {Ps : List Ty} {σ τ : Ty} {ε' ε : Row} {once : Bool} {env : Option (List Ty)}
      {acc : List Rgn} :
      CallOk Δ ϕ Γ f args n rs Ps σ ε' ε once env acc →
      Linear Δ Γ (atomVars (f :: args)) (fv body) →
      HasTm Δ ϕ (Γ ++ [σ.open rs]) body τ ε → HasTm Δ ϕ Γ (.call f args body) τ ε
  | tail {Γ : TEnv} {f : Atom} {args : List Atom} {n : Nat} {rs : List Rgn} {Ps : List Ty}
      {σ τ : Ty} {ε' ε : Row} {once : Bool} {env : Option (List Ty)} {acc : List Rgn} :
      CallOk Δ ϕ Γ f args n rs Ps σ ε' ε once env acc → σ.open rs = τ →
      Linear Δ Γ (atomVars (f :: args)) [] →
      HasTm Δ ϕ Γ (.tail f args) τ ε
  /-- A call that does not return can stand where a result of any type is
  expected, and the code after it can take its result to be of any type. This is
  what lets one label be applied in places that expect different types. -/
  | callNever {Γ : TEnv} {f : Atom} {args : List Atom} {body : Tm} {n : Nat} {rs : List Rgn}
      {Ps : List Ty} {σ τ : Ty} {ε' ε : Row} {once : Bool} {env : Option (List Ty)}
      {acc : List Rgn} :
      CallOk Δ ϕ Γ f args n rs Ps .never ε' ε once env acc →
      Linear Δ Γ (atomVars (f :: args)) (fv body) →
      HasTm Δ ϕ (Γ ++ [σ]) body τ ε → HasTm Δ ϕ Γ (.call f args body) τ ε
  | tailNever {Γ : TEnv} {f : Atom} {args : List Atom} {n : Nat} {rs : List Rgn} {Ps : List Ty}
      {τ : Ty} {ε' ε : Row} {once : Bool} {env : Option (List Ty)} {acc : List Rgn} :
      CallOk Δ ϕ Γ f args n rs Ps .never ε' ε once env acc →
      Linear Δ Γ (atomVars (f :: args)) [] →
      HasTm Δ ϕ Γ (.tail f args) τ ε
  | handle {Γ : TEnv} {ret : Nat} {ops : List (Nat × Nat)} {captures : List Atom}
      {thunk : Atom} {body : Tm} {Cs : List Ty} {σ ρ τ : Ty} {εt H ε : Row} {once : Bool}
      {env : Option (List Ty)} {acc Φ : List Rgn} :
      InstallOk Δ ϕ Γ ret ops captures thunk Cs σ ρ εt H ε once env acc Φ →
      Linear Δ Γ (atomVars [thunk]) (fv body) →
      HasTm Δ ϕ (Γ ++ [ρ]) body τ ε → HasTm Δ ϕ Γ (.handle ret ops captures thunk body) τ ε
  | handleTail {Γ : TEnv} {ret : Nat} {ops : List (Nat × Nat)} {captures : List Atom}
      {thunk : Atom} {Cs : List Ty} {σ τ : Ty} {εt H ε : Row} {once : Bool}
      {env : Option (List Ty)} {acc Φ : List Rgn} :
      InstallOk Δ ϕ Γ ret ops captures thunk Cs σ τ εt H ε once env acc Φ →
      HasTm Δ ϕ Γ (.handleTail ret ops captures thunk) τ ε
  | raise {Γ : TEnv} {op : Nat} {args : List Atom} {targs Ps : List Ty} {τ : Ty} {ε : Row} :
      ε.lookup op = some targs → Δ.opSig op targs = some (Ps, none) → HasAtoms Γ args Ps →
      Linear Δ Γ (atomVars args) [] → HasTm Δ ϕ Γ (.raise op args) τ ε
  | perform {Γ : TEnv} {op : Nat} {args : List Atom} {body : Tm} {targs Ps : List Ty}
      {σ τ : Ty} {ε : Row} :
      ε.lookup op = some targs → Δ.opSig op targs = some (Ps, some σ) → HasAtoms Γ args Ps →
      Linear Δ Γ (atomVars args) (fv body) →
      HasTm Δ ϕ (Γ ++ [σ]) body τ ε → HasTm Δ ϕ Γ (.perform op args body) τ ε
  | label {Γ : TEnv} {thunk : Atom} {body : Tm} {n : Nat} {σ ρ τ : Ty} {εl εt ε : Row}
      {once once' : Bool} {env : Option (List Ty)} {accl acc : List Rgn} :
      LabelOk Δ ϕ Γ thunk n σ ρ εl εt ε once once' env accl acc →
      Linear Δ Γ (atomVars [thunk]) (fv body) →
      HasTm Δ ϕ (Γ ++ [σ]) body τ ε → HasTm Δ ϕ Γ (.label thunk body) τ ε
  | labelTail {Γ : TEnv} {thunk : Atom} {n : Nat} {ρ τ : Ty} {εl εt ε : Row}
      {once once' : Bool} {env : Option (List Ty)} {accl acc : List Rgn} :
      LabelOk Δ ϕ Γ thunk n τ ρ εl εt ε once once' env accl acc →
      HasTm Δ ϕ Γ (.labelTail thunk) τ ε
  | guard {Γ : TEnv} {cleanup thunk : Atom} {body : Tm} {σc σ τ : Ty} {εt ε : Row}
      {once once' : Bool} {env env' : Option (List Ty)} {accc acc : List Rgn} :
      GuardOk Δ ϕ Γ cleanup thunk σc σ εt ε once once' env env' accc acc →
      Linear Δ Γ (atomVars [cleanup, thunk]) (fv body) →
      HasTm Δ ϕ (Γ ++ [σ]) body τ ε → HasTm Δ ϕ Γ (.guard cleanup thunk body) τ ε
  | guardTail {Γ : TEnv} {cleanup thunk : Atom} {σc τ : Ty} {εt ε : Row} {once once' : Bool}
      {env env' : Option (List Ty)} {accc acc : List Rgn} :
      GuardOk Δ ϕ Γ cleanup thunk σc τ εt ε once once' env env' accc acc →
      Linear Δ Γ (atomVars [cleanup, thunk]) [] →
      HasTm Δ ϕ Γ (.guardTail cleanup thunk) τ ε
  /-- Giving up a callable may run the cleanups of what it captured, among
  whatever that could still perform and touch. -/
  | cancel {Γ : TEnv} {k : Atom} {body : Tm} {n : Nat} {σ ρ τ : Ty} {ε' ε : Row} {once : Bool}
      {env : Option (List Ty)} {acc : List Rgn} :
      HasAtom Γ k (.fn n [σ] ρ ε' once env acc) → Row.le ε' ε → Sub acc ϕ →
      Linear Δ Γ (atomVars [k]) (fv body) →
      HasTm Δ ϕ (Γ ++ [.unit]) body τ ε → HasTm Δ ϕ Γ (.cancel k body) τ ε
  | cell {Γ : TEnv} {init thunk : Atom} {body : Tm} {n : Nat} {r : Rgn} {σ ρ τ : Ty}
      {εt ε : Row} {once : Bool} {env : Option (List Ty)} {acc : List Rgn} :
      CellOk Δ ϕ Γ init thunk n r σ ρ εt ε once env acc →
      Linear Δ Γ (atomVars [init, thunk]) (fv body) →
      HasTm Δ ϕ (Γ ++ [ρ]) body τ ε → HasTm Δ ϕ Γ (.cell init thunk body) τ ε
  | cellTail {Γ : TEnv} {init thunk : Atom} {n : Nat} {r : Rgn} {σ τ : Ty} {εt ε : Row}
      {once : Bool} {env : Option (List Ty)} {acc : List Rgn} :
      CellOk Δ ϕ Γ init thunk n r σ τ εt ε once env acc →
      Linear Δ Γ (atomVars [init, thunk]) [] →
      HasTm Δ ϕ Γ (.cellTail init thunk) τ ε
  | lend {Γ : TEnv} {uniq : Bool} {r thunk : Atom} {pre post : List Atom} {body : Tm} {n : Nat}
      {ρ κ : Rgn} {σ ρt τ : Ty} {Pre Post : List Ty} {εt ε : Row} {once : Bool}
      {env : Option (List Ty)} {acc : List Rgn} :
      LendOk Δ ϕ Γ uniq r thunk pre post n ρ κ σ ρt Pre Post εt ε once env acc →
      Linear Δ Γ (atomVars (thunk :: pre ++ post)) (fv body) →
      HasTm Δ ϕ (Γ ++ [ρt]) body τ ε → HasTm Δ ϕ Γ (.lend uniq r thunk pre post body) τ ε
  /-- Reading a cell copies its value, so the value must be duplicable. A value
  that is not is taken out with `swap`. Under the region rules, reading a cell
  needs its region. -/
  | load {Γ : TEnv} {a : Atom} {body : Tm} {r : Rgn} {σ τ : Ty} {ε : Row} :
      HasAtom Γ a (.ref r σ) → (Δ.regions → r ∈ ϕ) → Δ.dup σ →
      HasTm Δ ϕ (Γ ++ [σ]) body τ ε → HasTm Δ ϕ Γ (.mem .load [a] body) τ ε
  | store {Γ : TEnv} {a b : Atom} {body : Tm} {r : Rgn} {σ τ : Ty} {ε : Row} :
      WriteOk Δ ϕ Γ a b r σ → Linear Δ Γ (atomVars [b]) (fv body) →
      HasTm Δ ϕ (Γ ++ [.unit]) body τ ε → HasTm Δ ϕ Γ (.mem .store [a, b] body) τ ε
  | swap {Γ : TEnv} {a b : Atom} {body : Tm} {r : Rgn} {σ τ : Ty} {ε : Row} :
      WriteOk Δ ϕ Γ a b r σ → Linear Δ Γ (atomVars [b]) (fv body) →
      HasTm Δ ϕ (Γ ++ [σ]) body τ ε → HasTm Δ ϕ Γ (.mem .swap [a, b] body) τ ε
  /-- Asking a cell which constructor built what it holds, or a field of it:
  nothing is copied, so the value may be anything. Under the region rules it
  needs the cell's region, as reading does. -/
  | tag {Γ : TEnv} {a : Atom} {path : List Atom} {body : Tm} {r : Rgn} {σ τ : Ty} {ε : Row}
      {Ps : List Ty} :
      HasAtom Γ a (.ref r σ) → (Δ.regions → r ∈ ϕ) → HasAtoms Γ path Ps →
      HasTm Δ ϕ (Γ ++ [.int]) body τ ε → HasTm Δ ϕ Γ (.mem .tag (a :: path) body) τ ε
  | write {Γ : TEnv} {a : Atom} {body : Tm} {σ τ : Ty} {ε : Row} :
      HasAtom Γ a σ → HasTm Δ ϕ (Γ ++ [.unit]) body τ ε → HasTm Δ ϕ Γ (.host 0 [a] body) τ ε
  | read {Γ : TEnv} {body : Tm} {τ : Ty} {ε : Row} :
      HasTm Δ ϕ (Γ ++ [.tuple [.int, .int]]) body τ ε → HasTm Δ ϕ Γ (.host 1 [] body) τ ε

/-- A clause at a signature: its patterns fit the parameters, and its body is
typed in `arguments ++ captures ++ pattern bindings`, with the signature's call
regions as variables. An argument a pattern takes apart is used through what
the pattern binds, not as a whole as well. -/
def ClauseOk (Δ : Ctx) (sig : FnSig) (c : Clause) : Prop :=
  (∃ Bs, PatsOk Δ c.pats (sig.params.map (Ty.open sig.vars)) Bs ∧
    HasTm Δ (sig.acc.map (Rgn.openAt 0 sig.vars))
      (sig.params.map (Ty.open sig.vars) ++ sig.caps ++ Bs) c.body (sig.ret.open sig.vars)
      (sig.eff.open sig.vars))
  ∧ ∀ i p, c.pats[i]? = some p → isWild p = false → i ∉ fv c.body

/-- Every clause of a function is typed at a signature. -/
def FnTyped (Δ : Ctx) (sig : FnSig) (F : Fn) : Prop :=
  ∀ c, c ∈ F.clauses → ClauseOk Δ sig c

end Glorious.Typing
