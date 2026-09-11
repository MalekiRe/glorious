import Std

namespace Glorious.Proof

/-- Pointwise list relation, including equality of arities. -/
inductive Forall₂ (relation : α → β → Prop) : List α → List β → Prop where
  | nil : Forall₂ relation [] []
  | cons {a b as bs} : relation a b → Forall₂ relation as bs → Forall₂ relation (a :: as) (b :: bs)

theorem Forall₂.length_eq (proof : Forall₂ relation as bs) : as.length = bs.length := by
  induction proof with
  | nil => rfl
  | cons _ _ ih => simpa using congrArg Nat.succ ih

theorem eq_of_nodup_map {f : α → β} {xs : List α} {a b : α}
    (unique : (xs.map f).Nodup) (left : a ∈ xs) (right : b ∈ xs) (same : f a = f b) : a = b := by
  induction xs with
  | nil => simp at left
  | cons x xs ih =>
    have parts := List.nodup_cons.mp unique
    rcases List.mem_cons.mp left with rfl | tailA
    · rcases List.mem_cons.mp right with rfl | tailB
      · rfl
      · exact False.elim (parts.1 (List.mem_map.mpr ⟨b, tailB, same.symm⟩))
    · rcases List.mem_cons.mp right with rfl | tailB
      · exact False.elim (parts.1 (List.mem_map.mpr ⟨a, tailA, same⟩))
      · exact ih parts.2 tailA tailB

end Glorious.Proof

/-! Language-independent proof infrastructure. A behavior is not the return
value of an analysis algorithm. It is an observation of an unbounded transition
system. In particular, finite prefixes, successful exits, and infinite runs are
separate obligations. This file neither admits an implementation nor supplies
an axiom about one. -/
namespace Glorious.Proof

structure TransitionSystem (Event Result : Type) where
  State : Type
  initial : State → Prop
  step : State → Option Event → State → Prop
  final : State → Result → Prop
  fault : State → Prop

namespace TransitionSystem

inductive Steps (system : TransitionSystem Event Result) :
    system.State → List Event → system.State → Prop where
  | refl (state) : Steps system state [] state
  | silent {a b c events} (first : system.step a none b)
      (rest : Steps system b events c) : Steps system a events c
  | visible {a b c event events} (first : system.step a (some event) b)
      (rest : Steps system b events c) : Steps system a (event :: events) c

def Reachable (system : TransitionSystem Event Result) (state : system.State) : Prop :=
  ∃ initial events, system.initial initial ∧ system.Steps initial events state

def Prefix (system : TransitionSystem Event Result) (events : List Event) : Prop :=
  ∃ initial state, system.initial initial ∧ system.Steps initial events state

def Returns (system : TransitionSystem Event Result) (events : List Event) (result : Result) : Prop :=
  ∃ initial state, system.initial initial ∧ system.Steps initial events state ∧ system.final state result

/-- Infinite execution is not inferred from exhausting a finite evaluator. -/
def Infinite (system : TransitionSystem Event Result)
    (events : Nat → Option Event) : Prop :=
  ∃ states : Nat → system.State,
    system.initial (states 0) ∧ ∀ n, system.step (states n) (events n) (states (n + 1))

def Safe (system : TransitionSystem Event Result) : Prop :=
  ∀ state, system.Reachable state →
    ¬ system.fault state ∧
    ((∃ result, system.final state result) ∨ ∃ event next, system.step state event next)

theorem steps_trans {system : TransitionSystem Event Result}
    {a b c : system.State} {left right : List Event}
    (first : system.Steps a left b) (second : system.Steps b right c) :
    system.Steps a (left ++ right) c := by
  induction first generalizing c right with
  | refl => simpa using second
  | silent first _ ih => exact .silent first (ih second)
  | visible first _ ih => exact .visible first (ih second)

end TransitionSystem

/-- Observational equivalence includes an explicit divergence relation. Silent
administrative steps may differ; neither a stuck target nor an infinite silent
target loop can be justified by the absence of a terminating source result. -/
def SameObservations (left right : Nat → Option Event) : Prop :=
  ∀ trace : List Event,
    (∃ count, (List.range count).filterMap left = trace) ↔
    (∃ count, (List.range count).filterMap right = trace)

structure Preserves (source target : TransitionSystem Event Result) : Prop where
  prefixes : ∀ events, source.Prefix events ↔ target.Prefix events
  returns : ∀ events result, source.Returns events result ↔ target.Returns events result
  divergenceForward : ∀ events, source.Infinite events →
    ∃ matching, target.Infinite matching ∧ SameObservations events matching
  divergenceBackward : ∀ events, target.Infinite events →
    ∃ matching, source.Infinite matching ∧ SameObservations matching events
  safety : source.Safe → target.Safe

namespace Preserves

theorem refl (system : TransitionSystem Event Result) : Preserves system system where
  prefixes _ := Iff.rfl
  returns _ _ := Iff.rfl
  divergenceForward events h := ⟨events, h, fun _ => Iff.rfl⟩
  divergenceBackward events h := ⟨events, h, fun _ => Iff.rfl⟩
  safety h := h

theorem trans (first : Preserves a b) (second : Preserves b c) : Preserves a c where
  prefixes events := (first.prefixes events).trans (second.prefixes events)
  returns events result := (first.returns events result).trans (second.returns events result)
  divergenceForward events h := by
    obtain ⟨middle, hm, same⟩ := first.divergenceForward events h
    obtain ⟨last, hl, same'⟩ := second.divergenceForward middle hm
    exact ⟨last, hl, fun trace => (same trace).trans (same' trace)⟩
  divergenceBackward events h := by
    obtain ⟨middle, hm, same⟩ := second.divergenceBackward events h
    obtain ⟨start, hs, same'⟩ := first.divergenceBackward middle hm
    exact ⟨start, hs, fun trace => (same' trace).trans (same trace)⟩
  safety h := second.safety (first.safety h)

end Preserves

/-- A proved invariant must be established initially and preserved by *every*
semantic transition. Listing a collection of sampled states is not this proof. -/
structure Invariant (system : TransitionSystem Event Result)
    (holds : system.State → Prop) : Prop where
  initial : ∀ state, system.initial state → holds state
  step : ∀ before event after, holds before → system.step before event after → holds after

theorem invariant_reachable (proof : Invariant system holds)
    (reachable : system.Reachable state) : holds state := by
  obtain ⟨initial, events, admitted, path⟩ := reachable
  have run : ∀ a events b, system.Steps a events b → holds a → holds b := by
    intro a events b steps
    induction steps with
    | refl => exact id
    | silent first _ ih => intro start; exact ih (proof.step _ _ _ start first)
    | visible first _ ih => intro start; exact ih (proof.step _ _ _ start first)
  exact run initial events state path (proof.initial initial admitted)

/-- A phase's result is indexed by its exact input. The proof is required at
construction and erased only after kernel checking. -/
structure Certified (input : Input) (Output : Type) (relation : Input → Output → Prop) where
  value : Output
  sound : relation input value

def Certified.compose (first : Certified input Middle left)
    (second : Certified first.value Output right)
    (compose : ∀ a b c, left a b → right b c → whole a c) :
    Certified input Output whole :=
  ⟨second.value, compose input first.value second.value first.sound second.sound⟩

/-- Acceptance is deliberately separate from soundness. A compiler that always
returns an error cannot inhabit this specification for any admitted input. The
bound is existential, so exhausting a particular advertised budget is allowed. -/
def CompleteFor (admitted : Input → Prop) (compile : Nat → Input → Except Error Output) : Prop :=
  ∀ input, admitted input → ∃ budget output, compile budget input = .ok output

end Glorious.Proof
