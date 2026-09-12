import GloriousLanguage.Control

/-! An invocation interval is a restriction of the one executable transition
relation, not execution on a truncated or reconstructed machine. In particular,
the ambient callback frames and their host exposure remain present throughout.
The interval ends before consuming the caller's result continuation or routing
an outward request through a delimiter owned by the caller. -/
namespace Glorious.Language

namespace Execution

theorem Step.not_stopped {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event} {context : Context} {address : Address}
    (step : Step program host before event after) (stopped : before.task = .stopped context address) : False := by
  rcases step with step | step | step | step | step | step <;>
    cases step <;> simp_all only [reduceCtorEq]

end Execution

namespace Contracts

open Kernel Execution

inductive InvocationBoundary where
  | isolated
  | caller (returnTo : Execution.Context) (ambient : List Frame)
  deriving Repr, Inhabited

def InvocationBoundary.ambient : InvocationBoundary → List Frame
  | .isolated => []
  | .caller _ frames => frames

/-- Proper-tail entry inherits the actual outer return continuation. It does
not keep the activation which the machine's `enterTail` rule must retire. -/
def InvocationBoundary.Entry (boundary : InvocationBoundary) (state : State)
    (caller : Execution.Context) (source : EntrySource) (inputs : List InvocationInput) (tail : Bool) : Prop :=
  match boundary with
  | .isolated => tail = false ∧ state.frames = [] ∧ source = .supplied inputs
  | .caller returnTo ambient =>
      (tail = false ∧ returnTo = caller ∧ ambient = state.frames) ∨
      (tail = true ∧ ∃ regions, TailFrames state.frames caller.activation returnTo regions ambient)

theorem tailFrames_suffix {frames : List Frame} {activation : Identity} {caller : Execution.Context}
    {regions : List Identity} {ambient : List Frame} (tail : TailFrames frames activation caller regions ambient) :
    ∃ inner, frames = inner ++ ambient := by
  induction tail with
  | activation => exact ⟨[_],rfl⟩
  | scope _ ih => obtain ⟨inner,rfl⟩ := ih; exact ⟨_ :: inner,rfl⟩
  | label _ ih => obtain ⟨inner,rfl⟩ := ih; exact ⟨_ :: inner,rfl⟩

def InvocationBoundary.Normal (boundary : InvocationBoundary) (state : State) (result : Address) : Prop :=
  match boundary with
  | .isolated => ∃ context, state.task = .stopped context result
  | .caller returnTo ambient => state.task = .yield returnTo result ∧ state.frames = ambient

/-- The interval stops before any caller result continuation is consumed.
An incorrect return context does not count as a normal result; it must fail
progress admission instead of executing the caller inside the callee interval. -/
def InvocationBoundary.Handoff (boundary : InvocationBoundary) (state : State) : Prop :=
  match boundary with
  | .isolated => ∃ context result, state.task = .stopped context result
  | .caller _ ambient => ∃ context result, state.task = .yield context result ∧ state.frames = ambient

/-- The ordinary routing producer selects the first accepting handler. Only
the location of that selected delimiter relative to the saved boundary is new;
there is no second handler matcher and no erasure of foreign barriers. -/
def InvocationBoundary.InternalOperation (boundary : InvocationBoundary) (program : Kernel.Program)
    (state : State) (id : DeclId) (arguments : List Term) (payload : List ResolvedPlace) : Prop :=
  ∃ inner handler owns arm between,
    Routes program state id arguments payload inner handler owns arm (between ++ boundary.ambient)

def InvocationBoundary.InternalLabel (boundary : InvocationBoundary) (state : State) (brand : Identity) : Prop :=
  ∃ inner context region type between,
    LabelRoute state.frames brand inner context region type (between ++ boundary.ambient)

def InvocationBoundary.OutwardOperation (boundary : InvocationBoundary) (program : Kernel.Program)
    (state : State) (id : DeclId) (arguments : List Term) (payload : List ResolvedPlace) : Prop :=
  (∃ context, state.task = .perform context id arguments payload) ∧
    ¬ boundary.InternalOperation program state id arguments payload

def InvocationBoundary.OutwardLabel (boundary : InvocationBoundary) (state : State)
    (brand : Identity) (result : ResolvedPlace) : Prop :=
  (∃ context, state.task = .leave context brand result) ∧ ¬ boundary.InternalLabel state brand

def InvocationBoundary.Inside (boundary : InvocationBoundary) (program : Kernel.Program) (state : State) : Prop :=
  match boundary with
  | .isolated => True
  | .caller _ ambient =>
      (∃ inner, state.frames = inner ++ ambient) ∧
      (¬ boundary.Handoff state) ∧
      (∀ context id arguments payload, state.task = .perform context id arguments payload →
        boundary.InternalOperation program state id arguments payload) ∧
      (∀ context brand result, state.task = .leave context brand result → boundary.InternalLabel state brand)

def InvocationStep (program : Kernel.Program) (host : Foreign.Model) (boundary : InvocationBoundary)
    (before : State) (event : Option Event) (after : State) : Prop :=
  boundary.Inside program before ∧ Step program host before event after

/-- This derived system supplies only an interval guard. It has no independent
entry, evaluator, storage mutation, trace projection, or final-value producer. -/
def InvocationSystem (program : Kernel.Program) (host : Foreign.Model) (boundary : InvocationBoundary) :
    TransitionSystem Event Address where
  State := Execution.State
  initial _ := False
  step := InvocationStep program host boundary
  final := boundary.Normal
  invalid _ := False

abbrev InvocationRun (program : Kernel.Program) (host : Foreign.Model) (boundary : InvocationBoundary) :=
  (InvocationSystem program host boundary).Steps

theorem InvocationRun.execution {program : Kernel.Program} {host : Foreign.Model} {boundary : InvocationBoundary}
    {before after : State} {trace : List Event} (run : InvocationRun program host boundary before trace after) :
    Run program host before trace after := by
  refine TransitionSystem.Steps.rec
    (motive := fun before trace after _ => Run program host before trace after) ?_ ?_ ?_ run
  · intro state
    exact .refl
  · intro before middle after trace step rest ih
    exact .silent step.2 ih
  · intro before middle after event trace step rest ih
    exact .visible step.2 ih

theorem invocation_isolated {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {trace : List Event} (run : Run program host before trace after) :
    InvocationRun program host .isolated before trace after := by
  induction run with
  | refl => exact .refl
  | silent step _ ih => exact .silent ⟨True.intro,step⟩ ih
  | visible step _ ih => exact .visible ⟨True.intro,step⟩ ih

theorem InvocationStep.not_normal {program : Kernel.Program} {host : Foreign.Model} {boundary : InvocationBoundary}
    {before after : State} {event : Option Event} {result : Address}
    (step : InvocationStep program host boundary before event after) (normal : boundary.Normal before result) : False := by
  cases boundary with
  | isolated => obtain ⟨context,stopped⟩ := normal; exact step.2.not_stopped stopped
  | caller returnTo ambient => exact step.1.2.1 ⟨returnTo,result,normal⟩

theorem InvocationStep.not_handoff {program : Kernel.Program} {host : Foreign.Model} {boundary : InvocationBoundary}
    {before after : State} {event : Option Event}
    (step : InvocationStep program host boundary before event after) (handoff : boundary.Handoff before) : False := by
  cases boundary with
  | isolated => obtain ⟨context,result,stopped⟩ := handoff; exact step.2.not_stopped stopped
  | caller returnTo ambient => exact step.1.2.1 handoff

theorem InvocationStep.not_outward_operation {program : Kernel.Program} {host : Foreign.Model}
    {returnTo : Execution.Context} {ambient : List Frame} {before after : State} {event : Option Event}
    {id : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    (step : InvocationStep program host (.caller returnTo ambient) before event after)
    (outward : (InvocationBoundary.caller returnTo ambient).OutwardOperation program before id arguments payload) : False := by
  obtain ⟨⟨context,task⟩,outside⟩ := outward
  exact outside (step.1.2.2.1 context id arguments payload task)

theorem InvocationStep.not_outward_label {program : Kernel.Program} {host : Foreign.Model}
    {returnTo : Execution.Context} {ambient : List Frame} {before after : State} {event : Option Event}
    {brand : Identity} {result : ResolvedPlace}
    (step : InvocationStep program host (.caller returnTo ambient) before event after)
    (outward : (InvocationBoundary.caller returnTo ambient).OutwardLabel before brand result) : False := by
  obtain ⟨⟨context,task⟩,outside⟩ := outward
  exact outside (step.1.2.2.2 context brand result task)

/-- Every actual execution factors at the first interval exit. The suffix is
the original execution, not one replayed against an erased caller stack. This
also covers executions which later happen to re-enter the same boundary. -/
theorem invocation_first_exit {program : Kernel.Program} {host : Foreign.Model} {boundary : InvocationBoundary}
    {before after : State} {trace : List Event} (run : Run program host before trace after) :
    ∃ first last middle, trace = first ++ last ∧
      InvocationRun program host boundary before first middle ∧ Run program host middle last after ∧
      (¬ boundary.Inside program middle ∨ (last = [] ∧ middle = after)) := by
  classical
  induction run with
  | refl => exact ⟨[],[],_,rfl,.refl,.refl,Or.inr ⟨rfl,rfl⟩⟩
  | @silent before next after trace step rest ih =>
    by_cases inside : boundary.Inside program before
    · obtain ⟨first,last,middle,events,initial,rest,exit⟩ := ih
      exact ⟨first,last,middle,events,.silent ⟨inside,step⟩ initial,rest,exit⟩
    · exact ⟨[],trace,before,rfl,.refl,.silent step rest,Or.inl inside⟩
  | @visible before next after event trace step rest ih =>
    by_cases inside : boundary.Inside program before
    · obtain ⟨first,last,middle,events,initial,rest,exit⟩ := ih
      exact ⟨event :: first,last,middle,by simp only [List.cons_append,events],
        .visible ⟨inside,step⟩ initial,rest,exit⟩
    · exact ⟨[],event :: trace,before,rfl,.refl,.visible step rest,Or.inl inside⟩

theorem InvocationRun.prefix {program : Kernel.Program} {host : Foreign.Model} {boundary : InvocationBoundary}
    {states : Nat → State} {events : Nat → Option Event}
    (infinite : ∀ n, InvocationStep program host boundary (states n) (events n) (states (n+1))) (length : Nat) :
    InvocationRun program host boundary (states 0) ((List.range length).filterMap events) (states length) := by
  induction length with
  | zero => exact .refl
  | succ n ih =>
    have step := infinite n
    rw [List.range_succ,List.filterMap_append]
    cases present : events n with
    | none =>
      have one : InvocationRun program host boundary (states n) [] (states (n+1)) :=
        .silent (present ▸ step) .refl
      simpa only [List.filterMap_cons,present,List.filterMap_nil,List.append_nil] using ih.trans one
    | some event =>
      have one : InvocationRun program host boundary (states n) [event] (states (n+1)) :=
        .visible (present ▸ step) .refl
      simpa only [List.filterMap_cons,present,List.filterMap_nil] using ih.trans one

end Contracts
end Glorious.Language
