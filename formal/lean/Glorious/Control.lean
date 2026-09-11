import Glorious.Quantity

/-! Control composition, language §§5–12. State travels with *every* outcome.
    A normal value's tag never resets it. Guards name result origins and
    nominal variants, not source control-function spellings. -/
namespace Glorious

structure DeclId where
  packageId : Nat
  localId : Nat
  deriving DecidableEq, Repr, BEq

structure Brand where
  binder : DeclId
  generation : Nat
  deriving DecidableEq, Repr, BEq

structure ResultOrigin where
  invocation : Nat
  projection : List Nat
  deriving DecidableEq, Repr, BEq

structure TagGuard where
  origin : ResultOrigin
  constructor : DeclId
  positive : Bool
  deriving DecidableEq, Repr, BEq

inductive UnknownReason where
  | missingContract
  | opaqueInvocation
  | resourceLimit
  | unsolvedObligation
  deriving DecidableEq, Repr, BEq

inductive Fatal where
  | abort
  | primitiveFault
  | brokenHostContract
  | resourceEnforcement
  | runtimeFault
  deriving DecidableEq, Repr, BEq

/-- The type parameter is the normal result only; nonlocal payload ownership
    is retained by the surrounding resource state, never silently erased. -/
inductive Outcome (α : Type) where
  | normal (value : α)
  | transfer (target : Brand)
  | terminalEffect (operation : DeclId)
  | suspended (operation : DeclId)
  | cancelled
  | diverged
  | fatal (reason : Fatal)
  | unknown (reason : UnknownReason)
  deriving Repr

namespace Outcome

/-- Only normal completion executes a strict suffix. -/
def bind (o : Outcome α) (f : α → Outcome β) : Outcome β :=
  match o with
  | .normal a => f a
  | .transfer b => .transfer b
  | .terminalEffect op => .terminalEffect op
  | .suspended op => .suspended op
  | .cancelled => .cancelled
  | .diverged => .diverged
  | .fatal reason => .fatal reason
  | .unknown reason => .unknown reason

theorem bind_assoc (o : Outcome α) (f : α → Outcome β) (g : β → Outcome γ) :
    (o.bind f).bind g = o.bind (fun a => (f a).bind g) := by
  cases o <;> rfl

end Outcome

structure Route (σ α : Type) where
  guards : List TagGuard
  state : σ
  outcome : Outcome α
  deriving Repr

abbrev Flow (σ α : Type) := List (Route σ α)

namespace Route

def continueWith (r : Route σ α) (f : σ → α → Flow σ β) : Flow σ β :=
  match r.outcome with
  | .normal a => (f r.state a).map fun s => { s with guards := r.guards ++ s.guards }
  | .transfer b => [{ r with outcome := .transfer b }]
  | .terminalEffect op => [{ r with outcome := .terminalEffect op }]
  | .suspended op => [{ r with outcome := .suspended op }]
  | .cancelled => [{ r with outcome := .cancelled }]
  | .diverged => [{ r with outcome := .diverged }]
  | .fatal reason => [{ r with outcome := .fatal reason }]
  | .unknown reason => [{ r with outcome := .unknown reason }]

theorem normal_uses_poststate (guards : List TagGuard) (state : σ) (value : α)
    (f : σ → α → Flow σ β) :
    continueWith ⟨guards, state, .normal value⟩ f =
      (f state value).map (fun s => { s with guards := guards ++ s.guards }) := rfl

theorem unknown_is_not_empty (r : UnknownReason) (guards : List TagGuard) (state : σ)
    (f : σ → α → Flow σ β) :
    continueWith ⟨guards, state, .unknown r⟩ f ≠ [] := by
  simp [continueWith]

end Route

namespace Flow

def pure (state : σ) (a : α) : Flow σ α := [⟨[], state, .normal a⟩]

def bind (routes : Flow σ α) (f : σ → α → Flow σ β) : Flow σ β :=
  routes.flatMap (fun r => r.continueWith f)

/-- Branching preserves alternatives and their correlations; it does not
    intersect states or claim both callbacks execute. -/
def choice (left right : Flow σ α) : Flow σ α := left ++ right

theorem pure_bind (state : σ) (a : α) (f : σ → α → Flow σ β) :
    (pure state a).bind f = f state a := by
  simp [pure, bind, Route.continueWith]

theorem choice_bind (left right : Flow σ α) (f : σ → α → Flow σ β) :
    (left.choice right).bind f = (left.bind f).choice (right.bind f) := by
  simp [choice, bind]

theorem bind_pure (routes : Flow σ α) : routes.bind pure = routes := by
  induction routes with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨guards, state, outcome⟩
    cases outcome <;> simp_all [bind, pure, Route.continueWith]

private theorem prepend_continue (earlier : List TagGuard) (r : Route σ α)
    (f : σ → α → Flow σ β) :
    ({ r with guards := earlier ++ r.guards }).continueWith f =
      (r.continueWith f).map (fun s => { s with guards := earlier ++ s.guards }) := by
  rcases r with ⟨guards, state, outcome⟩
  cases outcome <;> simp [Route.continueWith, List.map_map, List.append_assoc]

theorem bind_assoc (routes : Flow σ α) (f : σ → α → Flow σ β)
    (g : σ → β → Flow σ γ) :
    (routes.bind f).bind g = routes.bind (fun s a => (f s a).bind g) := by
  simp only [bind, List.flatMap_assoc]
  apply congrArg (List.flatMap · routes)
  funext r
  rcases r with ⟨guards, state, outcome⟩
  cases outcome with
  | normal a =>
    simp only [Route.continueWith, List.flatMap_map, List.map_flatMap]
    apply congrArg (List.flatMap · (f state a))
    funext next
    exact prepend_continue guards next g
  | _ => simp [Route.continueWith]

end Flow

/-- Captures are invocation inputs, not a second interprocedural relation. -/
inductive InputPosition where
  | receiver
  | argument (index : Nat)
  | capture (projection : List Nat)
  deriving DecidableEq, Repr, BEq

structure InvocationInput (α : Type) where
  position : InputPosition
  resident : α
  deriving Repr

structure Invocation (α : Type) where
  declaration : DeclId
  inputs : List (InvocationInput α)
  deriving Repr

end Glorious
