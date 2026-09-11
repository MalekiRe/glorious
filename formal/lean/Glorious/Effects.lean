import Glorious.Cleanup

/-! Exact instance routing and resumption quantities, language §10.
    `κ` is the upstream normalizer's equality-preserving argument domain;
    neither source spelling nor payload-type compatibility participates in
    identity. Pattern predicates are supplied by checked pattern elaboration.
    This module establishes routing, not the correctness of those predicates. -/
namespace Glorious

structure EffectInstance (κ : Type) where
  declaration : DeclId
  arguments : List κ
  deriving DecidableEq, Repr

structure OperationKey (κ : Type) where
  effect : EffectInstance κ
  operation : DeclId
  deriving DecidableEq, Repr

/-- A row's equality is extensional. Deterministic serialization of normalized
    argument keys belongs to artifact lowering, not to list ordering here. -/
abbrev EffectRow (κ : Type) := List (EffectInstance κ)

namespace EffectRow

def Equivalent (a b : EffectRow κ) : Prop := ∀ e, e ∈ a ↔ e ∈ b
def Includes (allowed required : EffectRow κ) : Prop := ∀ e ∈ required, e ∈ allowed
def union (a b : EffectRow κ) : EffectRow κ := a ++ b

theorem union_member (a b : EffectRow κ) (e : EffectInstance κ) :
    e ∈ a.union b ↔ e ∈ a ∨ e ∈ b := List.mem_append

theorem union_comm (a b : EffectRow κ) : Equivalent (a.union b) (b.union a) := by
  intro e; simp only [union_member]; exact or_comm

theorem union_idempotent (a : EffectRow κ) : Equivalent (a.union a) a := by
  intro e; simp [union]

theorem union_associative (a b c : EffectRow κ) :
    Equivalent ((a.union b).union c) (a.union (b.union c)) := by
  intro e; simp [union, List.append_assoc]

theorem includes_union (allowed a b : EffectRow κ) :
    Includes allowed (a.union b) ↔ Includes allowed a ∧ Includes allowed b := by
  simp [Includes, union, or_imp, forall_and]

/-- Removal requires *complete* operation/payload coverage of this exact
    instance. The caller supplies only instances for which it has proved it.
    A partially matched operation is therefore never subtracted by dispatch. -/
def subtract [DecidableEq κ] (outward completelyHandled : EffectRow κ) : EffectRow κ :=
  outward.filter (fun e => decide (e ∉ completelyHandled))

theorem subtract_member [DecidableEq κ] (a handled : EffectRow κ) (e : EffectInstance κ) :
    e ∈ a.subtract handled ↔ e ∈ a ∧ e ∉ handled := by
  simp [subtract]

end EffectRow

structure OperationClause (κ payload body : Type) where
  key : OperationKey κ
  accepts : payload → Bool
  code : body

structure Handler (κ payload body : Type) where
  brand : Brand
  clauses : List (OperationClause κ payload body)
  completion : body

def firstClause [DecidableEq κ] (key : OperationKey κ) (value : payload)
    (handler : Handler κ payload body) : Option (OperationClause κ payload body) :=
  handler.clauses.find? (fun c => decide (c.key = key) && c.accepts value)

/-- `inner` is the captured continuation segment, innermost first. The
    serviced delimiter is absent from the operation clause's active stack.
    Resuming reinstalls it, including its normal completion transformation. -/
structure Dispatch (κ payload body : Type) where
  inner : List (Handler κ payload body)
  delimiter : Handler κ payload body
  clause : OperationClause κ payload body
  outer : List (Handler κ payload body)

namespace Dispatch

def clauseStack (d : Dispatch κ payload body) := d.outer
def resumptionStack (d : Dispatch κ payload body) := d.inner ++ d.delimiter :: d.outer

end Dispatch

inductive Routes [DecidableEq κ] (key : OperationKey κ) (value : payload) :
    List (Handler κ payload body) → Dispatch κ payload body → Prop where
  | here {handler outer clause} (selected : firstClause key value handler = some clause) :
      Routes key value (handler :: outer) ⟨[], handler, clause, outer⟩
  | skip {handler rest dispatch} (missed : firstClause key value handler = none)
      (next : Routes key value rest dispatch) :
      Routes key value (handler :: rest) { dispatch with inner := handler :: dispatch.inner }

/-- The interpreter consumes the selected clause, the clause stack and the
    deep-resumption stack from this single proof-producing routing function. -/
def route [DecidableEq κ] (key : OperationKey κ) (value : payload) :
    (stack : List (Handler κ payload body)) →
    Option { dispatch : Dispatch κ payload body // Routes key value stack dispatch }
  | [] => none
  | handler :: rest =>
    match h : firstClause key value handler with
    | some clause => some ⟨⟨[], handler, clause, rest⟩, .here h⟩
    | none =>
      match route key value rest with
      | none => none
      | some ⟨dispatch, proof⟩ =>
        some ⟨{ dispatch with inner := handler :: dispatch.inner }, .skip h proof⟩

theorem routing_reconstructs_stack [DecidableEq κ] {key : OperationKey κ}
    {value : payload} {stack : List (Handler κ payload body)} {d : Dispatch κ payload body}
    (h : Routes key value stack d) : d.resumptionStack = stack := by
  induction h with
  | here _ => rfl
  | skip _ _ ih => simpa [Dispatch.resumptionStack] using ih

theorem routed_clause_is_selected [DecidableEq κ] {key : OperationKey κ}
    {value : payload} {stack : List (Handler κ payload body)} {d : Dispatch κ payload body}
    (h : Routes key value stack d) : firstClause key value d.delimiter = some d.clause := by
  induction h with
  | here h => exact h
  | skip _ _ ih => exact ih

theorem routed_clause_has_exact_identity [DecidableEq κ] {key : OperationKey κ}
    {value : payload} {stack : List (Handler κ payload body)} {d : Dispatch κ payload body}
    (h : Routes key value stack d) : d.clause.key = key ∧ d.clause.accepts value = true := by
  have selected := routed_clause_is_selected h
  have accepted := List.find?_some selected
  simpa using accepted

theorem routed_handlers_were_skipped [DecidableEq κ] {key : OperationKey κ}
    {value : payload} {stack : List (Handler κ payload body)} {d : Dispatch κ payload body}
    (h : Routes key value stack d) : ∀ handler ∈ d.inner, firstClause key value handler = none := by
  induction h with
  | here _ => simp
  | skip missed _ ih => simpa using And.intro missed ih

/-- No nonexact finite or unbounded surface quantity can inhabit this type. -/
inductive ResumptionPolicy where
  | optional
  | exact (count : Nat) (positive : 0 < count) (bounded : count ≤ 4294967295)

namespace ResumptionPolicy

def required : ResumptionPolicy → Nat
  | .optional => 0
  | .exact n _ _ => n

def maximum : ResumptionPolicy → Nat
  | .optional => 1
  | .exact n _ _ => n

def Allows (policy : ResumptionPolicy) (uses : Nat) : Prop :=
  policy.required ≤ uses ∧ uses ≤ policy.maximum

instance (policy : ResumptionPolicy) (uses : Nat) : Decidable (policy.Allows uses) :=
  inferInstanceAs (Decidable (policy.required ≤ uses ∧ uses ≤ policy.maximum))

def tailResumeAllowed (policy : ResumptionPolicy) : Bool := decide (policy.Allows 1)

def parse (lower : Nat) (upper : Option Nat) : Option ResumptionPolicy :=
  match upper with
  | none => none
  | some maximum =>
    if lower = 0 ∧ maximum = 1 then some .optional
    else if h : lower = maximum ∧ 0 < lower ∧ lower ≤ 4294967295 then
      some (.exact lower h.2.1 h.2.2)
    else none

theorem exact_two_rejects_abbreviation :
    tailResumeAllowed (.exact 2 (by decide) (by decide)) = false := rfl

theorem optional_allows_abbreviation : tailResumeAllowed .optional = true := rfl

theorem parse_unbounded_rejected (lower : Nat) : parse lower none = none := rfl

theorem exact_count (n positive bounded uses) :
    Allows (.exact n positive bounded) uses ↔ uses = n := by
  simp [Allows, required, maximum]; omega

end ResumptionPolicy
end Glorious
