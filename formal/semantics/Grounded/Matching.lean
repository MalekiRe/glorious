import Grounded.BindingStorage

/-! Runtime structural matching and first-clause selection. Matching interprets
the pattern subject; it does not change the callable argument-list shape. -/
namespace Grounded

mutual
def Pattern.matchValue (pattern : Pattern) (value : Value) : Option (List BindingInput) :=
  match pattern with
  | .wildcard => some []
  | .binder name type => some [⟨name, ⟨type, false⟩, value⟩]
  | .literal _ expected => if value = expected then some [] else none
  | .node head fields =>
      if head = value.head then matchPatterns fields value.children else none
termination_by sizeOf pattern

def matchPatterns (patterns : List Pattern) (values : List Value) : Option (List BindingInput) :=
  match patterns, values with
  | [], [] => some []
  | pattern :: patterns, value :: values => do
      let first ← pattern.matchValue value
      let rest ← matchPatterns patterns values
      pure (first ++ rest)
  | _, _ => none
termination_by sizeOf patterns
end


/-- The callable's argument list is retained; only pattern interpretation unwraps
one argument. A singleton tuple argument is not two arguments (§6.1). -/
def argumentType : List Ty → Ty
  | [] => .unit
  | [type] => type
  | head :: next :: tail => .tuple head (next :: tail)

def argumentValue : List Value → Value
  | [] => .unit
  | [value] => value
  | head :: next :: tail => .tuple head (next :: tail)

def selectArm (value : Value) : List (Pattern × Expr) → Option (List BindingInput × Expr)
  | [] => none
  | (pattern, body) :: rest =>
      match pattern.matchValue value with
      | some bindings => some (bindings, body)
      | none => selectArm value rest

/-- Failed clauses neither supply bindings nor change the selected subject. -/
theorem selectArm.skip_missed (value : Value) (front back : List (Pattern × Expr))
    (missed : ∀ earlier ∈ front, earlier.1.matchValue value = none) :
    selectArm value (front ++ back) = selectArm value back := by
  induction front with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.cons_append, selectArm, missed head (by simp)]
    exact ih (fun earlier member => missed earlier (List.mem_cons_of_mem _ member))

/-- First-match provenance identifies the clause itself, even when different
clauses have identical bodies and binding outputs. -/
theorem selectArm.first_unique {value : Value} {front back otherFront otherBack : List (Pattern × Expr)}
    {clause other : Pattern × Expr}
    (same : front ++ clause :: back = otherFront ++ other :: otherBack)
    (missed : ∀ earlier ∈ front, earlier.1.matchValue value = none)
    (otherMissed : ∀ earlier ∈ otherFront, earlier.1.matchValue value = none)
    (matched : clause.1.matchValue value ≠ none) (otherMatched : other.1.matchValue value ≠ none) :
    clause = other := by
  induction front generalizing otherFront with
  | nil =>
    cases otherFront with
    | nil => exact (List.cons.inj same).1
    | cons head tail =>
      have equal := (List.cons.inj same).1
      exact False.elim (matched (equal ▸ otherMissed head (by simp)))
  | cons head tail ih =>
    cases otherFront with
    | nil =>
      have equal := (List.cons.inj same).1
      exact False.elim (otherMatched (equal ▸ missed head (by simp)))
    | cons otherHead otherTail =>
      exact ih (List.cons.inj same).2
        (fun earlier member => missed earlier (List.mem_cons_of_mem _ member))
        (fun earlier member => otherMissed earlier (List.mem_cons_of_mem _ member))

end Grounded
