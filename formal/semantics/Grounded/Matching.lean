import Grounded.BindingStorage

/-! Runtime structural matching and first-clause selection. Matching interprets
the pattern subject; it does not change the callable argument-list shape. -/
namespace Grounded

/-- One successful match partitions its subject into retained bindings and
 discarded residents. Discards are ordered newest field first. -/
structure PatternMatch where
  bindings : List BindingInput
  discarded : List Value

def PatternMatch.empty : PatternMatch := ⟨[], []⟩

def PatternMatch.append (first second : PatternMatch) : PatternMatch :=
  ⟨first.bindings ++ second.bindings, second.discarded ++ first.discarded⟩

instance : Append PatternMatch := ⟨PatternMatch.append⟩

@[simp] theorem PatternMatch.append_bindings (first second : PatternMatch) :
    (first ++ second).bindings = first.bindings ++ second.bindings := rfl

@[simp] theorem PatternMatch.append_discarded (first second : PatternMatch) :
    (first ++ second).discarded = second.discarded ++ first.discarded := rfl

@[simp] theorem PatternMatch.empty_append (result : PatternMatch) : empty ++ result = result := by
  change mk ([] ++ result.bindings) (result.discarded ++ []) = result
  simp only [List.nil_append, List.append_nil]

@[simp] theorem PatternMatch.append_empty (result : PatternMatch) : result ++ empty = result := by
  change mk (result.bindings ++ []) ([] ++ result.discarded) = result
  simp only [List.nil_append, List.append_nil]

theorem PatternMatch.append_assoc (first second third : PatternMatch) :
    (first ++ second) ++ third = first ++ (second ++ third) := by
  change mk ((first.bindings ++ second.bindings) ++ third.bindings)
    (third.discarded ++ (second.discarded ++ first.discarded)) =
    mk (first.bindings ++ (second.bindings ++ third.bindings))
      ((third.discarded ++ second.discarded) ++ first.discarded)
  simp only [List.append_assoc]
mutual
def Pattern.matchValue (pattern : Pattern) (value : Value) : Option PatternMatch :=
  match pattern with
  | .wildcard => some ⟨[], [value]⟩
  | .binder name type => some ⟨[⟨name, ⟨type, false⟩, value⟩], []⟩
  | .literal _ expected => if value = expected then some ⟨[], [value]⟩ else none
  | .node head fields =>
      if head = value.head then matchPatterns fields value.children else none
termination_by sizeOf pattern

def matchPatterns (patterns : List Pattern) (values : List Value) : Option PatternMatch :=
  match patterns, values with
  | [], [] => some .empty
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

def selectArm (value : Value) : List (Pattern × Expr) → Option (PatternMatch × Expr)
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

/-- A positional observation inside the same pattern/subject pair used by
matchValue. This grants no matching, ownership or deconstruction permission. -/
inductive Pattern.SubjectAt : Pattern → Value → Pattern → Value → Prop where
  | root (pattern : Pattern) (value : Value) : SubjectAt pattern value pattern value
  | child {head : Head} {patterns : List Pattern} {value childValue owner : Value}
      {index : Nat} {childPattern selected : Pattern}
      (shape : head = value.head)
      (patternAt : patterns[index]? = some childPattern)
      (valueAt : value.children[index]? = some childValue)
      (nested : SubjectAt childPattern childValue selected owner) :
      SubjectAt (.node head patterns) value selected owner

/-- Successful aggregate matching uses the actual pattern/value pair at every
position, not an independently reconstructed child input. -/
theorem matchPatterns.at {patterns : List Pattern} {values : List Value} {bindings : PatternMatch}
    (matched : matchPatterns patterns values = some bindings) {index : Nat}
    {pattern : Pattern} {value : Value} (patternAt : patterns[index]? = some pattern)
    (valueAt : values[index]? = some value) :
    ∃ inputs front back, pattern.matchValue value = some inputs ∧ bindings = front ++ inputs ++ back := by
  induction patterns generalizing values bindings index with
  | nil => simp at patternAt
  | cons head tail ih =>
    cases values with
    | nil => simp [matchPatterns] at matched
    | cons first rest =>
      cases headMatch : head.matchValue first with
      | none => simp [matchPatterns, headMatch] at matched
      | some front =>
        cases tailMatch : matchPatterns tail rest with
        | none => simp [matchPatterns, headMatch, tailMatch] at matched
        | some back =>
          have joined : bindings = front ++ back := by
            simpa [matchPatterns, headMatch, tailMatch] using matched.symm
          cases index with
          | zero => cases patternAt; cases valueAt; exact ⟨front, .empty, back, headMatch, by simpa using joined⟩
          | succ index =>
            obtain ⟨inputs, before, after, selected, split⟩ := ih tailMatch patternAt valueAt
            exact ⟨inputs, front ++ before, after, selected, by simp [joined, split, PatternMatch.append_assoc]⟩

/-- Observing a subtree of a successful match exposes a successful use of the
same matcher; the observation itself supplies no success premise. -/
theorem Pattern.SubjectAt.matched {pattern selected : Pattern} {value owner : Value}
    (focus : Pattern.SubjectAt pattern value selected owner) {bindings : PatternMatch}
    (matched : pattern.matchValue value = some bindings) :
    ∃ inputs front back, selected.matchValue owner = some inputs ∧ bindings = front ++ inputs ++ back := by
  induction focus generalizing bindings with
  | root => exact ⟨bindings, .empty, .empty, matched, by simp⟩
  | child same patternAt valueAt nested ih =>
    simp only [Pattern.matchValue, same, ↓reduceIte] at matched
    obtain ⟨inputs, front, back, childMatch, split⟩ := matchPatterns.at matched patternAt valueAt
    obtain ⟨selectedInputs, before, after, selectedMatch, childSplit⟩ := ih childMatch
    exact ⟨selectedInputs, front ++ before, after ++ back, selectedMatch, by simp [split, childSplit, PatternMatch.append_assoc]⟩

/-- Adjacent constructor-field segments use the same matcher and preserve its
reverse declaration-order discard queue. -/
theorem matchPatterns.append {front back : List Pattern} {first rest : List Value}
    (aligned : front.length = first.length) :
    matchPatterns (front ++ back) (first ++ rest) = (do
      let left ← matchPatterns front first
      let right ← matchPatterns back rest
      pure (left ++ right)) := by
  induction front generalizing first with
  | nil =>
    cases first with
    | nil => simp [matchPatterns]
    | cons value values => simp at aligned
  | cons pattern patterns ih =>
    cases first with
    | nil => simp at aligned
    | cons value values =>
      have aligned : patterns.length = values.length := Nat.succ.inj aligned
      simp only [List.cons_append, matchPatterns, ih aligned]
      cases pattern.matchValue value <;>
        cases matchPatterns patterns values <;>
        cases matchPatterns back rest <;>
        simp [PatternMatch.append_assoc]

theorem matchPatterns.wildcards (values : List Value) :
    matchPatterns (List.replicate values.length .wildcard) values = some ⟨[], values.reverse⟩ := by
  induction values with
  | nil => simp [matchPatterns, PatternMatch.empty]
  | cons value values ih =>
    simp [List.replicate_succ, matchPatterns, Pattern.matchValue, ih, List.reverse_cons]
    rfl

/-- A positional remainder discards exactly the omitted residents, in reverse
order, without adding bindings or inspecting their contents. -/
theorem matchPatterns.remainder {front back : List Pattern} {first omitted rest : List Value}
    (aligned : front.length = first.length) :
    matchPatterns (front ++ List.replicate omitted.length .wildcard ++ back)
      (first ++ omitted ++ rest) = (do
      let left ← matchPatterns front first
      let right ← matchPatterns back rest
      pure (left ++ ⟨[], omitted.reverse⟩ ++ right)) := by
  rw [List.append_assoc, List.append_assoc, matchPatterns.append aligned,
    matchPatterns.append (by simp), matchPatterns.wildcards]
  cases matchPatterns front first <;> cases matchPatterns back rest <;>
    simp [PatternMatch.append_assoc]


end Grounded
