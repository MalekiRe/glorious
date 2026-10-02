import Grounded.SourceLocals
import Grounded.SourcePatterns

/-! Explicit named pattern binders allocate lexical identities before body
elaboration. Constants use the existing certified structural normalizer. -/
namespace Grounded

inductive NamedPattern where
  | wildcard
  | binder (name : Identifier)
  | node (head : Head) (fields : List NamedPattern)
  | constant (identity : Nat)
  | remainder (head : Head) (front back : List NamedPattern)

mutual
def NamedPattern.binders : NamedPattern → List Identifier
  | .wildcard | .constant _ => []
  | .binder name => [name]
  | .node _ fields => namedPatternBinders fields
  | .remainder _ front back => namedPatternBinders front ++ namedPatternBinders back
def namedPatternBinders : List NamedPattern → List Identifier
  | [] => []
  | first :: rest => first.binders ++ namedPatternBinders rest
end

/-- Positional source syntax cannot name record fields or add a remainder to a
scalar constant. Constructor identity and field shape use the declaration table. -/
def Head.Positional (program : Program) : Head → Prop
  | .unit | .tuple | .array => True
  | .nominal identity tag => ∃ declaration fields,
      program.data identity = some declaration ∧
      declaration.constructor tag = some (.tuple fields)
  | _ => False
noncomputable section
mutual
/-- Allocation proceeds from the tail so the final scope has precisely the
runtime matcher's head-before-tail binding order. This is static allocation,
not evaluation of pattern fields. Sibling clauses start with the same scope. -/
inductive NamedPattern.Elaborates (program : Program) (home : Module) :
    SourceScope → NamedPattern → Ty → Pattern → List (BindingId × BindingType) → SourceScope → Prop where
  | wildcard {scope type} (discard : UsePermitted program.data .discard type) :
      NamedPattern.Elaborates program home scope .wildcard type .wildcard [] scope
  | binder {scope type} (name : Identifier) :
      NamedPattern.Elaborates program home scope (.binder name) type (.binder ⟨scope.next⟩ type)
        [(⟨scope.next⟩, ⟨type, false⟩)] (scope.enter name ⟨type, false⟩)
  | constant {scope name type} (typed : HasType program home [] (.constant name) type [])
      (discard : UsePermitted program.data .discard type) :
      NamedPattern.Elaborates program home scope (.constant name) type
        (SourcePattern.Checked.constant type typed).normalize.val [] scope
  | node {scope after head fields types type patterns bindings}
      (shape : HeadType program head type types) (access : head.Accessible program home)
      (residents : NamedPatternsElaborate program home scope fields types patterns bindings after) :
      NamedPattern.Elaborates program home scope (.node head fields) type (.node head patterns) bindings after
  | remainder {scope after head front back types type patterns bindings}
      (shape : HeadType program head type types) (access : head.Accessible program home)
      (positional : head.Positional program) (arity : front.length + back.length ≤ types.length)
      (residents : NamedPatternsElaborate program home scope
        (front ++ List.replicate (types.length - front.length - back.length) .wildcard ++ back)
        types patterns bindings after) :
      NamedPattern.Elaborates program home scope (.remainder head front back) type
        (.node head patterns) bindings after
inductive NamedPatternsElaborate (program : Program) (home : Module) :
    SourceScope → List NamedPattern → List Ty → List Pattern → List (BindingId × BindingType) → SourceScope → Prop where
  | nil {scope} : NamedPatternsElaborate program home scope [] [] [] [] scope
  | cons {scope middle after head tail type types first rest front back}
      (tailTyped : NamedPatternsElaborate program home scope tail types rest back middle)
      (headTyped : NamedPattern.Elaborates program home middle head type first front after) :
      NamedPatternsElaborate program home scope (head :: tail) (type :: types)
        (first :: rest) (front ++ back) after
end

/-- Matching and body checking consume exactly the same allocated bindings.
Freshness is derived from scope entry, never supplied for the resulting IDs. -/
theorem NamedPattern.Elaborates.checked {program : Program} {home : Module}
    {scope after : SourceScope} {source : NamedPattern} {type : Ty} {pattern : Pattern}
    {bindings : List (BindingId × BindingType)}
    (elaborated : NamedPattern.Elaborates program home scope source type pattern bindings after) :
    PatternType program home pattern type bindings ∧ after.context = bindings ++ scope.context := by
  induction elaborated using NamedPattern.Elaborates.rec
    (motive_2 := fun scope _ types patterns bindings after _ =>
      PatternsType program home patterns types bindings ∧ after.context = bindings ++ scope.context) with
  | wildcard discard => exact ⟨.wildcard discard, rfl⟩
  | binder name => exact ⟨.binder _, rfl⟩
  | constant typed discard =>
    exact ⟨.literal (Classical.choose_spec (Classical.choose_spec (constant_correctness typed))).2.1 discard, rfl⟩
  | node shape access _ ih => exact ⟨.node shape access ih.1, ih.2⟩
  | remainder shape access _ _ _ ih => exact ⟨.node shape access ih.1, ih.2⟩
  | nil => exact ⟨.nil, rfl⟩
  | cons _ _ tail head => exact ⟨.cons head.1 tail.1, by rw [head.2, tail.2, List.append_assoc]⟩

theorem SourceScope.context_distinct (scope : SourceScope) : (scope.context.map Prod.fst).Nodup := by
  simpa [SourceScope.context, List.map_map, Function.comp_def] using scope.distinct

theorem NamedPattern.Elaborates.fresh {program : Program} {home : Module}
    {scope after : SourceScope} {source : NamedPattern} {type : Ty} {pattern : Pattern}
    {bindings : List (BindingId × BindingType)}
    (elaborated : NamedPattern.Elaborates program home scope source type pattern bindings after) :
    ((bindings ++ scope.context).map Prod.fst).Nodup := by
  rw [← elaborated.checked.2]
  exact after.context_distinct

/-- The expanded wildcard segment checks every omitted type through ordinary
zero-use admission; the remainder marker grants no disposal authority. -/
theorem NamedPatternsElaborate.omitted_permissions {program : Program} {home : Module}
    {scope after : SourceScope} {front back : List NamedPattern} {count : Nat}
    {types : List Ty} {patterns : List Pattern} {bindings : List (BindingId × BindingType)}
    (elaborated : NamedPatternsElaborate program home scope
      (front ++ List.replicate count .wildcard ++ back) types patterns bindings after) :
    ∀ type ∈ (types.drop front.length).take count, UsePermitted program.data .discard type := by
  induction front generalizing scope after types patterns bindings with
  | nil =>
    simp only [List.nil_append] at elaborated
    simp only [List.length_nil, List.drop_zero]
    induction count generalizing scope after types patterns bindings with
    | zero => simp
    | succ count ih =>
      simp only [List.replicate_succ, List.cons_append] at elaborated
      cases elaborated with
      | cons tail head =>
        cases head with
        | wildcard permission =>
          intro type member
          simp only [List.take_succ_cons, List.mem_cons] at member
          rcases member with rfl | member
          · exact permission
          · exact ih tail type member
  | cons first front ih =>
    simp only [List.cons_append] at elaborated
    cases elaborated with
    | cons tail head =>
      simpa only [List.length_cons, List.drop_succ_cons] using ih tail

/-- Remainder admission exposes the declaration-selected field types and
rejects any omitted subtree whose ownership excludes zero uses. -/
theorem NamedPattern.Elaborates.remainder_permissions {program : Program} {home : Module}
    {scope after : SourceScope} {head : Head} {front back : List NamedPattern}
    {type : Ty} {pattern : Pattern} {bindings : List (BindingId × BindingType)}
    (elaborated : NamedPattern.Elaborates program home scope (.remainder head front back)
      type pattern bindings after) :
    ∃ types, HeadType program head type types ∧ front.length + back.length ≤ types.length ∧
      ∀ omitted ∈ (types.drop front.length).take (types.length - front.length - back.length),
        UsePermitted program.data .discard omitted := by
  cases elaborated with
  | remainder shape _ _ arity residents =>
    exact ⟨_, shape, arity, residents.omitted_permissions⟩


/-- Even an exhaustive remainder pattern cannot discard a must-move subtree. -/
theorem NamedPattern.Elaborates.no_exact_remainder {program : Program} {home : Module}
    {scope after : SourceScope} {head : Head} {front back : List NamedPattern}
    {type omitted : Ty} {types : List Ty} {pattern : Pattern}
    {bindings : List (BindingId × BindingType)}
    (elaborated : NamedPattern.Elaborates program home scope (.remainder head front back)
      type pattern bindings after) (shape : HeadType program head type types)
    (member : omitted ∈ (types.drop front.length).take (types.length - front.length - back.length))
    (exactOwner : omitted.HasPrincipal program.data .exact) : False := by
  obtain ⟨selected, selectedShape, _, permissions⟩ := elaborated.remainder_permissions
  cases selectedShape.fields_unique shape
  have denied := (exactOwner .discard).mp (permissions omitted member)
  simp [UsePermission.Allows] at denied


private theorem NamedPatternsElaborate.wildcard_prefix {program : Program} {home : Module}
    {scope after : SourceScope} {back : List NamedPattern} {count : Nat}
    {types : List Ty} {patterns : List Pattern} {bindings : List (BindingId × BindingType)}
    (elaborated : NamedPatternsElaborate program home scope
      (List.replicate count .wildcard ++ back) types patterns bindings after) :
    ∃ suffix, patterns = List.replicate count .wildcard ++ suffix := by
  induction count generalizing scope after types patterns bindings with
  | zero => exact ⟨patterns, rfl⟩
  | succ count ih =>
    simp only [List.replicate_succ, List.cons_append] at elaborated
    cases elaborated with
    | cons tail head =>
      cases head with
      | wildcard permission =>
        obtain ⟨suffix, same⟩ := ih tail
        exact ⟨suffix, by simp [List.replicate_succ, same]⟩

private theorem NamedPatternsElaborate.remainder_parts {program : Program} {home : Module}
    {scope after : SourceScope} {front back : List NamedPattern} {count : Nat}
    {types : List Ty} {patterns : List Pattern} {bindings : List (BindingId × BindingType)}
    (elaborated : NamedPatternsElaborate program home scope
      (front ++ List.replicate count .wildcard ++ back) types patterns bindings after) :
    ∃ frontCore suffix, patterns = frontCore ++ List.replicate count .wildcard ++ suffix ∧
      frontCore.length = front.length := by
  induction front generalizing scope after types patterns bindings with
  | nil =>
    obtain ⟨suffix, same⟩ := elaborated.wildcard_prefix
    exact ⟨[], suffix, same, rfl⟩
  | cons first front ih =>
    simp only [List.cons_append] at elaborated
    cases elaborated with
    | cons tail head =>
      obtain ⟨frontCore, suffix, same, length⟩ := ih tail
      exact ⟨_ :: frontCore, suffix, by simp only [same, List.cons_append]; rfl, by simp [length]⟩

/-- Source remainder elaboration determines the real matcher's result, not a
separate disposal approximation. Omitted values contribute no bindings and
appear in reverse order between suffix and prefix discards. -/
theorem NamedPattern.Elaborates.remainder_matching {program : Program} {home : Module}
    {scope after : SourceScope} {head : Head} {front back : List NamedPattern}
    {type : Ty} {pattern : Pattern} {bindings : List (BindingId × BindingType)}
    (elaborated : NamedPattern.Elaborates program home scope (.remainder head front back)
      type pattern bindings after) :
    ∃ types frontCore suffix, HeadType program head type types ∧
      front.length + back.length ≤ types.length ∧ frontCore.length = front.length ∧
      (∀ omitted ∈ (types.drop front.length).take (types.length - front.length - back.length),
        UsePermitted program.data .discard omitted) ∧
      ∀ (value : Value) (first omitted rest : List Value), first.length = front.length →
        omitted.length = types.length - front.length - back.length →
        value.head = head → value.children = first ++ omitted ++ rest →
        pattern.matchValue value = (do
          let left ← matchPatterns frontCore first
          let right ← matchPatterns suffix rest
          pure (left ++ ⟨[], omitted.reverse⟩ ++ right)) := by
  cases elaborated with
  | remainder shape _ _ arity residents =>
    obtain ⟨frontCore, suffix, emitted, length⟩ := residents.remainder_parts
    refine ⟨_, frontCore, suffix, shape, arity, length, residents.omitted_permissions, ?_⟩
    intro value first omitted rest firstLength omittedLength selected fields
    simp only [Pattern.matchValue, selected, ↓reduceIte, emitted, ← omittedLength, fields]
    exact matchPatterns.remainder (length.trans firstLength.symm)

end
end Grounded
