import Grounded.SourceLocals
import Grounded.SourcePatterns

/-! Explicit named pattern binders allocate lexical identities before body
elaboration. Constants use the existing certified structural normalizer. -/
namespace Grounded

inductive NamedPattern where
  | wildcard
  | binder (name : String)
  | node (head : Head) (fields : List NamedPattern)
  | constant (name : String)

mutual
def NamedPattern.binders : NamedPattern → List String
  | .wildcard | .constant _ => []
  | .binder name => [name]
  | .node _ fields => namedPatternBinders fields
def namedPatternBinders : List NamedPattern → List String
  | [] => []
  | first :: rest => first.binders ++ namedPatternBinders rest
end

noncomputable section
mutual
/-- Allocation proceeds from the tail so the final scope has precisely the
runtime matcher's head-before-tail binding order. This is static allocation,
not evaluation of pattern fields. Sibling clauses start with the same scope. -/
inductive NamedPattern.Elaborates (program : Program) (home : Module) :
    SourceScope → NamedPattern → Ty → Pattern → List (BindingId × BindingType) → SourceScope → Prop where
  | wildcard {scope type} (discard : Duplicable program.data type) :
      NamedPattern.Elaborates program home scope .wildcard type .wildcard [] scope
  | binder {scope type} (name : String) (discard : Duplicable program.data type) :
      NamedPattern.Elaborates program home scope (.binder name) type (.binder ⟨scope.next⟩ type)
        [(⟨scope.next⟩, ⟨type, false⟩)] (scope.enter name ⟨type, false⟩)
  | constant {scope name type} (typed : HasType program home [] (.constant name) type [])
      (discard : Duplicable program.data type) :
      NamedPattern.Elaborates program home scope (.constant name) type
        (SourcePattern.Checked.constant type typed).normalize.val [] scope
  | node {scope after head fields types type patterns bindings}
      (shape : HeadType program head type types) (access : head.Accessible program home)
      (residents : NamedPatternsElaborate program home scope fields types patterns bindings after) :
      NamedPattern.Elaborates program home scope (.node head fields) type (.node head patterns) bindings after
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
  | binder name discard => exact ⟨.binder _ discard, rfl⟩
  | constant typed discard =>
    exact ⟨.literal (Classical.choose_spec (Classical.choose_spec (constant_correctness typed))).2.1 discard, rfl⟩
  | node shape access _ ih => exact ⟨.node shape access ih.1, ih.2⟩
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

end
end Grounded
