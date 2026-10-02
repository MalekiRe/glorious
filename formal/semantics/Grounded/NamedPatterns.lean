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
  | record (identity : Nat) (tag : Option Nat) (fields : List (String × NamedPattern))

mutual
def NamedPattern.binders : NamedPattern → List Identifier
  | .wildcard | .constant _ => []
  | .binder name => [name]
  | .node _ fields => namedPatternBinders fields
  | .remainder _ front back => namedPatternBinders front ++ namedPatternBinders back
  | .record _ _ fields => namedRecordPatternBinders fields
def namedPatternBinders : List NamedPattern → List Identifier
  | [] => []
  | first :: rest => first.binders ++ namedPatternBinders rest
def namedRecordPatternBinders : List (String × NamedPattern) → List Identifier
  | [] => []
  | (_, pattern) :: rest => pattern.binders ++ namedRecordPatternBinders rest
end

/-- Named source fields are arranged by declaration order. Missing entries are
ordinary wildcard requests, never implicit permission to discard their types. -/
def recordPatternFields (fields : List (String × Field))
    (supplied : List (String × NamedPattern)) : List NamedPattern :=
  fields.map fun field =>
    match supplied.find? (fun entry => entry.1 == field.1) with
    | some entry => entry.2
    | none => .wildcard


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
  | record {scope after identity tag supplied declaration fields patterns bindings}
      (declared : program.data identity = some declaration)
      (chosen : declaration.constructor tag = some (.record fields))
      (access : (Head.nominal identity tag).Accessible program home)
      (distinct : (supplied.map Prod.fst).Nodup)
      (known : ∀ entry ∈ supplied, ∃ index, (Fields.record fields).index (.named entry.1) = some index)
      (residents : NamedPatternsElaborate program home scope (recordPatternFields fields supplied)
        ((Fields.record fields).residents.map Field.type) patterns bindings after) :
      NamedPattern.Elaborates program home scope (.record identity tag supplied) (.nominal identity)
        (.node (.nominal identity tag) patterns) bindings after
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
  | record declared chosen access _ _ _ ih => exact ⟨.node (.nominal declared chosen) access ih.1, ih.2⟩
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

/-- The emitted field at an index is elaborated from the source field at that
same index, with the actual lexical scopes chosen by batch allocation. -/
theorem NamedPatternsElaborate.at {program : Program} {home : Module}
    {scope after : SourceScope} {sources : List NamedPattern} {types : List Ty}
    {patterns : List Pattern} {bindings : List (BindingId × BindingType)}
    (elaborated : NamedPatternsElaborate program home scope sources types patterns bindings after)
    {index : Nat} {source : NamedPattern} {type : Ty}
    (sourceAt : sources[index]? = some source) (typeAt : types[index]? = some type) :
    ∃ pattern locals before next, patterns[index]? = some pattern ∧
      NamedPattern.Elaborates program home before source type pattern locals next := by
  induction sources generalizing scope after types patterns bindings index with
  | nil => simp at sourceAt
  | cons first rest ih =>
    cases elaborated with
    | cons tail head =>
      cases index with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at sourceAt typeAt
        cases sourceAt
        cases typeAt
        exact ⟨_, _, _, _, rfl, head⟩
      | succ index =>
        exact ih tail sourceAt typeAt

/-- Absence of a source label selects a wildcard at the declaration's field
position. The ordinary wildcard elaborator must then authorize its disposal. -/
theorem NamedPattern.Elaborates.record_omitted {program : Program} {home : Module}
    {scope after : SourceScope} {identity : Nat} {tag : Option Nat}
    {supplied : List (String × NamedPattern)} {pattern : Pattern}
    {bindings : List (BindingId × BindingType)}
    (elaborated : NamedPattern.Elaborates program home scope (.record identity tag supplied)
      (.nominal identity) pattern bindings after)
    {declaration : DataDecl} {fields : List (String × Field)}
    (declared : program.data identity = some declaration)
    (chosen : declaration.constructor tag = some (.record fields))
    {index : Nat} {name : String} {field : Field}
    (fieldAt : fields[index]? = some (name, field))
    (absent : name ∉ supplied.map Prod.fst) :
    UsePermitted program.data .discard field.type ∧
      ∀ (value resident : Value) (result : PatternMatch), value.head = .nominal identity tag →
        value.children[index]? = some resident → pattern.matchValue value = some result →
        resident ∈ result.discarded := by
  have missing : supplied.find? (fun entry => entry.1 == name) = none := by
    apply List.find?_eq_none.mpr
    intro entry member same
    apply absent
    exact List.mem_map.mpr ⟨entry, member, by simpa using same⟩
  cases elaborated with
  | record original selected access distinct known residents =>
    have declarationSame := Option.some.inj (original.symm.trans declared)
    cases declarationSame
    have fieldsSame := Option.some.inj (selected.symm.trans chosen)
    cases fieldsSame
    have sourceAt : (recordPatternFields fields supplied)[index]? = some .wildcard := by
      simp [recordPatternFields, List.getElem?_map, fieldAt, missing]
    have typeAt : ((Fields.record fields).residents.map Field.type)[index]? = some field.type := by
      simp [Fields.residents, List.getElem?_map, fieldAt]
    obtain ⟨child, locals, before, next, childAt, childTyped⟩ := residents.at sourceAt typeAt
    cases childTyped with
    | wildcard permission =>
      refine ⟨permission, ?_⟩
      intro value resident result head valueAt matched
      have focus : Pattern.SubjectAt _ value .wildcard resident :=
        .child head.symm childAt valueAt (.root .wildcard resident)
      obtain ⟨inputs, front, back, selected, joined⟩ := focus.matched matched
      have inputsSame : inputs = ⟨[], [resident]⟩ := by simpa [Pattern.matchValue] using selected.symm
      simp [joined, inputsSame]


/-- A supplied label selects its declaration-indexed resident and the same
lexically allocated subpattern consumed by matching and clause-body checking. -/
theorem NamedPattern.Elaborates.record_field {program : Program} {home : Module}
    {scope after : SourceScope} {identity : Nat} {tag : Option Nat}
    {supplied : List (String × NamedPattern)} {pattern : Pattern}
    {bindings : List (BindingId × BindingType)}
    (elaborated : NamedPattern.Elaborates program home scope (.record identity tag supplied)
      (.nominal identity) pattern bindings after)
    {declaration : DataDecl} {fields : List (String × Field)}
    (declared : program.data identity = some declaration)
    (chosen : declaration.constructor tag = some (.record fields))
    {index : Nat} {name : String} {field : Field} {source : NamedPattern}
    (fieldAt : fields[index]? = some (name, field))
    (suppliedAt : supplied.find? (fun entry => entry.1 == name) = some (name, source)) :
    ∃ child locals before next, NamedPattern.Elaborates program home before source field.type child locals next ∧
      ∀ (value resident : Value), value.head = .nominal identity tag →
        value.children[index]? = some resident → Pattern.SubjectAt pattern value child resident := by
  cases elaborated with
  | record original selected access distinct known residents =>
    have declarationSame := Option.some.inj (original.symm.trans declared)
    cases declarationSame
    have fieldsSame := Option.some.inj (selected.symm.trans chosen)
    cases fieldsSame
    have sourceAt : (recordPatternFields fields supplied)[index]? = some source := by
      simp [recordPatternFields, List.getElem?_map, fieldAt, suppliedAt]
    have typeAt : ((Fields.record fields).residents.map Field.type)[index]? = some field.type := by
      simp [Fields.residents, List.getElem?_map, fieldAt]
    obtain ⟨child, locals, before, next, childAt, childTyped⟩ := residents.at sourceAt typeAt
    refine ⟨child, locals, before, next, childTyped, ?_⟩
    intro value resident head valueAt
    exact .child head.symm childAt valueAt (.root child resident)

/-- Omitting a named field cannot hide an exact-owned obligation. -/
theorem NamedPattern.Elaborates.no_exact_record_omission {program : Program} {home : Module}
    {scope after : SourceScope} {identity : Nat} {tag : Option Nat}
    {supplied : List (String × NamedPattern)} {pattern : Pattern}
    {bindings : List (BindingId × BindingType)}
    (elaborated : NamedPattern.Elaborates program home scope (.record identity tag supplied)
      (.nominal identity) pattern bindings after)
    {declaration : DataDecl} {fields : List (String × Field)}
    (declared : program.data identity = some declaration)
    (chosen : declaration.constructor tag = some (.record fields))
    {index : Nat} {name : String} {field : Field}
    (fieldAt : fields[index]? = some (name, field)) (absent : name ∉ supplied.map Prod.fst)
    (exactOwner : field.type.HasPrincipal program.data .exact) : False := by
  have permission := (elaborated.record_omitted declared chosen fieldAt absent).1
  have denied := (exactOwner .discard).mp permission
  simp [UsePermission.Allows] at denied


private theorem record_lookup_permute {first second : List (String × NamedPattern)}
    (permuted : first.Perm second) (distinct : (first.map Prod.fst).Nodup) (name : String) :
    first.find? (fun entry => entry.1 == name) = second.find? (fun entry => entry.1 == name) := by
  induction permuted with
  | nil => rfl
  | cons entry permuted ih =>
    simp only [List.map_cons, List.nodup_cons] at distinct
    simp only [List.find?_cons, ih distinct.2]
  | swap first second rest =>
    by_cases left : first.1 = name <;> by_cases right : second.1 = name <;>
      simp_all [List.map_cons, List.nodup_cons]
  | trans first second firstIH secondIH =>
    exact (firstIH distinct).trans (secondIH ((first.map Prod.fst).nodup_iff.mp distinct))

/-- Named field order does not affect declaration-order normalization. The
unique-label check is essential: conflicting duplicate labels are not reordered. -/
theorem recordPatternFields.permute (fields : List (String × Field))
    {first second : List (String × NamedPattern)} (permuted : first.Perm second)
    (distinct : (first.map Prod.fst).Nodup) :
    recordPatternFields fields first = recordPatternFields fields second := by
  unfold recordPatternFields
  congr 1
  funext field
  rw [record_lookup_permute permuted distinct field.1]

/-- Reordering supplied labels preserves the exact Core pattern, binding IDs
and final lexical scope; it does not merely find another well-typed result. -/
theorem NamedPattern.Elaborates.record_permute {program : Program} {home : Module}
    {scope after : SourceScope} {identity : Nat} {tag : Option Nat}
    {first second : List (String × NamedPattern)} {type : Ty} {pattern : Pattern}
    {bindings : List (BindingId × BindingType)}
    (elaborated : NamedPattern.Elaborates program home scope (.record identity tag first)
      type pattern bindings after) (permuted : first.Perm second) :
    NamedPattern.Elaborates program home scope (.record identity tag second)
      type pattern bindings after := by
  cases elaborated with
  | record declared chosen access distinct known residents =>
    refine .record declared chosen access ((permuted.map Prod.fst).nodup_iff.mp distinct)
      (fun entry member => known entry (permuted.mem_iff.mpr member)) ?_
    rw [← recordPatternFields.permute _ permuted distinct]
    exact residents


theorem namedRecordPatternBinders.permute {first second : List (String × NamedPattern)}
    (permuted : first.Perm second) :
    (namedRecordPatternBinders first).Perm (namedRecordPatternBinders second) := by
  induction permuted with
  | nil => exact .nil
  | cons entry permuted ih => exact List.Perm.append_left _ ih
  | swap first second rest =>
    simpa only [namedRecordPatternBinders, List.append_assoc] using
      List.Perm.append_right (namedRecordPatternBinders rest)
        (List.perm_append_comm (l₁ := second.2.binders) (l₂ := first.2.binders))
  | trans _ _ first second => exact first.trans second


end
end Grounded
