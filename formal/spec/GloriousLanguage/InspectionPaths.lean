import GloriousLanguage.HeadInspectionInstantiation

/-! Fixed ordered determining paths are extracted from actual admitted
source inspections. Their identities are data, unlike a proof of existence of
some structural origin; reading the same path therefore gives an actual raw
value identity even when a binder occurs at several source positions. -/
namespace Glorious.Language

private instance (term : Term) : Decidable term.StructuralHead := by
  cases term <;> unfold Term.StructuralHead <;> infer_instance

/-- Only genuine ordered constructor positions may be traversed. Aliases,
projections and row unions must not be silently inspected as constructors. -/
def Term.structuralAt (term : Term) : List Nat → Option Term
  | [] => some term
  | index :: rest => if term.StructuralHead then
      (term.children[index]?).bind (fun child => child.structuralAt rest) else none

theorem StructuralHeadOrigin.fixed_path {binder : Binder} {template query value : Term}
    (origin : StructuralHeadOrigin binder template query value) :
    ∃ path, template.structuralAt path = some (.parameter binder.id binder.kind) ∧
      query.structuralAt path = some value := by
  induction origin with
  | parameter => exact ⟨[],rfl,rfl⟩
  | @child template query _ _ _ index structural same sourceAt queryAt _ ih =>
    obtain ⟨path,source,actual⟩ := ih
    refine ⟨index :: path,?_,?_⟩
    · simp only [Term.structuralAt,if_pos structural,sourceAt,Option.bind_some]
      exact source
    · simp only [Term.structuralAt,if_pos (same.structuralHead_iff.mp structural),queryAt,Option.bind_some]
      exact actual

theorem Term.structuralAt_substitute {source value : Term} {path : List Nat}
    (found : source.structuralAt path = some value) (substitution : Substitution) :
    (source.substitute substitution).structuralAt path = some (value.substitute substitution) := by
  induction path generalizing source with
  | nil =>
    cases Option.some.inj found
    rfl
  | cons index rest ih =>
    simp only [Term.structuralAt] at found
    split at found
    next structural =>
      obtain ⟨child,childAt,nested⟩ := Option.bind_eq_some_iff.mp found
      have notParameter : ∀ id kind, source ≠ .parameter id kind := by
        intro id kind equal
        subst source
        simp [Term.children] at childAt
      have same : SameHead source (source.substitute substitution) := (Term.substitute_head notParameter substitution).symm
      simp only [Term.structuralAt,if_pos (same.structuralHead_iff.mp structural)]
      rw [Term.substitute_children notParameter,List.getElem?_map,childAt]
      exact ih nested
    next => cases found

/-- A fixed path remains defined under a relation with genuine structural
decomposition, and its value follows that very relation. -/
theorem Term.structuralAt_related {relation : Term → Term → Prop}
    (decomposes : ∀ left right, relation left right → left.StructuralHead →
      SameHead left right ∧ ListRel relation left.children right.children)
    {left right value : Term} {path : List Nat} (related : relation left right)
    (found : left.structuralAt path = some value) :
    ∃ result, right.structuralAt path = some result ∧ relation value result := by
  induction path generalizing left right with
  | nil =>
    cases Option.some.inj found
    exact ⟨right,rfl,related⟩
  | cons index rest ih =>
    simp only [Term.structuralAt] at found
    split at found
    next structural =>
      obtain ⟨child,childAt,nested⟩ := Option.bind_eq_some_iff.mp found
      obtain ⟨same,children⟩ := decomposes left right related structural
      have bound : index < right.children.length := by
        rw [← children.length_eq]
        exact (List.getElem?_eq_some_iff.mp childAt).1
      have nextAt : right.children[index]? = some right.children[index] := List.getElem?_eq_getElem bound
      obtain ⟨result,resultAt,changed⟩ := ih (children.at childAt nextAt) nested
      refine ⟨result,?_,changed⟩
      simp only [Term.structuralAt,if_pos (same.structuralHead_iff.mp structural),nextAt,Option.bind_some]
      exact resultAt
    next => cases found

/-- A path is accompanied by the exact source admission position and a
positive source exposure at the implementation's canonical inspection level. -/
structure HeadInspectionPath (program : Program) (implementation : ImplDefinition) (binder : Binder) (level : Nat) where
  argument : Nat
  template : Term
  expanded : Term
  sourceAt : implementation.arguments[argument]? = some template
  reduced : DefinitionalReduction program implementation.context template expanded
  certificate : FullHeadInspectionReductionAt program level reduced
  children : List Nat
  parameterAt : expanded.structuralAt children = some (.parameter binder.id binder.kind)

noncomputable def ImplementationInspected.path {program : Program} {implementation : ImplDefinition}
    (inspected : ImplementationInspected program implementation) (binder : Binder) (member : binder ∈ implementation.generics) :
    HeadInspectionPath program implementation binder inspected.level := by
  apply Classical.choice
  obtain ⟨argument,template,expanded,reduced,sourceAt,certificate,origin⟩ := inspected.minimum_full_source_exposure member
  obtain ⟨children,parameterAt,_⟩ := origin.fixed_path
  exact ⟨⟨argument,template,expanded,sourceAt,reduced,certificate,children,parameterAt⟩⟩

def HeadInspectionPath.read {program : Program} {implementation : ImplDefinition} {binder : Binder} {level : Nat}
    (path : HeadInspectionPath program implementation binder level) (arguments : List Term) : Option Term :=
  (arguments[path.argument]?).bind (fun query => query.structuralAt path.children)

theorem HeadInspectionPath.read_related {program : Program} {implementation : ImplDefinition} {binder : Binder} {level : Nat}
    (path : HeadInspectionPath program implementation binder level) {relation : Term → Term → Prop}
    (decomposes : ∀ left right, relation left right → left.StructuralHead →
      SameHead left right ∧ ListRel relation left.children right.children)
    {before after : List Term} (related : ListRel relation before after) {value : Term}
    (found : path.read before = some value) :
    ∃ result, path.read after = some result ∧ relation value result := by
  obtain ⟨query,queryAt,nested⟩ := Option.bind_eq_some_iff.mp found
  have bound : path.argument < after.length := by
    rw [← related.length_eq]
    exact (List.getElem?_eq_some_iff.mp queryAt).1
  have nextAt : after[path.argument]? = some after[path.argument] := List.getElem?_eq_getElem bound
  obtain ⟨result,resultAt,changed⟩ := Term.structuralAt_related decomposes (related.at queryAt nextAt) nested
  exact ⟨result,by simp only [HeadInspectionPath.read,nextAt,Option.bind_some]; exact resultAt,changed⟩

/-- Readiness is checked against the actual raw table. Full instantiation in
the real selection judgment supplies every binder lookup; a missing read is
not permission to invent a value. -/
def ImplementationInspected.Ready {program : Program} {implementation : ImplDefinition}
    (inspected : ImplementationInspected program implementation) (arguments : List Term) (substitution : Substitution) : Prop :=
  ∀ binder (member : binder ∈ implementation.generics), (inspected.path binder member).read arguments = substitution.get binder.id

private theorem Instantiates.table_ext {binders : List Binder} {firstValues secondValues : List Term} {first second : Substitution}
    (firstInst : Instantiates binders firstValues first) (secondInst : Instantiates binders secondValues second)
    (lookup : ∀ binder ∈ binders, first.get binder.id = second.get binder.id) : first = second := by
  have lengths := firstInst.2.1.length_eq.symm.trans secondInst.2.1.length_eq
  have values : firstValues = secondValues := by
    apply List.ext_getElem lengths
    intro index firstBound secondBound
    have binderBound : index < binders.length := by rw [firstInst.2.1.length_eq]; exact firstBound
    have binderAt : binders[index]? = some binders[index] := List.getElem?_eq_getElem binderBound
    have firstAt : firstValues[index]? = some firstValues[index] := List.getElem?_eq_getElem firstBound
    have secondAt : secondValues[index]? = some secondValues[index] := List.getElem?_eq_getElem secondBound
    have equal := lookup binders[index] (List.mem_of_getElem? binderAt)
    rw [firstInst.binder_lookup_at binderAt firstAt,secondInst.binder_lookup_at binderAt secondAt] at equal
    exact Option.some.inj equal
  rw [firstInst.2.2,secondInst.2.2,values]

/-- Fixed-path readiness identifies the actual raw generic table, not merely
its equivalence class under definitional conversion. -/
theorem ImplementationInspected.Ready.table_unique {program : Program} {implementation : ImplDefinition}
    {inspected : ImplementationInspected program implementation} {arguments : List Term}
    {firstValues secondValues : List Term} {first second : Substitution}
    (left : inspected.Ready arguments first) (right : inspected.Ready arguments second)
    (firstInst : Instantiates implementation.generics firstValues first)
    (secondInst : Instantiates implementation.generics secondValues second) : first = second :=
  firstInst.table_ext secondInst (fun binder member => (left binder member).symm.trans (right binder member))

/-- A proof-only subrelation of actual root expansion whose generic values
are read at the fixed admitted paths. Declaration lookup, head matching,
requirements, and body substitution remain the existing actual judgments. -/
inductive PathInspectedStep (program : Program) (valid : ProgramWellFormed program) :
    {context : Context} → {left right : Term} → DefinitionalStep program context left right → Prop where
  | alias {context id declaration arguments substitution value}
      {found : program.alias id = some declaration}
      {instantiated : Instantiates declaration.generics arguments substitution}
      {kinded : ∀ argument ∈ arguments, Kinding program context argument argument.kind}
      {substituted : Substitutes substitution declaration.value value} :
      PathInspectedStep program valid (.alias found instantiated kinded substituted)
  | projection {context trait member owners items associated ownerSub itemSub implementation implSub body value}
      {domain : ProjectionDomain program context trait member owners items associated ownerSub itemSub}
      {selected : SelectsImpl program context trait owners false implementation implSub}
      {present : (member,body) ∈ implementation.associated}
      {substituted : Substitutes (implSub ++ itemSub) body value} :
      (valid.implementation_inspected selected.declaration).Ready owners implSub →
      PathInspectedStep program valid (.projection domain selected present substituted)
  | defaultProjection {context trait member owners items associated ownerSub itemSub implementation implSub body value}
      {domain : ProjectionDomain program context trait member owners items associated ownerSub itemSub}
      {selected : SelectsImpl program context trait owners false implementation implSub}
      {absent : ∀ body, (member,body) ∉ implementation.associated}
      {default : associated.defaultValue = some body}
      {substituted : Substitutes (ownerSub ++ itemSub) body value} :
      (valid.implementation_inspected selected.declaration).Ready owners implSub →
      PathInspectedStep program valid (.defaultProjection domain selected absent default substituted)

/-- Canonical readiness removes raw-value ambiguity at the actual root.
No injectivity of definitional equality or conversion-to-join rule is used. -/
theorem PathInspectedStep.root_equal {program : Program} {valid : ProgramWellFormed program}
    {context : Context} {term left right : Term}
    {first : DefinitionalStep program context term left} {second : DefinitionalStep program context term right}
    (certificate : PathInspectedStep program valid first) (other : PathInspectedStep program valid second) : left = right := by
  have unique : ∀ {changed result} (next : DefinitionalStep program context changed result),
      PathInspectedStep program valid next → term = changed → left = result := by
    intro changed result next nextCertificate sourceEqual
    cases certificate with
    | @alias _ _ _ _ _ found instantiated _ graph =>
      cases nextCertificate with
      | alias =>
        rename_i otherFound otherInstantiated otherKinds otherGraph
        cases sourceEqual
        obtain rfl := Option.some.inj (found.symm.trans otherFound)
        rw [graph.2.1,otherGraph.2.1,instantiated.2.2,otherInstantiated.2.2]
      | projection => cases sourceEqual
      | defaultProjection => cases sourceEqual
    | @projection _ _ _ _ _ _ _ _ _ _ _ domain selected present graph ready =>
      cases nextCertificate with
      | alias => cases sourceEqual
      | @projection _ _ _ _ _ _ _ _ _ _ _ otherDomain otherSelected otherPresent otherGraph otherReady =>
        rcases Term.projection.inj sourceEqual with ⟨rfl,rfl,rfl,rfl,_⟩
        obtain ⟨rfl,_,rfl⟩ := domain.unique otherDomain
        obtain rfl := selected.implementation_unique valid otherSelected
        obtain ⟨_,firstInst,_⟩ := selected.instantiates
        obtain ⟨_,secondInst,_⟩ := otherSelected.instantiates
        have tables := ready.table_unique otherReady firstInst secondInst
        obtain rfl := List.pair_value_unique (valid.associated_members_unique selected.declaration) present otherPresent
        rw [graph.2.1,otherGraph.2.1,tables]
      | @defaultProjection _ _ _ _ _ _ _ _ _ _ _ _ otherSelected absent _ _ _ =>
        rcases Term.projection.inj sourceEqual with ⟨rfl,rfl,rfl,rfl,_⟩
        obtain rfl := selected.implementation_unique valid otherSelected
        exact False.elim (absent _ present)
    | @defaultProjection _ _ _ _ _ _ _ _ _ _ _ domain selected absent default graph _ =>
      cases nextCertificate with
      | alias => cases sourceEqual
      | @projection _ _ _ _ _ _ _ _ _ _ _ _ otherSelected present _ _ =>
        rcases Term.projection.inj sourceEqual with ⟨rfl,rfl,rfl,rfl,_⟩
        obtain rfl := selected.implementation_unique valid otherSelected
        exact False.elim (absent _ present)
      | @defaultProjection _ _ _ _ _ _ _ _ _ _ _ otherDomain _ _ otherDefault otherGraph _ =>
        rcases Term.projection.inj sourceEqual with ⟨rfl,rfl,rfl,rfl,_⟩
        obtain ⟨rfl,rfl,rfl⟩ := domain.unique otherDomain
        obtain rfl := Option.some.inj (default.symm.trans otherDefault)
        rw [graph.2.1,otherGraph.2.1]
  exact unique second other rfl

end Glorious.Language
