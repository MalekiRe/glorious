import GloriousLanguage.InspectionPaths
import GloriousLanguage.HeadOriginSubstitution

/-! Residual construction for fixed-path root inspections updates actual
generic values through their ordered query paths. It reconstructs real
selection using source admission and existing logical substitution transport;
it does not retain stale generic values after the query changes. -/
namespace Glorious.Language

private theorem ListRel.choose_right {α β γ : Type} {relation : α → β → Prop}
    {changed : β → γ → Prop} {result : α → γ → Prop} {left : List α} {right : List β}
    (related : ListRel relation left right)
    (choose : ∀ a ∈ left, ∀ b ∈ right, relation a b → ∃ c, changed b c ∧ result a c) :
    ∃ middle, ListRel changed right middle ∧ ListRel result left middle := by
  induction related with
  | nil => exact ⟨[],.nil,.nil⟩
  | @cons a b as bs head _ ih =>
    obtain ⟨c,first,second⟩ := choose a List.mem_cons_self b List.mem_cons_self head
    obtain ⟨middle,tail,rest⟩ := ih (fun a member b present pair =>
      choose a (List.mem_cons_of_mem _ member) b (List.mem_cons_of_mem _ present) pair)
    exact ⟨c :: middle,.cons first tail,.cons second rest⟩

/-- All changed generic values come from the same fixed reads in the actual
changed query. Full instantiation, target kinding, and table alignment are
derived together from the old selection inputs. -/
theorem ImplementationInspected.Ready.relate_values {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {implementation : ImplDefinition} {inspected : ImplementationInspected program implementation}
    {arguments changed : List Term} {values : List Term} {substitution : Substitution}
    (ready : inspected.Ready arguments substitution)
    (instantiated : Instantiates implementation.generics values substitution)
    (kinded : ∀ value ∈ values, Kinding program context value value.kind)
    {relation : Term → Term → Prop}
    (converts : ∀ left right, relation left right → DefinitionallyEqual program context left right)
    (decomposes : ∀ left right, relation left right → left.StructuralHead →
      SameHead left right ∧ ListRel relation left.children right.children)
    (queries : ListRel relation arguments changed) :
    ∃ newValues newSub, Instantiates implementation.generics newValues newSub ∧
      (∀ value ∈ newValues, Kinding program context value value.kind) ∧ inspected.Ready changed newSub ∧
      ListRel (fun first second => first.1 = second.1 ∧ relation first.2 second.2) substitution newSub := by
  have alignment : ListRel (fun binder value => substitution.get binder.id = some value) implementation.generics values :=
    ListRel.of_at instantiated.2.1.length_eq (fun _ _ _ binderAt valueAt => instantiated.binder_lookup_at binderAt valueAt)
  let result := fun binder value => ∀ member : binder ∈ implementation.generics,
    (inspected.path binder member).read changed = some value
  obtain ⟨newValues,related,readable⟩ := ListRel.choose_right (result := result) alignment (by
    intro binder member value _ lookup
    have read : (inspected.path binder member).read arguments = some value := (ready binder member).trans lookup
    obtain ⟨next,readNext,related⟩ := (inspected.path binder member).read_related decomposes queries read
    exact ⟨next,related,fun _ => readNext⟩)
  have transport : ListRel (KindTransport program context) values newValues :=
    related.imp (fun _ _ pair kind typed => ((converts _ _ pair).kinding_iff valid kind).mp typed)
  have nextInst := instantiated.kind_transport kinded transport
  refine ⟨newValues,_,nextInst,transport.arguments_kinded_right kinded,?_,instantiated.related_values related⟩
  intro binder member
  obtain ⟨index,binderAt⟩ := List.mem_iff_getElem?.mp member
  have bound : index < newValues.length := by
    rw [← readable.length_eq]
    exact (List.getElem?_eq_some_iff.mp binderAt).1
  have valueAt : newValues[index]? = some newValues[index] := List.getElem?_eq_getElem bound
  exact (readable.at binderAt valueAt member).trans (nextInst.binder_lookup_at binderAt valueAt).symm

/-- Existing source admission reconstructs selection for the changed values
read from the changed query. Logical requirement graphs are transported by
the proved substitution rule, including all quantified binder masks. -/
theorem SelectsImpl.relate_inspected_query {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {trait : DeclId} {arguments changed : List Term} {negative : Bool}
    {implementation : ImplDefinition} {substitution : Substitution}
    (selected : SelectsImpl program context trait arguments negative implementation substitution)
    {inspected : ImplementationInspected program implementation} (ready : inspected.Ready arguments substitution)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    {relation : Term → Term → Prop}
    (converts : ∀ left right, relation left right → DefinitionallyEqual program context left right)
    (decomposes : ∀ left right, relation left right → left.StructuralHead →
      SameHead left right ∧ ListRel relation left.children right.children)
    (queries : ListRel relation arguments changed) :
    ∃ newSub, SelectsImpl program context trait changed negative implementation newSub ∧
      inspected.Ready changed newSub ∧
      ListRel (fun first second => first.1 = second.1 ∧ relation first.2 second.2) substitution newSub := by
  cases selected with
  | selected declared traitIs negativeIs matched requirements =>
    cases traitIs
    cases negativeIs
    cases matched with
    | inferred instantiated kinded graph lengths head _ =>
      obtain ⟨newValues,newSub,nextInst,nextKinded,nextReady,tables⟩ :=
        ready.relate_values valid instantiated kinded converts decomposes queries
      have converted := tables.imp (fun _ _ pair => And.intro pair.1 (converts _ _ pair.2))
      have lookups := converted.substitution_getD_related (fun _ => .refl)
      have requirementsNext : ∀ requirement ∈ implementation.requirements,
          EntailsSubstitution program context newSub requirement := by
        intro requirement member
        exact (requirements requirement member).convert_logical_substitution valid contextKinded
          (converted.imp (fun _ _ pair => And.intro pair.1 (.definitional pair.2)))
      have actual : ListRel (fun term value => value = term.substitute substitution)
          implementation.arguments (implementation.arguments.map (Term.substitute substitution)) := by
        simpa only [List.map_id] using ListRel.maps implementation.arguments id (Term.substitute substitution) (fun _ _ => rfl)
      have specialized := ListRel.functional (fun _ _ _ first second => first.trans second.symm)
        (graph.imp (fun _ _ graph => graph.2.1)) actual
      have oldHead : ListRel (DefinitionallyEqual program context)
          (implementation.arguments.map (Term.substitute substitution)) arguments := by
        rw [← specialized]
        exact ListRel.of_at lengths head
      have newOld := ListRel.maps implementation.arguments (Term.substitute newSub) (Term.substitute substitution)
        (fun term _ => term.substitutions_convert program context (fun id kind => (lookups id kind).symm))
      have newHead := newOld.transitive (fun _ _ _ first second => first.trans second)
        (oldHead.transitive (fun _ _ _ first second => first.trans second) (queries.imp converts))
      exact ⟨newSub,SelectsImpl.of_admitted_head valid declared contextKinded nextInst nextKinded newHead requirementsNext,
        nextReady,tables⟩

theorem PathInspectedStep.alias_argument_relation {program : Program} {valid : ProgramWellFormed program}
    {relation : Term → Term → Prop} {context : Context} {id : DeclId} {arguments changed : List Term} {value : Term}
    {stepped : DefinitionalStep program context (.alias id arguments) value}
    (_certificate : PathInspectedStep program valid stepped)
    (reflexive : ∀ term, relation term term)
    (converts : ∀ left right, relation left right → DefinitionallyEqual program context left right)
    (substitutionPreserves : ∀ (term : Term) (left right : Substitution),
      (∀ id kind, relation ((left.get id).getD (.parameter id kind))
        ((right.get id).getD (.parameter id kind))) → relation (term.substitute left) (term.substitute right))
    (argumentsRelated : ListRel relation arguments changed) :
    ∃ result, (∃ residual : DefinitionalStep program context (.alias id changed) result,
      PathInspectedStep program valid residual) ∧ relation value result := by
  obtain ⟨result,residual,related⟩ := stepped.alias_argument_relation valid reflexive converts substitutionPreserves argumentsRelated
  cases residual with
  | alias found instantiated kinded graph =>
    exact ⟨result,⟨.alias found instantiated kinded graph,
      .alias (found := found) (instantiated := instantiated) (kinded := kinded) (substituted := graph)⟩,related⟩

theorem PathInspectedStep.projection_argument_relation {program : Program} {valid : ProgramWellFormed program}
    {relation : Term → Term → Prop} {context : Context} {trait member : DeclId} {owners items changedOwners changedItems : List Term}
    {kind : Kind} {value : Term} {stepped : DefinitionalStep program context (.projection trait member owners items kind) value}
    (certificate : PathInspectedStep program valid stepped)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    (reflexive : ∀ term, relation term term)
    (converts : ∀ left right, relation left right → DefinitionallyEqual program context left right)
    (decomposes : ∀ left right, relation left right → left.StructuralHead →
      SameHead left right ∧ ListRel relation left.children right.children)
    (substitutionPreserves : ∀ (term : Term) (left right : Substitution),
      (∀ id kind, relation ((left.get id).getD (.parameter id kind))
        ((right.get id).getD (.parameter id kind))) → relation (term.substitute left) (term.substitute right))
    (ownerRelated : ListRel relation owners changedOwners) (itemRelated : ListRel relation items changedItems) :
    ∃ result, (∃ residual : DefinitionalStep program context (.projection trait member changedOwners changedItems kind) result,
      PathInspectedStep program valid residual) ∧ relation value result := by
  cases certificate with
  | @projection _ _ _ _ _ _ _ _ _ _ _ domain selected present graph ready =>
    obtain ⟨newOwnerSub,newItemSub,nextDomain,_,itemTables⟩ := domain.relate_arguments valid converts ownerRelated itemRelated
    obtain ⟨newImplSub,nextSelected,nextReady,implTables⟩ :=
      selected.relate_inspected_query valid ready contextKinded converts decomposes ownerRelated
    have lookup := (implTables.append itemTables).substitution_getD_related reflexive
    have nextGraph := graph.congr_substitution valid (right := newImplSub ++ newItemSub)
      (fun id kind => converts _ _ (lookup id kind))
    refine ⟨_,⟨.projection nextDomain nextSelected present nextGraph,
      .projection (domain := nextDomain) (selected := nextSelected) (present := present) (substituted := nextGraph) nextReady⟩,?_⟩
    rw [graph.2.1]
    exact substitutionPreserves _ _ _ lookup
  | @defaultProjection _ _ _ _ _ _ _ _ _ _ _ domain selected absent default graph ready =>
    obtain ⟨newOwnerSub,newItemSub,nextDomain,ownerTables,itemTables⟩ := domain.relate_arguments valid converts ownerRelated itemRelated
    obtain ⟨newImplSub,nextSelected,nextReady,_⟩ :=
      selected.relate_inspected_query valid ready contextKinded converts decomposes ownerRelated
    have lookup := (ownerTables.append itemTables).substitution_getD_related reflexive
    have nextGraph := graph.congr_substitution valid (right := newOwnerSub ++ newItemSub)
      (fun id kind => converts _ _ (lookup id kind))
    refine ⟨_,⟨.defaultProjection nextDomain nextSelected absent default nextGraph,
      .defaultProjection (domain := nextDomain) (selected := nextSelected) (absent := absent)
        (default := default) (substituted := nextGraph) nextReady⟩,?_⟩
    rw [graph.2.1]
    exact substitutionPreserves _ _ _ lookup

/-- Fixed-path inspection has an actual residual after all ordered query
children change. The generic values and root body follow the given relation;
the new selection and readiness proof are constructed, not postulated. -/
theorem PathInspectedStep.children_relation {program : Program} {valid : ProgramWellFormed program}
    {relation : Term → Term → Prop} {context : Context} {term value changed : Term}
    {stepped : DefinitionalStep program context term value} (certificate : PathInspectedStep program valid stepped)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    (reflexive : ∀ term, relation term term)
    (converts : ∀ left right, relation left right → DefinitionallyEqual program context left right)
    (decomposes : ∀ left right, relation left right → left.StructuralHead →
      SameHead left right ∧ ListRel relation left.children right.children)
    (substitutionPreserves : ∀ (term : Term) (left right : Substitution),
      (∀ id kind, relation ((left.get id).getD (.parameter id kind))
        ((right.get id).getD (.parameter id kind))) → relation (term.substitute left) (term.substitute right))
    (same : SameHead term changed) (children : ListRel relation term.children changed.children) :
    ∃ result, (∃ residual : DefinitionalStep program context changed result, PathInspectedStep program valid residual) ∧
      relation value result := by
  cases certificate <;> cases changed <;> simp [SameHead,Term.mapChildren] at same
  all_goals simp only [Term.children] at children
  case alias.alias =>
    rcases same with ⟨rfl,_⟩
    exact PathInspectedStep.alias_argument_relation
      (.alias (found := by assumption) (instantiated := by assumption) (kinded := by assumption) (substituted := by assumption))
      reflexive converts substitutionPreserves children
  case projection.projection =>
    rcases same with ⟨rfl,rfl,ownerShapes,_,kindIs⟩
    have split := children.split_append (by simpa using congrArg List.length ownerShapes)
    rw [← kindIs]
    exact PathInspectedStep.projection_argument_relation
      (.projection (domain := by assumption) (selected := by assumption) (present := by assumption) (substituted := by assumption)
        (by assumption)) contextKinded reflexive converts decomposes substitutionPreserves split.1 split.2
  case defaultProjection.projection =>
    rcases same with ⟨rfl,rfl,ownerShapes,_,kindIs⟩
    have split := children.split_append (by simpa using congrArg List.length ownerShapes)
    rw [← kindIs]
    exact PathInspectedStep.projection_argument_relation
      (.defaultProjection (domain := by assumption) (selected := by assumption) (absent := by assumption)
        (default := by assumption) (substituted := by assumption) (by assumption))
      contextKinded reflexive converts decomposes substitutionPreserves split.1 split.2

/-- Actual positive child reductions update fixed reads and preserve the
canonical root restriction. This is a residual square, not confluence. -/
theorem PathInspectedStep.children_residual {program : Program} {valid : ProgramWellFormed program}
    {context : Context} {term value changed : Term} {stepped : DefinitionalStep program context term value}
    (certificate : PathInspectedStep program valid stepped)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    (same : SameHead term changed)
    (children : ListRel (DefinitionalReduction program context) term.children changed.children) :
    ∃ result, (∃ residual : DefinitionalStep program context changed result, PathInspectedStep program valid residual) ∧
      DefinitionalReduction program context value result :=
  certificate.children_relation contextKinded (fun _ => .refl) (fun _ _ reduced => reduced.equal)
    (fun _ _ reduced structural => reduced.structural_decomposition structural)
    (fun term _ _ agree => term.substitutions_reduce program context agree) same children

/-- Row-equivalent queries retain their actual fixed-path root and return a
row-equivalent body. The shared row closure theorem handles all row laws. -/
theorem PathInspectedStep.row_residual {program : Program} {valid : ProgramWellFormed program}
    {context : Context} {term value changed : Term} {stepped : DefinitionalStep program context term value}
    (certificate : PathInspectedStep program valid stepped)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    (equivalent : RowEquivalent term changed) :
    ∃ result, (∃ residual : DefinitionalStep program context changed result, PathInspectedStep program valid residual) ∧
      RowEquivalent value result :=
  (equivalent.root_relation_residuals
    (root := fun left right => ∃ root : DefinitionalStep program context left right, PathInspectedStep program valid root)
    (fun _ _ _ impossible => by obtain ⟨root,_⟩ := impossible; cases root)
    (fun ⟨_,rootCertificate⟩ same children => rootCertificate.children_relation contextKinded
      (fun _ => .refl) (fun _ _ equivalent => .row equivalent)
      (fun _ _ equivalent structural => equivalent.structural_decomposition structural)
      (fun term _ _ agree => term.substitutions_rowEquivalent agree) same children)).1 value ⟨stepped,certificate⟩

end Glorious.Language
