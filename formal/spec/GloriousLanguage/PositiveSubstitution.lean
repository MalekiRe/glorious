import GloriousLanguage.LogicalInstantiation
import GloriousLanguage.SubstitutionAtomModel
import GloriousLanguage.AtomRelations
import GloriousLanguage.AtomOpening
import GloriousLanguage.HeadInspection

/-! Positive source reductions survive lawful caller instantiation. Logical
requirements use the proved hygienic cut; they are not smuggled into the
positive relation as arbitrary equality. Internal unkinded congruence nodes
use the same guarded proof-model map as capability substitution. -/
namespace Glorious.Language

private theorem Instantiates.guarded_substitution_table {program : Program} {source target : Context}
    {binders : List Binder} {values : List Term} {inner : Substitution}
    (instantiated : Instantiates binders values inner)
    (typed : ∀ value ∈ values, Kinding program source value value.kind) (outer : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute outer) binder.kind) :
    inner.map (fun entry => (entry.1,SubstitutionAtomModel.term outer entry.2)) =
      inner.map (fun entry => (entry.1,entry.2.substitute outer)) := by
  apply List.map_congr_left
  intro entry member
  have present : entry.2 ∈ values := by
    rw [instantiated.2.2] at member
    exact (List.of_mem_zip member).2
  rw [SubstitutionAtomModel.kinded_eq (typed entry.2 present) outer parameters]

theorem DefinitionalStep.map_substitute_inspected {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {left right : Term} (stepped : DefinitionalStep program source left right)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (outer : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute outer) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (assumptions : ∀ requirement ∈ source.assumptions, EntailsSubstitution program target outer requirement) :
    ∃ mapped : DefinitionalStep program target (SubstitutionAtomModel.term outer left) (SubstitutionAtomModel.term outer right),
      ∀ level, HeadInspectionStepAt program level stepped → HeadInspectionStepAt program level mapped := by
  let map := SubstitutionAtomModel.term outer
  let mapSub := fun (substitution : Substitution) => substitution.map (fun entry => (entry.1,map entry.2))
  have shape : AtomHomomorphism map := SubstitutionAtomModel.shape outer
  have mapKinds : ∀ term, (map term).kind = term.kind := SubstitutionAtomModel.kind outer
  have mappedKind {term : Term} {kind : Kind} (typed : Kinding program source term kind) :
      Kinding program target (map term) kind := by
    change Kinding program target (SubstitutionAtomModel.term outer term) kind
    rw [SubstitutionAtomModel.kinded_eq typed outer parameters]
    exact typed.substitute outer parameters levels regions brands
  refine DefinitionalStep.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun context trait arguments negative implementation substitution _ => context = source →
      SelectsImpl program target trait (arguments.map map) negative implementation (mapSub substitution))
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ => True)
    (motive_8 := fun _ _ _ => True)
    (motive_9 := fun _ _ _ _ => True)
    (motive_10 := fun context left right stepped => context = source →
      ∃ mapped : DefinitionalStep program target (map left) (map right),
        ∀ level, HeadInspectionStepAt program level stepped → HeadInspectionStepAt program level mapped)
    (motive_11 := fun context left right _ => context = source → DefinitionallyEqual program target (map left) (map right))
    (motive_12 := fun context left right _ => context = source → DefinitionalReduction program target (map left) (map right))
    (motive_13 := fun context implementation arguments substitution _ => context = source →
      Definition.implementation implementation ∈ program.declarations →
        MatchesImplHead program target implementation (arguments.map map) (mapSub substitution))
    (motive_14 := fun context trait member owners items associated ownerSub itemSub _ => context = source →
      ProjectionDomain program target trait member (owners.map map) (items.map map) associated (mapSub ownerSub) (mapSub itemSub))
    (motive_15 := fun sourceContext context binder template query value _ => context = source →
      InfersHeadParameter program sourceContext target binder template (map query) (map value))
    (motive_16 := fun context implementation arguments binder value _ => context = source →
      InfersHeadArgument program target implementation (arguments.map map) binder (map value))
    ?unused_structural ?unused_logical ?unused_capEqual ?unused_equation ?unused_evidence
    ?unused_refl ?unused_symm ?unused_trans ?unused_congrChildren ?unused_assumed ?unused_entailed ?unused_definitional
    ?unused_rowDuplicate ?unused_tailDuplicate ?selected ?unused_head ?unused_tail ?unused_equal_1 ?unused_empty ?unused_assumed_1 ?unused_same ?unused_trans_1 ?unused_instances ?unused_entailed_1
    ?unused_assumed_2 ?unused_scalar ?unused_unit ?unused_pointer ?unused_reference ?unused_bottom ?unused_tuple ?unused_array ?unused_nominal ?unused_callable ?unused_label ?unused_environment
    ?unused_available ?unused_bindings ?unused_equal_2 ?unused_entailed_2 ?unused_checkedCallable ?unused_checkedRunsIn ?unused_assumed_3 ?unused_congrSubstitution ?unused_equality
    ?unused_outlivesRefl ?unused_outlivesStatic ?unused_outlivesTrans ?unused_typeOutlives
    ?unused_rows ?unused_implementation ?unused_use ?unused_quantified ?unused_quantifiedInstance ?unused_instantiated
    ?alias ?projection ?defaultProjection
    ?refl ?symm ?trans ?congr ?step ?row
    ?refl_1 ?step_1 ?trans_1 ?congr_1 ?row_1
    ?inferred ?domainValid ?parameter ?child ?sourceReduction ?queryConversion ?argument stepped rfl
  all_goals intros
  all_goals try exact True.intro
  case selected _ _ _ _ implementation substitution declared trait negative matched requirements headIH _ sameContext =>
    cases sameContext
    have predicates := (valid.2.2.2.2.1 _ declared).2.2
    obtain ⟨values,instantiated,typed⟩ : ∃ values, Instantiates implementation.generics values substitution ∧
        ∀ value ∈ values, Kinding program source value value.kind := by
      cases matched with
      | inferred instantiated typed _ _ _ _ => exact ⟨_,instantiated,typed⟩
    refine .selected declared trait negative (headIH rfl declared) ?_
    intro requirement member
    rw [show mapSub substitution = substitution.map (fun entry => (entry.1,entry.2.substitute outer)) from
      instantiated.guarded_substitution_table typed outer parameters]
    exact (requirements requirement member).substitute_values valid sourceKinded targetKinded
      (predicates requirement member) instantiated typed outer parameters (Nat.zero_le _)
      (fun _ member => False.elim (List.not_mem_nil member))
      (fun _ member => False.elim (List.not_mem_nil member)) levels regions brands assumptions
  case alias _ _ _ arguments _ _ found instantiated typed graph sameContext =>
    cases sameContext
    rw [shape (.alias _ _)]
    have targetInst := instantiated.map_values map (fun term _ => mapKinds term)
    have targetKinds : ∀ term ∈ arguments.map map, Kinding program target term term.kind := by
      intro term member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      simpa only [mapKinds] using mappedKind (typed original present)
    have targetGraph := graph.map_instantiated (valid.alias_body found) instantiated map shape
      (SubstitutionAtomModel.fixed outer _) mapKinds
    exact ⟨.alias found targetInst targetKinds targetGraph,fun _ _ =>
      .alias (found := found) (instantiated := targetInst) (kinded := targetKinds) (substituted := targetGraph)⟩
  case projection _ _ _ _ _ _ _ _ _ _ _ domain selected member graph domainIH selectedIH sameContext =>
    cases sameContext
    rw [shape (.projection _ _ _ _ _)]
    have targetDomain := domainIH rfl
    obtain ⟨values,instantiated,_⟩ := selected.instantiates
    cases domain with
    | valid _ _ associatedFound _ _ itemInst _ _ _ =>
      obtain ⟨unique,_,bodyKinded⟩ := valid.override_body selected.declaration associatedFound member
      have targetGraph := graph.map_instantiated bodyKinded
        (instantiated.append itemInst unique) map shape (SubstitutionAtomModel.fixed outer _) mapKinds
      have targetSelected := selectedIH rfl
      simp only [List.map_append] at targetGraph
      refine ⟨.projection targetDomain targetSelected member targetGraph,?_⟩
      intro bound certificate
      obtain ⟨level,inspected,lower⟩ := certificate.selected_level valid rfl selected
      exact .projection (domain := targetDomain) (selected := targetSelected)
        (present := member) (substituted := targetGraph) inspected lower
  case defaultProjection _ _ _ _ _ _ _ _ _ _ _ _ domain selected absent default graph domainIH selectedIH sameContext =>
    cases sameContext
    rw [shape (.projection _ _ _ _ _)]
    have targetDomain := domainIH rfl
    cases domain with
    | valid traitFound _ associatedFound owner ownerInst itemInst _ _ _ =>
      obtain ⟨unique,bodyKinded⟩ := valid.default_body traitFound associatedFound owner default
      have targetGraph := graph.map_instantiated bodyKinded
        (ownerInst.append itemInst unique) map shape (SubstitutionAtomModel.fixed outer _) mapKinds
      have targetSelected := selectedIH rfl
      simp only [List.map_append] at targetGraph
      refine ⟨.defaultProjection targetDomain targetSelected absent default targetGraph,?_⟩
      intro bound certificate
      obtain ⟨level,inspected,lower⟩ := certificate.selected_level valid rfl selected
      exact .defaultProjection (domain := targetDomain) (selected := targetSelected)
        (absent := absent) (default := default) (substituted := targetGraph) inspected lower
  case refl _ _ sameContext => cases sameContext; exact .refl
  case symm _ _ _ _ ih sameContext => cases sameContext; exact .symm (ih rfl)
  case trans _ _ _ _ _ _ first second sameContext => cases sameContext; exact .trans (first rfl) (second rfl)
  case congr _ _ _ same _ children sameContext =>
    cases sameContext
    exact shape.congr_relation (fun _ => .refl) DefinitionallyEqual.congr same
      (ListRel.of_at same.children_length (fun index first second leftAt rightAt => children index first second leftAt rightAt rfl))
  case step _ _ _ _ ih sameContext =>
    cases sameContext
    obtain ⟨mapped,_⟩ := ih rfl
    exact .step mapped
  case row _ _ _ equivalent sameContext => cases sameContext; exact .row (equivalent.map_atoms map shape)
  case refl_1 _ _ sameContext => cases sameContext; exact .refl
  case step_1 _ _ _ _ ih sameContext =>
    cases sameContext
    obtain ⟨mapped,_⟩ := ih rfl
    exact .step mapped
  case trans_1 _ _ _ _ _ _ first second sameContext => cases sameContext; exact .trans (first rfl) (second rfl)
  case congr_1 _ _ _ same _ children sameContext =>
    cases sameContext
    exact shape.congr_relation (fun _ => .refl) DefinitionalReduction.congr same
      (ListRel.of_at same.children_length (fun index first second leftAt rightAt => children index first second leftAt rightAt rfl))
  case row_1 _ _ _ equivalent sameContext => cases sameContext; exact .row (equivalent.map_atoms map shape)
  case inferred _ _ _ _ _ specialized instantiated typed graph lengths _ _ head origins sameContext declared =>
    cases sameContext
    obtain ⟨_,_,_,_,_,_,_,signature,_⟩ := (valid.2.2.2.2.1 _ declared).2.1
    obtain ⟨_,_,_,_,headKinded,_,_⟩ := signature
    refine .inferred (specialized := specialized.map map) (instantiated.map_values map (fun term _ => mapKinds term)) ?_ ?_ ?_ ?_ ?_
    · intro term member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      simpa only [mapKinds] using mappedKind (typed original present)
    · exact graph.map_instantiated_kinded (fun term member => (headKinded term member).1) instantiated map shape
        (fun term _ => SubstitutionAtomModel.fixed outer term) mapKinds
    · simpa only [List.length_map] using lengths
    · exact AtomHomomorphism.list_at (fun index first second leftAt rightAt => head index first second leftAt rightAt rfl)
    · intro index binder value binderAt valueAt
      obtain ⟨original,originalAt,rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using valueAt)
      exact origins index binder original binderAt originalAt rfl
  case domainValid context traitId memberId owners items declaration associated ownerSub itemSub
      found member associatedFound owner ownerInst itemInst typed ownerRequirements itemRequirements _ _ sameContext =>
    cases sameContext
    have traitAdmitted := valid.2.2.2.2.1 _ (List.mem_of_find?_eq_some (Program.trait_lookup found))
    have itemAdmitted := valid.2.2.2.2.1 _ (List.mem_of_find?_eq_some (Program.associated_lookup associatedFound))
    obtain ⟨sourceTrait,sourceFound,itemPredicates⟩ := itemAdmitted.2.2
    rw [owner,found] at sourceFound
    cases Option.some.inj sourceFound
    obtain ⟨sourceTrait,sourceFound,_,unique,_⟩ := itemAdmitted.2.1
    rw [owner,found] at sourceFound
    cases Option.some.inj sourceFound
    refine .valid found member associatedFound owner
      (ownerInst.map_values map (fun term _ => mapKinds term))
      (itemInst.map_values map (fun term _ => mapKinds term)) ?_ ?_ ?_
    · intro term present
      rw [← List.map_append] at present
      obtain ⟨original,inside,rfl⟩ := List.mem_map.mp present
      simpa only [mapKinds] using mappedKind (typed original inside)
    · intro requirement present
      have ownerTyped := fun value inside => typed value (List.mem_append_left items inside)
      rw [show mapSub ownerSub = ownerSub.map (fun entry => (entry.1,entry.2.substitute outer)) from
        ownerInst.guarded_substitution_table ownerTyped outer parameters]
      exact (ownerRequirements requirement present).substitute_values valid sourceKinded targetKinded
        (traitAdmitted.2.2 requirement present) ownerInst ownerTyped outer parameters (Nat.zero_le _)
        (fun _ member => False.elim (List.not_mem_nil member))
        (fun _ member => False.elim (List.not_mem_nil member)) levels regions brands assumptions
    · intro requirement present
      have fullInstance := ownerInst.append itemInst unique
      have tables := fullInstance.guarded_substitution_table typed outer parameters
      simp only [List.map_append] at tables
      change EntailsSubstitution program target (mapSub ownerSub ++ mapSub itemSub) requirement
      rw [show mapSub ownerSub ++ mapSub itemSub =
        (ownerSub ++ itemSub).map (fun entry => (entry.1,entry.2.substitute outer)) from
          by simpa only [mapSub,List.map_append] using tables]
      exact (itemRequirements requirement present).substitute_values valid sourceKinded targetKinded
        (itemPredicates requirement present) fullInstance typed outer parameters (Nat.zero_le _)
        (fun _ member => False.elim (List.not_mem_nil member))
        (fun _ member => False.elim (List.not_mem_nil member)) levels regions brands assumptions
  case parameter _ _ _ _ same sameContext => cases sameContext; exact .parameter ((mapKinds _).trans same)
  case child _ _ _ _ _ _ _ _ _ structural same leftAt rightAt _ ih sameContext =>
    cases sameContext
    obtain ⟨sameMapped,children⟩ := shape.child_head same (List.mem_of_getElem? rightAt)
    exact .child structural sameMapped leftAt (by rw [children,List.getElem?_map,rightAt]; rfl) (ih rfl)
  case sourceReduction _ _ _ _ _ _ _ reduction _ _ ih sameContext =>
    cases sameContext
    exact .sourceReduction reduction (ih rfl)
  case queryConversion _ _ _ _ _ _ _ _ _ equal origin sameContext =>
    cases sameContext
    exact .queryConversion (equal rfl) (origin rfl)
  case argument _ _ _ _ _ _ _ _ leftAt rightAt _ ih sameContext =>
    cases sameContext
    exact .argument leftAt (by rw [List.getElem?_map,rightAt]; rfl) (ih rfl)

theorem DefinitionalStep.map_substitute {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {left right : Term} (stepped : DefinitionalStep program source left right)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (outer : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute outer) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (assumptions : ∀ requirement ∈ source.assumptions, EntailsSubstitution program target outer requirement) :
    DefinitionalStep program target (SubstitutionAtomModel.term outer left) (SubstitutionAtomModel.term outer right) := by
  obtain ⟨mapped,_⟩ := stepped.map_substitute_inspected valid sourceKinded targetKinded outer parameters levels regions brands assumptions
  exact mapped

/-- Positive closure delegates every genuine root step to the single
selection-and-predicate transport above. -/
theorem DefinitionalReduction.map_substitute {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {left right : Term} (reduced : DefinitionalReduction program source left right)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (outer : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute outer) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (assumptions : ∀ requirement ∈ source.assumptions, EntailsSubstitution program target outer requirement) :
    DefinitionalReduction program target (SubstitutionAtomModel.term outer left) (SubstitutionAtomModel.term outer right) := by
  let map := SubstitutionAtomModel.term outer
  have shape : AtomHomomorphism map := SubstitutionAtomModel.shape outer
  have transported : source = source → DefinitionalReduction program target (map left) (map right) := by
    apply DefinitionalReduction.rec
      (motive_1 := fun _ _ _ _ => True)
      (motive_2 := fun _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ _ => True)
      (motive_5 := fun _ _ _ _ => True)
      (motive_6 := fun _ _ _ _ => True)
      (motive_7 := fun _ _ _ _ => True)
      (motive_8 := fun _ _ _ => True)
      (motive_9 := fun _ _ _ _ => True)
      (motive_10 := fun _ _ _ _ => True)
      (motive_11 := fun _ _ _ _ => True)
      (motive_12 := fun context left right _ => context = source → DefinitionalReduction program target (map left) (map right))
      (motive_13 := fun _ _ _ _ _ => True)
      (motive_14 := fun _ _ _ _ _ _ _ _ _ => True)
      (motive_15 := fun _ _ _ _ _ _ _ => True)
      (motive_16 := fun _ _ _ _ _ _ => True)
      <;> try assumption
    all_goals intros
    all_goals try exact True.intro
    case refl _ _ sameContext => cases sameContext; exact .refl
    case step _ _ _ stepped _ sameContext =>
      cases sameContext
      exact .step (stepped.map_substitute valid sourceKinded targetKinded outer parameters levels regions brands assumptions)
    case trans _ _ _ _ _ _ first second sameContext =>
      cases sameContext
      exact .trans (first rfl) (second rfl)
    case congrChildren _ _ _ same _ children sameContext =>
      cases sameContext
      exact shape.congr_relation (fun _ => .refl) DefinitionalReduction.congr same
        (ListRel.of_at same.children_length (fun index first second leftAt rightAt =>
          children index first second leftAt rightAt rfl))
    case row _ _ _ equivalent sameContext => cases sameContext; exact .row (equivalent.map_atoms map shape)
  exact transported rfl

/-- The proof-model map agrees with actual simultaneous substitution on
both endpoints of every admitted positive source reduction. -/
theorem DefinitionalReduction.substitute {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {left right : Term} {kind : Kind}
    (reduced : DefinitionalReduction program source left right)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (kinded : Kinding program source left kind) (outer : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute outer) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (assumptions : ∀ requirement ∈ source.assumptions, EntailsSubstitution program target outer requirement) :
    DefinitionalReduction program target (left.substitute outer) (right.substitute outer) := by
  have transported := reduced.map_substitute valid sourceKinded targetKinded outer parameters levels regions brands assumptions
  rw [SubstitutionAtomModel.kinded_eq kinded outer parameters,
    SubstitutionAtomModel.kinded_eq (reduced.kinding valid kinded) outer parameters] at transported
  exact transported

theorem DefinitionalReduction.instantiate {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {left right : Term} {kind : Kind}
    (reduced : DefinitionalReduction program source left right)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (kinded : Kinding program source left kind) {values : List Term} {substitution : Substitution}
    (instantiated : Instantiates source.binders values substitution)
    (valuesKinded : ∀ value ∈ values, Kinding program target value value.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (assumptions : ∀ requirement ∈ source.assumptions, EntailsSubstitution program target substitution requirement) :
    DefinitionalReduction program target (left.substitute substitution) (right.substitute substitution) :=
  reduced.substitute valid sourceKinded targetKinded kinded substitution (instantiated.kinding_parameters valuesKinded)
    levels regions brands assumptions

end Glorious.Language
