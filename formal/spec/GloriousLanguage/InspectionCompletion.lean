import GloriousLanguage.InspectionConfluence
import GloriousLanguage.FullInspectionSubstitution

/-! Ordinary root completion through actual admitted source paths. The source
and head-query subobligations remain explicit until discharged by full finite
inspection induction; no ordinary-to-canonical simulation is assumed here. -/
namespace Glorious.Language

/-- This is the exact data-selected source path, replayed in the real caller
at the same FULL inspection level. It does not choose another binder origin. -/
theorem HeadInspectionPath.caller_replay {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {implementation : ImplDefinition} {binder : Binder} {level : Nat}
    (path : HeadInspectionPath program implementation binder level)
    (declared : Definition.implementation implementation ∈ program.declarations)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    {values : List Term} {substitution : Substitution} (instantiated : Instantiates implementation.generics values substitution)
    (valuesKinded : ∀ value ∈ values, Kinding program context value value.kind)
    (requirements : ∀ requirement ∈ implementation.requirements, EntailsSubstitution program context substitution requirement) :
    ∃ replay : DefinitionalReduction program context (path.template.substitute substitution) (path.expanded.substitute substitution),
      FullHeadInspectionReductionAt program level replay := by
  obtain ⟨_,_,_,_,_,_,_,signature,_⟩ := (valid.2.2.2.2.1 _ declared).2.1
  obtain ⟨_,_,_,_,headKinded,_,_⟩ := signature
  exact path.certificate.instantiate valid (valid.implementation_requirements declared) contextKinded
    (headKinded path.template (List.mem_of_getElem? path.sourceAt)).1 instantiated valuesKinded (Nat.zero_le _)
    (fun _ absent => False.elim (List.not_mem_nil absent)) (fun _ absent => False.elim (List.not_mem_nil absent)) requirements

private def HeadInspectionPath.exposed_query {program : Program} {implementation : ImplDefinition} {binder : Binder} {level : Nat}
    (path : HeadInspectionPath program implementation binder level) (substitution : Substitution) : List Term :=
  (implementation.arguments.map (Term.substitute substitution)).set path.argument (path.expanded.substitute substitution)

private theorem HeadInspectionPath.exposed_read {program : Program} {implementation : ImplDefinition} {binder : Binder} {level : Nat}
    (path : HeadInspectionPath program implementation binder level) (substitution : Substitution) :
    path.read (path.exposed_query substitution) = some ((substitution.get binder.id).getD (.parameter binder.id binder.kind)) := by
  have bound : path.argument < (implementation.arguments.map (Term.substitute substitution)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp path.sourceAt).1
  simp only [HeadInspectionPath.read,HeadInspectionPath.exposed_query,List.getElem?_set_self bound,Option.bind_some]
  simpa only [Term.substitute] using Term.structuralAt_substitute path.parameterAt substitution

private theorem HeadInspectionPath.exposed_join {program : Program} {valid : ProgramWellFormed program} {context : Context}
    {implementation : ImplDefinition} {binder : Binder} {level : Nat}
    (path : HeadInspectionPath program implementation binder level) (substitution : Substitution)
    (sourceJoin : InspectionJoinable program valid context (path.template.substitute substitution) (path.expanded.substitute substitution)) :
    ListRel (InspectionJoinable program valid context) (implementation.arguments.map (Term.substitute substitution))
      (path.exposed_query substitution) := by
  apply ListRel.set_at (fun term => InspectionJoinable.refl term) _ sourceJoin
  rw [List.getElem?_map,path.sourceAt]
  rfl

/-- All fixed paths become simultaneously readable in one actual canonical
query development. Their old raw values positively develop to those reads. -/
theorem ImplementationInspected.common_reads {program : Program} {valid : ProgramWellFormed program} {context : Context}
    {implementation : ImplDefinition} (inspected : ImplementationInspected program implementation)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    {queries : List Term} {substitution : Substitution}
    (headJoin : ListRel (InspectionJoinable program valid context)
      (implementation.arguments.map (Term.substitute substitution)) queries)
    (sourceJoin : ∀ binder (member : binder ∈ implementation.generics),
      InspectionJoinable program valid context ((inspected.path binder member).template.substitute substitution)
        ((inspected.path binder member).expanded.substitute substitution)) :
    ∃ common, ListRel (InspectionReduction program valid context) queries common ∧
      ∀ binder (member : binder ∈ implementation.generics), ∃ value,
        (inspected.path binder member).read common = some value ∧
        InspectionReduction program valid context ((substitution.get binder.id).getD (.parameter binder.id binder.kind)) value := by
  let variants := implementation.generics.attach.map (fun binder => (inspected.path binder.val binder.property).exposed_query substitution)
  have joined : ∀ variant ∈ variants, ListRel (InspectionJoinable program valid context) queries variant := by
    intro variant member
    obtain ⟨binder,_,rfl⟩ := List.mem_map.mp member
    exact (headJoin.swap.imp (fun _ _ same => same.symm)).transitive
      (fun _ _ _ first second => first.trans contextKinded second)
      ((inspected.path binder.val binder.property).exposed_join substitution (sourceJoin binder.val binder.property))
  obtain ⟨common,queryCommon,variantsCommon⟩ := ListRel.inspection_common_family contextKinded queries variants joined
  refine ⟨common,queryCommon,?_⟩
  intro binder member
  have exposed : (inspected.path binder member).exposed_query substitution ∈ variants := by
    apply List.mem_map.mpr
    exact ⟨⟨binder,member⟩,List.mem_attach _ _,rfl⟩
  exact (inspected.path binder member).read_related
    (fun _ _ reduced structural => reduced.structural_decomposition structural)
    (variantsCommon _ exposed) ((inspected.path binder member).exposed_read substitution)

/-- Completion reconstructs an actual selection at the common query, with
the related raw generic table produced by the shared instantiation rule. -/
theorem SelectsImpl.complete_query {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {trait : DeclId} {arguments : List Term} {negative : Bool}
    {implementation : ImplDefinition} {substitution : Substitution}
    (selected : SelectsImpl program context trait arguments negative implementation substitution)
    (inspected : ImplementationInspected program implementation)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    (headJoin : ListRel (InspectionJoinable program valid context)
      (implementation.arguments.map (Term.substitute substitution)) arguments)
    (sourceJoin : ∀ binder (member : binder ∈ implementation.generics),
      InspectionJoinable program valid context ((inspected.path binder member).template.substitute substitution)
        ((inspected.path binder member).expanded.substitute substitution)) :
    ∃ common newSub, SelectsImpl program context trait common negative implementation newSub ∧
      inspected.Ready common newSub ∧ ListRel (InspectionReduction program valid context) arguments common ∧
      ListRel (fun first second => first.1 = second.1 ∧ InspectionReduction program valid context first.2 second.2) substitution newSub := by
  obtain ⟨common,queryCommon,reads⟩ := inspected.common_reads contextKinded headJoin sourceJoin
  obtain ⟨values,instantiated,kinded⟩ := selected.instantiates
  obtain ⟨newValues,newSub,nextInst,nextKinds,ready,tables⟩ :=
    inspected.instantiate_reads valid instantiated kinded (fun _ _ reduced => reduced.positive.equal) reads
  exact ⟨common,newSub,selected.with_related_values valid contextKinded nextInst nextKinds
    (tables.imp (fun _ _ pair => And.intro pair.1 pair.2.positive.equal))
    (queryCommon.imp (fun _ _ reduced => reduced.positive.equal)),ready,queryCommon,tables⟩

private theorem projection_head {trait member : DeclId} {owners changed items : List Term} {kind : Kind}
    (lengths : owners.length = changed.length) :
    SameHead (.projection trait member owners items kind) (.projection trait member changed items kind) := by
  simp only [SameHead,Term.mapChildren,Term.projection.injEq,true_and,and_true]
  simpa only [List.map_const'] using congrArg (fun length => List.replicate length Term.unit) lengths

/-- An ordinary override root and its canonical completion actually join.
Only its proper head-query and fixed source-exposure obligations are inputs. -/
theorem DefinitionalStep.override_complete {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {trait member : DeclId} {owners items : List Term} {associated : AssociatedDefinition}
    {ownerSub itemSub : Substitution} {implementation : ImplDefinition} {implSub : Substitution} {body value : Term}
    (domain : ProjectionDomain program context trait member owners items associated ownerSub itemSub)
    (selected : SelectsImpl program context trait owners false implementation implSub)
    (present : (member,body) ∈ implementation.associated) (graph : Substitutes (implSub ++ itemSub) body value)
    (inspected : ImplementationInspected program implementation)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    (headJoin : ListRel (InspectionJoinable program valid context) (implementation.arguments.map (Term.substitute implSub)) owners)
    (sourceJoin : ∀ binder (member : binder ∈ implementation.generics),
      InspectionJoinable program valid context ((inspected.path binder member).template.substitute implSub)
        ((inspected.path binder member).expanded.substitute implSub)) :
    InspectionJoinable program valid context (.projection trait member owners items associated.kind) value := by
  obtain ⟨common,newImplSub,nextSelected,ready,queryCommon,implTables⟩ :=
    selected.complete_query valid inspected contextKinded headJoin sourceJoin
  have itemsSame : ListRel (InspectionReduction program valid context) items items := .reflexive (fun _ => .refl) _
  obtain ⟨newOwnerSub,newItemSub,nextDomain,_,itemTables⟩ :=
    domain.relate_arguments valid (fun _ _ reduced => reduced.positive.equal) queryCommon itemsSame
  have lookup := (implTables.append itemTables).substitution_getD_related (fun _ => PositiveClosure.refl)
  have nextGraph := graph.congr_substitution valid (fun id kind => (InspectionReduction.positive (lookup id kind)).equal)
  have bodyReduced : InspectionReduction program valid context value (body.substitute (newImplSub ++ newItemSub)) := by
    rw [graph.2.1]
    exact body.substitutions_related InspectionReduction.congr lookup
  refine ⟨_,?_,bodyReduced⟩
  apply PositiveClosure.trans
  · exact InspectionReduction.congr (projection_head queryCommon.length_eq) (queryCommon.append itemsSame)
  · exact InspectionReduction.root
      (PathInspectedStep.projection (domain := nextDomain) (selected := nextSelected) (present := present)
        (substituted := nextGraph) ready)

theorem DefinitionalStep.default_complete {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {trait member : DeclId} {owners items : List Term} {associated : AssociatedDefinition}
    {ownerSub itemSub : Substitution} {implementation : ImplDefinition} {implSub : Substitution} {body value : Term}
    (domain : ProjectionDomain program context trait member owners items associated ownerSub itemSub)
    (selected : SelectsImpl program context trait owners false implementation implSub)
    (absent : ∀ body, (member,body) ∉ implementation.associated) (default : associated.defaultValue = some body)
    (graph : Substitutes (ownerSub ++ itemSub) body value) (inspected : ImplementationInspected program implementation)
    (contextKinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement)
    (headJoin : ListRel (InspectionJoinable program valid context) (implementation.arguments.map (Term.substitute implSub)) owners)
    (sourceJoin : ∀ binder (member : binder ∈ implementation.generics),
      InspectionJoinable program valid context ((inspected.path binder member).template.substitute implSub)
        ((inspected.path binder member).expanded.substitute implSub)) :
    InspectionJoinable program valid context (.projection trait member owners items associated.kind) value := by
  obtain ⟨common,newImplSub,nextSelected,ready,queryCommon,_⟩ :=
    selected.complete_query valid inspected contextKinded headJoin sourceJoin
  have itemsSame : ListRel (InspectionReduction program valid context) items items := .reflexive (fun _ => .refl) _
  obtain ⟨newOwnerSub,newItemSub,nextDomain,ownerTables,itemTables⟩ :=
    domain.relate_arguments valid (fun _ _ reduced => reduced.positive.equal) queryCommon itemsSame
  have lookup := (ownerTables.append itemTables).substitution_getD_related (fun _ => PositiveClosure.refl)
  have nextGraph := graph.congr_substitution valid (fun id kind => (InspectionReduction.positive (lookup id kind)).equal)
  have bodyReduced : InspectionReduction program valid context value (body.substitute (newOwnerSub ++ newItemSub)) := by
    rw [graph.2.1]
    exact body.substitutions_related InspectionReduction.congr lookup
  refine ⟨_,?_,bodyReduced⟩
  apply PositiveClosure.trans
  · exact InspectionReduction.congr (projection_head queryCommon.length_eq) (queryCommon.append itemsSame)
  · exact InspectionReduction.root
      (PathInspectedStep.defaultProjection (domain := nextDomain) (selected := nextSelected) (absent := absent)
        (default := default) (substituted := nextGraph) ready)

end Glorious.Language
