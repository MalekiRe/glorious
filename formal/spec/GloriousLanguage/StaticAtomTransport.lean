import GloriousLanguage.AtomEmbedding
import GloriousLanguage.CapabilityModels

/-! One mutual transport proof for the actual static relations. Elementary
atom bijections preserve the finite declaration templates and correspond
exactly on universe domains; no logical transport conclusion is an input. -/
namespace Glorious.Language

def AtomRenaming.Fixes (rename : AtomRenaming) (program : Program) : Prop :=
  ∀ declaration ∈ program.declarations, ∀ term ∈ declaration.terms, rename.term term = term

theorem CallableFields.renameAtoms {program : Program} {id : DeclId} {arguments fields : List Term}
    (declared : CallableFields program id arguments fields) (rename : AtomRenaming) (fixed : rename.Fixes program) :
    CallableFields program id (arguments.map rename.term) (fields.map rename.term) := by
  cases declared with
  | function found instantiated substituted =>
    have kept := fixed _ (List.mem_of_find?_eq_some (Program.function_lookup found))
    exact .function found (instantiated.renameAtoms rename) (rename.substitutes_fixed_list (fun term member =>
      kept term (by simp only [Definition.terms,List.mem_append]; exact Or.inl (Or.inr member))) substituted)
  | operation found instantiated => exact .operation found (instantiated.renameAtoms rename)

def AtomEmbedding.assignment (embedding : AtomEmbedding) (assignment : Term → Option Principal) : Term → Option Principal :=
  fun term => assignment (embedding.inverse.term term)

theorem AtomEmbedding.assignment_at (embedding : AtomEmbedding) (assignment : Term → Option Principal) (term : Term) :
    embedding.assignment assignment (embedding.term term) = assignment term := by
  simp only [AtomEmbedding.assignment,embedding.term_leftInverse]

theorem AtomEmbedding.assignment_fields (embedding : AtomEmbedding) {assignment : Term → Option Principal}
    {fields : List Term} {principals : List Principal}
    (related : ListRel (fun field principal => assignment field = some principal) fields principals) :
    ListRel (fun field principal => embedding.assignment assignment field = some principal)
      (fields.map embedding.term) principals := by
  induction related with
  | nil => exact .nil
  | cons first _ ih => exact .cons (by simpa only [embedding.assignment_at] using first) ih

theorem CapabilityEquation.renameAtoms {program : Program} {assignment : Term → Option Principal} {term : Term} {principal : Principal}
    (equation : CapabilityEquation program assignment term principal) (embedding : AtomEmbedding)
    (fixed : embedding.Fixes program) :
    CapabilityEquation program (embedding.assignment assignment) (embedding.term term) principal := by
  cases equation <;> simp only [AtomRenaming.term]
  case unit => exact .unit
  case bottom => exact .bottom
  case scalar => exact .scalar
  case raw => exact .raw
  case shared => exact .shared
  case unique => exact .unique
  case label => exact .label
  case tuple fields => exact .tuple (embedding.assignment_fields fields)
  case emptyArray => exact .emptyArray
  case array positive found => exact .array positive (by simpa only [embedding.assignment_at] using found)
  case nominal id data arguments substitution fields principals marker structural found instantiated
      substituted capabilities marked meets restricted drops =>
    have kept := fixed _ (List.mem_of_find?_eq_some (Program.data_lookup found))
    refine .nominal found (instantiated.renameAtoms embedding.toAtomRenaming)
      (embedding.substitutes_fixed_list (fun term member => kept term (by
        simp only [Definition.terms,List.mem_append]
        exact Or.inl (Or.inl (Or.inl member)))) substituted)
      (embedding.assignment_fields capabilities) ?_ meets restricted drops
    rcases marked with noMarker | ⟨source,value,sourceFound,sourceSub,valueKind⟩
    · exact Or.inl noMarker
    · refine Or.inr ⟨source,embedding.term value,sourceFound,
        embedding.substitutes_fixed (kept source (by
          simp only [Definition.terms,List.mem_append]
          exact Or.inl (Or.inl (Or.inr (by simp [sourceFound]))))) sourceSub,?_⟩
      rcases valueKind with markerValue | ⟨typeKind,selected⟩
      · exact Or.inl (by rw [markerValue]; simp only [AtomRenaming.term])
      · exact Or.inr ⟨by simpa only [embedding.kind] using typeKind,
          by simpa only [embedding.assignment_at] using selected⟩
  case callable fields capabilities =>
    exact .callable (fields.renameAtoms embedding.toAtomRenaming fixed) (embedding.assignment_fields capabilities)
  case environment capabilities => exact .environment (embedding.assignment_fields capabilities)
  case available selected =>
    apply CapabilityEquation.available
    simpa only [AtomRenaming.term] using
      (show embedding.assignment assignment (embedding.term _) = _ from (embedding.assignment_at assignment _).trans selected)
  case bindings capabilities => exact .bindings (embedding.assignment_fields capabilities)
  case optionalContinuation => exact .optionalContinuation
  case exactContinuation positive => exact .exactContinuation positive

theorem Entails.renameAtoms {program : Program} {context : Context} {constraint : Constraint}
    (entailed : Entails program context constraint) (embedding : AtomEmbedding) (fixed : embedding.Fixes program) :
    Entails program (embedding.context context) (embedding.constraint constraint) := by
  refine Entails.rec
    (motive_1 := fun context type principal _ =>
      CapabilityEvidence program (embedding.context context) (embedding.term type) principal)
    (motive_2 := fun context assignment type principal _ => CapabilityUnfolds program (embedding.context context)
      (embedding.assignment assignment) (embedding.term type) principal)
    (motive_3 := fun context a b _ => Equal program (embedding.context context) (embedding.term a) (embedding.term b))
    (motive_4 := fun context trait arguments negative implementation substitution _ =>
      SelectsImpl program (embedding.context context) trait (arguments.map embedding.term) negative implementation
        (embedding.substitution substitution))
    (motive_5 := fun context effect row _ => RowMember program (embedding.context context) (embedding.term effect) (embedding.term row))
    (motive_6 := fun context required allowed _ => RowSubset program (embedding.context context)
      (embedding.term required) (embedding.term allowed))
    (motive_7 := fun context type region _ => TypeOutlives program (embedding.context context)
      (embedding.term type) (embedding.term region))
    (motive_8 := fun context constraint _ => Entails program (embedding.context context) (embedding.constraint constraint))
    (motive_9 := fun context substitution constraint _ => EntailsSubstitution program (embedding.context context)
      (embedding.substitution substitution) (embedding.constraint constraint))
    (motive_10 := fun context left right _ =>
      DefinitionalStep program (embedding.context context) (embedding.term left) (embedding.term right))
    (motive_11 := fun context left right _ =>
      DefinitionallyEqual program (embedding.context context) (embedding.term left) (embedding.term right))
    (motive_12 := fun context left right _ =>
      DefinitionalReduction program (embedding.context context) (embedding.term left) (embedding.term right))
    (motive_13 := fun context implementation arguments substitution _ =>
      Definition.implementation implementation ∈ program.declarations →
      MatchesImplHead program (embedding.context context) implementation
        (arguments.map embedding.term) (embedding.substitution substitution))
    (motive_14 := fun context trait member owners items associated ownerSub itemSub _ =>
      ProjectionDomain program (embedding.context context) trait member
        (owners.map embedding.term) (items.map embedding.term) associated
        (embedding.substitution ownerSub) (embedding.substitution itemSub))
    (motive_15 := fun sourceContext context binder template query value _ =>
      InfersHeadParameter program sourceContext (embedding.context context)
        binder template (embedding.term query) (embedding.term value))
    (motive_16 := fun context implementation arguments binder value _ =>
      InfersHeadArgument program (embedding.context context) implementation
        (arguments.map embedding.term) binder (embedding.term value))
    ?capStructural ?capLogical ?capEqual ?capEquation ?capEvidence ?capExpansion
    ?refl ?symm ?trans ?congr ?assumed ?equalEntailed ?definitional
    ?rowDuplicate ?tailDuplicate ?selected ?head ?tail ?equal ?empty ?assumed_1 ?same ?trans_1 ?instances ?rowEntailed
    ?assumed_2 ?scalar ?unit ?pointer ?reference ?bottom ?tuple ?array ?nominal ?callable ?label ?environment
    ?available ?bindings ?equal_1 ?typeEntailed ?checkedCallable ?checkedRunsIn ?assumed_3 ?constraintCongr ?equality
    ?outlivesRefl ?outlivesStatic ?outlivesTrans ?typeOutlives
    ?rows ?implementation ?use ?quantified ?quantifiedInstance ?instantiated
    ?stepAlias ?stepProjection ?stepDefault
    ?defRefl ?defSymm ?defTrans ?defCongr ?defStep ?defRow
    ?redRefl ?redStep ?redTrans ?redCongr ?redRow
    ?matched ?domainValid ?inferParameter ?inferChild ?inferSource ?inferQuery ?inferArgument entailed
  all_goals intros
  all_goals try simp only [AtomRenaming.term,AtomRenaming.constraint,Constraint.mapTerms,
    List.map_cons,List.map_nil]
  all_goals try simp only [← AtomRenaming.term_def]
  case capStructural context type principal assignment found _ unfolded =>
    apply CapabilityEvidence.structural (assignment := embedding.assignment assignment)
      (by simpa only [embedding.assignment_at] using found)
    intro term claimed selected
    have original : assignment (embedding.inverse.term term) = some claimed := selected
    simpa only [embedding.term_rightInverse] using unfolded (embedding.inverse.term term) claimed original
  case capLogical _ admitted lower logical =>
    exact .logical (by simpa only [AtomRenaming.constraint,Constraint.mapTerms] using logical) admitted lower
  case capEqual _ _ equal evidence => exact .equal equal evidence
  case capEquation restriction equation => exact .equation restriction (equation.renameAtoms embedding fixed)
  case capEvidence restriction _ evidence => exact .evidence restriction evidence
  case capExpansion _ _ reduced unfolded => exact .expansion reduced unfolded
  case refl => exact .refl
  case symm _ ih => exact .symm ih
  case trans _ _ first second => exact .trans first second
  case congr same _ children =>
    exact .congrChildren (same.renameAtoms embedding.toAtomRenaming) (embedding.children_at children)
  case assumed member => exact .assumed (List.mem_map.mpr ⟨_,member,by
    simp only [AtomRenaming.constraint,Constraint.mapTerms]⟩)
  case equalEntailed _ ih => exact .entailed (by simpa only [AtomRenaming.constraint,Constraint.mapTerms] using ih)
  case definitional _ ih => exact .definitional ih
  case rowDuplicate _ ih => exact .rowDuplicate ih
  case tailDuplicate _ ih => exact .tailDuplicate ih
  case selected member trait negative _ _ head requirements =>
    have lexical := fixed _ member
    refine .selected member trait negative (head member) ?_
    intro constraint present
    simpa only [embedding.fixed_constraint (fun term nested => lexical term (by
      simp only [Definition.terms,List.mem_append,List.mem_flatMap]
      exact Or.inl (Or.inr ⟨constraint,present,nested⟩)))] using requirements constraint present
  case head present _ equal => exact .head (List.mem_map.mpr ⟨_,present,rfl⟩) equal
  case tail present _ nested => exact .tail (List.mem_map.mpr ⟨_,present,rfl⟩) nested
  case equal _ _ equal nested => exact .equal equal nested
  case empty => exact .empty
  case assumed_1 member => exact .assumed (List.mem_map.mpr ⟨_,member,by
    simp only [AtomRenaming.constraint,Constraint.mapTerms]⟩)
  case same _ equal => exact .same equal
  case trans_1 _ _ first second => exact .trans first second
  case instances _ _ instances tails =>
    refine .instances ?_ ?_
    · intro term member; obtain ⟨original,present,rfl⟩ := List.mem_map.mp member; exact instances original present
    · intro term member; obtain ⟨original,present,rfl⟩ := List.mem_map.mp member; exact tails original present
  case rowEntailed _ ih => exact .entailed (by simpa only [AtomRenaming.constraint,Constraint.mapTerms] using ih)
  case assumed_2 member => exact .assumed (List.mem_map.mpr ⟨_,member,by
    simp only [AtomRenaming.constraint,Constraint.mapTerms]⟩)
  case scalar => exact .scalar
  case unit => exact .unit
  case pointer => exact .pointer
  case reference _ included => exact .reference (by simpa only [AtomRenaming.constraint,Constraint.mapTerms] using included)
  case bottom => exact .bottom
  case tuple _ fields =>
    exact .tuple (by intro term member; obtain ⟨original,present,rfl⟩ := List.mem_map.mp member; exact fields original present)
  case array _ element => exact .array element
  case nominal found instantiated substituted _ fields =>
    have lexical := fixed _ (List.mem_of_find?_eq_some (Program.data_lookup found))
    exact .nominal found (instantiated.renameAtoms embedding.toAtomRenaming)
      (embedding.substitutes_fixed_list (fun term member => lexical term (by
        simp only [Definition.terms,List.mem_append]
        exact Or.inl (Or.inl (Or.inl member)))) substituted)
      (by intro term member; obtain ⟨original,present,rfl⟩ := List.mem_map.mp member; exact fields original present)
  case callable selected _ fields =>
    exact .callable (selected.renameAtoms embedding.toAtomRenaming fixed)
      (by intro term member; obtain ⟨original,present,rfl⟩ := List.mem_map.mp member; exact fields original present)
  case label _ included => exact .label (by simpa only [AtomRenaming.constraint,Constraint.mapTerms] using included)
  case environment context brand long residents short _ _ included fields =>
    apply TypeOutlives.environment
    · simpa only [AtomRenaming.constraint,Constraint.mapTerms] using
        (by assumption : Entails program (embedding.context context) (embedding.constraint (.outlives _ _)))
    · intro term member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact (by assumption : ∀ field ∈ _, TypeOutlives program (embedding.context context) (embedding.term field) _) original present
  case available _ environment =>
    exact .available (by simpa only [AtomRenaming.term] using environment)
  case bindings context brand long residents short _ _ included fields =>
    apply TypeOutlives.bindings
    · simpa only [AtomRenaming.constraint,Constraint.mapTerms] using
        (by assumption : Entails program (embedding.context context) (embedding.constraint (.outlives _ _)))
    · intro term member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact (by assumption : ∀ field ∈ _, TypeOutlives program (embedding.context context) (embedding.term field) _) original present
  case equal_1 _ _ equal previous => exact .equal equal previous
  case typeEntailed _ ih => exact .entailed (by simpa only [AtomRenaming.constraint,Constraint.mapTerms] using ih)
  case checkedCallable found member receiver arguments result effects =>
    have lexical := fixed _ (List.mem_of_find?_eq_some (Program.function_lookup found))
    have invocation : ∀ (term : Term), term ∈ _ → embedding.term term = term := fun term present => lexical term (by
      simp only [Definition.terms,List.mem_append,List.mem_flatMap]
      exact Or.inr ⟨_,member,present⟩)
    exact .checkedCallable found member
      (embedding.substitutes_fixed (invocation _ (by simp [InvocationRelation.terms])) receiver)
      (embedding.substitutes_fixed_list (fun term present => invocation term (by simp [InvocationRelation.terms,present])) arguments)
      (embedding.substitutes_fixed (invocation _ (by simp [InvocationRelation.terms])) result)
      (embedding.substitutes_fixed (invocation _ (by simp [InvocationRelation.terms])) effects)
  case checkedRunsIn found member receiver access arguments after =>
    have lexical := fixed _ (List.mem_of_find?_eq_some (Program.function_lookup found))
    have invocation : ∀ (term : Term), term ∈ _ → embedding.term term = term := fun term present => lexical term (by
      simp only [Definition.terms,List.mem_append,List.mem_flatMap]
      exact Or.inr ⟨_,member,present⟩)
    exact .checkedRunsIn found member
      (embedding.substitutes_fixed (invocation _ (by simp [InvocationRelation.terms])) receiver)
      (embedding.substitutes_fixed (invocation _ (by simp [InvocationRelation.terms])) access)
      (embedding.substitutes_fixed_list (fun term present => invocation term (by simp [InvocationRelation.terms,present])) arguments)
      (embedding.substitutes_fixed (invocation _ (by simp [InvocationRelation.terms])) after)
  case assumed_3 member => exact .assumed (List.mem_map.mpr ⟨_,member,rfl⟩)
  case constraintCongr context template before after leftSub rightSub _ beforeSub afterSub _ pairs previous =>
    refine .congrSubstitution (leftSub := embedding.substitution leftSub)
      (rightSub := embedding.substitution rightSub) ?_
      (embedding.substitute_constraint beforeSub) (embedding.substitute_constraint afterSub) previous
    intro id kind
    rw [embedding.lookup_default,embedding.lookup_default]
    exact pairs id kind
  case equality _ equal => exact .equality equal
  case outlivesRefl => exact .outlivesRefl
  case outlivesStatic => exact .outlivesStatic
  case outlivesTrans _ _ first second =>
    exact .outlivesTrans (by simpa only [AtomRenaming.constraint,Constraint.mapTerms] using first)
      (by simpa only [AtomRenaming.constraint,Constraint.mapTerms] using second)
  case typeOutlives _ outlives => exact .typeOutlives outlives
  case rows _ subset => exact .rows subset
  case implementation _ selected => exact .implementation selected
  case use _ request capability => exact .use capability request
  case quantified context binders requirements _ allInstances =>
    apply Entails.quantified
    intro values substitution instantiated kinds requirement member
    change Instantiates (binders.map embedding.binder) values substitution at instantiated
    have originalInstantiation : Instantiates binders (values.map embedding.inverse.term)
        (embedding.inverse.substitution substitution) := by
      have inverse : (binders.map embedding.binder).map embedding.inverse.binder = binders := by
        simp only [List.map_map,Function.comp_def,embedding.binder_leftInverse,List.map_id']
      simpa only [inverse] using
        (instantiated.renameAtoms embedding.inverse).renameBinders embedding.inverse
    have originalKinds : ∀ term ∈ values.map embedding.inverse.term, Kinding program context term term.kind := by
      intro term present
      obtain ⟨original,inOriginal,rfl⟩ := List.mem_map.mp present
      simpa only [embedding.inverse.kind] using Kinding.unrenameAtoms embedding (kinds original inOriginal)
    obtain ⟨original,inOriginal,rfl⟩ := List.mem_map.mp member
    have transported := allInstances _ _ originalInstantiation originalKinds original inOriginal
    simpa only [embedding.substitution_rightInverse,AtomRenaming.constraint] using transported
  case instantiated substituted _ holds => exact .instantiated (embedding.substitute_constraint substituted) holds
  case quantifiedInstance _ instantiated kinded present substituted quantified =>
    simp only [AtomRenaming.constraint,Constraint.mapTerms] at quantified
    refine .quantifiedInstance quantified ((instantiated.renameAtoms embedding.toAtomRenaming).renameBinders embedding.toAtomRenaming) ?_
      (List.mem_map.mpr ⟨_,present,rfl⟩) (embedding.substitute_constraint substituted)
    intro term member
    obtain ⟨original,inOriginal,rfl⟩ := List.mem_map.mp member
    simpa only [embedding.kind] using (kinded original inOriginal).renameAtoms embedding
  case stepAlias found instantiated kinded substituted =>
    have lexical := fixed _ (List.mem_of_find?_eq_some (Program.alias_lookup found))
    refine .alias found (instantiated.renameAtoms embedding.toAtomRenaming) ?_
      (embedding.substitutes_fixed (lexical _ (by simp [Definition.terms])) substituted)
    intro term present
    obtain ⟨original,inOriginal,rfl⟩ := List.mem_map.mp present
    simpa only [embedding.kind] using (kinded original inOriginal).renameAtoms embedding
  case stepProjection _ selected member substituted domainIH selectedIH =>
    have lexical := fixed _ selected.declaration
    exact .projection domainIH selectedIH member (by
      simpa only [AtomRenaming.substitution,List.map_append] using
        (embedding.substitutes_fixed (lexical _ (by
          simp only [Definition.terms,List.mem_append,List.mem_map]
          exact Or.inl (Or.inl (Or.inr ⟨_,member,rfl⟩)))) substituted))
  case stepDefault context trait member rawOwners rawItems associated ownerSub itemSub implementation implSub rawBody value
      domain _ missing default substituted domainIH selectedIH =>
    have found : program.associated member = some associated := by cases domain; assumption
    have lexical := fixed _ (List.mem_of_find?_eq_some (Program.associated_lookup found))
    exact .defaultProjection domainIH selectedIH missing default (by
      simpa only [AtomRenaming.substitution,List.map_append] using
        (embedding.substitutes_fixed (lexical rawBody (by
          simp only [Definition.terms,List.mem_append]
          exact Or.inl (Or.inl (by simp [default])))) substituted))
  case defRefl => exact .refl
  case defSymm _ ih => exact .symm ih
  case defTrans _ _ first second => exact .trans first second
  case defCongr same _ children =>
    exact .congrChildren (same.renameAtoms embedding.toAtomRenaming) (embedding.children_at children)
  case defStep _ ih => exact .step ih
  case defRow equal => exact .row (equal.renameAtoms embedding.toAtomRenaming)
  case redRefl => exact .refl
  case redStep _ ih => exact .step ih
  case redTrans _ _ first second => exact .trans first second
  case redCongr same _ children =>
    exact .congrChildren (same.renameAtoms embedding.toAtomRenaming) (embedding.children_at children)
  case redRow equal => exact .row (equal.renameAtoms embedding.toAtomRenaming)
  case matched context implementation arguments values substitution specialized
      instantiated kinded substituted lengths _ _ head inferred member =>
    have lexical := fixed _ member
    refine .inferred (specialized := specialized.map embedding.term) (instantiated.renameAtoms embedding.toAtomRenaming) ?_ ?_ ?_ ?_ ?_
    · intro term present
      obtain ⟨original,inOriginal,rfl⟩ := List.mem_map.mp present
      simpa only [embedding.kind] using (kinded original inOriginal).renameAtoms embedding
    · exact embedding.substitutes_fixed_list (fun term present => lexical term (by
        simp only [Definition.terms,List.mem_append]
        exact Or.inl (Or.inl (Or.inl present)))) substituted
    · simpa only [List.length_map] using lengths
    · exact embedding.list_at head
    · intro index binder value binderAt valueAt
      obtain ⟨original,originalAt,rfl⟩ := Option.map_eq_some_iff.mp (by
        simpa only [List.getElem?_map] using valueAt)
      exact inferred index binder original binderAt originalAt
  case domainValid traitFound member associatedFound owner ownerInst itemInst kinded _ _ ownerRequirements itemRequirements =>
    have traitLexical := fixed _ (List.mem_of_find?_eq_some (Program.trait_lookup traitFound))
    have itemLexical := fixed _ (List.mem_of_find?_eq_some (Program.associated_lookup associatedFound))
    refine .valid traitFound member associatedFound owner (ownerInst.renameAtoms embedding.toAtomRenaming) (itemInst.renameAtoms embedding.toAtomRenaming) ?_ ?_ ?_
    · intro term present
      rw [← List.map_append] at present
      obtain ⟨original,inOriginal,rfl⟩ := List.mem_map.mp present
      simpa only [embedding.kind] using (kinded original inOriginal).renameAtoms embedding
    · intro constraint present
      simpa only [embedding.fixed_constraint (fun term nested => traitLexical term (by
        simp only [Definition.terms,List.mem_append,List.mem_flatMap]
        exact Or.inl ⟨constraint,present,nested⟩))] using ownerRequirements constraint present
    · intro constraint present
      simpa only [AtomRenaming.substitution,List.map_append,
        embedding.fixed_constraint (fun term nested => itemLexical term (by
          simp only [Definition.terms,List.mem_append,List.mem_flatMap]
          exact Or.inl (Or.inr ⟨constraint,present,nested⟩)))] using itemRequirements constraint present
  case inferParameter kind =>
    exact .parameter (by simpa only [embedding.kind] using kind)
  case inferChild structural same templateAt queryAt _ inferred =>
    exact .child structural (same.renameAtoms_right embedding.toAtomRenaming (List.mem_of_getElem? queryAt))
      templateAt (by rw [embedding.children,List.getElem?_map,queryAt]; rfl) inferred
  case inferSource sourceProof _ _ inferred => exact .sourceReduction sourceProof inferred
  case inferQuery _ _ equal inferred => exact .queryConversion equal inferred
  case inferArgument context implementation arguments binder value template query index
      templateAt queryAt _ inferred =>
    exact .argument templateAt (by rw [List.getElem?_map,queryAt]; rfl) inferred

end Glorious.Language
