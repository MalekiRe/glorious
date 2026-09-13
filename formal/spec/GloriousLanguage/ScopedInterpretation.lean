import GloriousLanguage.ScopedInstantiation
import GloriousLanguage.CapabilityTransport
import GloriousLanguage.LogicalCut

/-! Interpretation of the actual mutual static semantics under lexical scope
closing. The only logical inputs are the decoded source assumptions. Quantified
predicates retain their real argument domain; declaration templates are fixed
by program admission, not by an assumed law about arbitrary predicates. -/
namespace Glorious.Language

theorem CallableFields.decode_scope {program : Program} (valid : ProgramWellFormed program)
    {id : DeclId} {arguments fields : List Term} (declared : CallableFields program id arguments fields)
    (scope : ScopeInstantiation) : CallableFields program id (arguments.map scope.term) (fields.map scope.term) := by
  cases declared with
  | function found instantiated substituted =>
    have fixed := valid.declaration_fixed (scope := scope)
      (List.mem_of_find?_eq_some (Program.function_lookup found))
    exact .function found (instantiated.map_values scope.term (fun term _ => scope.kind term))
      (scope.substitutes_values substituted (fun term member => fixed term (by
        simp only [Definition.terms,List.mem_append]
        exact Or.inl (Or.inr member))))
  | operation found instantiated => exact .operation found (instantiated.map_values scope.term (fun term _ => scope.kind term))

/-- The existing greatest-witness image handles merged scope images. Each
structural equation retains its actual declaration and ordered field graph. -/
theorem CapabilityEquation.decode_scope {program : Program} (valid : ProgramWellFormed program)
    {first last : Term → Option Principal} {type : Term} {principal : Principal}
    (equation : CapabilityEquation program first type principal) (scope : ScopeInstantiation)
    (related : ∀ term claimed, first term = some claimed →
      ∃ result, last (scope.term term) = some result ∧ claimed.Restricts result) :
    ∃ result, CapabilityEquation program last (scope.term type) result ∧ principal.Restricts result := by
  have fields {terms : List Term} {principals : List Principal}
      (assigned : ListRel (fun term claimed => first term = some claimed) terms principals) :
      ∃ results, ListRel (fun term claimed => last term = some claimed) (terms.map scope.term) results ∧
        ListRel Principal.Restricts principals results := by
    induction assigned with
    | nil => exact ⟨[],.nil,.nil⟩
    | cons found _ ih =>
      obtain ⟨result,selected,ordered⟩ := related _ _ found
      obtain ⟨results,rest,orders⟩ := ih
      exact ⟨result :: results,.cons selected rest,.cons ordered orders⟩
  cases equation <;> simp only [ScopeInstantiation.term]
  case unit => exact ⟨_,.unit,.refl _⟩
  case bottom => exact ⟨_,.bottom,.refl _⟩
  case scalar => exact ⟨_,.scalar,.refl _⟩
  case raw => exact ⟨_,.raw,.refl _⟩
  case shared => exact ⟨_,.shared,.refl _⟩
  case unique => exact ⟨_,.unique,.refl _⟩
  case label => exact ⟨_,.label,.refl _⟩
  case tuple assigned =>
    obtain ⟨results,assigned,ordered⟩ := fields assigned
    exact ⟨_,.tuple assigned,Principal.fields_monotone ordered⟩
  case emptyArray => exact ⟨_,.emptyArray,.refl _⟩
  case array positive assigned =>
    obtain ⟨result,selected,ordered⟩ := related _ _ assigned
    exact ⟨result,.array positive selected,ordered⟩
  case nominal id data arguments inner residentTypes residentPrincipals sourceMarker structuralPrincipal
      found instantiated substituted assigned marked meets restricted drops =>
    have fixed := valid.declaration_fixed (scope := scope) (List.mem_of_find?_eq_some (Program.data_lookup found))
    have mapped := instantiated.map_values scope.term (fun term _ => scope.kind term)
    have graph := scope.substitutes_values substituted (fun term member => fixed term (by
      simp only [Definition.terms,List.mem_append]
      exact Or.inl (Or.inl (Or.inl member))))
    obtain ⟨results,assigned,ordered⟩ := fields assigned
    have marker : ∃ changed,
        (data.quantitySource = none ∧ changed = .duplicable ∨
          ∃ sourceValue value, data.quantitySource = some sourceValue ∧
            Substitutes (inner.map (fun entry => (entry.1,scope.term entry.2))) sourceValue value ∧
            (value = .principal changed ∨ value.kind = .type ∧ last value = some changed)) ∧
        sourceMarker.Restricts changed := by
      rcases marked with none | ⟨sourceValue,value,sourceAt,substituted,marked⟩
      · obtain ⟨none,rfl⟩ := none
        exact ⟨.duplicable,Or.inl ⟨none,rfl⟩,.refl _⟩
      · have graph := scope.substitute_values _ _ _ substituted (fixed _ (by
          simp only [Definition.terms,List.mem_append]
          exact Or.inl (Or.inl (Or.inr (by simp [sourceAt])))))
        rcases marked with valueMarker | ⟨typeKind,assigned⟩
        · exact ⟨_,Or.inr ⟨sourceValue,scope.term value,sourceAt,graph,
            Or.inl (by rw [valueMarker]; simp only [ScopeInstantiation.term])⟩,.refl _⟩
        · obtain ⟨changed,selected,ordered⟩ := related value _ assigned
          exact ⟨changed,Or.inr ⟨sourceValue,scope.term value,sourceAt,graph,
            Or.inr ⟨(scope.kind value).trans typeKind,selected⟩⟩,ordered⟩
    obtain ⟨marker,marked,markerOrder⟩ := marker
    have structural := Principal.meet_monotone (Principal.fields_monotone ordered) markerOrder
    rw [← meets] at structural
    rcases restricted with ⟨none,rfl⟩ | ⟨restriction,permitted⟩
    · refine ⟨_,.nominal found mapped graph assigned marked rfl (Or.inl ⟨none,rfl⟩) ?_,structural⟩
      intro dropped
      exact structural 0 (drops dropped)
    · exact ⟨_,.nominal found mapped graph assigned marked rfl
        (Or.inr ⟨restriction,permitted.trans structural⟩) drops,.refl _⟩
  case callable captured assigned =>
    obtain ⟨results,assigned,ordered⟩ := fields assigned
    exact ⟨_,.callable (captured.decode_scope valid scope) assigned,Principal.fields_monotone ordered⟩
  case environment assigned =>
    obtain ⟨results,assigned,ordered⟩ := fields assigned
    exact ⟨_,.environment assigned,Principal.fields_monotone ordered⟩
  case available assigned =>
    obtain ⟨result,selected,ordered⟩ := related _ _ assigned
    exact ⟨result,.available (by simpa only [ScopeInstantiation.term] using selected),ordered⟩
  case bindings assigned =>
    obtain ⟨results,assigned,ordered⟩ := fields assigned
    exact ⟨_,.bindings assigned,Principal.fields_monotone ordered⟩
  case optionalContinuation => exact ⟨_,.optionalContinuation,.refl _⟩
  case exactContinuation positive => exact ⟨_,.exactContinuation positive,.refl _⟩


private abbrev ScopeResult (program : Program) (scope : ScopeInstantiation) (source target : Context)
    (judgment : Prop) : Prop :=
  (∀ term kind, Kinding program source term kind → Kinding program target (scope.term term) kind) →
  (∀ term kind, Kinding program target term kind → Kinding program source term kind ∧ scope.term term = term) →
  (∀ requirement ∈ source.assumptions, Entails program target (requirement.mapTerms scope.term)) → judgment

private theorem scope_list_at (scope : ScopeInstantiation) {left right : List Term} {relation : Term → Term → Prop}
    (related : ∀ (index : Nat) first second, left[index]? = some first → right[index]? = some second →
      relation (scope.term first) (scope.term second)) :
    ∀ (index : Nat) first second, (left.map scope.term)[index]? = some first →
      (right.map scope.term)[index]? = some second → relation first second := by
  intro index first second leftAt rightAt
  rw [List.getElem?_map] at leftAt rightAt
  obtain ⟨originalLeft,selectedLeft,rfl⟩ := Option.map_eq_some_iff.mp leftAt
  obtain ⟨originalRight,selectedRight,rfl⟩ := Option.map_eq_some_iff.mp rightAt
  exact related index originalLeft originalRight selectedLeft selectedRight

/-- General logical preservation under scope closing. Only source assumptions
are discharged. The quantified branch pulls each actual target argument back
into the source domain; it never assumes transport of an arbitrary entailment
or leaves the quantified template undecoded. -/
theorem Entails.decode_scope {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {constraint : Constraint} (held : Entails program source constraint)
    (scope : ScopeInstantiation)
    (forward : ∀ term kind, Kinding program source term kind → Kinding program target (scope.term term) kind)
    (pullback : ∀ term kind, Kinding program target term kind → Kinding program source term kind ∧ scope.term term = term)
    (assumptions : ∀ requirement ∈ source.assumptions, Entails program target (requirement.mapTerms scope.term)) :
    Entails program target (constraint.mapTerms scope.term) := by
  let mapSub : Substitution → Substitution := fun substitution => substitution.map (fun entry => (entry.1,scope.term entry.2))
  have lookup (substitution : Substitution) (id : Identity) (kind : Kind) :
      ((mapSub substitution).get id).getD (.parameter id kind) =
        scope.term ((substitution.get id).getD (.parameter id kind)) := by
    simp only [mapSub,Table.get_map_values]
    cases found : substitution.get id <;> simp only [Option.map,Option.getD,ScopeInstantiation.parameter_fixed]
  have predicateFixed {declaration : Definition} (member : declaration ∈ program.declarations)
      (requirement : Constraint) (terms : ∀ term ∈ requirement.terms, term ∈ declaration.terms) :
      requirement.mapTerms scope.term = requirement :=
    requirement.mapTerms_eq_self (fun term present => valid.declaration_fixed member term (terms term present))
  refine Entails.rec
    (motive_1 := fun source type principal _ => ScopeResult program scope source target
      (CapabilityEvidence program target (scope.term type) principal))
    (motive_2 := fun source assignment type principal _ => ScopeResult program scope source target
      (∀ image, (∀ term claimed, assignment term = some claimed →
        ∃ result, image (scope.term term) = some result ∧ claimed.Restricts result) →
        CapabilityUnfolds program target image (scope.term type) principal))
    (motive_3 := fun source left right _ => ScopeResult program scope source target (Equal program target (scope.term left) (scope.term right)))
    (motive_4 := fun source trait arguments negative implementation substitution _ => ScopeResult program scope source target
      (SelectsImpl program target trait (arguments.map scope.term) negative implementation (mapSub substitution)))
    (motive_5 := fun source effect row _ => ScopeResult program scope source target (RowMember program target (scope.term effect) (scope.term row)))
    (motive_6 := fun source required allowed _ => ScopeResult program scope source target (RowSubset program target (scope.term required) (scope.term allowed)))
    (motive_7 := fun source type region _ => ScopeResult program scope source target (TypeOutlives program target (scope.term type) (scope.term region)))
    (motive_8 := fun source constraint _ => ScopeResult program scope source target (Entails program target (constraint.mapTerms scope.term)))
    (motive_9 := fun source substitution constraint _ => ScopeResult program scope source target
      (EntailsSubstitution program target (mapSub substitution) (constraint.mapTerms scope.term)))
    (motive_10 := fun source left right _ => ScopeResult program scope source target (DefinitionalStep program target (scope.term left) (scope.term right)))
    (motive_11 := fun source left right _ => ScopeResult program scope source target (DefinitionallyEqual program target (scope.term left) (scope.term right)))
    (motive_12 := fun source left right _ => ScopeResult program scope source target (DefinitionalReduction program target (scope.term left) (scope.term right)))
    (motive_13 := fun source implementation arguments substitution _ => ScopeResult program scope source target
      (Definition.implementation implementation ∈ program.declarations →
        MatchesImplHead program target implementation (arguments.map scope.term) (mapSub substitution)))
    (motive_14 := fun source trait member owners items associated ownerSub itemSub _ => ScopeResult program scope source target
      (ProjectionDomain program target trait member (owners.map scope.term) (items.map scope.term) associated (mapSub ownerSub) (mapSub itemSub)))
    (motive_15 := fun sourceContext source binder template query value _ => ScopeResult program scope source target
      (InfersHeadParameter program sourceContext target binder template (scope.term query) (scope.term value)))
    (motive_16 := fun source implementation arguments binder value _ => ScopeResult program scope source target
      (InfersHeadArgument program target implementation (arguments.map scope.term) binder (scope.term value)))
    ?structural ?logical ?capEqual ?equation ?evidence ?capExpansion
    ?refl ?symm ?trans ?congrChildren ?assumed ?entailed ?definitional
    ?rowDuplicate ?tailDuplicate ?selected ?head ?tail ?equal_1 ?empty ?assumed_1 ?same ?trans_1 ?instances ?entailed_1
    ?assumed_2 ?scalar ?unit ?pointer ?reference ?bottom ?tuple ?array ?nominal ?callable ?label ?environment
    ?available ?bindings ?equal_2 ?entailed_2 ?checkedCallable ?checkedRunsIn ?assumed_3 ?congrSubstitution ?equality
    ?outlivesRefl ?outlivesStatic ?outlivesTrans ?typeOutlives
    ?rows ?implementation ?use ?quantified ?quantifiedInstance ?instantiated
    ?alias ?projection ?defaultProjection
    ?refl_1 ?symm_1 ?trans_2 ?congrChildren_1 ?step ?row
    ?refl_2 ?step_1 ?trans_3 ?congrChildren_2 ?row_1
    ?inferred ?domainValid ?parameter ?child ?sourceReduction ?queryConversion ?argument held forward pullback assumptions
  all_goals dsimp only [ScopeResult]
  all_goals intros
  all_goals try simp only [ScopeInstantiation.term,Constraint.mapTerms,List.map_cons,List.map_nil]
  case structural _ _ _ assignment found _ unfolded forward pullback assumptions =>
    apply CapabilityEvidence.image_coinduction scope.term (fun _ => True) True.intro found
    intro image related term principal _ selected
    exact unfolded term principal selected forward pullback assumptions image
      (fun term principal selected => related term principal True.intro selected)
  case logical _ _ _ _ _ requested lower ih forward pullback assumptions =>
    exact .logical (by simpa only [Constraint.mapTerms] using ih forward pullback assumptions) requested lower
  case capEqual _ _ _ _ _ _ equal evidence forward pullback assumptions =>
    exact .equal (equal forward pullback assumptions) (evidence forward pullback assumptions)
  case equation _ _ _ _ _ restriction equation forward pullback assumptions image related =>
    obtain ⟨result,mapped,ordered⟩ := equation.decode_scope valid scope related
    exact .equation (restriction.trans ordered) mapped
  case evidence _ _ _ _ _ restriction _ ih forward pullback assumptions image related =>
    exact .evidence restriction (ih forward pullback assumptions)
  case capExpansion _ _ _ _ _ _ _ reduced unfolded forward pullback assumptions image related =>
    exact .expansion (reduced forward pullback assumptions) (unfolded forward pullback assumptions image related)
  case refl => exact .refl
  case symm _ _ _ _ ih forward pullback assumptions => exact .symm (ih forward pullback assumptions)
  case trans _ _ _ _ _ _ first second forward pullback assumptions => exact .trans (first forward pullback assumptions) (second forward pullback assumptions)
  case congrChildren _ _ _ same _ children forward pullback assumptions =>
    apply Equal.congrChildren (SameHead.scopedAtoms same)
    rw [scope.children,scope.children]
    exact scope_list_at scope (fun index first second leftAt rightAt => children index first second leftAt rightAt forward pullback assumptions)
  case assumed _ _ _ member forward pullback assumptions => exact .entailed (by simpa only [Constraint.mapTerms] using assumptions _ member)
  case entailed _ _ _ _ ih forward pullback assumptions => exact .entailed (by simpa only [Constraint.mapTerms] using ih forward pullback assumptions)
  case definitional _ _ _ _ ih forward pullback assumptions => exact .definitional (ih forward pullback assumptions)
  case rowDuplicate _ _ _ _ _ _ ih forward pullback assumptions => exact .rowDuplicate (ih forward pullback assumptions)
  case tailDuplicate _ _ _ _ _ _ ih forward pullback assumptions => exact .tailDuplicate (ih forward pullback assumptions)
  case selected _ _ _ _ implementation _ declared trait negative _ _ head requirements forward pullback assumptions =>
    refine .selected declared trait negative (head forward pullback assumptions declared) ?_
    intro requirement member
    have fixed := predicateFixed declared requirement (fun term present => by
      simp only [Definition.terms,List.mem_append,List.mem_flatMap]
      exact Or.inl (Or.inr ⟨requirement,member,present⟩))
    exact fixed ▸ requirements requirement member forward pullback assumptions
  case head _ _ _ _ _ member _ ih forward pullback assumptions => exact .head (List.mem_map.mpr ⟨_,member,rfl⟩) (ih forward pullback assumptions)
  case tail _ _ _ _ _ member _ ih forward pullback assumptions => exact .tail (List.mem_map.mpr ⟨_,member,rfl⟩) (ih forward pullback assumptions)
  case equal_1 _ _ _ _ _ _ first second forward pullback assumptions => exact .equal (first forward pullback assumptions) (second forward pullback assumptions)
  case empty => exact .empty
  case assumed_1 _ _ _ member forward pullback assumptions => exact .entailed (by simpa only [Constraint.mapTerms] using assumptions _ member)
  case same _ _ _ _ ih forward pullback assumptions => exact .same (ih forward pullback assumptions)
  case trans_1 _ _ _ _ _ _ first second forward pullback assumptions => exact .trans (first forward pullback assumptions) (second forward pullback assumptions)
  case instances _ _ _ _ _ _ fields tails forward pullback assumptions =>
    exact .instances (fun term member => by
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact fields original present forward pullback assumptions)
      (fun term member => by
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        exact tails original present forward pullback assumptions)
  case entailed_1 _ _ _ _ ih forward pullback assumptions => exact .entailed (by simpa only [Constraint.mapTerms] using ih forward pullback assumptions)
  case assumed_2 _ _ _ member forward pullback assumptions => exact .entailed (by simpa only [Constraint.mapTerms] using assumptions _ member)
  case scalar => exact .scalar
  case unit => exact .unit
  case pointer => exact .pointer
  case reference _ _ _ _ _ _ ih forward pullback assumptions => exact .reference (by simpa only [Constraint.mapTerms] using ih forward pullback assumptions)
  case bottom => exact .bottom
  case tuple _ _ _ _ fields forward pullback assumptions =>
    exact .tuple (fun term member => by
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact fields original present forward pullback assumptions)
  case array _ _ _ _ _ ih forward pullback assumptions => exact .array (ih forward pullback assumptions)
  case nominal _ _ _ _ _ _ _ found instantiated substituted _ fields forward pullback assumptions =>
    have fixed := valid.declaration_fixed (scope := scope) (List.mem_of_find?_eq_some (Program.data_lookup found))
    exact .nominal found (instantiated.map_values scope.term (fun term _ => scope.kind term))
      (scope.substitutes_values substituted (fun term member => fixed term (by
        simp only [Definition.terms,List.mem_append]
        exact Or.inl (Or.inl (Or.inl member)))))
      (fun term member => by
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        exact fields original present forward pullback assumptions)
  case callable _ _ _ _ _ declared _ fields forward pullback assumptions =>
    exact .callable (declared.decode_scope valid scope) (fun term member => by
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact fields original present forward pullback assumptions)
  case label _ _ _ _ _ _ ih forward pullback assumptions => exact .label (by simpa only [Constraint.mapTerms] using ih forward pullback assumptions)
  case environment _ _ _ _ _ _ _ outlives fields forward pullback assumptions =>
    exact .environment (by simpa only [Constraint.mapTerms] using outlives forward pullback assumptions) (fun term member => by
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact fields original present forward pullback assumptions)
  case available _ _ _ _ _ _ ih forward pullback assumptions => exact .available (by simpa only [ScopeInstantiation.term] using ih forward pullback assumptions)
  case bindings _ _ _ _ _ _ _ outlives fields forward pullback assumptions =>
    exact .bindings (by simpa only [Constraint.mapTerms] using outlives forward pullback assumptions) (fun term member => by
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact fields original present forward pullback assumptions)
  case equal_2 _ _ _ _ _ _ first second forward pullback assumptions => exact .equal (first forward pullback assumptions) (second forward pullback assumptions)
  case entailed_2 _ _ _ _ ih forward pullback assumptions => exact .entailed (by simpa only [Constraint.mapTerms] using ih forward pullback assumptions)
  case checkedCallable _ _ relation _ _ _ _ _ found member receiver arguments result effects forward pullback assumptions =>
    have declared := List.mem_of_find?_eq_some (Program.function_lookup found)
    have fixed (term : Term) (present : term ∈ relation.terms) := valid.declaration_fixed (scope := scope) declared term (by
      simp only [Definition.terms,List.mem_append,List.mem_flatMap]
      exact Or.inr ⟨relation,member,present⟩)
    exact .checkedCallable found member
      (scope.substitute_values _ _ _ receiver (fixed _ (by simp [InvocationRelation.terms])))
      (scope.substitutes_values arguments (fun term present => fixed term (by simp [InvocationRelation.terms,present])))
      (scope.substitute_values _ _ _ result (fixed _ (by simp [InvocationRelation.terms])))
      (scope.substitute_values _ _ _ effects (fixed _ (by simp [InvocationRelation.terms])))
  case checkedRunsIn _ _ relation _ _ _ _ _ found member receiver access arguments after forward pullback assumptions =>
    have declared := List.mem_of_find?_eq_some (Program.function_lookup found)
    have fixed (term : Term) (present : term ∈ relation.terms) := valid.declaration_fixed (scope := scope) declared term (by
      simp only [Definition.terms,List.mem_append,List.mem_flatMap]
      exact Or.inr ⟨relation,member,present⟩)
    exact .checkedRunsIn found member
      (scope.substitute_values _ _ _ receiver (fixed _ (by simp [InvocationRelation.terms])))
      (scope.substitute_values _ _ _ access (fixed _ (by simp [InvocationRelation.terms])))
      (scope.substitutes_values arguments (fun term present => fixed term (by simp [InvocationRelation.terms,present])))
      (scope.substitute_values _ _ _ after (fixed _ (by simp [InvocationRelation.terms])))
  case assumed_3 _ _ member forward pullback assumptions => exact assumptions _ member
  case congrSubstitution _ _ _ _ _ _ _ before after _ equal held forward pullback assumptions =>
    refine .congrSubstitution ?_ (scope.substitute_constraint before) (scope.substitute_constraint after) (held forward pullback assumptions)
    intro id kind
    change Equal program target ((mapSub _).get id |>.getD (.parameter id kind)) ((mapSub _).get id |>.getD (.parameter id kind))
    rw [lookup,lookup]
    exact equal id kind forward pullback assumptions
  case equality _ _ _ _ ih forward pullback assumptions => exact .equality (ih forward pullback assumptions)
  case outlivesRefl => exact .outlivesRefl
  case outlivesStatic => exact .outlivesStatic
  case outlivesTrans _ _ _ _ _ _ first second forward pullback assumptions =>
    exact .outlivesTrans (by simpa only [Constraint.mapTerms] using first forward pullback assumptions)
      (by simpa only [Constraint.mapTerms] using second forward pullback assumptions)
  case typeOutlives _ _ _ _ ih forward pullback assumptions => exact .typeOutlives (ih forward pullback assumptions)
  case rows _ _ _ _ ih forward pullback assumptions => exact .rows (ih forward pullback assumptions)
  case implementation _ _ _ _ _ _ _ ih forward pullback assumptions => exact .implementation (ih forward pullback assumptions)
  case use _ _ _ _ _ requested ih forward pullback assumptions => exact .use (ih forward pullback assumptions) requested
  case quantified _ binders requirements _ instances forward pullback assumptions =>
    apply Entails.quantified
    intro values substitution instantiated kinded requirement member
    obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
    have sourceInstance := scope.instantiates_binders.mp instantiated
    have fixedValues : values.map scope.term = values := List.map_eq_self_of _ _
      (fun term member => (pullback term term.kind (kinded term member)).2)
    have mapped := sourceInstance.map_values scope.term (fun term _ => scope.kind term)
    rw [fixedValues] at mapped
    have tableFixed : mapSub substitution = substitution := mapped.2.2.trans sourceInstance.2.2.symm
    exact tableFixed ▸ instances values substitution sourceInstance
      (fun term member => (pullback term term.kind (kinded term member)).1) original present forward pullback assumptions
  case quantifiedInstance _ _ _ _ _ _ _ _ instantiated kinded member graph ih forward pullback assumptions =>
    exact .quantifiedInstance (by simpa only [Constraint.mapTerms] using ih forward pullback assumptions)
      (scope.instantiates_binders.mpr (instantiated.map_values scope.term (fun term _ => scope.kind term)))
      (fun term member => by
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        simpa only [scope.kind] using forward original original.kind (kinded original present))
      (List.mem_map.mpr ⟨_,member,rfl⟩) (scope.substitute_constraint graph)
  case instantiated _ _ _ _ graph _ ih forward pullback assumptions => exact .instantiated (scope.substitute_constraint graph) (ih forward pullback assumptions)
  case alias _ _ _ _ _ _ found instantiated kinded graph forward pullback assumptions =>
    exact .alias found (instantiated.map_values scope.term (fun term _ => scope.kind term))
      (fun term member => by
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        simpa only [scope.kind] using forward original original.kind (kinded original present))
      (scope.substitute_values _ _ _ graph (scope.aliasValue_fixed valid found))
  case projection _ _ memberId _ _ _ _ _ implementation _ body _ _ _ member graph domain selected forward pullback assumptions =>
    have actual := selected forward pullback assumptions
    have declared : Definition.implementation implementation ∈ program.declarations := by cases actual; assumption
    have fixed := valid.declaration_fixed (scope := scope) declared body (by
      simp only [Definition.terms,List.mem_append]
      exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨(memberId,body),member,rfl⟩))))
    exact .projection (domain forward pullback assumptions) actual member
      (by simpa only [mapSub,List.map_append] using scope.substitute_values _ _ _ graph fixed)
  case defaultProjection _ _ member _ _ associated _ _ _ _ body _ _ _ absent default graph domain selected forward pullback assumptions =>
    have actual := domain forward pullback assumptions
    have found : program.associated member = some associated := by cases actual; assumption
    have fixed := valid.declaration_fixed (scope := scope)
      (List.mem_of_find?_eq_some (Program.associated_lookup found)) body
      (by simp only [Definition.terms,List.mem_append]; exact Or.inl (by simp [default]))
    exact .defaultProjection actual (selected forward pullback assumptions) absent default
      (by simpa only [mapSub,List.map_append] using scope.substitute_values _ _ _ graph fixed)
  case refl_1 => exact .refl
  case symm_1 _ _ _ _ ih forward pullback assumptions => exact .symm (ih forward pullback assumptions)
  case trans_2 _ _ _ _ _ _ first second forward pullback assumptions => exact .trans (first forward pullback assumptions) (second forward pullback assumptions)
  case congrChildren_1 _ _ _ same _ children forward pullback assumptions =>
    apply DefinitionallyEqual.congrChildren (SameHead.scopedAtoms same)
    rw [scope.children,scope.children]
    exact scope_list_at scope (fun index first second leftAt rightAt => children index first second leftAt rightAt forward pullback assumptions)
  case step _ _ _ _ ih forward pullback assumptions => exact .step (ih forward pullback assumptions)
  case row _ _ _ equivalent forward pullback assumptions => exact .row (scope.rowEquivalent_term equivalent)
  case refl_2 => exact .refl
  case step_1 _ _ _ _ ih forward pullback assumptions => exact .step (ih forward pullback assumptions)
  case trans_3 _ _ _ _ _ _ first second forward pullback assumptions => exact .trans (first forward pullback assumptions) (second forward pullback assumptions)
  case congrChildren_2 _ _ _ same _ children forward pullback assumptions =>
    apply DefinitionalReduction.congrChildren (SameHead.scopedAtoms same)
    rw [scope.children,scope.children]
    exact scope_list_at scope (fun index first second leftAt rightAt => children index first second leftAt rightAt forward pullback assumptions)
  case row_1 _ _ _ equivalent forward pullback assumptions => exact .row (scope.rowEquivalent_term equivalent)
  case inferred _ implementation _ _ _ _ instantiated kinded graph lengths _ _ head origins forward pullback assumptions declared =>
    have fixed := valid.declaration_fixed (scope := scope) declared
    refine .inferred (instantiated.map_values scope.term (fun term _ => scope.kind term)) ?_
      (scope.substitutes_values graph (fun term member => fixed term (by simp [Definition.terms,member])))
      (by simpa only [List.length_map] using lengths) ?_ ?_
    · intro term member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      simpa only [scope.kind] using forward original original.kind (kinded original present)
    · exact scope_list_at scope (fun index first second leftAt rightAt => head index first second leftAt rightAt forward pullback assumptions)
    · intro index binder value binderAt valueAt
      rw [List.getElem?_map] at valueAt
      obtain ⟨original,present,rfl⟩ := Option.map_eq_some_iff.mp valueAt
      exact origins index binder original binderAt present forward pullback assumptions
  case domainValid _ _ _ _ _ declaration associated _ _ found member associatedFound owner owners items kinded _ _ ownerIH itemIH forward pullback assumptions =>
    refine .valid found member associatedFound owner
      (owners.map_values scope.term (fun term _ => scope.kind term))
      (items.map_values scope.term (fun term _ => scope.kind term)) ?_ ?_ ?_
    · intro term present
      rw [← List.map_append] at present
      obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp present
      simpa only [scope.kind] using forward original original.kind (kinded original originalMember)
    · intro requirement present
      have fixed := predicateFixed (List.mem_of_find?_eq_some (Program.trait_lookup found)) requirement (fun term nested => by
        simp only [Definition.terms,List.mem_append,List.mem_flatMap]
        exact Or.inl ⟨requirement,present,nested⟩)
      exact fixed ▸ ownerIH requirement present forward pullback assumptions
    · intro requirement present
      have fixed := predicateFixed (List.mem_of_find?_eq_some (Program.associated_lookup associatedFound)) requirement (fun term nested => by
        simp only [Definition.terms,List.mem_append,List.mem_flatMap]
        exact Or.inl (Or.inr ⟨requirement,present,nested⟩))
      simpa only [mapSub,List.map_append,fixed] using itemIH requirement present forward pullback assumptions
  case parameter _ _ _ _ same forward pullback assumptions => exact .parameter ((scope.kind _).trans same)
  case child _ _ _ _ _ _ _ _ _ structural same templateAt queryAt _ ih forward pullback assumptions =>
    exact .child structural (SameHead.scopedAtoms_right same (List.mem_of_getElem? queryAt))
      templateAt (by rw [scope.children,List.getElem?_map,queryAt]; rfl) (ih forward pullback assumptions)
  case sourceReduction _ _ _ _ _ _ _ reduction _ _ ih forward pullback assumptions => exact .sourceReduction reduction (ih forward pullback assumptions)
  case queryConversion _ _ _ _ _ _ _ _ _ equal origin forward pullback assumptions => exact .queryConversion (equal forward pullback assumptions) (origin forward pullback assumptions)
  case argument _ _ _ _ _ _ _ _ templateAt queryAt _ ih forward pullback assumptions =>
    exact .argument templateAt (by rw [List.getElem?_map,queryAt]; rfl) (ih forward pullback assumptions)

/-- Source equality closes through the same complete logical transport. -/
theorem Equal.decode_scope {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {left right : Term} (equal : Equal program source left right)
    (scope : ScopeInstantiation)
    (forward : ∀ term kind, Kinding program source term kind → Kinding program target (scope.term term) kind)
    (pullback : ∀ term kind, Kinding program target term kind → Kinding program source term kind ∧ scope.term term = term)
    (assumptions : ∀ requirement ∈ source.assumptions, Entails program target (requirement.mapTerms scope.term)) :
    Equal program target (scope.term left) (scope.term right) := by
  exact .entailed (by simpa only [Constraint.mapTerms] using
    (Entails.equality equal).decode_scope valid scope forward pullback assumptions)

end Glorious.Language
