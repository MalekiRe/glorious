import GloriousLanguage.FreshAtomInterpretation
import GloriousLanguage.AtomRelations
import GloriousLanguage.CapabilityAtomTransport

/-! Fresh generative specialization transports the actual mutual proof.
Quantified predicates use the existing hygienic interpreter; all executable
term judgments retain their actual mapped terms and raw opening tables. -/
namespace Glorious.Language

open PredicateSemantics

private abbrev FreshResult (program : Program) (target : Context) (specialization : FreshAtomSpecialization)
    (source : Context) (judgment : Prop) : Prop :=
  (∀ term kind, Kinding program source term kind → Kinding program target (specialization.term term) kind) →
  (∀ term kind, Kinding program target term kind → Kinding program source term kind ∧ specialization.term term = term) →
  (∀ requirement ∈ source.assumptions, FreshAtomInterpretation.Holds specialization program target requirement) → judgment

theorem Entails.interpret_fresh {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {constraint : Constraint} (held : Entails program source constraint)
    (specialization : FreshAtomSpecialization) (admitted : specialization.Admitted program target)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (forward : ∀ term kind, Kinding program source term kind → Kinding program target (specialization.term term) kind)
    (pullback : ∀ term kind, Kinding program target term kind → Kinding program source term kind ∧ specialization.term term = term)
    (assumptions : ∀ requirement ∈ source.assumptions, FreshAtomInterpretation.Holds specialization program target requirement) :
    FreshAtomInterpretation.Holds specialization program target constraint := by
  let map := specialization.term
  let mapSub := fun (substitution : Substitution) => substitution.map (fun entry => (entry.1,map entry.2))
  have parameters : ∀ id kind, map (.parameter id kind) = .parameter id kind := by
    intro id kind
    simp only [map,FreshAtomSpecialization.term]
  have fixed := specialization.source_fixed valid
  have atoms {predicate : Constraint} (atomic : predicate.Atomic) :=
    FreshAtomInterpretation.holds_atomic_iff specialization valid targetKinded atomic
  refine Entails.rec
    (motive_1 := fun source type principal _ => FreshResult program target specialization source
      (CapabilityEvidence program target (map type) principal))
    (motive_2 := fun source assignment type principal _ => FreshResult program target specialization source
      (∃ supported, principal.Restricts supported ∧ (CapabilityEquation program assignment type supported ∨
        CapabilityEvidence program target (map type) supported)))
    (motive_3 := fun source left right _ => FreshResult program target specialization source (Equal program target (map left) (map right)))
    (motive_4 := fun source trait arguments negative implementation substitution _ => FreshResult program target specialization source
      (SelectsImpl program target trait (arguments.map map) negative implementation (mapSub substitution)))
    (motive_5 := fun source effect row _ => FreshResult program target specialization source (RowMember program target (map effect) (map row)))
    (motive_6 := fun source required allowed _ => FreshResult program target specialization source (RowSubset program target (map required) (map allowed)))
    (motive_7 := fun source type region _ => FreshResult program target specialization source (TypeOutlives program target (map type) (map region)))
    (motive_8 := fun source constraint _ => FreshResult program target specialization source
      (FreshAtomInterpretation.Holds specialization program target constraint))
    (motive_9 := fun source substitution constraint _ => FreshResult program target specialization source
      (FreshAtomInterpretation.Holds specialization program target (constraint.substitute substitution)))
    (motive_10 := fun source left right _ => FreshResult program target specialization source (DefinitionalStep program target (map left) (map right)))
    (motive_11 := fun source left right _ => FreshResult program target specialization source (DefinitionallyEqual program target (map left) (map right)))
    (motive_12 := fun source left right _ => FreshResult program target specialization source (DefinitionalReduction program target (map left) (map right)))
    (motive_13 := fun source implementation arguments substitution _ => FreshResult program target specialization source
      (Definition.implementation implementation ∈ program.declarations →
        MatchesImplHead program target implementation (arguments.map map) (mapSub substitution)))
    (motive_14 := fun source trait member owners items associated ownerSub itemSub _ => FreshResult program target specialization source
      (ProjectionDomain program target trait member (owners.map map) (items.map map) associated (mapSub ownerSub) (mapSub itemSub)))
    (motive_15 := fun sourceContext source binder template query value _ => FreshResult program target specialization source
      (InfersHeadParameter program sourceContext target binder template (map query) (map value)))
    (motive_16 := fun source implementation arguments binder value _ => FreshResult program target specialization source
      (InfersHeadArgument program target implementation (arguments.map map) binder (map value)))
    ?structural ?logical ?capEqual ?equation ?evidence
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
  all_goals dsimp only [FreshResult]
  all_goals intros
  all_goals try simp only [map,FreshAtomSpecialization.term,List.map_cons,List.map_nil]
  case structural _ _ _ assignment found _ unfolded forward pullback assumptions =>
    exact CapabilityEvidence.map_atoms_coinduction valid found map specialization.shape fixed specialization.kind
      (fun term principal selected => unfolded term principal selected forward pullback assumptions)
  case logical _ _ _ _ _ requested lower ih forward pullback assumptions =>
    exact .logical (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (ih forward pullback assumptions)) requested lower
  case capEqual _ _ _ _ _ _ equal evidence forward pullback assumptions =>
    exact .equal (equal forward pullback assumptions) (evidence forward pullback assumptions)
  case equation _ _ _ _ _ restriction equation forward pullback assumptions => exact ⟨_,restriction,Or.inl equation⟩
  case evidence _ _ _ _ _ restriction _ ih forward pullback assumptions => exact ⟨_,restriction,Or.inr (ih forward pullback assumptions)⟩
  case refl => exact .refl
  case symm _ _ _ _ ih forward pullback assumptions => exact .symm (ih forward pullback assumptions)
  case trans _ _ _ _ _ _ first second forward pullback assumptions => exact .trans (first forward pullback assumptions) (second forward pullback assumptions)
  case congrChildren _ _ _ same _ children forward pullback assumptions =>
    exact specialization.shape.congr_relation (fun _ => .refl) Equal.congr same
      (ListRel.of_at same.children_length (fun index first second leftAt rightAt => children index first second leftAt rightAt forward pullback assumptions))
  case assumed _ _ _ member forward pullback assumptions => exact .entailed (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (assumptions _ member))
  case entailed _ _ _ _ ih forward pullback assumptions => exact .entailed (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (ih forward pullback assumptions))
  case definitional _ _ _ _ ih forward pullback assumptions => exact .definitional (ih forward pullback assumptions)
  case rowDuplicate _ _ _ _ _ _ ih forward pullback assumptions => exact .rowDuplicate (ih forward pullback assumptions)
  case tailDuplicate _ _ _ _ _ _ ih forward pullback assumptions => exact .tailDuplicate (ih forward pullback assumptions)
  case selected _ _ _ _ implementation _ declared trait negative matched _ head requirements forward pullback assumptions =>
    have lexical := fixed _ declared
    have predicates := (valid.2.2.2.2.1 _ declared).2.2
    obtain ⟨values,instantiated,typed⟩ : ∃ values, Instantiates implementation.generics values _ ∧
        ∀ value ∈ values, Kinding program _ value value.kind := by
      cases matched with
      | inferred instantiated typed _ _ _ _ => exact ⟨_,instantiated,typed⟩
    refine .selected declared trait negative (head forward pullback assumptions declared) ?_
    intro requirement member
    exact (FreshAtomInterpretation.entails_instantiated specialization valid targetKinded admitted.1
      (predicates requirement member) instantiated (fun value present => forward value value.kind (typed value present))
      (Nat.zero_le _) (fun _ member => False.elim (List.not_mem_nil member))
      (fun _ member => False.elim (List.not_mem_nil member)) (fun term nested => lexical term (by
        simp only [Definition.terms,List.mem_append,List.mem_flatMap]
        exact Or.inl (Or.inr ⟨requirement,member,nested⟩)))).mp (requirements requirement member forward pullback assumptions)
  case head _ _ _ _ _ member _ ih forward pullback assumptions => exact .head (List.mem_map.mpr ⟨_,member,rfl⟩) (ih forward pullback assumptions)
  case tail _ _ _ _ _ member _ ih forward pullback assumptions => exact .tail (List.mem_map.mpr ⟨_,member,rfl⟩) (ih forward pullback assumptions)
  case equal_1 _ _ _ _ _ _ first second forward pullback assumptions => exact .equal (first forward pullback assumptions) (second forward pullback assumptions)
  case empty => exact .empty
  case assumed_1 _ _ _ member forward pullback assumptions => exact .entailed (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (assumptions _ member))
  case same _ _ _ _ ih forward pullback assumptions => exact .same (ih forward pullback assumptions)
  case trans_1 _ _ _ _ _ _ first second forward pullback assumptions => exact .trans (first forward pullback assumptions) (second forward pullback assumptions)
  case instances _ _ _ _ _ _ fields tails forward pullback assumptions =>
    exact .instances (fun term member => by
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact fields original present forward pullback assumptions)
      (fun term member => by
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        exact tails original present forward pullback assumptions)
  case entailed_1 _ _ _ _ ih forward pullback assumptions => exact .entailed (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (ih forward pullback assumptions))
  case assumed_2 _ _ _ member forward pullback assumptions => exact .entailed (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (assumptions _ member))
  case scalar => exact .scalar
  case unit => exact .unit
  case pointer => exact .pointer
  case reference _ _ _ _ _ _ ih forward pullback assumptions => exact .reference (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (ih forward pullback assumptions))
  case bottom => exact .bottom
  case tuple _ _ _ _ fields forward pullback assumptions =>
    exact .tuple (fun term member => by
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact fields original present forward pullback assumptions)
  case array _ _ _ _ _ ih forward pullback assumptions => exact .array (ih forward pullback assumptions)
  case nominal _ _ _ _ _ _ _ found instantiated substituted _ fields forward pullback assumptions =>
    have lexical := fixed _ (List.mem_of_find?_eq_some (Program.data_lookup found))
    exact .nominal found (instantiated.map_values map (fun term _ => specialization.kind term))
      (substituted.map_atoms_fixed map specialization.shape parameters (fun term member => lexical term (by
        simp only [Definition.terms,List.mem_append]
        exact Or.inl (Or.inl (Or.inl member)))) specialization.kind)
      (fun term member => by
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        exact fields original present forward pullback assumptions)
  case callable _ _ _ _ _ declared _ fields forward pullback assumptions =>
    exact .callable (declared.map_atoms valid map specialization.shape fixed specialization.kind)
      (fun term member => by
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        exact fields original present forward pullback assumptions)
  case label _ _ _ _ _ _ ih forward pullback assumptions => exact .label (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (ih forward pullback assumptions))
  case environment _ _ _ _ _ _ _ outlives fields forward pullback assumptions =>
    exact .environment (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (outlives forward pullback assumptions))
      (fun term member => by
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        exact fields original present forward pullback assumptions)
  case available _ _ _ _ _ _ ih forward pullback assumptions =>
    exact .available (by simpa only [map,FreshAtomSpecialization.term] using ih forward pullback assumptions)
  case bindings _ _ _ _ _ _ _ outlives fields forward pullback assumptions =>
    exact .bindings (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (outlives forward pullback assumptions))
      (fun term member => by
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        exact fields original present forward pullback assumptions)
  case equal_2 _ _ _ _ _ _ first second forward pullback assumptions => exact .equal (first forward pullback assumptions) (second forward pullback assumptions)
  case entailed_2 _ _ _ _ ih forward pullback assumptions => exact .entailed (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (ih forward pullback assumptions))
  case checkedCallable _ _ _ _ _ _ _ _ found member receiver arguments result effects forward pullback assumptions =>
    have lexical := fixed _ (List.mem_of_find?_eq_some (Program.function_lookup found))
    have invocation : ∀ (term : Term), term ∈ _ → term.AtomsFixed map := fun term present => lexical term (by
      simp only [Definition.terms,List.mem_append,List.mem_flatMap]
      exact Or.inr ⟨_,member,present⟩)
    apply (atoms (by trivial)).mpr
    simp only [Constraint.mapTerms]
    exact (.checkedCallable found member
      (receiver.map_atoms_fixed map specialization.shape parameters (invocation _ (by simp [InvocationRelation.terms])) specialization.kind)
      (arguments.map_atoms_fixed map specialization.shape parameters (fun term present => invocation term (by simp [InvocationRelation.terms,present])) specialization.kind)
      (result.map_atoms_fixed map specialization.shape parameters (invocation _ (by simp [InvocationRelation.terms])) specialization.kind)
      (effects.map_atoms_fixed map specialization.shape parameters (invocation _ (by simp [InvocationRelation.terms])) specialization.kind))
  case checkedRunsIn _ _ _ _ _ _ _ _ found member receiver access arguments after forward pullback assumptions =>
    have lexical := fixed _ (List.mem_of_find?_eq_some (Program.function_lookup found))
    have invocation : ∀ (term : Term), term ∈ _ → term.AtomsFixed map := fun term present => lexical term (by
      simp only [Definition.terms,List.mem_append,List.mem_flatMap]
      exact Or.inr ⟨_,member,present⟩)
    apply (atoms (by trivial)).mpr
    simp only [Constraint.mapTerms]
    exact (.checkedRunsIn found member
      (receiver.map_atoms_fixed map specialization.shape parameters (invocation _ (by simp [InvocationRelation.terms])) specialization.kind)
      (access.map_atoms_fixed map specialization.shape parameters (invocation _ (by simp [InvocationRelation.terms])) specialization.kind)
      (arguments.map_atoms_fixed map specialization.shape parameters (fun term present => invocation term (by simp [InvocationRelation.terms,present])) specialization.kind)
      (after.map_atoms_fixed map specialization.shape parameters (invocation _ (by simp [InvocationRelation.terms])) specialization.kind))
  case assumed_3 _ _ member forward pullback assumptions => exact assumptions _ member
  case congrSubstitution _ _ _ _ _ _ _ before after _ equal held forward pullback assumptions =>
    apply ((FreshAtomInterpretation.algebra specialization program target).holds_substitution_congr
      program target LogicalQuotient.canonical LogicalQuotient.canonical ?_ before after).mp (held forward pullback assumptions)
    intro id kind
    rw [FreshAtomInterpretation.eval_canonical,FreshAtomInterpretation.eval_canonical]
    exact LogicalQuotient.ofTerm_eq.mpr (equal id kind forward pullback assumptions)
  case equality _ _ _ _ ih forward pullback assumptions =>
    apply (atoms (by trivial)).mpr
    simp only [Constraint.mapTerms]
    exact (.equality (ih forward pullback assumptions))
  case outlivesRefl =>
    apply (atoms (by trivial)).mpr
    simp only [Constraint.mapTerms]
    exact .outlivesRefl
  case outlivesStatic =>
    apply (atoms (by trivial)).mpr
    simp only [Constraint.mapTerms,FreshAtomSpecialization.term]
    exact .outlivesStatic
  case outlivesTrans _ _ _ _ _ _ first second forward pullback assumptions =>
    apply (atoms (by trivial)).mpr
    simp only [Constraint.mapTerms]
    exact (.outlivesTrans (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (first forward pullback assumptions))
      (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (second forward pullback assumptions)))
  case typeOutlives _ _ _ _ ih forward pullback assumptions =>
    apply (atoms (by trivial)).mpr
    simp only [Constraint.mapTerms]
    exact (.typeOutlives (ih forward pullback assumptions))
  case rows _ _ _ _ ih forward pullback assumptions =>
    apply (atoms (by trivial)).mpr
    simp only [Constraint.mapTerms]
    exact (.rows (ih forward pullback assumptions))
  case implementation _ _ _ _ _ _ _ ih forward pullback assumptions =>
    apply (atoms (by trivial)).mpr
    simp only [Constraint.mapTerms]
    exact (.implementation (ih forward pullback assumptions))
  case use _ _ _ _ _ requested ih forward pullback assumptions =>
    apply (atoms (by trivial)).mpr
    simp only [Constraint.mapTerms]
    exact (.use (ih forward pullback assumptions) requested)
  case quantified _ _ _ _ instances forward pullback assumptions =>
    apply (FreshAtomInterpretation.algebra specialization program target).holds_quantified program target LogicalQuotient.canonical
    intro values substitution instantiated typed requirement member
    exact instances values substitution instantiated (fun term present => (pullback term term.kind (typed term present)).1)
      requirement member forward pullback assumptions
  case quantifiedInstance _ _ _ _ _ _ _ _ instantiated typed member graph ih forward pullback assumptions =>
    exact FreshAtomInterpretation.quantified_instance specialization admitted (ih forward pullback assumptions) instantiated
      (fun term present => forward term term.kind (typed term present)) member graph
  case instantiated _ _ _ _ graph _ ih forward pullback assumptions =>
    rw [← graph.2]
    exact ih forward pullback assumptions
  case alias _ _ _ _ _ _ found instantiated typed graph forward pullback assumptions =>
    have lexical := fixed _ (List.mem_of_find?_eq_some (Program.alias_lookup found))
    exact .alias found (instantiated.map_values map (fun term _ => specialization.kind term))
      (fun term member => by
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        simpa only [specialization.kind] using forward original original.kind (typed original present))
      (graph.map_atoms_fixed map specialization.shape parameters (lexical _ (by simp [Definition.terms])) specialization.kind)
  case projection _ _ _ _ _ _ _ _ _ _ _ _ selected member graph domain selectedIH forward pullback assumptions =>
    have lexical := fixed _ selected.declaration
    exact .projection (domain forward pullback assumptions) (selectedIH forward pullback assumptions) member (by
      simpa only [mapSub,List.map_append] using graph.map_atoms_fixed map specialization.shape parameters (lexical _ (by
        simp only [Definition.terms,List.mem_append,List.mem_map]
        exact Or.inl (Or.inl (Or.inr ⟨_,member,rfl⟩)))) specialization.kind)
  case defaultProjection _ _ memberId _ _ associated _ _ _ _ _ _ domain _ absent default graph domainIH selectedIH forward pullback assumptions =>
    have found : program.associated memberId = some associated := by cases domain; assumption
    have lexical := fixed _ (List.mem_of_find?_eq_some (Program.associated_lookup found))
    exact .defaultProjection (domainIH forward pullback assumptions) (selectedIH forward pullback assumptions) absent default (by
      simpa only [mapSub,List.map_append] using graph.map_atoms_fixed map specialization.shape parameters (lexical _ (by
        simp only [Definition.terms,List.mem_append]
        exact Or.inl (Or.inl (by simp [default])))) specialization.kind)
  case refl_1 => exact .refl
  case symm_1 _ _ _ _ ih forward pullback assumptions => exact .symm (ih forward pullback assumptions)
  case trans_2 _ _ _ _ _ _ first second forward pullback assumptions => exact .trans (first forward pullback assumptions) (second forward pullback assumptions)
  case congrChildren_1 _ _ _ same _ children forward pullback assumptions =>
    exact specialization.shape.congr_relation (fun _ => .refl) DefinitionallyEqual.congr same
      (ListRel.of_at same.children_length (fun index first second leftAt rightAt => children index first second leftAt rightAt forward pullback assumptions))
  case step _ _ _ _ ih forward pullback assumptions => exact .step (ih forward pullback assumptions)
  case row _ _ _ equivalent forward pullback assumptions => exact .row (equivalent.map_atoms map specialization.shape)
  case refl_2 => exact .refl
  case step_1 _ _ _ _ ih forward pullback assumptions => exact .step (ih forward pullback assumptions)
  case trans_3 _ _ _ _ _ _ first second forward pullback assumptions => exact .trans (first forward pullback assumptions) (second forward pullback assumptions)
  case congrChildren_2 _ _ _ same _ children forward pullback assumptions =>
    exact specialization.shape.congr_relation (fun _ => .refl) DefinitionalReduction.congr same
      (ListRel.of_at same.children_length (fun index first second leftAt rightAt => children index first second leftAt rightAt forward pullback assumptions))
  case row_1 _ _ _ equivalent forward pullback assumptions => exact .row (equivalent.map_atoms map specialization.shape)
  case inferred _ _ _ _ _ specialized instantiated typed graph lengths _ _ head origins forward pullback assumptions declared =>
    have lexical := fixed _ declared
    refine .inferred (specialized := specialized.map map) (instantiated.map_values map (fun term _ => specialization.kind term)) ?_ ?_ ?_ ?_ ?_
    · intro term member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      simpa only [map,specialization.kind] using forward original original.kind (typed original present)
    · exact graph.map_atoms_fixed map specialization.shape parameters (fun term member => lexical term (by
        simp only [Definition.terms,List.mem_append]
        exact Or.inl (Or.inl (Or.inl member)))) specialization.kind
    · simpa only [List.length_map] using lengths
    · exact AtomHomomorphism.list_at (fun index first second leftAt rightAt => head index first second leftAt rightAt forward pullback assumptions)
    · intro index binder value binderAt valueAt
      obtain ⟨original,originalAt,rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using valueAt)
      exact origins index binder original binderAt originalAt forward pullback assumptions
  case domainValid context traitId memberId owners items declaration associated ownerSub itemSub
      found member associatedFound owner ownerInst itemInst typed _ _ ownerIH itemIH forward pullback assumptions =>
    have traitDeclared := List.mem_of_find?_eq_some (Program.trait_lookup found)
    have itemDeclared := List.mem_of_find?_eq_some (Program.associated_lookup associatedFound)
    have traitLexical := fixed _ traitDeclared
    have itemLexical := fixed _ itemDeclared
    have traitPredicates := (valid.2.2.2.2.1 _ traitDeclared).2.2
    have itemAdmitted := valid.2.2.2.2.1 _ itemDeclared
    obtain ⟨sourceTrait,sourceFound,itemPredicates⟩ := itemAdmitted.2.2
    rw [owner,found] at sourceFound
    cases Option.some.inj sourceFound
    obtain ⟨sourceTrait,sourceFound,_,unique,_⟩ := itemAdmitted.2.1
    rw [owner,found] at sourceFound
    cases Option.some.inj sourceFound
    refine .valid found member associatedFound owner
      (ownerInst.map_values map (fun term _ => specialization.kind term))
      (itemInst.map_values map (fun term _ => specialization.kind term)) ?_ ?_ ?_
    · intro term present
      rw [← List.map_append] at present
      obtain ⟨original,inside,rfl⟩ := List.mem_map.mp present
      simpa only [specialization.kind] using forward original original.kind (typed original inside)
    · intro requirement present
      exact (FreshAtomInterpretation.entails_instantiated specialization valid targetKinded admitted.1
        (traitPredicates requirement present) ownerInst
        (fun value inside => forward value value.kind (typed value (List.mem_append_left _ inside)))
        (Nat.zero_le _) (fun _ member => False.elim (List.not_mem_nil member))
        (fun _ member => False.elim (List.not_mem_nil member)) (fun term nested => traitLexical term (by
          simp only [Definition.terms,List.mem_append,List.mem_flatMap]
          exact Or.inl ⟨requirement,present,nested⟩))).mp (ownerIH requirement present forward pullback assumptions)
    · intro requirement present
      simpa only [mapSub,List.map_append] using
        (FreshAtomInterpretation.entails_instantiated specialization valid targetKinded admitted.1
          (itemPredicates requirement present) (ownerInst.append itemInst unique)
          (fun value inside => forward value value.kind (typed value inside))
          (Nat.zero_le _) (fun _ member => False.elim (List.not_mem_nil member))
          (fun _ member => False.elim (List.not_mem_nil member)) (fun term nested => itemLexical term (by
            simp only [Definition.terms,List.mem_append,List.mem_flatMap]
            exact Or.inl (Or.inr ⟨requirement,present,nested⟩)))).mp (itemIH requirement present forward pullback assumptions)
  case parameter _ _ _ _ same forward pullback assumptions => exact .parameter ((specialization.kind _).trans same)
  case child _ _ _ _ _ _ _ _ _ structural same leftAt rightAt _ ih forward pullback assumptions =>
    obtain ⟨sameMapped,children⟩ := specialization.shape.child_head same (List.mem_of_getElem? rightAt)
    exact .child structural sameMapped leftAt (by rw [children,List.getElem?_map,rightAt]; rfl) (ih forward pullback assumptions)
  case sourceReduction _ _ _ _ _ _ _ reduction _ _ ih forward pullback assumptions => exact .sourceReduction reduction (ih forward pullback assumptions)
  case queryConversion _ _ _ _ _ _ _ _ _ equal origin forward pullback assumptions => exact .queryConversion (equal forward pullback assumptions) (origin forward pullback assumptions)
  case argument _ _ _ _ _ _ _ _ leftAt rightAt _ ih forward pullback assumptions =>
    exact .argument leftAt (by rw [List.getElem?_map,rightAt]; rfl) (ih forward pullback assumptions)

end Glorious.Language
