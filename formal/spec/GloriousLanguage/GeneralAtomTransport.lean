import GloriousLanguage.CurrentAtomInterpretation
import GloriousLanguage.AtomOpening
import GloriousLanguage.CapabilityAtomTransport

/-! Fresh generative specialization transports the actual mutual proof.
Quantified predicates use the existing hygienic interpreter; all executable
term judgments retain their actual mapped terms and raw opening tables. -/
namespace Glorious.Language

open PredicateSemantics

private abbrev AtomResult (program : Program) (target : Context) (specialization : FreshAtomSpecialization)
    (current : Valuation (LogicalQuotient.Class program target)) (map : Term → Term)
    (source : Context) (judgment : Prop) : Prop :=
  (∀ term kind, Kinding program source term kind → Kinding program target (map term) kind) →
  (∀ term kind, Kinding program target term kind → ∃ original, Kinding program source original kind ∧ map original = term) →
  (∀ requirement ∈ source.assumptions, FreshAtomInterpretation.HoldsAt specialization program target current requirement) → judgment

theorem Entails.interpret_atoms {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {constraint : Constraint} (held : Entails program source constraint)
    (specialization : FreshAtomSpecialization) (admitted : specialization.Admitted program target)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (current : Valuation (LogicalQuotient.Class program target)) (map : Term → Term)
    (shape : AtomHomomorphism map) (fixed : program.AtomsFixed map)
    (mapKinds : ∀ term, (map term).kind = term.kind)
    (evaluated : ∀ term, (FreshAtomInterpretation.algebra specialization program target).eval current term =
      LogicalQuotient.ofTerm (map term))
    (forward : ∀ term kind, Kinding program source term kind → Kinding program target (map term) kind)
    (pullback : ∀ term kind, Kinding program target term kind → ∃ original, Kinding program source original kind ∧ map original = term)
    (assumptions : ∀ requirement ∈ source.assumptions, FreshAtomInterpretation.HoldsAt specialization program target current requirement) :
    FreshAtomInterpretation.HoldsAt specialization program target current constraint := by
  let mapSub := fun (substitution : Substitution) => substitution.map (fun entry => (entry.1,map entry.2))
  have sourceFixed := specialization.source_fixed valid
  have atoms {predicate : Constraint} (atomic : predicate.Atomic) :=
    FreshAtomInterpretation.holds_at_atomic_iff specialization valid targetKinded current map evaluated atomic
  refine Entails.rec
    (motive_1 := fun source type principal _ => AtomResult program target specialization current map source
      (CapabilityEvidence program target (map type) principal))
    (motive_2 := fun source assignment type principal _ => AtomResult program target specialization current map source
      (∃ supported, principal.Restricts supported ∧ (CapabilityEquation program assignment type supported ∨
        CapabilityEvidence program target (map type) supported)))
    (motive_3 := fun source left right _ => AtomResult program target specialization current map source (Equal program target (map left) (map right)))
    (motive_4 := fun source trait arguments negative implementation substitution _ => AtomResult program target specialization current map source
      (SelectsImpl program target trait (arguments.map map) negative implementation (mapSub substitution)))
    (motive_5 := fun source effect row _ => AtomResult program target specialization current map source (RowMember program target (map effect) (map row)))
    (motive_6 := fun source required allowed _ => AtomResult program target specialization current map source (RowSubset program target (map required) (map allowed)))
    (motive_7 := fun source type region _ => AtomResult program target specialization current map source (TypeOutlives program target (map type) (map region)))
    (motive_8 := fun source constraint _ => AtomResult program target specialization current map source
      (FreshAtomInterpretation.HoldsAt specialization program target current constraint))
    (motive_9 := fun source substitution constraint _ => AtomResult program target specialization current map source
      (FreshAtomInterpretation.HoldsAt specialization program target current (constraint.substitute substitution)))
    (motive_10 := fun source left right _ => AtomResult program target specialization current map source (DefinitionalStep program target (map left) (map right)))
    (motive_11 := fun source left right _ => AtomResult program target specialization current map source (DefinitionallyEqual program target (map left) (map right)))
    (motive_12 := fun source left right _ => AtomResult program target specialization current map source (DefinitionalReduction program target (map left) (map right)))
    (motive_13 := fun source implementation arguments substitution _ => AtomResult program target specialization current map source
      (Definition.implementation implementation ∈ program.declarations →
        MatchesImplHead program target implementation (arguments.map map) (mapSub substitution)))
    (motive_14 := fun source trait member owners items associated ownerSub itemSub _ => AtomResult program target specialization current map source
      (ProjectionDomain program target trait member (owners.map map) (items.map map) associated (mapSub ownerSub) (mapSub itemSub)))
    (motive_15 := fun sourceContext source binder template query value _ => AtomResult program target specialization current map source
      (InfersHeadParameter program sourceContext target binder template (map query) (map value)))
    (motive_16 := fun source implementation arguments binder value _ => AtomResult program target specialization current map source
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
  all_goals dsimp only [AtomResult]
  all_goals intros
  case structural _ _ _ assignment found _ unfolded forward pullback assumptions =>
    exact CapabilityEvidence.map_atoms_coinduction valid found map shape fixed mapKinds
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
    exact shape.congr_relation (fun _ => .refl) Equal.congr same
      (ListRel.of_at same.children_length (fun index first second leftAt rightAt => children index first second leftAt rightAt forward pullback assumptions))
  case assumed _ _ _ member forward pullback assumptions => exact .entailed (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (assumptions _ member))
  case entailed _ _ _ _ ih forward pullback assumptions => exact .entailed (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (ih forward pullback assumptions))
  case definitional _ _ _ _ ih forward pullback assumptions => exact .definitional (ih forward pullback assumptions)
  case rowDuplicate _ _ _ _ _ _ ih forward pullback assumptions =>
    rw [shape (.row _ _),shape (.row _ _)]
    exact .rowDuplicate (ih forward pullback assumptions)
  case tailDuplicate _ _ _ _ _ _ ih forward pullback assumptions =>
    rw [shape (.row _ _),shape (.row _ _)]
    exact .tailDuplicate (ih forward pullback assumptions)
  case selected _ _ _ _ implementation _ declared trait negative matched _ head requirements forward pullback assumptions =>
    have lexical := sourceFixed _ declared
    have predicates := (valid.2.2.2.2.1 _ declared).2.2
    obtain ⟨values,instantiated,typed⟩ : ∃ values, Instantiates implementation.generics values _ ∧
        ∀ value ∈ values, Kinding program _ value value.kind := by
      cases matched with
      | inferred instantiated typed _ _ _ _ => exact ⟨_,instantiated,typed⟩
    refine .selected declared trait negative (head forward pullback assumptions declared) ?_
    intro requirement member
    exact (FreshAtomInterpretation.entails_at_instantiated specialization valid targetKinded admitted.1 current map mapKinds evaluated
      (predicates requirement member) instantiated (fun value present => forward value value.kind (typed value present))
      (Nat.zero_le _) (fun _ member => False.elim (List.not_mem_nil member))
      (fun _ member => False.elim (List.not_mem_nil member)) (fun term nested => lexical term (by
        simp only [Definition.terms,List.mem_append,List.mem_flatMap]
        exact Or.inl (Or.inr ⟨requirement,member,nested⟩)))).mp (requirements requirement member forward pullback assumptions)
  case head _ _ _ _ _ member _ ih forward pullback assumptions =>
    rw [shape (.row _ _)]
    exact .head (List.mem_map.mpr ⟨_,member,rfl⟩) (ih forward pullback assumptions)
  case tail _ _ _ _ _ member _ ih forward pullback assumptions =>
    rw [shape (.row _ _)]
    exact .tail (List.mem_map.mpr ⟨_,member,rfl⟩) (ih forward pullback assumptions)
  case equal_1 _ _ _ _ _ _ first second forward pullback assumptions => exact .equal (first forward pullback assumptions) (second forward pullback assumptions)
  case empty =>
    rw [shape (.row _ _)]
    exact .empty
  case assumed_1 _ _ _ member forward pullback assumptions => exact .entailed (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (assumptions _ member))
  case same _ _ _ _ ih forward pullback assumptions => exact .same (ih forward pullback assumptions)
  case trans_1 _ _ _ _ _ _ first second forward pullback assumptions => exact .trans (first forward pullback assumptions) (second forward pullback assumptions)
  case instances _ _ _ _ _ _ fields tails forward pullback assumptions =>
    rw [shape (.row _ _)]
    exact .instances (fun term member => by
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact fields original present forward pullback assumptions)
      (fun term member => by
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        exact tails original present forward pullback assumptions)
  case entailed_1 _ _ _ _ ih forward pullback assumptions => exact .entailed (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (ih forward pullback assumptions))
  case assumed_2 _ _ _ member forward pullback assumptions => exact .entailed (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (assumptions _ member))
  case scalar =>
    rw [shape (.scalar _)]
    exact .scalar
  case unit =>
    rw [shape (.unit)]
    exact .unit
  case pointer =>
    rw [shape (.rawPointer _ _)]
    exact .pointer
  case reference _ _ _ _ _ _ ih forward pullback assumptions =>
    rw [shape (.reference _ _ _)]
    exact .reference (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (ih forward pullback assumptions))
  case bottom =>
    rw [shape (.bottom)]
    exact .bottom
  case tuple _ _ _ _ fields forward pullback assumptions =>
    rw [shape (.tuple _)]
    exact .tuple (fun term member => by
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact fields original present forward pullback assumptions)
  case array _ _ _ _ _ ih forward pullback assumptions =>
    rw [shape (.array _ _)]
    exact .array (ih forward pullback assumptions)
  case nominal _ _ _ _ _ _ _ found instantiated substituted _ fields forward pullback assumptions =>
    rw [shape (.nominal _ _)]
    have lexical := fixed _ (List.mem_of_find?_eq_some (Program.data_lookup found))
    exact .nominal found (instantiated.map_values map (fun term _ => mapKinds term))
      (substituted.map_instantiated (valid.data_field_types found) instantiated map shape (fun term member => lexical term (by
        simp only [Definition.terms,List.mem_append]
        exact Or.inl (Or.inl (Or.inl member)))) mapKinds)
      (fun term member => by
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        exact fields original present forward pullback assumptions)
  case callable _ _ _ _ _ declared _ fields forward pullback assumptions =>
    rw [shape (.callable _ _)]
    exact .callable (declared.map_atoms valid map shape fixed mapKinds)
      (fun term member => by
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        exact fields original present forward pullback assumptions)
  case label _ _ _ _ _ _ ih forward pullback assumptions =>
    rw [shape (.label _ _ _)]
    exact .label (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (ih forward pullback assumptions))
  case environment _ _ _ _ _ _ _ outlives fields forward pullback assumptions =>
    rw [shape (.environment _ _ _)]
    exact .environment (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (outlives forward pullback assumptions))
      (fun term member => by
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        exact fields original present forward pullback assumptions)
  case available _ _ _ _ _ _ ih forward pullback assumptions =>
    rw [shape (.available _ _ _)]
    exact .available (by simpa only [shape (.environment _ _ _),Term.mapChildren] using ih forward pullback assumptions)
  case bindings _ _ _ _ _ _ _ outlives fields forward pullback assumptions =>
    rw [shape (.bindings _ _ _)]
    exact .bindings (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (outlives forward pullback assumptions))
      (fun term member => by
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        exact fields original present forward pullback assumptions)
  case equal_2 _ _ _ _ _ _ first second forward pullback assumptions => exact .equal (first forward pullback assumptions) (second forward pullback assumptions)
  case entailed_2 _ _ _ _ ih forward pullback assumptions => exact .entailed (by simpa only [Constraint.mapTerms,FreshAtomSpecialization.term] using (atoms (by trivial)).mp (ih forward pullback assumptions))
  case checkedCallable _ _ _ _ _ _ _ _ found member receiver arguments result effects forward pullback assumptions =>
    have declared := List.mem_of_find?_eq_some (Program.function_lookup found)
    have lexical := fixed _ declared
    have functionAdmitted := valid.2.2.2.2.1 _ declared
    have unique := functionAdmitted.2.1.1.1
    have invocationKinded := (functionAdmitted.2.2.2 _ member).1
    have invocation : ∀ (term : Term), term ∈ _ → term.AtomsFixed map := fun term present => lexical term (by
      simp only [Definition.terms,List.mem_append,List.mem_flatMap]
      exact Or.inr ⟨_,member,present⟩)
    apply (atoms (by trivial)).mpr
    simp only [Constraint.mapTerms]
    cases invocationKinded with
    | callable receiverTyped argumentsTyped resultTyped effectsTyped =>
      exact (.checkedCallable found member
        (receiver.map_completed receiverTyped unique map shape (invocation _ (by simp [InvocationRelation.terms])) mapKinds)
        (arguments.map_completed argumentsTyped unique map shape (fun term present => invocation term (by simp [InvocationRelation.terms,present])) mapKinds)
        (result.map_completed resultTyped unique map shape (invocation _ (by simp [InvocationRelation.terms])) mapKinds)
        (effects.map_completed effectsTyped unique map shape (invocation _ (by simp [InvocationRelation.terms])) mapKinds))
  case checkedRunsIn _ _ _ _ _ _ _ _ found member receiver access arguments after forward pullback assumptions =>
    have declared := List.mem_of_find?_eq_some (Program.function_lookup found)
    have lexical := fixed _ declared
    have functionAdmitted := valid.2.2.2.2.1 _ declared
    have unique := functionAdmitted.2.1.1.1
    have invocationKinded := (functionAdmitted.2.2.2 _ member).2
    have invocation : ∀ (term : Term), term ∈ _ → term.AtomsFixed map := fun term present => lexical term (by
      simp only [Definition.terms,List.mem_append,List.mem_flatMap]
      exact Or.inr ⟨_,member,present⟩)
    apply (atoms (by trivial)).mpr
    simp only [Constraint.mapTerms]
    cases invocationKinded with
    | runsIn receiverTyped accessTyped argumentsTyped afterTyped =>
      exact (.checkedRunsIn found member
        (receiver.map_completed receiverTyped unique map shape (invocation _ (by simp [InvocationRelation.terms])) mapKinds)
        (access.map_completed accessTyped unique map shape (invocation _ (by simp [InvocationRelation.terms])) mapKinds)
        (arguments.map_completed argumentsTyped unique map shape (fun term present => invocation term (by simp [InvocationRelation.terms,present])) mapKinds)
        (after.map_completed afterTyped unique map shape (invocation _ (by simp [InvocationRelation.terms])) mapKinds))
  case assumed_3 _ _ member forward pullback assumptions => exact assumptions _ member
  case congrSubstitution _ _ _ _ _ _ _ before after _ equal held forward pullback assumptions =>
    apply ((FreshAtomInterpretation.algebra specialization program target).holds_substitution_congr
      program target LogicalQuotient.canonical current ?_ before after).mp (held forward pullback assumptions)
    intro id kind
    rw [evaluated,evaluated]
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
    simp only [Constraint.mapTerms]
    rw [shape]
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
    exact FreshAtomInterpretation.quantified_at specialization admitted current map mapKinds evaluated forward pullback
      (fun values substitution instantiated typed requirement member =>
        instances values substitution instantiated typed requirement member forward pullback assumptions)
  case quantifiedInstance _ _ _ _ _ _ _ _ instantiated typed member graph ih forward pullback assumptions =>
    exact FreshAtomInterpretation.quantified_instance_at specialization admitted current map mapKinds evaluated
      (ih forward pullback assumptions) instantiated
      (fun term present => forward term term.kind (typed term present)) member graph
  case instantiated _ _ _ _ graph _ ih forward pullback assumptions =>
    rw [← graph.2]
    exact ih forward pullback assumptions
  case alias _ _ _ _ _ _ found instantiated typed graph forward pullback assumptions =>
    rw [shape (.alias _ _)]
    have lexical := fixed _ (List.mem_of_find?_eq_some (Program.alias_lookup found))
    exact .alias found (instantiated.map_values map (fun term _ => mapKinds term))
      (fun term member => by
        obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
        simpa only [mapKinds] using forward original original.kind (typed original present))
      (graph.map_instantiated (valid.alias_body found) instantiated map shape (lexical _ (by simp [Definition.terms])) mapKinds)
  case projection _ _ _ _ _ _ _ _ _ _ _ domain selected member graph domainIH selectedIH forward pullback assumptions =>
    rw [shape (.projection _ _ _ _ _)]
    have lexical := fixed _ selected.declaration
    have targetDomain := domainIH forward pullback assumptions
    obtain ⟨values,instantiated,_⟩ := selected.instantiates
    cases domain with
    | valid _ _ associatedFound _ _ itemInst _ _ _ =>
      obtain ⟨unique,_,bodyKinded⟩ := valid.override_body selected.declaration associatedFound member
      exact .projection targetDomain (selectedIH forward pullback assumptions) member (by
        simpa only [mapSub,List.map_append] using graph.map_instantiated bodyKinded
          (instantiated.append itemInst unique) map shape (lexical _ (by
            simp only [Definition.terms,List.mem_append,List.mem_map]
            exact Or.inl (Or.inl (Or.inr ⟨_,member,rfl⟩)))) mapKinds)
  case defaultProjection _ _ memberId _ _ associated _ _ _ _ _ _ domain _ absent default graph domainIH selectedIH forward pullback assumptions =>
    rw [shape (.projection _ _ _ _ _)]
    have found : program.associated memberId = some associated := by cases domain; assumption
    have lexical := fixed _ (List.mem_of_find?_eq_some (Program.associated_lookup found))
    have targetDomain := domainIH forward pullback assumptions
    cases domain with
    | valid traitFound _ associatedFound owner ownerInst itemInst _ _ _ =>
      obtain ⟨unique,bodyKinded⟩ := valid.default_body traitFound associatedFound owner default
      exact .defaultProjection targetDomain (selectedIH forward pullback assumptions) absent default (by
        simpa only [mapSub,List.map_append] using graph.map_instantiated bodyKinded
          (ownerInst.append itemInst unique) map shape (lexical _ (by
            simp only [Definition.terms,List.mem_append]
            exact Or.inl (Or.inl (by simp [default])))) mapKinds)
  case refl_1 => exact .refl
  case symm_1 _ _ _ _ ih forward pullback assumptions => exact .symm (ih forward pullback assumptions)
  case trans_2 _ _ _ _ _ _ first second forward pullback assumptions => exact .trans (first forward pullback assumptions) (second forward pullback assumptions)
  case congrChildren_1 _ _ _ same _ children forward pullback assumptions =>
    exact shape.congr_relation (fun _ => .refl) DefinitionallyEqual.congr same
      (ListRel.of_at same.children_length (fun index first second leftAt rightAt => children index first second leftAt rightAt forward pullback assumptions))
  case step _ _ _ _ ih forward pullback assumptions => exact .step (ih forward pullback assumptions)
  case row _ _ _ equivalent forward pullback assumptions => exact .row (equivalent.map_atoms map shape)
  case refl_2 => exact .refl
  case step_1 _ _ _ _ ih forward pullback assumptions => exact .step (ih forward pullback assumptions)
  case trans_3 _ _ _ _ _ _ first second forward pullback assumptions => exact .trans (first forward pullback assumptions) (second forward pullback assumptions)
  case congrChildren_2 _ _ _ same _ children forward pullback assumptions =>
    exact shape.congr_relation (fun _ => .refl) DefinitionalReduction.congr same
      (ListRel.of_at same.children_length (fun index first second leftAt rightAt => children index first second leftAt rightAt forward pullback assumptions))
  case row_1 _ _ _ equivalent forward pullback assumptions => exact .row (equivalent.map_atoms map shape)
  case inferred _ _ _ _ _ specialized instantiated typed graph lengths _ _ head origins forward pullback assumptions declared =>
    have lexical := fixed _ declared
    obtain ⟨_,_,_,_,_,_,_,signature,_⟩ := (valid.2.2.2.2.1 _ declared).2.1
    obtain ⟨_,_,_,_,headKinded,_,_⟩ := signature
    refine .inferred (specialized := specialized.map map) (instantiated.map_values map (fun term _ => mapKinds term)) ?_ ?_ ?_ ?_ ?_
    · intro term member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      simpa only [mapKinds] using forward original original.kind (typed original present)
    · exact graph.map_instantiated_kinded (fun term member => (headKinded term member).1) instantiated map shape (fun term member => lexical term (by
        simp only [Definition.terms,List.mem_append]
        exact Or.inl (Or.inl (Or.inl member)))) mapKinds
    · simpa only [List.length_map] using lengths
    · exact AtomHomomorphism.list_at (fun index first second leftAt rightAt => head index first second leftAt rightAt forward pullback assumptions)
    · intro index binder value binderAt valueAt
      obtain ⟨original,originalAt,rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using valueAt)
      exact origins index binder original binderAt originalAt forward pullback assumptions
  case domainValid context traitId memberId owners items declaration associated ownerSub itemSub
      found member associatedFound owner ownerInst itemInst typed _ _ ownerIH itemIH forward pullback assumptions =>
    have traitDeclared := List.mem_of_find?_eq_some (Program.trait_lookup found)
    have itemDeclared := List.mem_of_find?_eq_some (Program.associated_lookup associatedFound)
    have traitLexical := sourceFixed _ traitDeclared
    have itemLexical := sourceFixed _ itemDeclared
    have traitPredicates := (valid.2.2.2.2.1 _ traitDeclared).2.2
    have itemAdmitted := valid.2.2.2.2.1 _ itemDeclared
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
      simpa only [mapKinds] using forward original original.kind (typed original inside)
    · intro requirement present
      exact (FreshAtomInterpretation.entails_at_instantiated specialization valid targetKinded admitted.1 current map mapKinds evaluated
        (traitPredicates requirement present) ownerInst
        (fun value inside => forward value value.kind (typed value (List.mem_append_left _ inside)))
        (Nat.zero_le _) (fun _ member => False.elim (List.not_mem_nil member))
        (fun _ member => False.elim (List.not_mem_nil member)) (fun term nested => traitLexical term (by
          simp only [Definition.terms,List.mem_append,List.mem_flatMap]
          exact Or.inl ⟨requirement,present,nested⟩))).mp (ownerIH requirement present forward pullback assumptions)
    · intro requirement present
      simpa only [mapSub,List.map_append] using
        (FreshAtomInterpretation.entails_at_instantiated specialization valid targetKinded admitted.1 current map mapKinds evaluated
          (itemPredicates requirement present) (ownerInst.append itemInst unique)
          (fun value inside => forward value value.kind (typed value inside))
          (Nat.zero_le _) (fun _ member => False.elim (List.not_mem_nil member))
          (fun _ member => False.elim (List.not_mem_nil member)) (fun term nested => itemLexical term (by
            simp only [Definition.terms,List.mem_append,List.mem_flatMap]
            exact Or.inl (Or.inr ⟨requirement,present,nested⟩)))).mp (itemIH requirement present forward pullback assumptions)
  case parameter _ _ _ _ same forward pullback assumptions => exact .parameter ((mapKinds _).trans same)
  case child _ _ _ _ _ _ _ _ _ structural same leftAt rightAt _ ih forward pullback assumptions =>
    obtain ⟨sameMapped,children⟩ := shape.child_head same (List.mem_of_getElem? rightAt)
    exact .child structural sameMapped leftAt (by rw [children,List.getElem?_map,rightAt]; rfl) (ih forward pullback assumptions)
  case sourceReduction _ _ _ _ _ _ _ reduction _ _ ih forward pullback assumptions => exact .sourceReduction reduction (ih forward pullback assumptions)
  case queryConversion _ _ _ _ _ _ _ _ _ equal origin forward pullback assumptions => exact .queryConversion (equal forward pullback assumptions) (origin forward pullback assumptions)
  case argument _ _ _ _ _ _ _ _ leftAt rightAt _ ih forward pullback assumptions =>
    exact .argument leftAt (by rw [List.getElem?_map,rightAt]; rfl) (ih forward pullback assumptions)

end Glorious.Language
