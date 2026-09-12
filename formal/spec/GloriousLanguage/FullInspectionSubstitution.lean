import GloriousLanguage.HeadOriginSubstitution

/-! Same-level caller replay of complete source inspection. The proof recurses
over full evidence, retaining each actual head-query conversion. Selection is
reconstructed through source admission; projection domains and logical
substitution remain the existing authoritative producers. -/
namespace Glorious.Language

private def FullEqualBetween (program : Program) (context : Context) (level : Nat) (left right : Term) : Prop :=
  ∃ equal : DefinitionallyEqual program context left right, FullHeadInspectionEqualityAt program level equal

private def FullReducedBetween (program : Program) (context : Context) (level : Nat) (left right : Term) : Prop :=
  ∃ reduced : DefinitionalReduction program context left right, FullHeadInspectionReductionAt program level reduced

private theorem FullEqualBetween.reflexive (program : Program) (context : Context) (level : Nat) (term : Term) :
    FullEqualBetween program context level term term := ⟨.refl,.refl⟩

private theorem FullEqualBetween.congr {program : Program} {context : Context} {level : Nat} {left right : Term}
    (same : SameHead left right) (children : ListRel (FullEqualBetween program context level) left.children right.children) :
    FullEqualBetween program context level left right := by
  classical
  let equal := fun index first second (firstAt : left.children[index]? = some first)
      (secondAt : right.children[index]? = some second) => Classical.choose (children.at firstAt secondAt)
  exact ⟨.congrChildren same equal,.congrChildren (same := same) (children := equal)
    (fun _ _ _ firstAt secondAt => Classical.choose_spec (children.at firstAt secondAt))⟩

private theorem FullReducedBetween.reflexive (program : Program) (context : Context) (level : Nat) (term : Term) :
    FullReducedBetween program context level term term := ⟨.refl,.refl⟩

private theorem FullReducedBetween.congr {program : Program} {context : Context} {level : Nat} {left right : Term}
    (same : SameHead left right) (children : ListRel (FullReducedBetween program context level) left.children right.children) :
    FullReducedBetween program context level left right := by
  classical
  let reduced := fun index first second (firstAt : left.children[index]? = some first)
      (secondAt : right.children[index]? = some second) => Classical.choose (children.at firstAt secondAt)
  exact ⟨.congrChildren same reduced,.congrChildren (same := same) (children := reduced)
    (fun _ _ _ firstAt secondAt => Classical.choose_spec (children.at firstAt secondAt))⟩

private theorem SelectsImpl.map_full_query {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {trait : DeclId} {arguments : List Term} {negative : Bool}
    {implementation : ImplDefinition} {substitution : Substitution} {level : Nat}
    (selected : SelectsImpl program source trait arguments negative implementation substitution)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (outer : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute outer) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (assumptions : ∀ requirement ∈ source.assumptions, EntailsSubstitution program target outer requirement)
    (queries : ∀ (index : Nat) first second,
      (implementation.arguments.map (Term.substitute substitution))[index]? = some first → arguments[index]? = some second →
      FullEqualBetween program target level (SubstitutionAtomModel.term outer first) (SubstitutionAtomModel.term outer second)) :
    ∃ (_next : SelectsImpl program target trait (arguments.map (SubstitutionAtomModel.term outer)) negative implementation
        (substitution.map (fun entry => (entry.1,SubstitutionAtomModel.term outer entry.2))))
      (query : ∀ (index : Nat) first second,
        (implementation.arguments.map (Term.substitute (substitution.map (fun entry => (entry.1,SubstitutionAtomModel.term outer entry.2)))))[index]? = some first →
        (arguments.map (SubstitutionAtomModel.term outer))[index]? = some second → DefinitionallyEqual program target first second),
      ∀ (index : Nat) first second firstAt secondAt, FullHeadInspectionEqualityAt program level (query index first second firstAt secondAt) := by
  classical
  let map := SubstitutionAtomModel.term outer
  let mapSub := fun (substitution : Substitution) => substitution.map (fun entry => (entry.1,map entry.2))
  have shape := SubstitutionAtomModel.shape outer
  have mapKinds : ∀ term, (map term).kind = term.kind := SubstitutionAtomModel.kind outer
  have mappedKind {term : Term} {kind : Kind} (typed : Kinding program source term kind) :
      Kinding program target (map term) kind := by
    change Kinding program target (SubstitutionAtomModel.term outer term) kind
    rw [SubstitutionAtomModel.kinded_eq typed outer parameters]
    exact typed.substitute outer parameters levels regions brands
  have declared := selected.declaration
  obtain ⟨values,instantiated,typed⟩ := selected.instantiates
  have nextInst := instantiated.map_values map (fun term _ => mapKinds term)
  have nextKinded : ∀ value ∈ values.map map, Kinding program target value value.kind := by
    intro value member
    obtain ⟨term,present,rfl⟩ := List.mem_map.mp member
    simpa only [mapKinds] using mappedKind (typed term present)
  obtain ⟨_,_,_,_,_,_,_,signature,_⟩ := (valid.2.2.2.2.1 _ declared).2.1
  obtain ⟨_,_,_,_,headKinded,_,_⟩ := signature
  have specialized : (implementation.arguments.map (Term.substitute substitution)).map map =
      implementation.arguments.map (Term.substitute (mapSub substitution)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro term member
    exact (headKinded term member).1.map_instantiated_values instantiated map shape (SubstitutionAtomModel.fixed outer term)
  have lengths : (implementation.arguments.map (Term.substitute substitution)).length = arguments.length := by
    cases selected with
    | selected _ _ _ matched _ =>
      cases matched with
      | inferred _ _ graph lengths _ _ => simpa only [List.length_map] using graph.length_eq.trans lengths
  have mappedQueries : ListRel (FullEqualBetween program target level)
      (implementation.arguments.map (Term.substitute (mapSub substitution))) (arguments.map map) := by
    rw [← specialized]
    exact ListRel.of_at (by simpa only [List.length_map] using lengths) (AtomHomomorphism.list_at queries)
  have predicates := (valid.2.2.2.2.1 _ declared).2.2
  have nextRequirements : ∀ requirement ∈ implementation.requirements,
      EntailsSubstitution program target (mapSub substitution) requirement := by
    intro requirement member
    have requirements : EntailsSubstitution program source substitution requirement := by
      cases selected with
      | selected _ _ _ _ requirements => exact requirements requirement member
    rw [show mapSub substitution = substitution.map (fun entry => (entry.1,entry.2.substitute outer)) from
      instantiated.guarded_substitution_table typed outer parameters]
    exact requirements.substitute_values valid sourceKinded targetKinded (predicates requirement member) instantiated typed
      outer parameters (Nat.zero_le _) (fun _ absent => False.elim (List.not_mem_nil absent))
      (fun _ absent => False.elim (List.not_mem_nil absent)) levels regions brands assumptions
  have next := SelectsImpl.of_admitted_head valid declared targetKinded nextInst nextKinded
    (mappedQueries.imp (fun _ _ query => query.choose)) nextRequirements
  cases selected with
  | selected _ traitIs negativeIs _ _ =>
    rw [traitIs,negativeIs] at next
    exact ⟨next,(fun _ _ _ firstAt secondAt => Classical.choose (mappedQueries.at firstAt secondAt)),
      (fun _ _ _ firstAt secondAt => Classical.choose_spec (mappedQueries.at firstAt secondAt))⟩

/-- Full caller transport recurses through actual finite query certificates.
Its result remains at the original complete source-inspection level. -/
theorem FullHeadInspectionReductionAt.map_substitute {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {left right : Term} {reduced : DefinitionalReduction program source left right}
    {level : Nat} (certificate : FullHeadInspectionReductionAt program level reduced)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (outer : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute outer) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (assumptions : ∀ requirement ∈ source.assumptions, EntailsSubstitution program target outer requirement) :
    ∃ mapped : DefinitionalReduction program target (SubstitutionAtomModel.term outer left) (SubstitutionAtomModel.term outer right),
      FullHeadInspectionReductionAt program level mapped := by
  let map := SubstitutionAtomModel.term outer
  let mapSub := fun (substitution : Substitution) => substitution.map (fun entry => (entry.1,map entry.2))
  have shape : AtomHomomorphism map := SubstitutionAtomModel.shape outer
  have mapKinds : ∀ term, (map term).kind = term.kind := SubstitutionAtomModel.kind outer
  have transported : source = source → FullReducedBetween program target level (map left) (map right) := by
    apply FullHeadInspectionReductionAt.rec
      (motive_1 := fun _ _ _ => True)
      (motive_2 := fun _ _ _ _ => True)
      (motive_3 := fun level context left right _ _ => context = source →
        ∃ mapped : DefinitionalStep program target (map left) (map right), FullHeadInspectionStepAt program level mapped)
      (motive_4 := fun level context left right _ _ => context = source → FullEqualBetween program target level (map left) (map right))
      (motive_5 := fun level context left right _ _ => context = source → FullReducedBetween program target level (map left) (map right))
      <;> try assumption
    all_goals intros
    all_goals try exact True.intro
    case alias _ _ id _ arguments _ value found instantiated kinded substituted sameContext =>
      cases sameContext
      have mapped := (DefinitionalStep.alias found instantiated kinded substituted).map_substitute
        valid sourceKinded targetKinded outer parameters levels regions brands assumptions
      change DefinitionalStep program target (map (.alias id arguments)) (map value) at mapped
      rw [shape (.alias _ _)] at mapped
      rw [shape (.alias _ _)]
      cases mapped with
      | alias nextFound nextInst nextKinds nextGraph =>
        exact ⟨.alias nextFound nextInst nextKinds nextGraph,
          .alias (found := nextFound) (instantiated := nextInst) (kinded := nextKinds) (substituted := nextGraph)⟩
    case projection =>
      rename_i sourceLevel bound context trait member owners items associated ownerSub itemSub implementation implSub body value
        domain selected present graph _ inspected below _ _ queryIH sameContext
      cases sameContext
      have nextDomain := domain.map_substitute valid sourceKinded targetKinded outer parameters levels regions brands assumptions
      obtain ⟨nextSelected,nextQuery,nextCertificates⟩ := selected.map_full_query valid sourceKinded targetKinded outer
        parameters levels regions brands assumptions (fun index first second firstAt secondAt => queryIH index first second firstAt secondAt rfl)
      obtain ⟨values,instantiated,_⟩ := selected.instantiates
      cases domain with
      | valid _ _ associatedFound _ _ itemInst _ _ _ =>
        obtain ⟨unique,_,bodyKinded⟩ := valid.override_body selected.declaration associatedFound present
        have nextGraph := graph.map_instantiated bodyKinded (instantiated.append itemInst unique) map shape
          (SubstitutionAtomModel.fixed outer _) mapKinds
        simp only [List.map_append] at nextGraph
        rw [shape (.projection _ _ _ _ _)]
        exact ⟨.projection nextDomain nextSelected present nextGraph,
          .projection (domain := nextDomain) (selected := nextSelected) (present := present) (substituted := nextGraph)
            (query := nextQuery) inspected below nextCertificates⟩
    case defaultProjection =>
      rename_i sourceLevel bound context trait member owners items associated ownerSub itemSub implementation implSub body value
        domain selected absent default graph _ inspected below _ _ queryIH sameContext
      cases sameContext
      have nextDomain := domain.map_substitute valid sourceKinded targetKinded outer parameters levels regions brands assumptions
      obtain ⟨nextSelected,nextQuery,nextCertificates⟩ := selected.map_full_query valid sourceKinded targetKinded outer
        parameters levels regions brands assumptions (fun index first second firstAt secondAt => queryIH index first second firstAt secondAt rfl)
      cases domain with
      | valid traitFound _ associatedFound owner ownerInst itemInst _ _ _ =>
        obtain ⟨unique,bodyKinded⟩ := valid.default_body traitFound associatedFound owner default
        have nextGraph := graph.map_instantiated bodyKinded (ownerInst.append itemInst unique) map shape
          (SubstitutionAtomModel.fixed outer _) mapKinds
        simp only [List.map_append] at nextGraph
        rw [shape (.projection _ _ _ _ _)]
        exact ⟨.defaultProjection nextDomain nextSelected absent default nextGraph,
          .defaultProjection (domain := nextDomain) (selected := nextSelected) (absent := absent) (default := default)
            (substituted := nextGraph) (query := nextQuery) inspected below nextCertificates⟩
    all_goals try {
      rename_i sameContext
      cases sameContext
      exact ⟨.refl,.refl⟩ }
    all_goals try {
      rename_i _ _ rootIH sameContext
      cases sameContext
      obtain ⟨mapped,next⟩ := rootIH rfl
      exact ⟨.step mapped,.step (stepped := mapped) next⟩ }
    all_goals try {
      rename_i _ firstIH secondIH sameContext
      cases sameContext
      obtain ⟨first,firstCertificate⟩ := firstIH rfl
      obtain ⟨second,secondCertificate⟩ := secondIH rfl
      exact ⟨.trans first second,.trans (first := first) (second := second) firstCertificate secondCertificate⟩ }
    all_goals try {
      rename_i level context left right same _ _ children sameContext
      cases sameContext
      exact shape.congr_relation (FullEqualBetween.reflexive program target level) FullEqualBetween.congr same
        (ListRel.of_at same.children_length (fun index first second firstAt secondAt => children index first second firstAt secondAt rfl)) }
    all_goals try {
      rename_i level context left right same _ _ children sameContext
      cases sameContext
      exact shape.congr_relation (FullReducedBetween.reflexive program target level) FullReducedBetween.congr same
        (ListRel.of_at same.children_length (fun index first second firstAt secondAt => children index first second firstAt secondAt rfl)) }
    all_goals try {
      rename_i _ context left right equivalent sameContext
      cases sameContext
      exact ⟨.row (equivalent.map_atoms map shape),.row (equivalent := equivalent.map_atoms map shape)⟩ }
    case symm _ _ _ _ _ _ ih sameContext =>
      cases sameContext
      obtain ⟨equal,certificate⟩ := ih rfl
      exact ⟨equal.symm,.symm (equal := equal) certificate⟩
  exact transported rfl

theorem FullHeadInspectionReductionAt.instantiate {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {left right : Term} {kind : Kind}
    {reduced : DefinitionalReduction program source left right} {level : Nat}
    (certificate : FullHeadInspectionReductionAt program level reduced)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (kinded : Kinding program source left kind) {values : List Term} {substitution : Substitution}
    (instantiated : Instantiates source.binders values substitution)
    (valuesKinded : ∀ value ∈ values, Kinding program target value value.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (assumptions : ∀ requirement ∈ source.assumptions, EntailsSubstitution program target substitution requirement) :
    ∃ mapped : DefinitionalReduction program target (left.substitute substitution) (right.substitute substitution),
      FullHeadInspectionReductionAt program level mapped := by
  have parameters := instantiated.kinding_parameters valuesKinded
  have transported := certificate.map_substitute valid sourceKinded targetKinded substitution parameters levels regions brands assumptions
  rw [SubstitutionAtomModel.kinded_eq kinded substitution parameters,
    SubstitutionAtomModel.kinded_eq (reduced.kinding valid kinded) substitution parameters] at transported
  exact transported

end Glorious.Language
