import GloriousLanguage.InstantiationComposition
import GloriousLanguage.CapabilityTransport

/-! Lawful source substitution preserves the actual structural capability
equation. This is the local equation component of the shared logical cut;
the coinductive proposal may merge distinct source types after substitution. -/
namespace Glorious.Language

theorem CapabilityEquation.substitute {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {first last : Term → Option Principal} {type : Term} {principal : Principal}
    (equation : CapabilityEquation program first type principal) (kinded : Kinding program source type .type)
    (outer : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute outer) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (related : ∀ term claimed, Kinding program source term .type → first term = some claimed →
      ∃ result, last (term.substitute outer) = some result ∧ claimed.Restricts result) :
    ∃ result, CapabilityEquation program last (type.substitute outer) result ∧ principal.Restricts result := by
  have fields {terms : List Term} {principals : List Principal}
      (kinded : ∀ term ∈ terms, Kinding program source term .type)
      (assigned : ListRel (fun term claimed => first term = some claimed) terms principals) :
      ∃ results, ListRel (fun term claimed => last term = some claimed) (terms.map (Term.substitute outer)) results ∧
        ListRel Principal.Restricts principals results := by
    induction assigned with
    | nil => exact ⟨[],.nil,.nil⟩
    | cons found _ ih =>
      obtain ⟨result,selected,ordered⟩ := related _ _ (kinded _ List.mem_cons_self) found
      obtain ⟨results,rest,orders⟩ := ih (fun term present => kinded term (List.mem_cons_of_mem _ present))
      exact ⟨result :: results,.cons selected rest,.cons ordered orders⟩
  have arguments {terms : List Term}
      (kinded : ∀ term ∈ terms, Kinding program source term term.kind) :
      ∀ term ∈ terms, Kinding program target (term.substitute outer) term.kind :=
    fun term member => (kinded term member).substitute outer parameters levels regions brands
  cases equation with
  | unit => simp only [Term.substitute]; exact ⟨_,.unit,.refl _⟩
  | bottom => simp only [Term.substitute]; exact ⟨_,.bottom,.refl _⟩
  | scalar => simp only [Term.substitute]; exact ⟨_,.scalar,.refl _⟩
  | raw => simp only [Term.substitute]; exact ⟨_,.raw,.refl _⟩
  | shared => simp only [Term.substitute]; exact ⟨_,.shared,.refl _⟩
  | unique => simp only [Term.substitute]; exact ⟨_,.unique,.refl _⟩
  | label => simp only [Term.substitute]; exact ⟨_,.label,.refl _⟩
  | tuple assigned =>
    simp only [Term.substitute]
    cases kinded with
    | tuple kinded =>
      obtain ⟨results,assigned,ordered⟩ := fields kinded assigned
      exact ⟨_,.tuple assigned,Principal.fields_monotone ordered⟩
  | emptyArray => simp only [Term.substitute]; exact ⟨_,.emptyArray,.refl _⟩
  | array positive assigned =>
    simp only [Term.substitute]
    cases kinded with
    | array element _ =>
      obtain ⟨result,selected,ordered⟩ := related _ _ element assigned
      exact ⟨result,.array positive selected,ordered⟩
  | alias found instantiated substituted assigned =>
    simp only [Term.substitute]
    cases kinded with
    | alias actual _ argumentKinds =>
      obtain rfl := Option.some.inj (found.symm.trans actual)
      obtain ⟨mapped,_,graph⟩ := (valid.alias_body actual).instantiate_substitute instantiated outer
        (arguments argumentKinds) (Nat.zero_le _)
        (fun _ present => False.elim (List.not_mem_nil present))
        (fun _ present => False.elim (List.not_mem_nil present))
      have dependency := (valid.alias_specialization actual instantiated argumentKinds).1
      rw [← substituted.2.1] at dependency graph
      obtain ⟨result,selected,ordered⟩ := related _ _ dependency assigned
      exact ⟨result,.alias actual mapped graph selected,ordered⟩
  | @nominal id data ownerArguments inner residentTypes residentPrincipals sourceMarker structuralPrincipal resultPrincipal
      found instantiated substituted assigned marked meets restricted drops =>
    simp only [Term.substitute]
    cases kinded with
    | @nominal _ actualData _ _ actual _ argumentKinds =>
      have same : data = actualData := Option.some.inj (found.symm.trans actual)
      subst actualData
      have mapped := instantiated.substitute_values argumentKinds outer parameters levels regions brands
      have graph := substituted.instantiate_substitute (valid.data_field_types actual) instantiated outer
        (arguments argumentKinds) (Nat.zero_le _)
        (fun _ present => False.elim (List.not_mem_nil present))
        (fun _ present => False.elim (List.not_mem_nil present))
      obtain ⟨results,assigned,ordered⟩ := fields
        (valid.data_fields_specialization actual instantiated argumentKinds substituted) assigned
      have marker : ∃ changed,
          (data.quantitySource = none ∧ changed = .duplicable ∨
            ∃ sourceValue value, data.quantitySource = some sourceValue ∧
              Substitutes (inner.map (fun entry => (entry.1,entry.2.substitute outer))) sourceValue value ∧
              (value = .principal changed ∨ value.kind = .type ∧ last value = some changed)) ∧
          sourceMarker.Restricts changed := by
        rcases marked with none | ⟨sourceValue,value,sourceAt,substituted,marked⟩
        · obtain ⟨none,rfl⟩ := none
          exact ⟨.duplicable,Or.inl ⟨none,rfl⟩,.refl _⟩
        · obtain ⟨sourceKind,_⟩ := valid.quantity_source actual sourceAt
          have graph := (sourceKind.instantiate_substitute instantiated outer (arguments argumentKinds) (Nat.zero_le _)
            (fun _ present => False.elim (List.not_mem_nil present))
            (fun _ present => False.elim (List.not_mem_nil present))).2.2
          rw [← substituted.2.1] at graph
          rcases marked with literal | ⟨typeKind,assigned⟩
          · refine ⟨_,Or.inr ⟨sourceValue,value.substitute outer,sourceAt,graph,Or.inl ?_⟩,.refl _⟩
            simp only [literal,Term.substitute]
          · have dependency := (valid.quantity_source_specialization actual sourceAt instantiated argumentKinds substituted).1
            rw [typeKind] at dependency
            obtain ⟨changed,selected,ordered⟩ := related value _ dependency assigned
            exact ⟨changed,Or.inr ⟨sourceValue,value.substitute outer,sourceAt,graph,
              Or.inr ⟨(dependency.substitute outer parameters levels regions brands).term_kind,selected⟩⟩,ordered⟩
      obtain ⟨marker,marked,markerOrder⟩ := marker
      have structural := Principal.meet_monotone (Principal.fields_monotone ordered) markerOrder
      rw [← meets] at structural
      rcases restricted with ⟨none,rfl⟩ | ⟨restriction,permitted⟩
      · refine ⟨_,.nominal actual mapped graph assigned marked rfl (Or.inl ⟨none,rfl⟩) ?_,structural⟩
        intro dropped
        exact structural 0 (drops dropped)
      · exact ⟨_,.nominal actual mapped graph assigned marked rfl
          (Or.inr ⟨restriction,permitted.trans structural⟩) drops,.refl _⟩
  | callable captured assigned =>
    simp only [Term.substitute]
    obtain ⟨results,assigned,ordered⟩ := fields (captured.kinding valid kinded) assigned
    exact ⟨_,.callable (captured.substitute valid kinded outer parameters levels regions brands) assigned,
      Principal.fields_monotone ordered⟩
  | environment assigned =>
    simp only [Term.substitute]
    cases kinded with
    | environment _ _ residents =>
      obtain ⟨results,assigned,ordered⟩ := fields residents assigned
      exact ⟨_,.environment assigned,Principal.fields_monotone ordered⟩
  | available assigned =>
    simp only [Term.substitute]
    cases kinded with
    | available brand region residents =>
      obtain ⟨result,selected,ordered⟩ := related _ _ (.environment brand region residents) assigned
      exact ⟨result,.available (by simpa only [Term.substitute] using selected),ordered⟩
  | bindings assigned =>
    simp only [Term.substitute]
    cases kinded with
    | bindings _ _ residents =>
      obtain ⟨results,assigned,ordered⟩ := fields residents assigned
      exact ⟨_,.bindings assigned,Principal.fields_monotone ordered⟩
  | optionalContinuation => simp only [Term.substitute]; exact ⟨_,.optionalContinuation,.refl _⟩
  | exactContinuation positive => simp only [Term.substitute]; exact ⟨_,.exactContinuation positive,.refl _⟩

/-- The complete coinductive structural component commutes with a lawful
source substitution, including recursive and noninjective type instances.
Only its actual finite logical leaves are delegated to the mutual cut. -/
theorem CapabilityEvidence.substitute_coinduction {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {assignment : Term → Option Principal} {type : Term} {principal : Principal}
    (kinded : Kinding program source type .type) (found : assignment type = some principal)
    (outer : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute outer) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (unfolded : ∀ term claimed, Kinding program source term .type → assignment term = some claimed → ∃ supported,
      claimed.Restricts supported ∧
        (CapabilityEquation program assignment term supported ∨
          CapabilityEvidence program target (term.substitute outer) supported)) :
    CapabilityEvidence program target (type.substitute outer) principal := by
  apply CapabilityEvidence.map_coinduction (map := Term.substitute outer)
    (domain := fun term => Kinding program source term .type) kinded found unfolded
  intro targetAssignment related term supported admitted equation
  obtain ⟨result,mapped,ordered⟩ := equation.substitute valid admitted outer parameters levels regions brands related
  exact ⟨result,ordered,mapped⟩

end Glorious.Language
