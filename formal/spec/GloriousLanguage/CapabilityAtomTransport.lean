import GloriousLanguage.AtomInstantiation
import GloriousLanguage.CapabilityTransport

/-! Capability equations commute with arbitrary kind-preserving atom
replacement. Source declaration atoms stay fixed, parameters are opened by
their existing table, and noninjective images use the same greatest-witness
coinduction as the parameter-substitution theorem. -/
namespace Glorious.Language

theorem CapabilityEquation.map_atoms {program : Program} (valid : ProgramWellFormed program)
    {first last : Term → Option Principal} {type : Term} {principal : Principal}
    (equation : CapabilityEquation program first type principal) (map : Term → Term)
    (shape : AtomHomomorphism map) (fixed : program.AtomsFixed map)
    (kinds : ∀ term, (map term).kind = term.kind)
    (related : ∀ term claimed, first term = some claimed →
      ∃ result, last (map term) = some result ∧ claimed.Restricts result) :
    ∃ result, CapabilityEquation program last (map type) result ∧ principal.Restricts result := by
  have fields {terms : List Term} {principals : List Principal}
      (assigned : ListRel (fun term claimed => first term = some claimed) terms principals) :
      ∃ results, ListRel (fun term claimed => last term = some claimed) (terms.map map) results ∧
        ListRel Principal.Restricts principals results := by
    induction assigned with
    | nil => exact ⟨[],.nil,.nil⟩
    | cons found _ ih =>
      obtain ⟨result,selected,ordered⟩ := related _ _ found
      obtain ⟨results,rest,orders⟩ := ih
      exact ⟨result :: results,.cons selected rest,.cons ordered orders⟩
  have literal : ∀ value, map (.constant value) = .constant value := fun value => shape (.constant value)
  have markerLiteral : ∀ value, map (.principal value) = .principal value := fun value => shape (.principal value)
  cases equation with
  | unit => rw [shape]; exact ⟨_,.unit,.refl _⟩
  | bottom => rw [shape]; exact ⟨_,.bottom,.refl _⟩
  | scalar => rw [shape]; exact ⟨_,.scalar,.refl _⟩
  | raw => rw [shape]; exact ⟨_,.raw,.refl _⟩
  | shared => rw [shape]; exact ⟨_,.shared,.refl _⟩
  | unique => rw [shape]; exact ⟨_,.unique,.refl _⟩
  | label => rw [shape]; exact ⟨_,.label,.refl _⟩
  | tuple assigned =>
    rw [shape]
    obtain ⟨results,assigned,ordered⟩ := fields assigned
    exact ⟨_,.tuple assigned,Principal.fields_monotone ordered⟩
  | emptyArray => rw [shape]; simp only [Term.mapChildren,literal]; exact ⟨_,.emptyArray,.refl _⟩
  | array positive assigned =>
    rw [shape]
    simp only [Term.mapChildren,literal]
    obtain ⟨result,selected,ordered⟩ := related _ _ assigned
    exact ⟨result,.array positive selected,ordered⟩
  | alias found instantiated substituted assigned =>
    rw [shape]
    have template := fixed _ (List.mem_of_find?_eq_some (Program.alias_lookup found))
    have graph := substituted.map_instantiated (valid.alias_body found) instantiated map shape
      (template _ (by simp [Definition.terms])) kinds
    obtain ⟨result,selected,ordered⟩ := related _ _ assigned
    exact ⟨result,.alias found (instantiated.map_values map (fun term _ => kinds term)) graph selected,ordered⟩
  | @nominal id data arguments inner residentTypes residentPrincipals sourceMarker structuralPrincipal resultPrincipal
      found instantiated substituted assigned marked meets restricted drops =>
    rw [shape]
    have templates := fixed _ (List.mem_of_find?_eq_some (Program.data_lookup found))
    have mapped := instantiated.map_values map (fun term _ => kinds term)
    have graph := substituted.map_instantiated (valid.data_field_types found) instantiated map shape
      (fun term member => templates term (by
        simp only [Definition.terms,List.mem_append]
        exact Or.inl (Or.inl (Or.inl member)))) kinds
    obtain ⟨results,assigned,ordered⟩ := fields assigned
    have marker : ∃ changed,
        (data.quantitySource = none ∧ changed = .duplicable ∨
          ∃ sourceValue value, data.quantitySource = some sourceValue ∧
            Substitutes (inner.map (fun entry => (entry.1,map entry.2))) sourceValue value ∧
            (value = .principal changed ∨ value.kind = .type ∧ last value = some changed)) ∧
        sourceMarker.Restricts changed := by
      rcases marked with none | ⟨sourceValue,value,sourceAt,substituted,marked⟩
      · obtain ⟨none,rfl⟩ := none
        exact ⟨.duplicable,Or.inl ⟨none,rfl⟩,.refl _⟩
      · have graph := substituted.map_instantiated (valid.quantity_source found sourceAt).1 instantiated map shape
          (templates _ (by
            simp only [Definition.terms,List.mem_append]
            exact Or.inl (Or.inl (Or.inr (by simp [sourceAt]))))) kinds
        rcases marked with valueMarker | ⟨typeKind,assigned⟩
        · exact ⟨_,Or.inr ⟨sourceValue,map value,sourceAt,graph,
            Or.inl (by rw [valueMarker,markerLiteral])⟩,.refl _⟩
        · obtain ⟨changed,selected,ordered⟩ := related value _ assigned
          exact ⟨changed,Or.inr ⟨sourceValue,map value,sourceAt,graph,
            Or.inr ⟨(kinds value).trans typeKind,selected⟩⟩,ordered⟩
    obtain ⟨marker,marked,markerOrder⟩ := marker
    have structural := Principal.meet_monotone (Principal.fields_monotone ordered) markerOrder
    rw [← meets] at structural
    rcases restricted with ⟨none,rfl⟩ | ⟨restriction,permitted⟩
    · refine ⟨_,.nominal found mapped graph assigned marked rfl (Or.inl ⟨none,rfl⟩) ?_,structural⟩
      intro dropped
      exact structural 0 (drops dropped)
    · exact ⟨_,.nominal found mapped graph assigned marked rfl
        (Or.inr ⟨restriction,permitted.trans structural⟩) drops,.refl _⟩
  | callable captured assigned =>
    rw [shape]
    obtain ⟨results,assigned,ordered⟩ := fields assigned
    exact ⟨_,.callable (captured.map_atoms valid map shape fixed kinds) assigned,Principal.fields_monotone ordered⟩
  | environment assigned =>
    rw [shape]
    obtain ⟨results,assigned,ordered⟩ := fields assigned
    exact ⟨_,.environment assigned,Principal.fields_monotone ordered⟩
  | available assigned =>
    rw [shape]
    obtain ⟨result,selected,ordered⟩ := related _ _ assigned
    rw [shape] at selected
    exact ⟨result,.available (by simpa only [Term.mapChildren] using selected),ordered⟩
  | bindings assigned =>
    rw [shape]
    obtain ⟨results,assigned,ordered⟩ := fields assigned
    exact ⟨_,.bindings assigned,Principal.fields_monotone ordered⟩
  | optionalContinuation => rw [shape]; exact ⟨_,.optionalContinuation,.refl _⟩
  | exactContinuation positive => rw [shape]; exact ⟨_,.exactContinuation positive,.refl _⟩

/-- The finite logical leaves are the only logical premises delegated to
the mutual interpretation proof. Recursive structural claims, including
merged image types, are closed by this general coinductive theorem. -/
theorem CapabilityEvidence.map_atoms_coinduction {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {assignment : Term → Option Principal} {type : Term} {principal : Principal}
    (found : assignment type = some principal) (map : Term → Term)
    (shape : AtomHomomorphism map) (fixed : program.AtomsFixed map)
    (kinds : ∀ term, (map term).kind = term.kind)
    (unfolded : ∀ term claimed, assignment term = some claimed → ∃ supported,
      claimed.Restricts supported ∧ (CapabilityEquation program assignment term supported ∨
        CapabilityEvidence program context (map term) supported)) :
    CapabilityEvidence program context (map type) principal := by
  apply CapabilityEvidence.map_coinduction (map := map) (domain := fun _ => True) True.intro found
    (fun term claimed _ => unfolded term claimed)
  intro targetAssignment related term supported _ equation
  obtain ⟨result,mapped,ordered⟩ := equation.map_atoms valid map shape fixed kinds
    (fun term claimed found => related term claimed True.intro found)
  exact ⟨result,ordered,mapped⟩

end Glorious.Language
