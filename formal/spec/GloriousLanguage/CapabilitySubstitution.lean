import GloriousLanguage.SubstitutionAtomModel
import GloriousLanguage.CapabilityAtomTransport

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
    (_levels : source.universeLevel ≤ target.universeLevel)
    (_regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (_brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (related : ∀ term claimed, Kinding program source term .type → first term = some claimed →
      ∃ result, last (term.substitute outer) = some result ∧ claimed.Restricts result) :
    ∃ result, CapabilityEquation program last (type.substitute outer) result ∧ principal.Restricts result := by
  classical
  have restricted := equation.kinding_restrict valid kinded
  obtain ⟨result,mapped,ordered⟩ := restricted.map_atoms (last := last) valid (SubstitutionAtomModel.term outer)
    (SubstitutionAtomModel.shape outer)
    (fun _ _ term _ => SubstitutionAtomModel.fixed outer term) (SubstitutionAtomModel.kind outer) (by
      intro term claimed found
      have admitted : Kinding program source term .type := by
        by_cases admitted : Kinding program source term .type
        · exact admitted
        · simp only [kindedCapabilityAssignment,if_neg admitted] at found
          cases found
      have original : first term = some claimed := by
        simpa only [kindedCapabilityAssignment,if_pos admitted] using found
      obtain ⟨result,selected,ordered⟩ := related term claimed admitted original
      refine ⟨result,?_,ordered⟩
      rw [SubstitutionAtomModel.kinded_eq admitted outer parameters]
      exact selected)
  exact ⟨result,by
    simpa only [SubstitutionAtomModel.kinded_eq kinded outer parameters] using mapped,ordered⟩

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
