import GloriousLanguage.FreshArgumentPreimage
import GloriousLanguage.CurrentAtomInterpretation
import GloriousLanguage.SubstitutionAtomModel

/-! The parameter-cut model keeps caller terms fixed, interprets source
parameters simultaneously, and decodes fresh atoms into caller-only names.
Its semantic evaluation is derived from the shared term interpreter. -/
namespace Glorious.Language

open PredicateSemantics

namespace FreshSubstitutionModel

noncomputable def term (context : Context) (substitution : Substitution) : Term → Term :=
  (FreshArgumentPreimage.specialization context).term ∘ SubstitutionAtomModel.term substitution

theorem shape (context : Context) (substitution : Substitution) : AtomHomomorphism (term context substitution) :=
  (FreshArgumentPreimage.specialization context).shape.comp (SubstitutionAtomModel.shape substitution)

theorem kind (context : Context) (substitution : Substitution) (value : Term) :
    (term context substitution value).kind = value.kind := by
  unfold term Function.comp
  rw [FreshAtomSpecialization.kind,SubstitutionAtomModel.kind]

noncomputable def current (program : Program) (context : Context) (substitution : Substitution) :
    Valuation (LogicalQuotient.Class program context) :=
  fun id kind => LogicalQuotient.ofTerm (term context substitution (.parameter id kind))

theorem evaluated (program : Program) (context : Context) (substitution : Substitution) (value : Term) :
    (FreshAtomInterpretation.algebra (FreshArgumentPreimage.specialization context) program context).eval
      (current program context substitution) value = LogicalQuotient.ofTerm (term context substitution value) := by
  let algebra := FreshAtomInterpretation.algebra (FreshArgumentPreimage.specialization context) program context
  have interpreted := algebra.eval_parameter_map LogicalQuotient.canonical (SubstitutionAtomModel.term substitution)
    (fun _ notParameter => SubstitutionAtomModel.node substitution notParameter) value
  have valuation : (fun id kind => algebra.eval LogicalQuotient.canonical
      (SubstitutionAtomModel.term substitution (.parameter id kind))) = current program context substitution := by
    funext id kind
    rw [FreshAtomInterpretation.eval_canonical]
    rfl
  rw [valuation,FreshAtomInterpretation.eval_canonical] at interpreted
  exact interpreted.symm

theorem source_fixed {program : Program} (valid : ProgramWellFormed program)
    (context : Context) (substitution : Substitution) : program.AtomsFixed (term context substitution) := by
  intro declaration member value present atom occurs
  have unchanged := (SubstitutionAtomModel.fixed substitution value) atom occurs
  have freshFixed := (FreshArgumentPreimage.specialization context).source_fixed valid declaration member value present atom occurs
  cases atom <;> try exact True.intro
  all_goals change (FreshArgumentPreimage.specialization context).term (SubstitutionAtomModel.term substitution _) = _
  all_goals rw [unchanged]
  all_goals exact freshFixed

theorem forward {program : Program} {source target : Context} {value : Term} {kind : Kind}
    (typed : Kinding program source value kind) (substitution : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute substitution) binder.kind)
    (higher : target.universeLevel ≤ source.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    Kinding program target (term target substitution value) kind := by
  have opened : Kinding program { target with universeLevel := source.universeLevel }
      (value.substitute substitution) kind := typed.substitute substitution
    (fun binder member => (parameters binder member).raiseUniverse higher) (Nat.le_refl _) regions brands
  have specialized := opened.specializeFresh (FreshArgumentPreimage.specialization target)
    (FreshArgumentPreimage.admitted program target)
  rw [← SubstitutionAtomModel.kinded_eq typed substitution parameters] at specialized
  exact specialized

theorem preimages {program : Program} {source target : Context} (substitution : Substitution)
    (higher : target.universeLevel < source.universeLevel) {value : Term} {kind : Kind}
    (typed : Kinding program target value kind) :
    ∃ original, Kinding program source original kind ∧ term target substitution original = value := by
  obtain ⟨original,originalKinded,roundtrip,closed⟩ := FreshArgumentPreimage.preimage typed higher
  refine ⟨original,originalKinded,?_⟩
  unfold term Function.comp
  rw [(SubstitutionAtomModel.shape substitution).fixed_term original
    (fun id kind occurs => False.elim (closed id kind occurs)) (SubstitutionAtomModel.fixed substitution original)]
  exact roundtrip

/-- On every admitted source term, the proof-model totalization and fresh
decoding disappear. The result is exactly the language's raw simultaneous
substitution, with no normalization or altered source semantics. -/
theorem kinded_eq {program : Program} {source target : Context} {value : Term} {kind : Kind}
    (typed : Kinding program source value kind) (substitution : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute substitution) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    term target substitution value = value.substitute substitution := by
  unfold term Function.comp
  rw [SubstitutionAtomModel.kinded_eq typed substitution parameters]
  exact (FreshArgumentPreimage.specialization target).fixed rfl
    (typed.substitute substitution parameters levels regions brands)

/-- The model denotes exactly the admitted predicate's real hygienic
substitution. In particular, nested quantifiers still draw arguments from
the caller valuation, independently of the source parameter valuation. -/
theorem holds_iff_entails {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {constraint : Constraint}
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (typed : ConstraintKinded program source constraint) (substitution : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute substitution) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands) :
    FreshAtomInterpretation.HoldsAt (FreshArgumentPreimage.specialization target) program target
      (current program target substitution) constraint ↔ Entails program target (constraint.substitute substitution) := by
  apply Iff.trans _ (LogicalQuotient.holds_iff_entails valid targetKinded
    (typed.substitute substitution parameters levels regions brands))
  unfold FreshAtomInterpretation.HoldsAt LogicalQuotient.Holds
  rw [FreshAtomInterpretation.holds_fixed (FreshArgumentPreimage.specialization target) rfl constraint
    (typed.fresh_atoms_fixed _ levels),
    (LogicalQuotient.algebra program target).holds_substitute]
  apply (LogicalQuotient.algebra program target).holds_kinded_congr typed target LogicalQuotient.canonical
  intro binder member
  change LogicalQuotient.ofTerm (term target substitution (.parameter binder.id binder.kind)) = _
  rw [kinded_eq (Kinding.parameter member) substitution parameters levels regions brands]
  cases found : substitution.get binder.id <;>
    simp only [TermAlgebra.substituteValuation,found,Option.map,Option.getD,Term.substitute,
      LogicalQuotient.eval_canonical,LogicalQuotient.canonical]

end FreshSubstitutionModel
end Glorious.Language
