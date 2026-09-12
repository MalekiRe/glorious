import GloriousLanguage.GeneralAtomTransport
import GloriousLanguage.FreshSubstitutionModel

/-! General kind-preserving hygienic parameter cut. The existing logical
universe theorem supplies a fresh inspection universe; concrete atom
preimages discharge the contravariant domain of every nested universal.
The final result is the actual language substitution, not a proof model. -/
namespace Glorious.Language

/-- Logical evidence is preserved by every caller-kinded simultaneous
substitution, including noninjective and compound replacements. Source
requirements must be discharged by their actual caller instantiations.
No binder/scope back-inclusion, injectivity or quantifier transport oracle
is required. -/
theorem Entails.substitute {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {constraint : Constraint} (held : Entails program source constraint)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (typed : ConstraintKinded program source constraint) (substitution : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute substitution) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (assumptions : ∀ requirement ∈ source.assumptions, EntailsSubstitution program target substitution requirement) :
    Entails program target (constraint.substitute substitution) := by
  have raised := held.raiseUniverse valid sourceKinded typed (Nat.le_trans levels (Nat.le_succ _))
  apply (FreshSubstitutionModel.holds_iff_entails valid targetKinded typed substitution parameters levels regions brands).mp
  apply raised.interpret_atoms valid (FreshArgumentPreimage.specialization target)
    (FreshArgumentPreimage.admitted program target) targetKinded
    (FreshSubstitutionModel.current program target substitution) (FreshSubstitutionModel.term target substitution)
    (FreshSubstitutionModel.shape target substitution) (FreshSubstitutionModel.source_fixed valid target substitution)
    (FreshSubstitutionModel.kind target substitution) (FreshSubstitutionModel.evaluated program target substitution)
  · intro value kind admitted
    exact FreshSubstitutionModel.forward admitted substitution parameters (Nat.le_succ _) regions brands
  · intro value kind admitted
    exact FreshSubstitutionModel.preimages substitution (Nat.lt_succ_self _) admitted
  · intro requirement member
    exact (FreshSubstitutionModel.holds_iff_entails valid targetKinded (sourceKinded requirement member)
      substitution parameters levels regions brands).mpr (assumptions requirement member).actual_result

/-- The general cut also produces the authoritative hygienic substitution
judgment. Its graph is supplied by source predicate admission. -/
theorem Entails.substitutes {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {constraint : Constraint} (held : Entails program source constraint)
    (sourceKinded : ∀ requirement ∈ source.assumptions, ConstraintKinded program source requirement)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (typed : ConstraintKinded program source constraint) (substitution : Substitution)
    (parameters : ∀ binder ∈ source.binders,
      Kinding program target ((Term.parameter binder.id binder.kind).substitute substitution) binder.kind)
    (levels : source.universeLevel ≤ target.universeLevel)
    (regions : ∀ id ∈ source.scope.regions, id ∈ target.scope.regions)
    (brands : ∀ id ∈ source.scope.brands, id ∈ target.scope.brands)
    (assumptions : ∀ requirement ∈ source.assumptions, EntailsSubstitution program target substitution requirement) :
    EntailsSubstitution program target substitution constraint :=
  .instantiated (typed.substitutes substitution parameters levels regions brands).1
    (held.substitute valid sourceKinded targetKinded typed substitution parameters levels regions brands assumptions)

end Glorious.Language
