import GloriousLanguage.GeneralAtomTransport

/-! Fresh specialization is the identity-parameter instance of the general
current-valuation transport. Its established API keeps actual unchanged
caller preimages, while the shared proof also permits existential preimages. -/
namespace Glorious.Language

theorem Entails.interpret_fresh {program : Program} (valid : ProgramWellFormed program)
    {source target : Context} {constraint : Constraint} (held : Entails program source constraint)
    (specialization : FreshAtomSpecialization) (admitted : specialization.Admitted program target)
    (targetKinded : ∀ requirement ∈ target.assumptions, ConstraintKinded program target requirement)
    (forward : ∀ term kind, Kinding program source term kind → Kinding program target (specialization.term term) kind)
    (pullback : ∀ term kind, Kinding program target term kind → Kinding program source term kind ∧ specialization.term term = term)
    (assumptions : ∀ requirement ∈ source.assumptions, FreshAtomInterpretation.Holds specialization program target requirement) :
    FreshAtomInterpretation.Holds specialization program target constraint := by
  exact Entails.interpret_atoms valid held specialization admitted targetKinded
    LogicalQuotient.canonical specialization.term specialization.shape (specialization.source_fixed valid)
    specialization.kind (FreshAtomInterpretation.eval_canonical specialization) forward
    (fun term kind typed => ⟨term,(pullback term kind typed).1,(pullback term kind typed).2⟩) assumptions

end Glorious.Language
