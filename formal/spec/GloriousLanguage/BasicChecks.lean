import GloriousLanguage.Storage
import GloriousLanguage.SourceRules
import GloriousLanguage.CapabilityInversion

/-! Checked boundary regressions, independent of the still-being-repaired
execution aggregate. The default aggregate imports this module as well. -/
namespace Glorious.Language.BasicChecks

example : integerAnd (-1) 42 = 42 := by decide
example : integerAnd (-6) (-4) = -8 := by decide
example : integerOr (-6) 3 = -5 := by decide
example : integerXor (-1) 42 = -43 := by decide
example : integerOperation .divide (-7) 3 = some (-2) := by decide
example : integerOperation .remainder (-7) 3 = some (-1) := by decide

example : (Term.tuple [.parameter 4 .type,.unit]).substitute [(4,.scalar (.integer true (.fixed 64)))] =
    .tuple [.scalar (.integer true (.fixed 64)),.unit] := by
  simp [Term.substitute, Table.get]

example : ¬ Substitutes [(4,.staticRegion)] (.parameter 4 .type) .staticRegion := by
  intro proof
  cases proof.1

example {program : Program} (valid : ProgramWellFormed program) {id kind principal} :
    ¬ PrincipalOf program (.parameter id kind) principal := PrincipalOf.not_parameter valid

example {program : Program} :
    PrincipalOf program (.reference .shared (.rigid 3 .region 0) (.parameter 4 .type)) .duplicable :=
  PrincipalOf.shared program _ _

example {program : Program} (valid : ProgramWellFormed program) :
    PrincipalOf program (.reference .unique (.rigid 3 .region 0) (.parameter 4 .type)) .affine :=
  PrincipalOf.unique program valid _ _

private def unitValue : Value := .resident 1 .unit .unit true []
private def holed : Value := .resident 0 (.tuple [.unit,.unit]) .tuple true [none,some unitValue]

example : holed.replace [0] (some unitValue) = some (holed.withFields [some unitValue,some unitValue]) := by rfl
example : holed.replace [2] (some unitValue) = none := by rfl

example {program : Program} {module nameSpace name left right}
    (a : Resolves program module nameSpace name left) (b : Resolves program module nameSpace name right) :
    left.id = right.id := resolution_identity_unique a b

example : Source.DeclarationsSyntax [] [] := .nil
example : Source.TypeSyntax [.symbol "(",.symbol ")"] .unit := .unit
example : ¬ Source.UnicodeScalar 0xd800 := by simp [Source.UnicodeScalar]
example : Source.digitsValue 16 [15,15] = 255 := by decide

end Glorious.Language.BasicChecks
