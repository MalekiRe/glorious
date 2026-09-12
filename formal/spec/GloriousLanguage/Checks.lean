import GloriousLanguage.Specification
import GloriousLanguage.BasicChecks
import GloriousLanguage.ExecutionChecks
import GloriousLanguage.ControlChecks
import GloriousLanguage.BorrowChecks
import GloriousLanguage.BindingChecks
import GloriousLanguage.SourceChecks
import GloriousLanguage.RepresentationChecks

/-! Foundational regression propositions. These are checked by the default
build; they are not a claim that all language metatheory has been proved. -/
namespace Glorious.Language.Checks

example : Quantity.SurfaceResumption ⟨0,some 1⟩ := by left; rfl
example : Quantity.SurfaceResumption ⟨2,some 2⟩ := by right; exact ⟨2,by decide,by decide,rfl⟩
example : ¬ (Quantity.mk 2 (some 2)).Contains 1 := by simp [Quantity.Contains]
example : ¬ Quantity.SurfaceResumption ⟨0,none⟩ := by
  intro permitted
  rcases permitted with equal | ⟨n,_,_,equal⟩ <;> cases equal

example : Principal.affine.Restricts .duplicable := by
  simp [Principal.Restricts, Principal.Permits]
example : ¬ Principal.duplicable.Restricts .affine := by
  intro restriction
  have impossible := restriction 2 trivial
  simp [Principal.Permits] at impossible
example : ¬ Principal.exact.MayDiscard := Principal.exact_not_discardable

private def unitValue : Value := .resident 1 .unit .unit true []
private def holed : Value := .resident 0 (.tuple [.unit]) .tuple true [none]

example : holed.replace [0] (some unitValue) = some (holed.withFields [some unitValue]) := by rfl
example : ¬ holed.Initialized := by
  intro initialized
  have complete := (initialized [] holed .root).2 none (by simp [holed, Value.fields])
  cases complete

example {before after : World} {id loan}
    (found : before.loans.get id = some loan) (hole : ¬ before.Initialized loan.referent) :
    ¬ EndsLoan before id after := hole_cannot_end found hole

example {program : Language.Program} {world : World} {integer address type} :
    ¬ Memory.PointsTo program world (Memory.AddressOnly integer) address type := Memory.address_integer_has_no_provenance

example (relocation : Execution.Relocation) (value : Value) :
    (relocation.value value).fields.map Option.isSome = value.fields.map Option.isSome :=
  Execution.relocation_preserves_holes relocation value

example : Source.DeclarationsSyntax [] [] := .nil
example : Source.TypeSyntax [.symbol "(",.symbol ")"] .unit := .unit
example : Source.TypeSyntax [.symbol "(",.symbol "(",.symbol ")",.symbol ",",.symbol ")"] (.tuple [.unit]) :=
  .tuple .unit .nil

example : "if" ∉ Source.reserved ∧ "loop" ∉ Source.reserved ∧ "return" ∉ Source.reserved ∧ "true" ∉ Source.reserved :=
  Source.ordinary_control_names

example : ¬ Source.UnicodeScalar 0xd800 := by simp [Source.UnicodeScalar]
example : Source.Encodes 0x1f600 [0xf0,0x9f,0x98,0x80] := by
  exact .four (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) rfl (by decide) (by simp [Source.UnicodeScalar])

example : Memory.integerBytes .little 4 0x12345678 = [0x78,0x56,0x34,0x12] := by decide
example : Memory.integerBytes .big 4 0x12345678 = [0x12,0x34,0x56,0x78] := by decide
example : Source.digitsValue 16 [15,15] = 255 := by decide

example {program : Kernel.Program} {function : Kernel.Function} :
    Contracts.Derived program function (Contracts.ExactInterface program function) := Contracts.exact_interface_is_derived program function

end Glorious.Language.Checks
