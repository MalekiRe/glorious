import GloriousLanguage.Target

/-! Machine scalar domains and signatures are selected by primitive identity,
not by a manifest's otherwise unchecked result annotation. These declarative
shapes are shared by admission and scalar progress/preservation proofs. -/
namespace Glorious.Language

namespace Execution

def IntegerArity (operation : IntegerOperation) : Nat := if operation = .negate then 1 else 2
def FloatArity : FloatOperation → Nat
  | .negate | .absolute | .squareRoot => 1
  | .fusedMultiplyAdd => 3
  | _ => 2

end Execution

def Primitive.IsScalar : Primitive → Prop
  | .integer .. | .floating .. | .scalarEqual | .scalarLess | .scalarConvert .. => True
  | _ => False

/-- This is the machine conversion domain, not a source trait instance table.
Character construction is validating; character-to-floating and identity-char
calls have no conversion leaf and cannot be admitted by a matching annotation. -/
def ScalarConversionSupported : Scalar → Scalar → Prop
  | .integer .., .integer .. | .integer .., .floating .. | .integer .., .character => True
  | .floating .., .integer .. | .floating .., .floating .. => True
  | .character, .integer .. => True
  | _, _ => False

inductive ScalarPrimitiveSignature (target : TargetProfile) :
    Primitive → List Term → List Term → Term → Prop where
  | integer {operation sign width overflow} : (Scalar.integer sign width).Valid target →
      ScalarPrimitiveSignature target (.integer operation sign width overflow) []
        (List.replicate (Execution.IntegerArity operation) (.scalar (.integer sign width)))
        (.scalar (.integer sign width))
  | floating {operation width} : ScalarPrimitiveSignature target (.floating operation width) []
      (List.replicate (Execution.FloatArity operation) (.scalar (.floating width))) (.scalar (.floating width))
  | equal {scalar} : scalar.Valid target →
      ScalarPrimitiveSignature target .scalarEqual [] [.scalar scalar,.scalar scalar] (.scalar (.integer false (.fixed 8)))
  | less {scalar} : scalar.Valid target →
      ScalarPrimitiveSignature target .scalarLess [] [.scalar scalar,.scalar scalar] (.scalar (.integer false (.fixed 8)))
  | convert {policy source destination} : source.Valid target → destination.Valid target →
      ScalarConversionSupported source destination →
      ScalarPrimitiveSignature target (.scalarConvert policy) [.scalar destination] [.scalar source] (.scalar destination)

/-- Only the scalar branch is discharged here. Other machine families retain
their separate storage/control obligations; this predicate grants none of them
permission. Instantiated parameter/result shapes, not the generic spelling,
must agree at the actual primitive call. -/
def RuntimeBinding.ScalarSignature (binding : RuntimeBinding) (target : TargetProfile)
    (arguments : List Term) (signature : Signature) : Prop :=
  ∀ primitive, binding.primitive = some primitive → primitive.IsScalar →
    ScalarPrimitiveSignature target primitive arguments signature.parameters signature.result

end Glorious.Language
