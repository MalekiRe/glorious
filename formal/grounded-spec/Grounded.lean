/-!
# Unit expressions: source AST to value

Language specification §3.4 (tuple punctuation) states that `()` is both the
unit type and unit value; §4.1 includes unit among the language types.
Only the unit expression is represented. No parser, elaboration, physical
storage model, or compiler implementation is claimed here. Admission and
evaluation are independent relations; admission contains no execution premise.
-/

namespace Grounded

inductive Expr where
  | unit

inductive Ty where
  | unit

inductive Value where
  | unit

inductive HasType : Expr → Ty → Prop where
  | unit : HasType .unit .unit

inductive ValueHasType : Value → Ty → Prop where
  | unit : ValueHasType .unit .unit

inductive Evaluates : Expr → Value → Prop where
  | unit : Evaluates .unit .unit

/-- Every supported AST is admitted. Every admitted typing has a terminating
execution yielding the unique unit result, with the admitted type. This is the
complete logical evaluation boundary, not a physical-machine theorem. -/
theorem correctness (expression : Expr) :
    HasType expression .unit ∧
    (∀ type, HasType expression type →
      ∃ value, Evaluates expression value ∧ ValueHasType value type ∧
        value = .unit ∧
        ∀ other, Evaluates expression other → other = value) := by
  cases expression with
  | unit =>
    refine ⟨.unit, ?_⟩
    intro type admitted
    cases admitted
    refine ⟨.unit, .unit, .unit, rfl, ?_⟩
    intro other evaluated
    cases evaluated
    rfl

end Grounded
