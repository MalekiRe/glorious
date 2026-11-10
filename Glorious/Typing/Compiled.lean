import Glorious.Typing.Safety
import Glorious.Proof.Correct

/-!
# Type safety of compiled programs

The two proofs joined: the bytecode of a well-typed Core program goes wrong only
if the Core program reaches one of the faults.
-/

namespace Glorious.Typing

/-- If the bytecode compiled from a well-typed program goes wrong, the program
itself reaches a state it cannot step from, and that state is one of the four
faults. -/
theorem compiled_type_safety {Δ : Ctx} {p : Core.Program} (hp : ProgramOk Δ p)
    (input : List Int) (h : Bytecode.GoesWrong (compile p) input) :
    ∃ c, Machine.Reaches (Core.stepIO p) (Core.initIO p input) c ∧ Core.stepIO p c = .stuck
      ∧ Fault c.state :=
  type_safety hp input
    (Classical.byContradiction fun hn => (compile_correct p input hn).2.2 h)

end Glorious.Typing
