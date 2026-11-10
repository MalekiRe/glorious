import Glorious.Proof.Correct
import Glorious.Bytecode.Decode

/-!
# Axiom audit

The build fails if the public theorems come to depend on anything beyond Lean's
three standard axioms, in particular on `sorryAx` or a declared `axiom`.
-/

/-- info: 'Glorious.compile_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.compile_correct

/-- info: 'Glorious.compile_halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.compile_halts

/-- info: 'Glorious.compile_diverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.compile_diverges

/-- info: 'Glorious.compile_halts_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.compile_halts_reflect

/-- info: 'Glorious.compile_emits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.compile_emits

/-- info: 'Glorious.compile_emits_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.compile_emits_reflect

/-- info: 'Glorious.Bytecode.Decode.program_encode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Bytecode.Decode.program_encode
