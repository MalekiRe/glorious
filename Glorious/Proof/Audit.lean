import Glorious.Proof.Correct

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
