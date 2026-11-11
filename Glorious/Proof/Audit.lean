import Glorious.Proof.Correct
import Glorious.Bytecode.Decode
import Glorious.Typing.Compiled
import Glorious.Typing.Witness

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

/-- info: 'Glorious.compile_stack_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.compile_stack_depth

/-- info: 'Glorious.Typing.type_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.type_safety

/-- info: 'Glorious.Typing.compiled_type_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.compiled_type_safety

/-- info: 'Glorious.Typing.Witness.effects_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.Witness.effects_ok

/-- info: 'Glorious.Typing.checked_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.checked_safety

/-- info: 'Glorious.Typing.checked_compiled_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.checked_compiled_safety

/-- info: 'Glorious.Typing.Witness.effects_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.Witness.effects_checked

/-- info: 'Glorious.Typing.owned_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.owned_safety

/-- info: 'Glorious.Typing.checked_owned_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.checked_owned_safety

/-- info: 'Glorious.Typing.checked_compiled_owned_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.checked_compiled_owned_safety
