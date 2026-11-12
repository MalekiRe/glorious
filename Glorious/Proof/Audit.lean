import Glorious.Core.Cleanup
import Glorious.Proof.Correct
import Glorious.Bytecode.Decode
import Glorious.Typing.Compiled
import Glorious.Typing.Witness
import Glorious.Traits

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

/-- info: 'Glorious.Typing.borrow_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.borrow_safety

/-- info: 'Glorious.Typing.scoped_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.scoped_safety

/-- info: 'Glorious.Typing.compiled_scoped_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.compiled_scoped_safety

/-- info: 'Glorious.Typing.checked_borrow_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.checked_borrow_safety

/-- info: 'Glorious.Typing.checked_scoped_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.checked_scoped_safety

/-- info: 'Glorious.Typing.checked_compiled_scoped_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.checked_compiled_scoped_safety

/-- info: 'Glorious.Typing.checked_full_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.checked_full_safety

/-- info: 'Glorious.Typing.checked_compiled_full_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.checked_compiled_full_safety

/-- info: 'Glorious.Typing.Witness.counter_borrows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.Witness.counter_borrows

/-- info: 'Glorious.Typing.Witness.readers_borrows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.Witness.readers_borrows

/-- info: 'Glorious.Typing.label_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.label_safety

/-- info: 'Glorious.Typing.sound_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.sound_safety

/-- info: 'Glorious.Typing.compiled_sound_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.compiled_sound_safety

/-- info: 'Glorious.Typing.checked_label_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.checked_label_safety

/-- info: 'Glorious.Typing.Witness.jumps_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.Witness.jumps_sound

/-- info: 'Glorious.Typing.exclusive_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.exclusive_safety

/-- info: 'Glorious.Typing.checked_exclusive_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.checked_exclusive_safety

/-- info: 'Glorious.Typing.Witness.lender_exclusive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Typing.Witness.lender_exclusive

/-- info: 'Glorious.Typing.Witness.alias_aliased' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Glorious.Typing.Witness.alias_aliased

/-- info: 'Glorious.Traits.solve_sound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Glorious.Traits.solve_sound

/-- info: 'Glorious.Traits.coherent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Glorious.Traits.coherent

/-- info: 'Glorious.Traits.solve_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Traits.solve_unique

/-- info: 'Glorious.Core.step_accounts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Core.step_accounts

/-- info: 'Glorious.Core.cleanup_accounting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Core.cleanup_accounting

/-- info: 'Glorious.Core.halts_cleanup_accounting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Core.halts_cleanup_accounting

/-- info: 'Glorious.Core.cleanup_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glorious.Core.cleanup_exact
