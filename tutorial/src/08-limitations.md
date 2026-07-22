# 8. Current limitations and next steps

This project is deliberately honest about the current generation-1 surface:

- a directly recursive `Instruction::Loop(Vec<Instruction>)` currently creates
  a cyclic principal `Use` derivation, so the checked AST uses
  `LoopStart(usize)` and `LoopEnd`; parsing and execution remain recursive;
- visible output uses `Diagnostic` because the host protocol has no stdout;
- CLI input is a literal UTF-8 argument, not interactive stdin;
- the tutorial tape is bounded to 256 cells and reports overflow explicitly;
- parsing and execution have no configurable recursion or step limit;
- parse offsets are byte offsets, while compact CLI messages currently omit the
  numeric position;
- output must be valid UTF-8 to be displayed by this CLI, though the core keeps
  arbitrary bytes;
- mdBook is optional for compiler users; `book.toml` and `SUMMARY.md` make this
  tutorial buildable when mdBook is installed.

None of these use a hidden host evaluator. The package is checked and executed
through `grand`, `grc`, and `grvm`.

A useful extension exercise is to add a step-budget value to `execute_sequence`.
Pass it as `&mut StepBudget`, decrement it before each instruction, and return a
new `RuntimeError` variant on exhaustion. This reinforces unique borrowing,
explicit error propagation, and recursive state threading without changing the
effect interface.
