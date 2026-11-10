import Glorious.Value

/-!
# Bytecode syntax

Flat code addressed by a program counter. Every value-producing instruction
writes the next free local of the current frame.
-/

namespace Glorious.Bytecode

inductive Instr where
  /-- Evaluate a control-free computation into the next local. -/
  | op (rhs : Rhs)
  /-- Push a return frame and enter the callee; its result becomes the next local. -/
  | call (f : Atom) (args : List Atom)
  /-- Enter the callee, reusing the current frame. -/
  | tail (f : Atom) (args : List Atom)
  /-- Return a value to the frame below. -/
  | ret (a : Atom)

abbrev Code := List Instr

structure Fn where
  arity : Nat
  code : Code

structure Program where
  fns : List Fn
  main : Code

end Glorious.Bytecode
