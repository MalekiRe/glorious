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
  /-- Push a return frame and a handler delimiter, then enter `thunk`. -/
  | handle (ret : Nat) (ops : List (Nat × Nat)) (captures : List Atom) (thunk : Atom)
  /-- Abandon the frames up to the nearest handler of `op` and enter its arm. -/
  | raise (op : Nat) (args : List Atom)
  /-- Capture the frames up to the nearest handler of `op` as a resumption and
  enter its arm; the value it is resumed with becomes the next local. -/
  | perform (op : Nat) (args : List Atom)
  /-- Push a return frame and a fresh label scope, then enter `thunk` with the label. -/
  | label (thunk : Atom)
  /-- Fall through if the place holds constructor `tag` with `arity` fields;
  otherwise jump to `fail`. -/
  | testCtor (pl : Place) (tag arity : Nat) (fail : Nat)
  /-- Fall through if the place holds the integer `n`; otherwise jump to `fail`. -/
  | testInt (pl : Place) (n : Int) (fail : Nat)

abbrev Code := List Instr

structure Fn where
  code : Code

structure Program where
  fns : List Fn
  main : Code

end Glorious.Bytecode
