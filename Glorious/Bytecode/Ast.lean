module

public import Glorious.Control

/-!
# Bytecode syntax

Flat code addressed by a program counter. Every value-producing instruction
writes the next free local of the current frame.
-/

@[expose] public section

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
  /-- Capture the frames up to the nearest handler of `op` as a one-shot resumption
  and enter its arm; the value it is resumed with becomes the next local. -/
  | perform (op : Nat) (args : List Atom)
  /-- Push a return frame and a fresh label scope, then enter `thunk` with the label. -/
  | label (thunk : Atom)
  /-- Push a handler delimiter and enter `thunk`, reusing the current frame. -/
  | handleTail (ret : Nat) (ops : List (Nat × Nat)) (captures : List Atom) (thunk : Atom)
  /-- Push a fresh label scope and enter `thunk`, reusing the current frame. -/
  | labelTail (thunk : Atom)
  /-- Push a return frame and a guard, then enter `thunk`. -/
  | guard (cleanup : Atom) (thunk : Atom)
  /-- Push a guard and enter `thunk`, reusing the current frame. -/
  | guardTail (cleanup : Atom) (thunk : Atom)
  /-- Run the cleanups of a resumption's captured frames; unit becomes the next local. -/
  | cancel (k : Atom)
  /-- Push a return frame and the scope of a fresh memory cell holding `init`,
  then enter `thunk` with a reference to the cell. -/
  | cell (init : Atom) (thunk : Atom)
  /-- Push the scope of a fresh memory cell and enter `thunk`, reusing the current frame. -/
  | cellTail (init : Atom) (thunk : Atom)
  /-- `cell` and `cellTail` of a cell of memory, laid out so (`Core.Tm.cellL`). -/
  | cellL (lay : Laid) (init : Atom) (thunk : Atom)
  | cellTailL (lay : Laid) (init : Atom) (thunk : Atom)
  /-- Push a return frame, then call `thunk` with `pre`, a reference to the cell
  `r` refers to that is a new borrow, and `post`. Core marks where the borrow
  ends with a frame of its own; nothing here reads it, so it is not kept. -/
  | lend (uniq : Bool) (r : Atom) (thunk : Atom) (pre post : List Atom)
  /-- Perform a memory operation; its result becomes the next local. -/
  | mem (op : MemOp) (args : List Atom)
  /-- Ask the host to perform operation `id`; its result becomes the next local. -/
  | host (id : Nat) (args : List Atom)
  /-- Fall through if the place holds constructor `tag` with `arity` fields;
  otherwise jump to `fail`. -/
  | testCtor (pl : Place) (tag arity : Nat) (fail : Nat)
  /-- Fall through if the place holds the integer `n`; otherwise jump to `fail`. -/
  | testInt (pl : Place) (n : Int) (fail : Nat)

abbrev Code := List Instr

structure Fn where
  code : Code

structure Program where
  fns : Array Fn
  main : Code
  /-- As Core's: each function whose closures say how they are destroyed, and
  the function that destroys what one captured. -/
  drops : List (Nat × Nat) := []
  /-- As Core's: each function's name, by its index. -/
  names : Array String := #[]

end Glorious.Bytecode
