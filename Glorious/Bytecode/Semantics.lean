import Glorious.Machine
import Glorious.Bytecode.Ast

/-!
# Bytecode semantics

The virtual machine: a program counter into the current function's code, the
current frame's locals, and a stack of return frames.
-/

namespace Glorious.Bytecode

/-- A return frame: where to continue and the locals to restore. -/
structure Frame where
  code : Code
  pc : Nat
  locals : Env

structure State where
  code : Code
  pc : Nat
  locals : Env
  frames : List Frame

def enter (p : Program) (ρ : Env) (f : Atom) (args : List Atom) : Option (Code × Env) :=
  match evalCall ρ f args with
  | some (fn, captures, vs) =>
    match p.fns[fn]? with
    | some F => if vs.length = F.arity then some (F.code, captures ++ vs) else none
    | none => none
  | none => none

def step (p : Program) (s : State) : Step State Value :=
  match s.code[s.pc]? with
  | none => .stuck
  | some (.op rhs) =>
    match rhs.eval s.locals with
    | none => .stuck
    | some v => .next ⟨s.code, s.pc + 1, s.locals ++ [v], s.frames⟩
  | some (.call f args) =>
    match enter p s.locals f args with
    | none => .stuck
    | some (code, ρ) => .next ⟨code, 0, ρ, ⟨s.code, s.pc + 1, s.locals⟩ :: s.frames⟩
  | some (.tail f args) =>
    match enter p s.locals f args with
    | none => .stuck
    | some (code, ρ) => .next ⟨code, 0, ρ, s.frames⟩
  | some (.ret a) =>
    match a.eval s.locals with
    | none => .stuck
    | some v =>
      match s.frames with
      | [] => .halt v
      | fr :: frames => .next ⟨fr.code, fr.pc, fr.locals ++ [v], frames⟩

def init (p : Program) : State := ⟨p.main, 0, [], []⟩

def Halts (p : Program) (v : Value) : Prop := Machine.Halts (step p) (init p) v

def GoesWrong (p : Program) : Prop := Machine.GoesWrong (step p) (init p)

def Diverges (p : Program) : Prop := Machine.Diverges (step p) (init p)

end Glorious.Bytecode
