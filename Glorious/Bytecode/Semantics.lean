import Glorious.Machine
import Glorious.Control
import Glorious.Bytecode.Ast

/-!
# Bytecode semantics

The virtual machine: a program counter into the current function's code, the
current frame's locals, a stack of return frames and handler delimiters, and
the store of captured continuations.
-/

namespace Glorious.Bytecode

/-- A stack frame. -/
inductive Frame where
  /-- Where to continue after a call returns, and the locals to restore. -/
  | ret (code : Code) (pc : Nat) (locals : Env)
  /-- The delimiter of an installed handler. -/
  | handler (h : Handler)

def Frame.asHandler : Frame → Option Handler
  | .ret _ _ _ => none
  | .handler h => some h

structure State where
  code : Code
  pc : Nat
  locals : Env
  frames : List Frame
  conts : Conts Frame

/-- The code of function `fn` and its initial locals, `arguments ++ captures`.
Execution starts at its first instruction. -/
def invoke (p : Program) (fn : Nat) (captures vs : List Value) : Option (Code × Env) :=
  match p.fns[fn]? with
  | some F => some (F.code, vs ++ captures)
  | none => none

def callFn (p : Program) (fn : Nat) (captures vs : List Value) (frames : List Frame)
    (conts : Conts Frame) : Step State Value :=
  match invoke p fn captures vs with
  | some (code, ρ) => .next ⟨code, 0, ρ, frames, conts⟩
  | none => .stuck

def deliver (p : Program) (v : Value) (frames : List Frame) (conts : Conts Frame) :
    Step State Value :=
  match frames with
  | [] => .halt v
  | .ret code pc locals :: frames => .next ⟨code, pc, locals ++ [v], frames, conts⟩
  | .handler h :: frames => callFn p h.ret h.caps [v] frames conts

def apply (p : Program) (c : Callee) (frames : List Frame) (conts : Conts Frame) :
    Step State Value :=
  match c with
  | .fn fn captures vs => callFn p fn captures vs frames conts
  | .cont id v =>
    match takeCont conts id with
    | some (segment, conts') => deliver p v (segment ++ frames) conts'
    | none => .stuck

def step (p : Program) (s : State) : Step State Value :=
  match s.code[s.pc]? with
  | none => .stuck
  | some (.op rhs) =>
    match rhs.eval s.locals with
    | none => .stuck
    | some v => .next ⟨s.code, s.pc + 1, s.locals ++ [v], s.frames, s.conts⟩
  | some (.call f args) =>
    match evalCall s.locals f args with
    | none => .stuck
    | some c => apply p c (.ret s.code (s.pc + 1) s.locals :: s.frames) s.conts
  | some (.tail f args) =>
    match evalCall s.locals f args with
    | none => .stuck
    | some c => apply p c s.frames s.conts
  | some (.ret a) =>
    match a.eval s.locals with
    | none => .stuck
    | some v => deliver p v s.frames s.conts
  | some (.handle ret ops captures thunk) =>
    match evalAtoms s.locals captures, evalCall s.locals thunk [] with
    | some caps, some c =>
      apply p c (.handler ⟨ret, ops, caps⟩ :: .ret s.code (s.pc + 1) s.locals :: s.frames) s.conts
    | _, _ => .stuck
  | some (.raise op args) =>
    match evalAtoms s.locals args with
    | none => .stuck
    | some vs =>
      match findHandler Frame.asHandler op s.frames with
      | none => .stuck
      | some d => callFn p d.arm d.handler.caps vs d.below s.conts
  | some (.perform op args) =>
    match evalAtoms s.locals args with
    | none => .stuck
    | some vs =>
      match findHandler Frame.asHandler op s.frames with
      | none => .stuck
      | some d =>
        callFn p d.arm d.handler.caps (vs ++ [.cont s.conts.length]) d.below
          (s.conts ++ [some (.ret s.code (s.pc + 1) s.locals :: d.above ++ [.handler d.handler])])
  | some (.testCtor pl tag arity fail) =>
    match pl.eval s.locals with
    | none => .stuck
    | some v =>
      .next ⟨s.code, if v.isCtor tag arity then s.pc + 1 else fail, s.locals, s.frames, s.conts⟩
  | some (.testInt pl n fail) =>
    match pl.eval s.locals with
    | none => .stuck
    | some v =>
      .next ⟨s.code, if v.isInt n then s.pc + 1 else fail, s.locals, s.frames, s.conts⟩

def init (p : Program) : State := ⟨p.main, 0, [], [], []⟩

def Halts (p : Program) (v : Value) : Prop := Machine.Halts (step p) (init p) v

def GoesWrong (p : Program) : Prop := Machine.GoesWrong (step p) (init p)

def Diverges (p : Program) : Prop := Machine.Diverges (step p) (init p)

end Glorious.Bytecode
