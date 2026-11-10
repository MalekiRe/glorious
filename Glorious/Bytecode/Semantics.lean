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
  /-- The scope of a label. -/
  | label (id : Nat)

def Frame.asHandler : Frame → Option Handler
  | .handler h => some h
  | .ret _ _ _ => none
  | .label _ => none

def Frame.asLabel : Frame → Option Nat
  | .label id => some id
  | .ret _ _ _ => none
  | .handler _ => none

structure State where
  code : Code
  pc : Nat
  locals : Env
  frames : List Frame
  store : Store Frame

/-- The code of function `fn` and its initial locals, `arguments ++ captures`.
Execution starts at its first instruction. -/
def invoke (p : Program) (fn : Nat) (captures vs : List Value) : Option (Code × Env) :=
  match p.fns[fn]? with
  | some F => some (F.code, vs ++ captures)
  | none => none

def callFn (p : Program) (fn : Nat) (captures vs : List Value) (frames : List Frame)
    (store : Store Frame) : Step State Value :=
  match invoke p fn captures vs with
  | some (code, ρ) => .next ⟨code, 0, ρ, frames, store⟩
  | none => .stuck

def deliver (p : Program) (v : Value) : List Frame → Store Frame → Step State Value
  | [], _ => .halt v
  | .ret code pc locals :: frames, store => .next ⟨code, pc, locals ++ [v], frames, store⟩
  | .handler h :: frames, store => callFn p h.ret h.caps [v] frames store
  | .label _ :: frames, store => deliver p v frames store

def apply (p : Program) (c : Callee) (frames : List Frame) (store : Store Frame) :
    Step State Value :=
  match c with
  | .fn fn captures vs => callFn p fn captures vs frames store
  | .cont id v =>
    match takeCont store.conts id with
    | some (segment, conts) => deliver p v (segment ++ frames) ⟨conts, store.labels⟩
    | none => .stuck
  | .label id v =>
    match findLabel Frame.asLabel id frames with
    | some below => deliver p v below store
    | none => .stuck

def step (p : Program) (s : State) : Step State Value :=
  match s.code[s.pc]? with
  | none => .stuck
  | some (.op rhs) =>
    match rhs.eval s.locals with
    | none => .stuck
    | some v => .next ⟨s.code, s.pc + 1, s.locals ++ [v], s.frames, s.store⟩
  | some (.call f args) =>
    match evalCall s.locals f args with
    | none => .stuck
    | some c => apply p c (.ret s.code (s.pc + 1) s.locals :: s.frames) s.store
  | some (.tail f args) =>
    match evalCall s.locals f args with
    | none => .stuck
    | some c => apply p c s.frames s.store
  | some (.ret a) =>
    match a.eval s.locals with
    | none => .stuck
    | some v => deliver p v s.frames s.store
  | some (.handle ret ops captures thunk) =>
    match evalAtoms s.locals captures, evalCall s.locals thunk [] with
    | some caps, some c =>
      apply p c (.handler ⟨ret, ops, caps⟩ :: .ret s.code (s.pc + 1) s.locals :: s.frames) s.store
    | _, _ => .stuck
  | some (.raise op args) =>
    match evalAtoms s.locals args with
    | none => .stuck
    | some vs =>
      match findHandler Frame.asHandler op s.frames with
      | none => .stuck
      | some d => callFn p d.arm d.handler.caps vs d.below s.store
  | some (.perform op args) =>
    match evalAtoms s.locals args with
    | none => .stuck
    | some vs =>
      match findHandler Frame.asHandler op s.frames with
      | none => .stuck
      | some d =>
        callFn p d.arm d.handler.caps (vs ++ [.cont s.store.conts.length]) d.below
          ⟨s.store.conts
              ++ [some (.ret s.code (s.pc + 1) s.locals :: d.above ++ [.handler d.handler])],
            s.store.labels⟩
  | some (.label thunk) =>
    match evalClosure s.locals thunk with
    | none => .stuck
    | some (fn, captures) =>
      callFn p fn captures [.label s.store.labels]
        (.label s.store.labels :: .ret s.code (s.pc + 1) s.locals :: s.frames)
        ⟨s.store.conts, s.store.labels + 1⟩
  | some (.testCtor pl tag arity fail) =>
    match pl.eval s.locals with
    | none => .stuck
    | some v =>
      .next ⟨s.code, if v.isCtor tag arity then s.pc + 1 else fail, s.locals, s.frames, s.store⟩
  | some (.testInt pl n fail) =>
    match pl.eval s.locals with
    | none => .stuck
    | some v =>
      .next ⟨s.code, if v.isInt n then s.pc + 1 else fail, s.locals, s.frames, s.store⟩

def init (p : Program) : State := ⟨p.main, 0, [], [], ⟨[], 0⟩⟩

def Halts (p : Program) (v : Value) : Prop := Machine.Halts (step p) (init p) v

def GoesWrong (p : Program) : Prop := Machine.GoesWrong (step p) (init p)

def Diverges (p : Program) : Prop := Machine.Diverges (step p) (init p)

end Glorious.Bytecode
