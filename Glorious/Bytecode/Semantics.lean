import Glorious.Machine
import Glorious.Control
import Glorious.Host
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
  /-- A cleanup that runs when the computation above it is left, by any path. -/
  | guard (fn : Nat) (captures : List Value)
  /-- A pending call: whatever is delivered here is discarded and the function runs. -/
  | invoke (fn : Nat) (captures : List Value) (args : List Value)
  /-- A pending result: whatever is delivered here is discarded and `v` is delivered. -/
  | yield (v : Value)

def Frame.asHandler : Frame → Option Handler
  | .handler h => some h
  | .ret _ _ _ => none
  | .label _ => none
  | .guard _ _ => none
  | .invoke _ _ _ => none
  | .yield _ => none

def Frame.asLabel : Frame → Option Nat
  | .label id => some id
  | .ret _ _ _ => none
  | .handler _ => none
  | .guard _ _ => none
  | .invoke _ _ _ => none
  | .yield _ => none

/--
Leave the frames `above` behind and continue with `base`. What they were going
to do is dropped: returns, pending calls and pending results. What their
cleanups need stays, in place: each cleanup itself, and every label scope and
handler it was registered inside, so that a cleanup can still jump to such a
label or perform an operation such a handler serves. An abandoned handler is
made passive, so that it no longer runs its completion clause.
-/
def unwind : List Frame → List Frame → List Frame
  | [], base => base
  | .guard fn captures :: above, base => .guard fn captures :: unwind above base
  | .handler h :: above, base => .handler h.abandon :: unwind above base
  | .label id :: above, base => .label id :: unwind above base
  | .ret _ _ _ :: above, base => unwind above base
  | .invoke _ _ _ :: above, base => unwind above base
  | .yield _ :: above, base => unwind above base

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

def deliver (p : Program) : Value → List Frame → Store Frame → Step State Value
  | v, [], _ => .halt v
  | v, .ret code pc locals :: frames, store => .next ⟨code, pc, locals ++ [v], frames, store⟩
  | v, .handler h :: frames, store =>
    if h.passive then deliver p v frames store else callFn p h.ret h.caps [v] frames store
  | v, .label _ :: frames, store => deliver p v frames store
  | v, .guard fn captures :: frames, store => callFn p fn captures [] (.yield v :: frames) store
  | _, .invoke fn captures args :: frames, store => callFn p fn captures args frames store
  | _, .yield w :: frames, store => deliver p w frames store

def apply (p : Program) (c : Callee) (frames : List Frame) (store : Store Frame) :
    Step State Value :=
  match c with
  | .fn fn captures vs => callFn p fn captures vs frames store
  | .cont id v =>
    match takeCont store.conts id with
    | some (segment, conts) => deliver p v (segment ++ frames) ⟨conts, store.labels, store.cells⟩
    | none => .stuck
  | .label id v =>
    match findLabel Frame.asLabel id frames with
    | some (above, below) =>
      deliver p .unit (unwind above (.label id :: .yield v :: below)) store
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
      apply p c (.handler ⟨ret, ops, caps, false⟩ :: .ret s.code (s.pc + 1) s.locals :: s.frames) s.store
    | _, _ => .stuck
  | some (.raise op args) =>
    match evalAtoms s.locals args with
    | none => .stuck
    | some vs =>
      match findHandler Frame.asHandler op s.frames with
      | none => .stuck
      | some d =>
        deliver p .unit
          (unwind d.above
            (.handler d.handler.abandon :: .invoke d.arm d.handler.caps vs :: d.below))
          s.store
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
            s.store.labels, s.store.cells⟩
  | some (.label thunk) =>
    match evalClosure s.locals thunk with
    | none => .stuck
    | some (fn, captures) =>
      callFn p fn captures [.label s.store.labels]
        (.label s.store.labels :: .ret s.code (s.pc + 1) s.locals :: s.frames)
        ⟨s.store.conts, s.store.labels + 1, s.store.cells⟩
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
  | some (.handleTail ret ops captures thunk) =>
    match evalAtoms s.locals captures, evalCall s.locals thunk [] with
    | some caps, some c => apply p c (.handler ⟨ret, ops, caps, false⟩ :: s.frames) s.store
    | _, _ => .stuck
  | some (.labelTail thunk) =>
    match evalClosure s.locals thunk with
    | none => .stuck
    | some (fn, captures) =>
      callFn p fn captures [.label s.store.labels] (.label s.store.labels :: s.frames)
        ⟨s.store.conts, s.store.labels + 1, s.store.cells⟩
  | some (.guard cleanup thunk) =>
    match evalClosure s.locals cleanup, evalCall s.locals thunk [] with
    | some (fn, captures), some c =>
      apply p c (.guard fn captures :: .ret s.code (s.pc + 1) s.locals :: s.frames) s.store
    | _, _ => .stuck
  | some (.guardTail cleanup thunk) =>
    match evalClosure s.locals cleanup, evalCall s.locals thunk [] with
    | some (fn, captures), some c => apply p c (.guard fn captures :: s.frames) s.store
    | _, _ => .stuck
  | some (.cancel k) =>
    match evalCont s.locals k with
    | none => .stuck
    | some id =>
      match takeCont s.store.conts id with
      | some (segment, conts) =>
        deliver p .unit
          (unwind segment (.yield .unit :: .ret s.code (s.pc + 1) s.locals :: s.frames))
          ⟨conts, s.store.labels, s.store.cells⟩
      | none => .stuck
  | some (.mem op args) =>
    match evalAtoms s.locals args with
    | none => .stuck
    | some vs =>
      match op.eval s.store.cells vs with
      | none => .stuck
      | some (r, cells) =>
        .next ⟨s.code, s.pc + 1, s.locals ++ [r], s.frames,
          ⟨s.store.conts, s.store.labels, cells⟩⟩
  -- A host operation is a step of the program in its world; see `stepIO`.
  | some (.host _ _) => .stuck

def init (p : Program) : State := ⟨p.main, 0, [], [], ⟨[], 0, []⟩⟩

/-- A machine state together with the world outside the program. -/
structure Config where
  state : State
  world : World

def lift (w : World) : Step State Value → Step Config Result
  | .next s => .next ⟨s, w⟩
  | .halt v => .halt ⟨v, w⟩
  | .stuck => .stuck

/-- One step of a program in its world. Only a host instruction touches the world. -/
def stepIO (p : Program) (c : Config) : Step Config Result :=
  match c.state.code[c.state.pc]? with
  | some (.host id args) =>
    match evalAtoms c.state.locals args with
    | none => .stuck
    | some vs =>
      match Host.call c.world id vs with
      | none => .stuck
      | some (r, world) =>
        .next ⟨⟨c.state.code, c.state.pc + 1, c.state.locals ++ [r], c.state.frames,
          c.state.store⟩, world⟩
  | _ => lift c.world (step p c.state)

def initIO (p : Program) (input : List Int) : Config := ⟨init p, ⟨input, []⟩⟩

def Halts (p : Program) (input : List Int) (r : Result) : Prop :=
  Machine.Halts (stepIO p) (initIO p input) r

def GoesWrong (p : Program) (input : List Int) : Prop :=
  Machine.GoesWrong (stepIO p) (initIO p input)

def Diverges (p : Program) (input : List Int) : Prop :=
  Machine.Diverges (stepIO p) (initIO p input)

def Emits (p : Program) (input : List Int) (out : List Value) : Prop :=
  ∃ c, Machine.Reaches (stepIO p) (initIO p input) c ∧ c.world.output = out

end Glorious.Bytecode
