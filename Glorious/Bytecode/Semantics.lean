module

public import Glorious.Machine
public import Glorious.Host
public import Glorious.Bytecode.Ast

/-!
# Bytecode semantics

The virtual machine: a program counter into the current function's code, the
current frame's locals, a stack of return frames and handler delimiters, and
the store of captured continuations.
-/

@[expose] public section

namespace Glorious.Bytecode

/-- A stack frame. -/
inductive Frame where
  /-- Where to continue after a call returns, and the locals to restore. -/
  | ret (code : Code) (pc : Nat) (locals : Env)
  /-- The delimiter of an installed handler, with its identity. -/
  | handler (id : Nat) (h : Handler)
  /-- The scope of a label. -/
  | label (id : Nat)
  /-- A cleanup that runs when the computation above it is left, by any path. -/
  | guard (fn : Nat) (captures : List Value)
  /-- The scope of a memory cell: the cell is released when this frame is removed. -/
  | cell (addr : Nat)
  /-- A pending result: whatever is delivered here is discarded and `v` is delivered. -/
  | yield (v : Value)
  /-- An exit in progress. A cleanup was running above this frame; whatever it
  delivers is discarded and the exit continues towards its target. -/
  | exit (target : Target) (after : After)

def Frame.asHandler : Frame → Option (Nat × Handler)
  | .handler id h => some (id, h)
  | .ret _ _ _ | .label _ | .guard _ _ | .cell _ | .yield _ | .exit _ _ => none

def Frame.asLabel : Frame → Option Nat
  | .label id => some id
  | .ret _ _ _ | .handler _ _ | .guard _ _ | .cell _ | .yield _ | .exit _ _ => none

/-- Is this frame what an exit is heading for? -/
def Frame.isTarget : Frame → Target → Bool
  | .label id, .label id' => id == id'
  | .handler id _, .handler id' => id == id'
  | _, _ => false

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

mutual

/-- Deliver a result to the top of a stack. A caller binds it. A handler's
delimiter is removed and its completion function runs outside it. A label scope
simply ends. A guard runs its cleanup and then passes the result on. A cell's
scope ends and the cell is released. An exit in progress discards it and
continues. -/
def deliver (p : Program) : Value → List Frame → Store Frame → Step State Value
  | v, [], _ => .halt v
  | v, .ret code pc locals :: frames, store => .next ⟨code, pc, locals ++ [v], frames, store⟩
  | v, .handler _ h :: frames, store => callFn p h.ret h.caps [v] frames store
  | v, .label _ :: frames, store => deliver p v frames store
  | v, .guard fn captures :: frames, store => callFn p fn captures [] (.yield v :: frames) store
  | v, .cell a :: frames, store => deliver p v frames (store.release a)
  | _, .yield w :: frames, store => deliver p w frames store
  | _, .exit target after :: frames, store => leave p target after frames store

/--
Leave for `target`, abandoning the frames on the way. Each cleanup among them
runs in place: everything below it is still there, so it can jump to an
enclosing label or perform an operation an enclosing handler serves, exactly as
on a normal return. When the cleanup is done the exit goes on. A cell whose
scope is among them is released. Once the target
is reached it is removed and `after` happens on what is below it. A stack
without the target has no meaning.
-/
def leave (p : Program) (target : Target) (after : After) :
    List Frame → Store Frame → Step State Value
  | [], _ => .stuck
  | fr :: frames, store =>
    if fr.isTarget target then
      match after with
      | .yield v => deliver p v frames store
      | .invoke fn captures args => callFn p fn captures args frames store
    else
      match fr with
      | .guard fn captures => callFn p fn captures [] (.exit target after :: frames) store
      | .cell a => leave p target after frames (store.release a)
      | _ => leave p target after frames store

end

def apply (p : Program) (c : Callee) (frames : List Frame) (store : Store Frame) :
    Step State Value :=
  match c with
  | .fn fn captures vs => callFn p fn captures vs frames store
  | .cont id v =>
    match takeCont store.conts id with
    | some (segment, conts) =>
      deliver p v (segment ++ frames) ⟨conts, store.labels, store.cells⟩
    | none => .stuck
  | .label id v =>
    match findLabel Frame.asLabel id frames with
    | some _ => leave p (.label id) (.yield v) frames store
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
      apply p c (.handler s.store.labels ⟨ret, ops, caps⟩ :: .ret s.code (s.pc + 1) s.locals :: s.frames)
        ⟨s.store.conts, s.store.labels + 1, s.store.cells⟩
    | _, _ => .stuck
  | some (.raise op args) =>
    match evalAtoms s.locals args with
    | none => .stuck
    | some vs =>
      match findHandler Frame.asHandler op s.frames with
      | none => .stuck
      | some d =>
        -- The handler's arm runs once the abandoned frames are cleaned up, and
        -- outside the handler.
        leave p (.handler d.id) (.invoke d.arm d.handler.caps vs) s.frames s.store
  | some (.perform op args) =>
    match evalAtoms s.locals args with
    | none => .stuck
    | some vs =>
      match findHandler Frame.asHandler op s.frames with
      | none => .stuck
      | some d =>
        callFn p d.arm d.handler.caps (vs ++ [.cont s.store.conts.length]) d.below
          ⟨s.store.conts
              ++ [some (.ret s.code (s.pc + 1) s.locals :: d.above ++ [.handler d.id d.handler])],
            s.store.labels, s.store.cells⟩
  | some (.label thunk) =>
    match evalScope s.locals thunk (.label s.store.labels) with
    | none => .stuck
    | some c =>
      apply p c (.label s.store.labels :: .ret s.code (s.pc + 1) s.locals :: s.frames)
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
    | some caps, some c =>
      apply p c (.handler s.store.labels ⟨ret, ops, caps⟩ :: s.frames)
        ⟨s.store.conts, s.store.labels + 1, s.store.cells⟩
    | _, _ => .stuck
  | some (.labelTail thunk) =>
    match evalScope s.locals thunk (.label s.store.labels) with
    | none => .stuck
    | some c =>
      apply p c (.label s.store.labels :: s.frames)
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
    match dropOf p.drops s.locals k with
    | some (d, captures) => callFn p d [] captures (.ret s.code (s.pc + 1) s.locals :: s.frames) s.store
    | none =>
    match evalCont s.locals k with
    | none => .stuck
    | some none => .next ⟨s.code, s.pc + 1, s.locals ++ [.unit], s.frames, s.store⟩
    | some (some id) =>
      match takeCont s.store.conts id with
      | some (segment, conts) =>
        leave p (.label s.store.labels) (.yield .unit)
          (segment ++ .yield .unit :: .label s.store.labels
            :: .ret s.code (s.pc + 1) s.locals :: s.frames)
          ⟨conts, s.store.labels + 1, s.store.cells⟩
      | none => .stuck
  | some (.cell init thunk) =>
    match init.eval s.locals, evalScope s.locals thunk (.ref s.store.cells.size 0 []) with
    | some v, some c =>
      apply p c (.cell s.store.cells.size :: .ret s.code (s.pc + 1) s.locals :: s.frames)
        (s.store.alloc v)
    | _, _ => .stuck
  | some (.cellTail init thunk) =>
    match init.eval s.locals, evalScope s.locals thunk (.ref s.store.cells.size 0 []) with
    | some v, some c => apply p c (.cell s.store.cells.size :: s.frames) (s.store.alloc v)
    | _, _ => .stuck
  | some (.lend _ r thunk pre post) =>
    match evalLend s.locals r thunk pre post (s.store.labels + 1) with
    | none => .stuck
    | some (_, c) =>
      -- The scope of the borrow is nothing here: this is the call, and a
      -- counter that gives the borrow its identity.
      apply p c (.ret s.code (s.pc + 1) s.locals :: s.frames)
        ⟨s.store.conts, s.store.labels + 1, s.store.cells⟩
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

def init (p : Program) : State := ⟨p.main, 0, [], [], ⟨[], 0, #[]⟩⟩

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

def initIO (p : Program) (input : List Int) : Config := ⟨init p, { input := input, output := [], names := p.names }⟩

def Halts (p : Program) (input : List Int) (r : Result) : Prop :=
  Machine.Halts (stepIO p) (initIO p input) r

def GoesWrong (p : Program) (input : List Int) : Prop :=
  Machine.GoesWrong (stepIO p) (initIO p input)

def Diverges (p : Program) (input : List Int) : Prop :=
  Machine.Diverges (stepIO p) (initIO p input)

def Emits (p : Program) (input : List Int) (out : List Value) : Prop :=
  ∃ c, Machine.Reaches (stepIO p) (initIO p input) c ∧ c.world.output = out

end Glorious.Bytecode
