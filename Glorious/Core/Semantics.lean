module

public import Glorious.Machine
public import Glorious.Control
public import Glorious.Host
public import Glorious.Core.Ast

/-!
# Core semantics

The meaning of a Core program, as an abstract machine. This file is the
definition the compiler is proved against.
-/

@[expose] public section

namespace Glorious.Core

mutual

/-- Match a value against a pattern. On success, the bound values in binder order. -/
def Pat.matchVal : Pat → Value → Option (List Value)
  | .wild, _ => some []
  | .bind, v => some [v]
  | .int n, .int m => if n = m then some [] else none
  | .int _, .data _ _ => none
  | .int _, .clo _ _ => none
  | .int _, .cont _ => none
  | .int _, .label _ => none
  | .int _, .ref _ _ _ => none
  | .ctor tag ps, .data t fields => if tag = t then Pat.matchVals ps fields else none
  | .ctor _ _, .int _ => none
  | .ctor _ _, .clo _ _ => none
  | .ctor _ _, .cont _ => none
  | .ctor _ _, .label _ => none
  | .ctor _ _, .ref _ _ _ => none

/-- Match values against patterns pointwise. The two lists must have the same length. -/
def Pat.matchVals : List Pat → List Value → Option (List Value)
  | [], [] => some []
  | p :: ps, v :: vs =>
    match p.matchVal v, Pat.matchVals ps vs with
    | some b, some bs => some (b ++ bs)
    | _, _ => none
  | [], _ :: _ => none
  | _ :: _, [] => none

end

/-- The first clause whose patterns match the arguments: its body and bindings.
A clause with the wrong number of patterns has no meaning. -/
def selectClause : List Clause → List Value → Option (Tm × List Value)
  | [], _ => none
  | c :: cs, vs =>
    if c.pats.length = vs.length then
      match Pat.matchVals c.pats vs with
      | some bs => some (c.body, bs)
      | none => selectClause cs vs
    else none

/-- A stack frame. -/
inductive Frame where
  /-- A suspended caller: the environment and the code waiting for a result. -/
  | call (env : Env) (body : Tm)
  /-- The delimiter of an installed handler, with its identity. -/
  | handler (id : Nat) (h : Handler)
  /-- The scope of a label. -/
  | label (id : Nat)
  /-- A cleanup that runs when the computation above it is left, by any path. -/
  | guard (fn : Nat) (captures : List Value)
  /-- The scope of a memory cell: the cell is released when this frame is removed. -/
  | cell (addr : Nat)
  /-- The scope of a borrow of the cell at `addr`: for writing too if `uniq`. -/
  | lend (uniq : Bool) (addr borrow : Nat)
  /-- A pending result: whatever is delivered here is discarded and `v` is delivered. -/
  | yield (v : Value)
  /-- An exit in progress. A cleanup was running above this frame; whatever it
  delivers is discarded and the exit continues towards its target. -/
  | exit (target : Target) (after : After)


def Frame.asHandler : Frame → Option (Nat × Handler)
  | .handler id h => some (id, h)
  | .call _ _ => none
  | .label _ => none
  | .guard _ _ => none
  | .cell _ => none
  | .lend _ _ _ => none
  | .yield _ => none
  | .exit _ _ => none

def Frame.asLabel : Frame → Option Nat
  | .label id => some id
  | .call _ _ => none
  | .handler _ _ => none
  | .guard _ _ => none
  | .cell _ => none
  | .lend _ _ _ => none
  | .yield _ => none
  | .exit _ _ => none

/-- Is this frame what an exit is heading for? -/
def Frame.isTarget : Frame → Target → Bool
  | .label id, .label id' => id == id'
  | .handler id _, .handler id' => id == id'
  | _, _ => false

structure State where
  tm : Tm
  env : Env
  stack : List Frame
  store : Store Frame

/-- Select the clause of function `fn` matching the arguments: its body and the
environment it starts in, `arguments ++ captures ++ bindings`. -/
def invoke (p : Program) (fn : Nat) (captures vs : List Value) : Option (Tm × Env) :=
  match p.fns[fn]? with
  | some F =>
    match selectClause F.clauses vs with
    | some (body, bs) => some (body, vs ++ captures ++ bs)
    | none => none
  | none => none

/-- Start running a function on top of `stack`. -/
def callFn (p : Program) (fn : Nat) (captures vs : List Value) (stack : List Frame)
    (store : Store Frame) : Step State Value :=
  match invoke p fn captures vs with
  | some (body, ρ) => .next ⟨body, ρ, stack, store⟩
  | none => .stuck

mutual

/-- Deliver a result to the top of a stack. A caller binds it. A handler's
delimiter is removed and its completion function runs outside it. A label scope
simply ends. A guard runs its cleanup and then passes the result on. A cell's
scope ends and the cell is released. An exit in progress discards it and
continues. -/
def deliver (p : Program) : Value → List Frame → Store Frame → Step State Value
  | v, [], _ => .halt v
  | v, .call ρ body :: stack, store => .next ⟨body, ρ ++ [v], stack, store⟩
  | v, .handler _ h :: stack, store => callFn p h.ret h.caps [v] stack store
  | v, .label _ :: stack, store => deliver p v stack store
  | v, .guard fn captures :: stack, store => callFn p fn captures [] (.yield v :: stack) store
  | v, .cell a :: stack, store => deliver p v stack (store.release a)
  | v, .lend _ _ _ :: stack, store => deliver p v stack store
  | _, .yield w :: stack, store => deliver p w stack store
  | _, .exit target after :: stack, store => leave p target after stack store

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
  | fr :: stack, store =>
    if fr.isTarget target then
      match after with
      | .yield v => deliver p v stack store
      | .invoke fn captures args => callFn p fn captures args stack store
    else
      match fr with
      | .guard fn captures => callFn p fn captures [] (.exit target after :: stack) store
      | .cell a => leave p target after stack (store.release a)
      | _ => leave p target after stack store

end

/-- Apply a callee on top of `stack`: enter a function, reinstate a captured
continuation and deliver the argument to it, or leave a label scope, running
the cleanups of the frames it abandons before the scope yields the argument. -/
def apply (p : Program) (c : Callee) (stack : List Frame) (store : Store Frame) :
    Step State Value :=
  match c with
  | .fn fn captures vs => callFn p fn captures vs stack store
  | .cont id v =>
    match takeCont store.conts id with
    | some (segment, conts) =>
      deliver p v (segment ++ stack) ⟨conts, store.labels, store.cells⟩
    | none => .stuck
  | .label id v =>
    match findLabel Frame.asLabel id stack with
    | some _ => leave p (.label id) (.yield v) stack store
    | none => .stuck

def step (p : Program) (s : State) : Step State Value :=
  match s.tm with
  | .ret a =>
    match a.eval s.env with
    | none => .stuck
    | some v => deliver p v s.stack s.store
  | .let_ rhs body =>
    match rhs.eval s.env with
    | none => .stuck
    | some v => .next ⟨body, s.env ++ [v], s.stack, s.store⟩
  | .call f args body =>
    match evalCall s.env f args with
    | none => .stuck
    | some c => apply p c (.call s.env body :: s.stack) s.store
  | .tail f args =>
    match evalCall s.env f args with
    | none => .stuck
    | some c => apply p c s.stack s.store
  | .handle ret ops captures thunk body =>
    match evalAtoms s.env captures, evalCall s.env thunk [] with
    | some caps, some c =>
      apply p c (.handler s.store.labels ⟨ret, ops, caps⟩ :: .call s.env body :: s.stack)
        ⟨s.store.conts, s.store.labels + 1, s.store.cells⟩
    | _, _ => .stuck
  | .raise op args =>
    match evalAtoms s.env args with
    | none => .stuck
    | some vs =>
      match findHandler Frame.asHandler op s.stack with
      | none => .stuck
      | some d =>
        -- The handler's arm runs once the abandoned frames are cleaned up, and
        -- outside the handler.
        leave p (.handler d.id) (.invoke d.arm d.handler.caps vs) s.stack s.store
  | .perform op args body =>
    match evalAtoms s.env args with
    | none => .stuck
    | some vs =>
      match findHandler Frame.asHandler op s.stack with
      | none => .stuck
      | some d =>
        -- The continuation runs from the performer up to and including the
        -- handler, so resuming it reinstalls the handler: handlers are deep.
        callFn p d.arm d.handler.caps (vs ++ [.cont s.store.conts.length]) d.below
          ⟨s.store.conts
              ++ [some (.call s.env body :: d.above ++ [.handler d.id d.handler])],
            s.store.labels, s.store.cells⟩
  | .label thunk body =>
    match evalScope s.env thunk (.label s.store.labels) with
    | none => .stuck
    | some c =>
      apply p c (.label s.store.labels :: .call s.env body :: s.stack)
        ⟨s.store.conts, s.store.labels + 1, s.store.cells⟩
  | .handleTail ret ops captures thunk =>
    match evalAtoms s.env captures, evalCall s.env thunk [] with
    | some caps, some c =>
      apply p c (.handler s.store.labels ⟨ret, ops, caps⟩ :: s.stack)
        ⟨s.store.conts, s.store.labels + 1, s.store.cells⟩
    | _, _ => .stuck
  | .labelTail thunk =>
    match evalScope s.env thunk (.label s.store.labels) with
    | none => .stuck
    | some c =>
      apply p c (.label s.store.labels :: s.stack)
        ⟨s.store.conts, s.store.labels + 1, s.store.cells⟩
  | .guard cleanup thunk body =>
    match evalClosure s.env cleanup, evalCall s.env thunk [] with
    | some (fn, captures), some c =>
      apply p c (.guard fn captures :: .call s.env body :: s.stack) s.store
    | _, _ => .stuck
  | .guardTail cleanup thunk =>
    match evalClosure s.env cleanup, evalCall s.env thunk [] with
    | some (fn, captures), some c => apply p c (.guard fn captures :: s.stack) s.store
    | _, _ => .stuck
  | .cancel k body =>
    -- A closure of a function that says how it is destroyed: what it
    -- captured is given to that function, and the result of `cancel` is what
    -- that gives, unit.
    match dropOf p.drops s.env k with
    | some (d, captures) => callFn p d [] captures (.call s.env body :: s.stack) s.store
    | none =>
    match evalCont s.env k with
    | none => .stuck
    | some none => .next ⟨body, s.env ++ [.unit], s.stack, s.store⟩
    | some (some id) =>
      match takeCont s.store.conts id with
      | some (segment, conts) =>
        -- The captured computation is put back inside a fresh label scope and
        -- that scope is left at once, so that its cleanups run. Whatever the
        -- computation might still deliver is discarded: the result of
        -- `cancel` is unit.
        leave p (.label s.store.labels) (.yield .unit)
          (segment ++ .yield .unit :: .label s.store.labels :: .call s.env body :: s.stack)
          ⟨conts, s.store.labels + 1, s.store.cells⟩
      | none => .stuck
  | .cell init thunk body =>
    match init.eval s.env, evalScope s.env thunk (.ref s.store.cells.length 0 []) with
    | some v, some c =>
      apply p c (.cell s.store.cells.length :: .call s.env body :: s.stack) (s.store.alloc v)
    | _, _ => .stuck
  | .cellTail init thunk =>
    match init.eval s.env, evalScope s.env thunk (.ref s.store.cells.length 0 []) with
    | some v, some c => apply p c (.cell s.store.cells.length :: s.stack) (s.store.alloc v)
    | _, _ => .stuck
  | .lend uniq r thunk pre post body =>
    match evalLend s.env r thunk pre post (s.store.labels + 1) with
    | none => .stuck
    | some (a, c) =>
      -- The borrow's identity is new, as a label's is, and not zero.
      apply p c (.lend uniq a (s.store.labels + 1) :: .call s.env body :: s.stack)
        ⟨s.store.conts, s.store.labels + 1, s.store.cells⟩
  | .mem op args body =>
    match evalAtoms s.env args with
    | none => .stuck
    | some vs =>
      match op.eval s.store.cells vs with
      | none => .stuck
      | some (r, cells) =>
        .next ⟨body, s.env ++ [r], s.stack, ⟨s.store.conts, s.store.labels, cells⟩⟩
  -- A host operation is a step of the program in its world; see `stepIO`.
  | .host _ _ _ => .stuck

def init (p : Program) : State := ⟨p.main, [], [], ⟨[], 0, []⟩⟩

/-- A machine state together with the world outside the program. -/
structure Config where
  state : State
  world : World

/-- Carry the outcome of a step that does not touch the world. -/
def lift (w : World) : Step State Value → Step Config Result
  | .next s => .next ⟨s, w⟩
  | .halt v => .halt ⟨v, w⟩
  | .stuck => .stuck

/-- One step of a program in its world. Host operations are the only steps
that touch the world; every other step is a `step` of the machine state. -/
def stepIO (p : Program) (c : Config) : Step Config Result :=
  match c.state.tm with
  | .host id args body =>
    match evalAtoms c.state.env args with
    | none => .stuck
    | some vs =>
      match Host.call c.world id vs with
      | none => .stuck
      | some (r, world) =>
        .next ⟨⟨body, c.state.env ++ [r], c.state.stack, c.state.store⟩, world⟩
  | _ => lift c.world (step p c.state)

/-- The program about to start, with `input` waiting to be read. -/
def initIO (p : Program) (input : List Int) : Config := ⟨init p, ⟨input, [], []⟩⟩

/-- Given `input`, the program finishes with result `r`. -/
def Halts (p : Program) (input : List Int) (r : Result) : Prop :=
  Machine.Halts (stepIO p) (initIO p input) r

/-- Given `input`, the program reaches a state the semantics gives no meaning to. -/
def GoesWrong (p : Program) (input : List Int) : Prop :=
  Machine.GoesWrong (stepIO p) (initIO p input)

/-- Given `input`, the program runs forever. -/
def Diverges (p : Program) (input : List Int) : Prop :=
  Machine.Diverges (stepIO p) (initIO p input)

/-- Given `input`, at some point while running the program has written exactly `out`. -/
def Emits (p : Program) (input : List Int) (out : List Value) : Prop :=
  ∃ c, Machine.Reaches (stepIO p) (initIO p input) c ∧ c.world.output = out

end Glorious.Core
