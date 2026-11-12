import Glorious.Syntax.Parser
import Glorious.Elab
import Glorious.Check
import Glorious.Infer
import Glorious.Prelude
import Glorious.Compile
import Glorious.Core.Semantics
import Glorious.Bytecode.Semantics

/-!
# Driver

Source text to Core, and helpers to run a program on both machines.
-/

namespace Glorious

structure Compiled where
  core : Core.Program
  ctorNames : Array String
  fnNames : Array String
  opNames : Array String
  /-- The typing of `core` that `Typing.checkProgram` accepted, when the program
  was checked. With it, `Typing.checked_safety` applies to `core`; if the
  certificate is `strict`, so does `Typing.checked_owned_safety`; and if it has
  `regions`, so does `Typing.checked_borrow_safety`; and if it has `loans`,
  so does `Typing.checked_exclusive_safety`. -/
  cert : Option Typing.Cert := none
  /-- How many borrows are scopes of their own in `core`: those written as
  arguments of calls of functions, if the program could then be shown to
  follow the rules for borrows. `checked_exclusive_safety` is about these. -/
  lent : Nat := 0
  /-- The borrows that are not: each is, in `core`, the reference it borrows,
  and only the check of the source text keeps it exclusive. -/
  plain : List Elab.Borrow := []

/-- Find a certificate for a program's Core and have the proved checker accept
it: with the ownership rules and the region rules if the program can be shown
to meet them, and otherwise with those of them it can, or as a typing only.
An error here is a defect in the compiler, not in the program. -/
def certifyProgram (items : List Syntax.Item) (p : Core.Program)
    (envSizes : List (Nat × Nat) := []) : Except String Typing.Cert := do
  let attempt (strict regions loans : Bool) : Option Typing.Cert :=
    match Infer.certify items p strict envSizes regions loans with
    | .ok cert => if Typing.checkProgram cert p then some cert else none
    | .error _ => none
  if let some cert := attempt true true true then return cert
  if let some cert := attempt true true false then return cert
  if let some cert := attempt true false false then return cert
  if let some cert := attempt false true true then return cert
  if let some cert := attempt false true false then return cert
  let cert ← match Infer.certify items p false envSizes with
    | .ok cert => pure cert
    | .error e => throw s!"no certificate was found: {e}"
  if Typing.checkProgram cert p then pure cert
  else throw s!"the certificate was rejected: {Infer.rejected cert p}"

/-- Parse, check and elaborate a program together with the prelude, and have the
proved Core type checker accept the result. With `check := false` both checks
are skipped, so that programs which go wrong can still be run. -/
def compileSource (src : String) (check : Bool := true) : Except String Compiled := do
  let (prelude, fix) ← match Syntax.parse {} Prelude.source with
    | .ok r => pure r
    | .error e => throw s!"prelude: {e}"
  let (items, _) ← Syntax.parse fix src (base := 1000000)
  let all := prelude ++ items
  -- What the checker learnt about blocks that share an environment. A program
  -- it rejects is elaborated without that.
  let blocks ← match Check.checkProgram all with
    | .ok blocks => pure (some blocks)
    | .error e => if check then throw e else pure none
  let plain := fun (blocks : Option Elab.Blocks) => do
    let out ← Elab.elabProgram all blocks
    let cert ← if check then
        match certifyProgram all out.program out.envSizes with
        | .ok cert => pure (some cert)
        | .error e =>
          throw s!"the checker accepted this program, but its Core could not be shown to be well typed: {e}. This is a defect in the compiler"
      else pure none
    pure (⟨out.program, out.ctorNames, out.fnNames, out.opNames, cert, 0, out.plain⟩ : Compiled)
  -- A borrow given a name, or written as an argument of a call of a function,
  -- is a scope of its own in Core if the program can then be shown to follow
  -- every rule. Where it cannot, the borrow is the reference it borrows, as in
  -- a program that is not checked: first every place is tried with the
  -- narrower scope, then each as it passes alone.
  let lending := fun (blocks : Option Elab.Blocks) (sites : Nat → Nat) =>
    match Elab.elabProgram all blocks sites with
    | .ok out =>
      match Infer.certify all out.program true out.envSizes true true with
      | .ok cert =>
        if out.lent != 0 && Typing.checkProgram cert out.program then
          some (⟨out.program, out.ctorNames, out.fnNames, out.opNames, some cert, out.lent,
            out.plain⟩ : Compiled)
        else none
      | .error _ => none
    | .error _ => none
  let build := fun (blocks : Option Elab.Blocks) => do
    if check then
      if let .ok out := Elab.elabProgram all blocks (fun _ => 1) then
        if out.lent != 0 then
          if let some c := lending blocks (fun _ => 1) then return c
          if out.sites ≤ 32 then
            -- How each place fares alone, trying the narrower scope first.
            let alone := (List.range out.sites).map fun i =>
              if (lending blocks (fun j => if j == i then 1 else 0)).isSome then 1
              else if (lending blocks (fun j => if j == i then 2 else 0)).isSome then 2
              else 0
            if alone.any (· != 0) then
              if let some c := lending blocks (fun j => alone[j]?.getD 0) then return c
              -- Not all at once: take them one at a time, keeping each that
              -- passes with those kept before it.
              let mut kept : List Nat := List.replicate out.sites 0
              let mut best : Option Compiled := none
              for i in [0:out.sites] do
                let mode := alone[i]?.getD 0
                if mode != 0 then
                  let next := kept.set i mode
                  if let some c := lending blocks (fun j => next[j]?.getD 0) then
                    kept := next
                    best := some c
              if let some c := best then return c
    plain blocks
  -- Blocks can share an environment only where a type can state it. Where one
  -- cannot, as when what a block is given may also be a function that is not a
  -- block, every block captures for itself, as it would without the sharing.
  match build blocks with
  | .ok c => pure c
  | .error e =>
    match blocks with
    | some b => if b.links.isEmpty then throw e else build (some { b with links := [] })
    | none => throw e

/-- Whether a program's Core was shown to follow the ownership rules: `some true`
if so, `some false` if it was only shown to be well typed, `none` if it does not compile. -/
def owned (src : String) : Option Bool :=
  match compileSource src with
  | .ok c => c.cert.map (·.strict)
  | .error _ => none

/-- Whether a program's Core was shown to follow the region rules, likewise. -/
def borrowChecked (src : String) : Option Bool :=
  match compileSource src with
  | .ok c => c.cert.map (·.regions)
  | .error _ => none

/-- How many of a program's borrows are scopes of their own in its Core, which
was then shown to follow the rules for borrows: `none` if the program does not
compile or its Core was not shown to follow them. -/
def lentBorrows (src : String) : Option Nat :=
  match compileSource src with
  | .ok c => if (c.cert.map (·.loans)).getD false then some c.lent else none
  | .error _ => none

/-- The borrows of a program that nothing is proved about: those that are not
scopes of their own in its Core, or every one if the Core was not shown to
follow the rules for borrows. `none` if the program does not compile. A program
for which this is empty has every borrow covered by `checked_exclusive_safety`. -/
def unprovedBorrows (src : String) : Option (List Elab.Borrow) :=
  match compileSource src with
  | .ok c =>
    -- Where the rules were not shown to hold no borrow is a scope, and `plain`
    -- lists every one.
    some c.plain
  | .error _ => none

partial def showValue (names : Array String) : Value → String
  | .int n => toString n
  | .data tag fields =>
    let args := ", ".intercalate (fields.map (showValue names))
    if tag == 0 then s!"({args})"
    else
      let name := names[tag]?.getD s!"#{tag}"
      if fields.isEmpty then name else s!"{name}({args})"
  | .clo fn _ => s!"<fn {fn}>"
  | .cont id => s!"<resumption {id}>"
  | .label id => s!"<label {id}>"
  | .ref addr _ => s!"<ref {addr}>"

/-- Everything the program wrote, one value per line, then its result. -/
def showResult (names : Array String) (r : Result) : String :=
  "\n".intercalate (r.world.output.map (showValue names) ++ [showValue names r.value])

def showOutcome {σ : Type} (names : Array String) : Step σ Result → String
  | .halt r => showResult names r
  | .stuck => "went wrong"
  | .next _ => "out of fuel"

/--
Compile a program and run it on both machines with the given input. The result
is what it wrote followed by its value, or a description of what went wrong; if
the machines disagree, both are shown.
-/
def evalSource (src : String) (input : List Int := []) (fuel : Nat := 200000) : String :=
  match compileSource src with
  | .error e => s!"error: {e}"
  | .ok c =>
    let bytecode := compile c.core
    let onCore := showOutcome c.ctorNames
      (Machine.exec (Core.stepIO c.core) fuel (Core.initIO c.core input))
    let onVm := showOutcome c.ctorNames
      (Machine.exec (Bytecode.stepIO bytecode) (fuel * 20) (Bytecode.initIO bytecode input))
    if onCore == onVm then onVm else s!"MISMATCH: Core gives {onCore}, bytecode gives {onVm}"

/-- Why a Core configuration has no next step, in the program's own terms. This
is a diagnosis for the user and is not part of the semantics. -/
def explainStuck (c : Compiled) (cfg : Core.Config) : String :=
  let s := cfg.state
  let shown (vs : List Value) := ", ".intercalate (vs.map (showValue c.ctorNames))
  let fnName (fn : Nat) := c.fnNames[fn]?.getD s!"function {fn}"
  let opName (op : Nat) := c.opNames[op]?.getD s!"operation {op}"
  let unbound := "a local is read that has no value; this is a compiler defect"
  let enter (fn : Nat) (vs : List Value) : String :=
    match c.core.fns[fn]? with
    | none => s!"function {fn} does not exist; this is a compiler defect"
    | some _ => s!"no clause of {fnName fn} matches the arguments ({shown vs})"
  let applied (f : Atom) (args : Option (List Value)) : String :=
    match f.eval s.env, args with
    | some (.clo fn _), some vs => enter fn vs
    | some (.cont _), some [_] =>
      "a resumption is used a second time: it was already resumed or cancelled"
    | some (.cont _), some vs =>
      s!"a resumption takes exactly one argument, but is given {vs.length}"
    | some (.label _), some [_] => "a label is applied after its scope has ended"
    | some (.label _), some vs => s!"a label takes exactly one argument, but is given {vs.length}"
    | some v, some _ => s!"`{showValue c.ctorNames v}` is called, but it is not callable"
    | _, _ => unbound
  let performed (op : Nat) : String :=
    match findHandler Core.Frame.asHandler op s.stack with
    | none => s!"operation `{opName op}` is performed, but no handler for it is installed"
    | some _ => s!"the handler for `{opName op}` could not be entered"
  match s.tm with
  | .ret a =>
    match a.eval s.env with
    | none => unbound
    | some v =>
      match s.stack.dropWhile (fun fr => (Core.Frame.asLabel fr).isSome) with
      | .handler _ h :: _ => enter h.ret [v]
      | _ => "a result could not be delivered"
  | .let_ rhs _ =>
    match rhs with
    | .prim _ args =>
      match evalAtoms s.env args with
      | some vs =>
        if vs.all (fun v => match v with | .int _ => true | _ => false)
        then s!"integer overflow: the result of an operation on ({shown vs}) does not fit in 64 bits"
        else s!"an arithmetic intrinsic is applied to ({shown vs})"
      | none => unbound
    | .place pl =>
      match s.env[pl.var]? with
      | some v => s!"`{showValue c.ctorNames v}` does not have the field being read"
      | none => unbound
    | _ => unbound
  | .call f args _ => applied f (evalAtoms s.env args)
  | .tail f args => applied f (evalAtoms s.env args)
  | .handle _ _ _ thunk _ => applied thunk (some [])
  | .handleTail _ _ _ thunk => applied thunk (some [])
  | .label thunk _ => applied thunk (some [.label s.store.labels])
  | .labelTail thunk => applied thunk (some [.label s.store.labels])
  | .guard _ thunk _ => applied thunk (some [])
  | .guardTail _ thunk => applied thunk (some [])
  | .raise op _ => performed op
  | .perform op _ _ => performed op
  | .cancel _ _ => "`cancel` is applied to something that is not a usable resumption"
  | .cell _ thunk _ => applied thunk (some [.ref s.store.cells.length 0])
  | .cellTail _ thunk => applied thunk (some [.ref s.store.cells.length 0])
  | .lend _ r thunk _ =>
    match r.eval s.env with
    | some (.ref a _) => applied thunk (some [.ref a (s.store.labels + 1)])
    | some v => s!"`{showValue c.ctorNames v}` is lent, but it is not a reference"
    | none => unbound
  | .mem _ args _ =>
    match evalAtoms s.env args with
    | some (.ref _ _ :: _) => "a reference is used after the cell it points to was freed"
    | some vs => s!"a memory operation is applied to ({shown vs}), which is not a reference"
    | none => unbound
  | .host id _ _ => s!"host operation {id} rejected its arguments"

/-- Run a program on the Core machine and, if it goes wrong, say why. -/
def diagnose (src : String) (input : List Int := []) (fuel : Nat := 200000) : String :=
  match compileSource src (check := false) with
  | .error e => s!"error: {e}"
  | .ok c =>
    let rec go : Nat → Core.Config → String
      | 0, _ => "out of fuel"
      | n + 1, cfg =>
        match Core.stepIO c.core cfg with
        | .next cfg' => go n cfg'
        | .halt _ => "did not go wrong"
        | .stuck => explainStuck c cfg
    go fuel (Core.initIO c.core input)

/-- The deepest the bytecode machine's stack gets while running a program. -/
def peakStack (src : String) (input : List Int := []) (fuel : Nat := 4000000) : Option Nat :=
  match compileSource src with
  | .error _ => none
  | .ok c =>
    let bytecode := compile c.core
    let rec go : Nat → Bytecode.Config → Nat → Option Nat
      | 0, _, _ => none
      | n + 1, cfg, peak =>
        let peak := max peak cfg.state.frames.length
        match Bytecode.stepIO bytecode cfg with
        | .next cfg' => go n cfg' peak
        | .halt _ => some peak
        | .stuck => none
    go fuel (Bytecode.initIO bytecode input) 0

/-- How many memory cells are still live when a program finishes. The step that
ends the program also leaves the scopes still on the stack, so their cells do
not count. -/
def liveCells (src : String) (input : List Int := []) (fuel : Nat := 4000000) : Option Nat :=
  match compileSource src with
  | .error _ => none
  | .ok c =>
    let bytecode := compile c.core
    let rec go : Nat → Bytecode.Config → Option Nat
      | 0, _ => none
      | n + 1, cfg =>
        match Bytecode.stepIO bytecode cfg with
        | .next cfg' => go n cfg'
        | .halt _ =>
          let leaving := cfg.state.frames.filterMap fun
            | .cell a => some a
            | _ => none
          let cells := cfg.state.store.cells
          some ((List.range cells.length).filter fun a =>
            (cells[a]?.getD none).isSome && !leaving.contains a).length
        | .stuck => none
    go fuel (Bytecode.initIO bytecode input)

end Glorious
