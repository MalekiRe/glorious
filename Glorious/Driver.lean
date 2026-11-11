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
  was checked. With it, `Typing.checked_safety` applies to `core`. -/
  cert : Option Typing.Cert := none

/-- Find a certificate for a program's Core and have the proved checker accept
it. An error here is a defect in the compiler, not in the program. -/
def certifyProgram (items : List Syntax.Item) (p : Core.Program) : Except String Typing.Cert := do
  let cert ← match Infer.certify items p with
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
  let (items, _) ← Syntax.parse fix src
  if check then Check.checkProgram (prelude ++ items)
  let out ← Elab.elabProgram (prelude ++ items)
  let cert ← if check then
      match certifyProgram (prelude ++ items) out.program with
      | .ok cert => pure (some cert)
      | .error e =>
        throw s!"the checker accepted this program, but its Core could not be shown to be well typed: {e}. This is a defect in the compiler"
    else pure none
  pure ⟨out.program, out.ctorNames, out.fnNames, out.opNames, cert⟩

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
  | .ref addr => s!"<ref {addr}>"

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
  | .mem op args _ =>
    match evalAtoms s.env args with
    | some (.ref _ :: _) =>
      match op with
      | .free => "a memory cell is freed twice"
      | _ => "a reference is used after the cell it points to was freed"
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

/-- How many memory cells are still live when a program finishes. -/
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
        | .halt _ => some (cfg.state.store.cells.filter Option.isSome).length
        | .stuck => none
    go fuel (Bytecode.initIO bytecode input)

end Glorious
