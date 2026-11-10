import Glorious.Syntax.Parser
import Glorious.Elab
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

/-- Parse and elaborate a program together with the prelude. -/
def compileSource (src : String) : Except String Compiled := do
  let (prelude, fix) ← match Syntax.parse {} Prelude.source with
    | .ok r => pure r
    | .error e => throw s!"prelude: {e}"
  let (items, _) ← Syntax.parse fix src
  let out ← Elab.elabProgram (prelude ++ items)
  pure ⟨out.program, out.ctorNames⟩

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

end Glorious
