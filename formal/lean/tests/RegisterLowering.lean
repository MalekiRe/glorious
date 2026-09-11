import Glorious.Semantics.Lower
import Glorious.Semantics.Manifest

/-! Focused receiving-boundary regression. This supplies typed Core directly
to the real lowerer; it is not a second source compiler or a semantic proof. -/
open Glorious Glorious.Semantics

def boundaryProgram : Check AnalyzedProgram := do
  let source ← initialProgram emptyManifest [⟨"main", "<register-boundary>", []⟩]
  let output : TypedSlot := ⟨10, .unit, false, {}⟩
  let unitBody := Core.step (.declare output)
    (.step (.constant output.id (.constantTuple [])) (.result ⟨output.id, []⟩))
  let entry : CoreFunction := ⟨⟨0, 1⟩, { arguments := [], output := .unit }, [], [], .shared,
    .label 1 (.rigid 1 .brand 1) (.rigid 1 .region 1) .unit (.scopeBlock 2 unitBody), none, {}⟩
  let first : TypedSlot := ⟨20, .unit, false, {}⟩
  let second : TypedSlot := ⟨21, .unit, false, {}⟩
  let parameters : CoreFunction := ⟨⟨0, 2⟩, { arguments := [.unit, .unit], output := .unit },
    [first, second], [], .shared, .result ⟨first.id, []⟩, none, {}⟩
  return ⟨⟨source, [entry, parameters], [], {}⟩, []⟩

def main (arguments : List String) : IO UInt32 := do
  let artifact ← match boundaryProgram >>= fun program => lowerProgram program ⟨0, 1⟩ with
    | .ok artifact => pure artifact
    | .error error => IO.eprintln (repr error); return 1
  let artifact ← match arguments with
    | [] => pure artifact
    | ["invalid-flag"] =>
      let first := artifact.code.headD .nop
      pure { artifact with code := artifact.code.set 1 first }
    | ["invalid-abi"] =>
      let functions := artifact.functions.map fun function =>
        if function.signature.params.isEmpty then function else
          { function with registers := function.registers.set 2 4 }
      pure { artifact with functions }
    | _ => IO.eprintln "expected no option, invalid-flag, or invalid-abi"; return 2
  IO.println (artifact.json vm64Target).compress
  return 0
