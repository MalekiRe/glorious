import GloriousLanguage.SnapshotWorldTyping
import GloriousLanguage.RuntimeBodyTyping

/-! The actual finite snapshot action agrees with its permutation extension
through supported continuation signatures and bodies. -/
namespace Glorious.Language.Execution

theorem SnapshotMap.signature_permutation {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} (selected : SnapshotMap program before suspension map) (world : before.world.WellFormed)
    {signature : Signature} (supported : ∀ term ∈ signature.terms, term.RuntimeRegionsBelow before.world.nextRegion) :
    map.signature signature = (selected.permutation world).signature signature :=
  signature.mapTerms_congr _ _ (fun term member => selected.term_permutation world (supported term member))

theorem SnapshotMap.code_permutation {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} (selected : SnapshotMap program before suspension map) (world : before.world.WellFormed)
    {code : Kernel.Code} (supported : ∀ term ∈ code.terms, term.RuntimeRegionsBelow before.world.nextRegion) :
    map.code code = (selected.permutation world).code code := by
  let permutation := selected.permutation world
  have fixed : permutation.code (map.code code) = code := by
    simp only [RegionPermutation.code,Relocation.code,Kernel.Code.mapTerms_comp]
    apply code.mapTerms_eq_self
    intro term member
    change permutation.term (map.term term) = term
    rw [selected.term_permutation world (supported term member)]
    exact permutation.term_involutive term
  have equal := congrArg permutation.code fixed
  rw [permutation.code_involutive] at equal
  exact equal

/-- The actual checked instance supplies body agreement from its invocation
arguments; callers need not supply a second body-support derivation. -/
theorem SnapshotMap.instance_body_permutation {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} (inventory : Kernel.BodyInventory program)
    (selected : SnapshotMap program before suspension map) (world : before.world.WellFormed)
    {id : DeclId} {arguments : List Term} {function : Kernel.Function}
    (instantiated : Kernel.Instance program id arguments function)
    (supported : ∀ term ∈ arguments, term.RuntimeRegionsBelow before.world.nextRegion) :
    map.code function.body = (selected.permutation world).code function.body := by
  have equal := congrArg Kernel.Function.body (instantiated.relocation_permutation inventory map
    (selected.permutation world) (fun term member => selected.term_permutation world (supported term member)))
  exact equal

theorem SnapshotMap.instance_functionType {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (selected : SnapshotMap program before suspension map) (world : before.world.WellFormed)
    {id : DeclId} {arguments : List Term} {function : Kernel.Function}
    (instantiated : Kernel.Instance program id arguments function)
    (supported : ∀ term ∈ arguments, term.RuntimeRegionsBelow before.world.nextRegion)
    (typed : Typing.FunctionType program function) :
    Typing.FunctionType program (function.mapTerms map.term) := by
  rw [instantiated.relocation_permutation inventory map (selected.permutation world)
    (fun term member => selected.term_permutation world (supported term member))]
  exact typed.permute valid inventory (selected.permutation world)

end Glorious.Language.Execution
