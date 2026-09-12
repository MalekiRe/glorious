import GloriousLanguage.SnapshotWorldTyping

/-! The actual finite snapshot action agrees with its permutation extension
through supported continuation signatures and bodies. -/
namespace Glorious.Language.Execution

theorem SnapshotMap.signature_permutation {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} (selected : SnapshotMap program before suspension map) (world : before.world.WellFormed)
    {signature : Signature} (supported : ∀ term ∈ signature.terms, term.RuntimeRegionsBelow before.world.nextRegion) :
    map.signature signature = (selected.permutation world).signature signature :=
  signature.mapTerms_congr _ _ (fun term member => selected.term_permutation world (supported term member))

end Glorious.Language.Execution
