import GloriousLanguage.BufferReallocationProgress
import GloriousLanguage.UnitStorageConstruction

/-! Authenticated empty-buffer admission constructs the actual release and
unit-result primitive. Claim discharge and region closure are conclusions of
their shared before-world readiness, never supplied completed transitions. -/
namespace Glorious.Language.Execution

open Memory

theorem PrimitiveStep.release_typed_progress {program : Kernel.Program} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding}
    {pointerAddress allocation : ResolvedPlace} {pointer : RawPointer} {value : Value}
    {domain : Identity} {next : Kernel.Code}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding [] [pointerAddress] next)
    (identity : binding.primitive = some .release) (domainBound : binding.domain = some domain)
    (pointerAt : PointerAt before.world pointerAddress pointer)
    (resource : Kernel.ResolvesResource before.world context.environment (.activation context.activation) allocation)
    (buffer : BufferAt before.world allocation pointer domain value)
    (shell : value.shellLive = false) (resources : value.resources = [])
    (holes : ∀ field ∈ value.fields, field = none)
    (ready : ReleasesStorageClaimsReady before.world allocation)
    (unreserved : ∀ id available, before.world.availability.get id = some available → available.active = true →
      ∀ place ∈ available.reserved, place.address.root ≠ allocation.address.root)
    (regional : ∀ root, before.world.root allocation.address = some root → BufferRegionReady before.world allocation root.region)
    (destinationType : DestinationType before.world destination .unit) :
    ∃ after, PrimitiveStep program before none after ∧ Typing.WorldTyped program after.world ∧
      ∃ result, after.world.Stores destination result ∧ Typing.ValueTyped program after.world result ∧
        result.type = .unit ∧ result.head = .unit ∧ after.task = .run context next := by
  obtain ⟨released,release⟩ := ReleasesBuffer.exists buffer shell resources holes ready unreserved regional
  obtain ⟨after,stored⟩ := StoresUnit.exists (program := program) (release.destinationType destinationType)
  have afterTyped := stored.worldTyped valid inventory (release.worldTyped typed)
  obtain ⟨result,found,resultTyped,type,head⟩ := stored.typed_result
  exact ⟨_,.release task identity domainBound pointerAt resource release stored,afterTyped,
    result,found,resultTyped,type,head,rfl⟩

theorem Step.release_typed_progress {program : Kernel.Program} {host : Foreign.Model} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding}
    {pointerAddress allocation : ResolvedPlace} {pointer : RawPointer} {value : Value}
    {domain : Identity} {next : Kernel.Code}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding [] [pointerAddress] next)
    (identity : binding.primitive = some .release) (domainBound : binding.domain = some domain)
    (pointerAt : PointerAt before.world pointerAddress pointer)
    (resource : Kernel.ResolvesResource before.world context.environment (.activation context.activation) allocation)
    (buffer : BufferAt before.world allocation pointer domain value)
    (shell : value.shellLive = false) (resources : value.resources = [])
    (holes : ∀ field ∈ value.fields, field = none)
    (ready : ReleasesStorageClaimsReady before.world allocation)
    (unreserved : ∀ id available, before.world.availability.get id = some available → available.active = true →
      ∀ place ∈ available.reserved, place.address.root ≠ allocation.address.root)
    (regional : ∀ root, before.world.root allocation.address = some root → BufferRegionReady before.world allocation root.region)
    (destinationType : DestinationType before.world destination .unit) :
    ∃ after, Step program host before none after ∧ Typing.WorldTyped program after.world ∧
      ∃ result, after.world.Stores destination result ∧ Typing.ValueTyped program after.world result ∧
        result.type = .unit ∧ result.head = .unit ∧ after.task = .run context next := by
  obtain ⟨after,stepped,afterTyped,result⟩ := PrimitiveStep.release_typed_progress valid inventory typed
    task identity domainBound pointerAt resource buffer shell resources holes ready unreserved regional destinationType
  exact ⟨after,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl stepped)))),afterTyped,result⟩

end Glorious.Language.Execution
