import GloriousLanguage.Storage
import GloriousLanguage.LayoutValidity

/-! Positive allocation requests have exactly the actual physical alternatives.
No missing static proof is interpreted as an exhausted runtime resource. -/
namespace Glorious.Language

/-- Reference storage uses the declared pointer layout, not a supplied
allocation result. The target's object-size limit remains explicit admission. -/
theorem AllocationRequest.reference {program : Program} {world : World}
    {region : Identity} {mode : Mutability} {loanRegion referent : Term}
    (target : program.input.target.Valid) (live : region ∈ world.liveRegions)
    (supported : (Term.reference mode loanRegion referent).RuntimeRegionsBelow world.nextRegion)
    (capacity : program.input.target.pointerBits / 8 ≤ program.input.target.maximumObjectBytes) :
    AllocationRequest program world region (.reference mode loanRegion referent)
      ⟨program.input.target.pointerBits / 8,program.input.target.pointerBits / 8,[],0,0,[]⟩ :=
  ⟨live,supported,target.pointer_layout,capacity,⟨default,false,.reference⟩⟩

theorem Allocates.request {program : Program} {before after : World}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) :
    AllocationRequest program before region type layout := by
  cases allocated with
  | fresh request _ => exact request

theorem Allocates.extent {program : Program} {before after : World}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) :
    ∃ base, PhysicalExtent program.input.target before layout base := by
  cases allocated with
  | fresh _ extent => exact ⟨_,extent⟩

theorem AllocationRequest.success_iff_extent {program : Program} {world : World}
    {region : Identity} {type : Term} {layout : Layout}
    (request : AllocationRequest program world region type layout) (home : Home) (mutable : Bool) :
    (∃ address after, Allocates program world home region type layout mutable address after) ↔
      ∃ base, PhysicalExtent program.input.target world layout base := by
  constructor
  · rintro ⟨_,_,allocated⟩; exact allocated.extent
  · rintro ⟨base,extent⟩; exact ⟨_,_,.fresh (base := base) request extent⟩

theorem AllocationExhausted.no_success {program : Program} {world : World}
    {region : Identity} {type : Term} {layout : Layout}
    (exhausted : AllocationExhausted program world region type layout)
    {home : Home} {mutable : Bool} {address : Address} {after : World} :
    ¬ Allocates program world home region type layout mutable address after :=
  fun allocated => exhausted.2 allocated.extent

/-- This is a semantic alternative, not an executable allocator or an
assumption of success. Failure retains the same positively admitted request. -/
theorem AllocationRequest.success_or_exhausted {program : Program} {world : World}
    {region : Identity} {type : Term} {layout : Layout}
    (request : AllocationRequest program world region type layout) (home : Home) (mutable : Bool) :
    (∃ address after, Allocates program world home region type layout mutable address after) ∨
      AllocationExhausted program world region type layout := by
  classical
  by_cases extent : ∃ base, PhysicalExtent program.input.target world layout base
  · exact Or.inl ((request.success_iff_extent home mutable).mpr extent)
  · exact Or.inr ⟨request,extent⟩

end Glorious.Language
