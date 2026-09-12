import GloriousLanguage.Storage

/-! Positive allocation requests have exactly the actual physical alternatives.
No missing static proof is interpreted as an exhausted runtime resource. -/
namespace Glorious.Language

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
