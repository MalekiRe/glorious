import GloriousLanguage.PreparationOutcomes
import GloriousLanguage.StorageWrites

/-! Constructive ordered preparation under positive layout requests. The
only classical choice is the actual existence of an available physical extent;
all storage writes and successful handoffs are derived from their contracts. -/
namespace Glorious.Language
open Kernel

/-- Positive layout evidence is independent of the allocation lifetime. A
live target and monotone lifetime frontier suffice to retarget the request. -/
theorem AllocationRequest.retarget {program : Program} {before after : World}
    {original target : Identity} {type : Term} {layout : Layout}
    (request : AllocationRequest program before original type layout)
    (live : target ∈ after.liveRegions) (frontier : before.nextRegion ≤ after.nextRegion) :
    AllocationRequest program after target type layout :=
  ⟨live,request.type_supported.mono frontier,request.layout_valid,request.size_bound,request.layout_of⟩

theorem AllocationRequest.same_regions {program : Program} {before after : World}
    {region : Identity} {type : Term} {layout : Layout}
    (request : AllocationRequest program before region type layout)
    (regions : after.liveRegions = before.liveRegions) (frontier : after.nextRegion = before.nextRegion) :
    AllocationRequest program after region type layout :=
  request.retarget (by rw [regions]; exact request.region_live) (Nat.le_of_eq frontier.symm)

namespace Execution

theorem Protect.region_state {program : Kernel.Program} {context : Context} {before after : World}
    {source destination : Address} {authority : Authority}
    (kept : Protect program context before source authority destination after) :
    after.liveRegions = before.liveRegions ∧ after.nextRegion = before.nextRegion := by
  obtain ⟨_,_,_,⟨_,allocation⟩,moved⟩ := kept
  have regions := congrArg World.liveRegions moved.rest
  have frontier := congrArg World.nextRegion moved.rest
  cases allocation
  exact ⟨regions,frontier⟩

theorem Protect.success_or_exhausted {program : Kernel.Program} {context : Context} {before : World}
    {source : Address} {authority : Authority} {value : Value} {layout : Layout}
    (valid : before.WellFormed) (stored : before.Stores source value) (initialized : value.Initialized)
    (ready : value.MoveReady program before [source]) (permission : Permitted before authority .owned source)
    (request : AllocationRequest program.declarations before context.region value.type layout) :
    (∃ destination after, Protect program context before source authority destination after) ∨
      ProtectExhausted program context before source authority := by
  rcases request.success_or_exhausted (.temporary context.activation context.scope) true with
    ⟨destination,allocated,allocation⟩ | exhausted
  · have fresh := ready.1.supportOutside_fresh valid (Nat.le_of_eq allocation.fresh_root.1.symm)
    have extended : value.MoveReady program before [source,destination] := by
      refine ⟨ready.1,?_⟩
      intro address member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact ready.2 _ List.mem_cons_self
      · exact fresh
    have readyAfter := allocation.handoffReady valid extended
    have permittedAfter := permission.locationExtension (allocation.locationExtension valid) allocation.loans
    obtain ⟨root,selected,_⟩ := Option.bind_eq_some_iff.mp stored
    have bound := World.root_bound valid (World.root_found selected).1
    have separated : ¬ source.Overlaps destination := by
      intro overlap
      have same := overlap.1.trans allocation.fresh_root.1
      exact Nat.lt_irrefl _ (same ▸ bound)
    obtain ⟨after,moved⟩ := Transfers.exists ((allocation.read valid source).trans stored)
      initialized readyAfter permittedAfter allocation.created_vacant separated allocation.created_addressType
    exact Or.inl ⟨destination,after,value,allocated,stored,⟨layout,allocation⟩,moved⟩
  · exact Or.inr ⟨value,layout,stored,initialized,ready,permission,exhausted⟩

/-- Whole pending readiness is preserved through each constructed success.
Failure retains the same fold and its actual partial world, not a separately
chosen successful front. No successful allocation or write is a premise. -/
theorem ProtectsAttemptFor.progress {program : Kernel.Program} {context : Context}
    {before : World} {sources : List ResolvedPlace} {values : List Value} {footprint : List Address}
    (valid : before.WellFormed)
    (ready : ResidentHandoffReady program before sources values footprint)
    (coverage : ∀ source ∈ sources, source.address ∈ footprint)
    (requests : ∀ value ∈ values, ∃ layout,
      AllocationRequest program.declarations before context.region value.type layout) :
    ∃ destinations after outcome, ProtectsAttemptFor program context footprint before sources destinations after outcome := by
  induction sources generalizing before values with
  | nil => exact ⟨[],before,.complete,.nil⟩
  | cons source sources ih =>
    have snapshot := ready.1
    cases snapshot with
    | @cons _ value _ values firstStored restStored =>
      have firstReady := ready.2.1 value List.mem_cons_self
      have permission := ready.2.2.2 source List.mem_cons_self
      have clearCovered := coverage source List.mem_cons_self
      have moveReady : value.MoveReady program before [source.address] := by
        refine ⟨firstReady.2.1,?_⟩
        intro address member
        have same : address = source.address := List.mem_singleton.mp member
        subst address
        exact firstReady.2.2 source.address clearCovered
      obtain ⟨layout,request⟩ := requests value List.mem_cons_self
      rcases Protect.success_or_exhausted valid firstStored firstReady.1 moveReady permission request with
        ⟨destination,middle,kept⟩ | exhausted
      · have middleValid := kept.wellFormed valid
        have remaining : ResidentHandoffReady program middle sources values footprint := by
          refine ⟨kept.preserves_snapshot valid restStored (List.pairwise_cons.mp ready.2.2.1).1,
            ?_,(List.pairwise_cons.mp ready.2.2.1).2,?_⟩
          · intro resident member
            have old := ready.2.1 resident (List.mem_cons_of_mem _ member)
            exact ⟨old.1,kept.handoffReady valid old.2 clearCovered⟩
          · intro place member
            exact (ready.2.2.2 place (List.mem_cons_of_mem _ member)).locationExtension
              (kept.locationExtension valid) kept.loans
        have nextRequests : ∀ resident ∈ values, ∃ layout,
            AllocationRequest program.declarations middle context.region resident.type layout := by
          intro resident member
          obtain ⟨layout,request⟩ := requests resident (List.mem_cons_of_mem _ member)
          exact ⟨layout,request.same_regions kept.region_state.1 kept.region_state.2⟩
        obtain ⟨destinations,after,outcome,tail⟩ := ih middleValid remaining
          (fun place member => coverage place (List.mem_cons_of_mem _ member)) nextRequests
        exact ⟨destination :: destinations,after,outcome,.cons ⟨value :: values,ready,coverage⟩ kept tail⟩
      · exact ⟨[],before,.exhausted,.exhausted ⟨value :: values,ready,coverage⟩ exhausted⟩

end Execution
end Glorious.Language
