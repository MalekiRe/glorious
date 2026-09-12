import GloriousLanguage.AllocationFraming
import GloriousLanguage.OrderedHandoff

/-! Ordered handoff preservation follows the actual temporary allocation and
clear/install producer. The original footprint protects earlier outputs through
every later input, including their guarded references and raw-resource support. -/
namespace Glorious.Language

theorem Value.SupportFramed.trans {before middle after : World} {value : Value}
    (loans : middle.loans = before.loans) (first : value.SupportFramed before middle)
    (last : value.SupportFramed middle after) : value.SupportFramed before after := by
  intro address supported
  have middle := (Value.Support.frame loans first).mp supported
  exact ⟨(last address middle).1.trans (first address supported).1,
    (last address middle).2.trans (first address supported).2⟩

theorem Transfers.supportFramed_of_outside {program : RuntimeProgram} {before after : World}
    {authority : Authority} {source destination : Address} {value : Value}
    (moved : Transfers program before authority source destination after)
    (sourceOutside : value.SupportOutside before source)
    (destinationOutside : value.SupportOutside before destination) : value.SupportFramed before after := by
  have locations := moved.locations
  cases moved with
  | move _ _ _ _ _ _ _ clear install =>
      intro address supported
      exact ⟨(World.write_disjoint install (destinationOutside address supported)).trans
        (World.write_disjoint clear (sourceOutside address supported)),locations _⟩

theorem Transfers.nextRoot {program : RuntimeProgram} {before after : World}
    {authority : Authority} {source destination : Address}
    (moved : Transfers program before authority source destination after) :
    after.nextRoot = before.nextRoot := by
  cases moved with
  | move _ _ _ _ _ _ _ clear install =>
      obtain ⟨_,_,_,rfl⟩ := World.write_value_update clear
      obtain ⟨_,_,_,rfl⟩ := World.write_value_update install
      rfl

theorem Allocates.fresh_root {program : Program} {before after : World}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) :
    address.root = before.nextRoot ∧ after.nextRoot = before.nextRoot + 1 := by
  cases allocated
  exact ⟨rfl,rfl⟩

theorem Allocates.owner_permitted {program : Program} {before after : World}
    {home region type layout mutable address}
    (valid : before.WellFormed)
    (allocated : Allocates program before home region type layout mutable address after) :
    Permitted after .owner .owned address := by
  cases allocated
  refine ⟨⟨_,by simp [World.root,Table.get_set]; rfl⟩,?_⟩
  intro identity loan selected live overlap
  have original := valid
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,loans,_⟩ := valid
  obtain ⟨root,found⟩ := Option.isSome_iff_exists.mp ((loans identity loan selected).2.2 live).2
  have below := World.root_bound original (World.root_found found).1
  have same : before.nextRoot = loan.referent.root := overlap.1
  exact False.elim (Nat.lt_irrefl _ (same ▸ below))

namespace Execution

theorem Protect.loans {program : Kernel.Program} {context : Context} {before after : World}
    {source destination : Address} {authority : Authority}
    (kept : Protect program context before source authority destination after) :
    after.loans = before.loans := by
  obtain ⟨_,_,_,⟨_,allocated⟩,moved⟩ := kept
  exact moved.loans.trans allocated.loans

theorem Protect.fresh_root {program : Kernel.Program} {context : Context} {before after : World}
    {source destination : Address} {authority : Authority}
    (kept : Protect program context before source authority destination after) :
    destination.root = before.nextRoot ∧ after.nextRoot = before.nextRoot + 1 := by
  obtain ⟨_,_,_,⟨_,allocated⟩,moved⟩ := kept
  exact ⟨allocated.fresh_root.1,moved.nextRoot.trans allocated.fresh_root.2⟩

theorem Protect.wellFormed {program : Kernel.Program} {context : Context} {before after : World}
    {source destination : Address} {authority : Authority} (valid : before.WellFormed)
    (kept : Protect program context before source authority destination after) : after.WellFormed := by
  obtain ⟨_,_,_,⟨_,allocated⟩,moved⟩ := kept
  exact moved.wellFormed (allocated.wellFormed valid)

theorem Protect.locationExtension {program : Kernel.Program} {context : Context} {before after : World}
    {source destination : Address} {authority : Authority} (valid : before.WellFormed)
    (kept : Protect program context before source authority destination after) :
    before.LocationExtension after := by
  obtain ⟨_,_,_,⟨_,allocated⟩,moved⟩ := kept
  exact (allocated.locationExtension valid).trans (.of_locations moved.locations)

theorem Protect.supportFramed {program : Kernel.Program} {context : Context} {before after : World}
    {source destination : Address} {authority : Authority} {value : Value} {access : Access}
    (valid : before.WellFormed) (kept : Protect program context before source authority destination after)
    (ready : value.ResourcesAccessible program before access)
    (outside : value.SupportOutside before source) : value.SupportFramed before after := by
  obtain ⟨_,allocatedWorld,_,⟨_,allocated⟩,moved⟩ := kept
  have framed := allocated.supportFramed valid ready
  have fresh := ready.supportOutside_fresh valid (Nat.le_of_eq allocated.fresh_root.1.symm)
  have sourceFrame : value.SupportOutside allocatedWorld source := by
    intro address supported
    exact outside address ((Value.Support.frame allocated.loans framed).mpr supported)
  have destinationFrame : value.SupportOutside allocatedWorld destination := by
    intro address supported
    exact fresh address ((Value.Support.frame allocated.loans framed).mpr supported)
  exact framed.trans allocated.loans (moved.supportFramed_of_outside sourceFrame destinationFrame)

theorem Protect.handoffReady {program : Kernel.Program} {context : Context} {before after : World}
    {source destination : Address} {authority : Authority} {value : Value} {access : Access}
    {footprint : List Address} (valid : before.WellFormed)
    (kept : Protect program context before source authority destination after)
    (ready : value.HandoffReady program before access footprint)
    (covered : source ∈ footprint) : value.HandoffReady program after access footprint :=
  ready.frame (kept.locationExtension valid) kept.loans
    (kept.supportFramed valid ready.1 (ready.2 source covered))

theorem Protect.preserves_stored {program : Kernel.Program} {context : Context} {before after : World}
    {source destination observed : Address} {authority : Authority} {value : Value}
    (valid : before.WellFormed) (kept : Protect program context before source authority destination after)
    (stored : before.Stores observed value) (outside : ¬ source.Overlaps observed) :
    after.Stores observed value := by
  obtain ⟨_,allocatedWorld,_,⟨_,allocated⟩,moved⟩ := kept
  obtain ⟨root,selected,_⟩ := Option.bind_eq_some_iff.mp stored
  have bound := World.root_bound valid (World.root_found selected).1
  have fresh : ¬ destination.Overlaps observed := by
    intro overlap
    have same : before.nextRoot = observed.root := allocated.fresh_root.1.symm.trans overlap.1
    exact Nat.lt_irrefl _ (same ▸ bound)
  have stored : allocatedWorld.Stores observed value := (allocated.read valid observed).trans stored
  cases moved with
  | move _ _ _ _ _ _ _ clear install =>
      exact (World.write_disjoint install fresh).trans ((World.write_disjoint clear outside).trans stored)

theorem Protect.handed_off {program : Kernel.Program} {context : Context} {before after : World}
    {source destination : Address} {authority : Authority} {value : Value}
    (valid : before.WellFormed) (kept : Protect program context before source authority destination after)
    (stored : before.Stores source value) :
    after.Stores destination value ∧ value.Initialized ∧
      value.ResourcesAccessible program after .owned ∧ Permitted after .owner .owned destination := by
  obtain ⟨_,_,_,⟨_,allocated⟩,moved⟩ := kept
  obtain ⟨relocated,initialized,resources⟩ := moved.handed_off_ready ((allocated.read valid source).trans stored)
  exact ⟨relocated,initialized,resources,
    (allocated.owner_permitted valid).locationExtension (.of_locations moved.locations) moved.loans⟩

theorem ProtectsFor.wellFormed {program : Kernel.Program} {context : Context} {before after : World}
    {footprint destinations : List Address} {sources : List ResolvedPlace}
    (valid : before.WellFormed) (kept : ProtectsFor program context footprint before sources destinations after) :
    after.WellFormed := by
  induction kept using ProtectsFor.inductionOn with
  | nil => exact valid
  | cons _ first _ ih => exact ih (first.wellFormed valid)

theorem ProtectsFor.loans {program : Kernel.Program} {context : Context} {before after : World}
    {footprint destinations : List Address} {sources : List ResolvedPlace}
    (kept : ProtectsFor program context footprint before sources destinations after) :
    after.loans = before.loans := by
  induction kept using ProtectsFor.inductionOn with
  | nil => rfl
  | cons _ first _ ih => exact ih.trans first.loans

theorem ProtectsFor.locationExtension {program : Kernel.Program} {context : Context} {before after : World}
    {footprint destinations : List Address} {sources : List ResolvedPlace}
    (valid : before.WellFormed) (kept : ProtectsFor program context footprint before sources destinations after) :
    before.LocationExtension after := by
  induction kept using ProtectsFor.inductionOn with
  | nil => exact .refl _
  | cons _ first _ ih => exact (first.locationExtension valid).trans (ih (first.wellFormed valid))

theorem ProtectsFor.handoffReady {program : Kernel.Program} {context : Context} {before after : World}
    {footprint destinations : List Address} {sources : List ResolvedPlace} {value : Value} {access : Access}
    (valid : before.WellFormed) (kept : ProtectsFor program context footprint before sources destinations after)
    (ready : value.HandoffReady program before access footprint) :
    value.HandoffReady program after access footprint := by
  induction kept using ProtectsFor.inductionOn with
  | nil => exact ready
  | cons batch first _ ih =>
      exact ih (first.wellFormed valid) (first.handoffReady valid ready (batch.choose_spec.2 _ List.mem_cons_self))

theorem ProtectsFor.supportFramed {program : Kernel.Program} {context : Context} {before after : World}
    {footprint destinations : List Address} {sources : List ResolvedPlace} {value : Value} {access : Access}
    (valid : before.WellFormed) (kept : ProtectsFor program context footprint before sources destinations after)
    (ready : value.HandoffReady program before access footprint) : value.SupportFramed before after := by
  induction kept using ProtectsFor.inductionOn with
  | nil => exact fun _ _ => ⟨rfl,rfl⟩
  | cons batch first _ ih =>
      have covered := batch.choose_spec.2 _ List.mem_cons_self
      exact (first.supportFramed valid ready.1 (ready.2 _ covered)).trans first.loans
        (ih (first.wellFormed valid) (first.handoffReady valid ready covered))

theorem ProtectsFor.preserves_stored {program : Kernel.Program} {context : Context} {before after : World}
    {footprint destinations : List Address} {sources : List ResolvedPlace} {observed : Address} {value : Value}
    (valid : before.WellFormed) (kept : ProtectsFor program context footprint before sources destinations after)
    (stored : before.Stores observed value)
    (outside : ∀ source ∈ sources, ¬ source.address.Overlaps observed) : after.Stores observed value := by
  induction kept using ProtectsFor.inductionOn with
  | nil => exact stored
  | cons _ first _ ih =>
      exact ih (first.wellFormed valid) (first.preserves_stored valid stored (outside _ List.mem_cons_self))
        (fun source member => outside source (List.mem_cons_of_mem _ member))

theorem ProtectsFor.destination_bounds {program : Kernel.Program} {context : Context} {before after : World}
    {footprint destinations : List Address} {sources : List ResolvedPlace}
    (kept : ProtectsFor program context footprint before sources destinations after) :
    ∀ destination ∈ destinations, before.nextRoot ≤ destination.root := by
  induction kept using ProtectsFor.inductionOn with
  | nil => intro destination member; cases member
  | cons _ first _ ih =>
      intro destination member
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_of_eq first.fresh_root.1.symm
      · have bound := ih destination member
        rw [first.fresh_root.2] at bound
        exact Nat.le_trans (Nat.le_succ _) bound

theorem ProtectsFor.destinations_separated {program : Kernel.Program} {context : Context} {before after : World}
    {footprint destinations : List Address} {sources : List ResolvedPlace}
    (kept : ProtectsFor program context footprint before sources destinations after) :
    destinations.Pairwise (fun first last => ¬ first.Overlaps last) := by
  induction kept using ProtectsFor.inductionOn with
  | nil => exact .nil
  | cons _ first rest ih =>
      refine List.pairwise_cons.mpr ⟨?_,ih⟩
      intro destination member overlap
      have bound := rest.destination_bounds destination member
      rw [first.fresh_root.2,← first.fresh_root.1,overlap.1] at bound
      exact Nat.not_succ_le_self _ bound

theorem Protect.preserves_snapshot {program : Kernel.Program} {context : Context} {before after : World}
    {source destination : Address} {authority : Authority} {sources : List ResolvedPlace} {values : List Value}
    (valid : before.WellFormed) (kept : Protect program context before source authority destination after)
    (stored : ListRel (fun place value => before.Stores place.address value) sources values)
    (outside : ∀ place ∈ sources, ¬ source.Overlaps place.address) :
    ListRel (fun place value => after.Stores place.address value) sources values := by
  induction stored with
  | nil => exact .nil
  | cons first _ ih =>
      exact .cons (kept.preserves_stored valid first (outside _ List.mem_cons_self))
        (ih (fun place member => outside place (List.mem_cons_of_mem _ member)))

/-- Every final output is the very value read from the corresponding original
source. Its owned readiness survives the entire fold, not only its own move. -/
theorem ProtectsFor.resident_snapshot {program : Kernel.Program} {context : Context} {before after : World}
    {footprint destinations : List Address} {sources : List ResolvedPlace} {values : List Value}
    (valid : before.WellFormed) (kept : ProtectsFor program context footprint before sources destinations after)
    (stored : ListRel (fun place value => before.Stores place.address value) sources values) :
    ResidentHandoffReady program after (destinations.map (fun address => ⟨address,.owner⟩)) values footprint := by
  induction kept using ProtectsFor.inductionOn generalizing values with
  | nil =>
      cases stored
      refine ⟨.nil,?_,.nil,?_⟩
      · intro value member; cases member
      · intro source member; cases member
  | @cons before source sources destination destinations middle after batch first rest ih =>
      cases stored with
      | @cons _ value _ values firstStored restStored =>
          obtain ⟨actual,batch,covered⟩ := batch
          have same := ListRel.functional (fun _ _ _ left right => Option.some.inj (left.symm.trans right))
            batch.1 (ListRel.cons firstStored restStored)
          subst actual
          have firstReady := batch.2.1 value List.mem_cons_self
          have middleWell := first.wellFormed valid
          have restStored := Protect.preserves_snapshot valid first restStored (List.pairwise_cons.mp batch.2.2.1).1
          have restReady := ih middleWell restStored
          obtain ⟨firstStored,_,_,firstPermitted⟩ := first.handed_off valid firstStored
          have destinationOutside : ∀ place ∈ sources, ¬ place.address.Overlaps destination := by
            intro place member overlap
            obtain ⟨root,found⟩ := (batch.2.2.2 place (List.mem_cons_of_mem _ member)).root
            have bound := World.root_bound valid (World.root_found found).1
            have same : place.address.root = before.nextRoot := overlap.1.trans first.fresh_root.1
            exact Nat.lt_irrefl _ (same ▸ bound)
          have finalStored := rest.preserves_stored middleWell firstStored destinationOutside
          have finalReady := rest.handoffReady middleWell
            (first.handoffReady valid firstReady.2 (covered _ List.mem_cons_self))
          have finalPermitted := firstPermitted.locationExtension (rest.locationExtension middleWell) rest.loans
          refine ⟨.cons finalStored restReady.1,?_,?_,?_⟩
          · intro observed member
            rcases List.mem_cons.mp member with rfl | member
            · exact ⟨firstReady.1,finalReady⟩
            · exact restReady.2.1 observed member
          · exact List.pairwise_map.mpr (ProtectsFor.destinations_separated (.cons ⟨_,batch,covered⟩ first rest))
          · intro place member
            rcases List.mem_cons.mp member with rfl | member
            · exact finalPermitted
            · exact restReady.2.2.2 place member

end Execution
end Glorious.Language
