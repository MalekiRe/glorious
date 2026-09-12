import GloriousLanguage.SnapshotPlacementConstruction

/-! Constructive physical snapshot replay. The captured identity inventory is
built from the actual suspension, placed physically in order, and assembled into
the real `Relocation`, `SnapshotMap` and `CopiesSnapshot` of the machine's copy
replay. The ordered placement either completes, giving a real copied state, or
reports the genuine exhaustion of the next selected root. The source admission
(`Replayable`, control replay, snapshot frames, live renamed regions and scoped
external referents) is consumed as the suspend-time product; nothing here
assumes a successful copy, a successful extent or a successful handoff. -/
namespace Glorious.Language.Execution

open Kernel

/-- The source-side admission a suspension carries into replay: replayable
captured roots, replayable control authorities, snapshot frames, live renamed
regions, and the scoping law that unchanged external storage cannot acquire a
renamed local type. These are the persisted components of the suspend-time
`SuspendPermission`; they are not derived from any post-state. -/
structure Suspension.PhysicalAdmission (program : Kernel.Program) (before : State) (suspension : Suspension) : Prop where
  replayable : Replayable program before.world suspension.roots
  controlReplayable : ∀ authority ∈ suspension.controlAuthoritySupport, authority.Replayable before.world
  frames : ∀ frame ∈ suspension.frames, SnapshotFrame frame
  regionsLive : ∀ region ∈ (suspension.inventory program before []).regions, region ∈ before.world.liveRegions
  externalScoped : ∀ address value id loan,
    address.root ∈ suspension.roots → before.world.Resident address value → value.head = .reference id →
    before.world.loans.get id = some loan → loan.referent.root ∉ suspension.roots →
    ∀ type, AddressType program.declarations before.world loan.referent type →
    ∀ region ∈ (suspension.inventory program before []).regions, ¬ Occurs (.runtimeRegion region) type

/-- The captured roots recorded by a live suspension are live in the source
world, so they have real physical extents to copy. -/
theorem Suspension.roots_present {before : State} {id : Identity} {suspension : Suspension}
    (formed : before.SuspensionsWellFormed) (found : before.resumptions.get id = some suspension)
    (active : suspension.active = true) :
    ∀ rootId ∈ suspension.roots, ∃ root, Table.get before.world.roots rootId = some root := by
  intro rootId member
  obtain ⟨root,selected,_,_⟩ := (formed.active id suspension found active rootId).mp member
  exact ⟨root,selected⟩

/-- The captured inventory is a real storage plan: the physical placement
supplies the extent fields, and the inventory's membership laws supply the rest
against the actual captured authorities. -/
theorem Suspension.inventory_storagePlan {program : Kernel.Program} {before : State}
    {suspension : Suspension} {table : Table Nat}
    (well : before.world.WellFormed)
    (physical : SnapshotPhysical program.declarations before.world suspension.roots table)
    (liveRegions : ∀ region ∈ (suspension.inventory program before table).regions,
      region ∈ before.world.liveRegions) :
    Relocation.StoragePlan program.declarations before.world suspension.controlAuthoritySupport
      (suspension.inventory program before table) := by
  have members : ∀ id, id ∈ (suspension.inventory program before table).roots ↔ id ∈ suspension.roots :=
    fun id => by rw [Suspension.inventory_roots]
  refine
    { rootBase := rfl
      ownerBase := rfl
      loanBase := rfl
      regionBase := rfl
      owners := fun id => Suspension.inventory_owners (well := well) (id := id)
      loans := fun id => Suspension.inventory_loans (well := well) (id := id)
      liveRegions := liveRegions
      physicalUnique := physical.unique
      physicalRoots := physical.keys
      physical := ?_
      disjoint := ?_ }
  · intro id root member found
    exact physical.physical ((members id).mp member) found
  · intro a b left right x y memberA memberB different leftAt rightAt firstAt secondAt
    exact physical.separated a b left right x y ((members a).mp memberA) ((members b).mp memberB)
      different leftAt rightAt firstAt secondAt

/-- The captured inventory is the machine's snapshot map: the storage plan plus
the roots, base counters, region and frame-role inventories, and the external
scoping law of the admission. -/
theorem Suspension.inventory_snapshotMap {program : Kernel.Program} {before : State}
    {suspension : Suspension} {table : Table Nat}
    (well : before.world.WellFormed)
    (physical : SnapshotPhysical program.declarations before.world suspension.roots table)
    (liveRegions : ∀ region ∈ (suspension.inventory program before table).regions,
      region ∈ before.world.liveRegions)
    (externalFacts : ∀ address value id loan,
      address.root ∈ suspension.roots → before.world.Resident address value → value.head = .reference id →
      before.world.loans.get id = some loan → loan.referent.root ∉ suspension.roots →
      ∀ type, AddressType program.declarations before.world loan.referent type →
      ∀ region ∈ (suspension.inventory program before table).regions, ¬ Occurs (.runtimeRegion region) type) :
    SnapshotMap program before suspension (suspension.inventory program before table) :=
  { toStoragePlan := suspension.inventory_storagePlan well physical liveRegions
    roots := Suspension.inventory_roots
    activationBase := rfl
    handlerBase := rfl
    scopeBase := rfl
    regions := by
      intro id
      rw [Suspension.inventory_regions,Suspension.inventory_roots]
      exact Iff.rfl
    externalReferentsScoped := externalFacts
    activations := fun id => Suspension.inventory_activations (id := id)
    scopes := fun id => Suspension.inventory_scopes (id := id)
    handlers := fun id => Suspension.inventory_handlers (id := id) }

/-- The actual copy replay product of one live suspension, or the genuine
physical exhaustion of its ordered placement. In the successful case the map is
the captured inventory of the real suspension and the copied state is exactly
`map.copyWorld` of the source world with the saved homes; no successful extent,
copy or handoff is assumed. -/
theorem Suspension.copiesSnapshot_or_blocked {program : Kernel.Program} {before : State}
    {id : Identity} {suspension : Suspension}
    (well : before.world.WellFormed) (formed : before.SuspensionsWellFormed)
    (found : before.resumptions.get id = some suspension) (active : suspension.active = true)
    (admission : suspension.PhysicalAdmission program before) :
    (∃ (table : Table Nat) (copied : State),
      copied = { before with
        world := (suspension.inventory program before table).copyWorld before.world suspension.homes
        nextActivation := (suspension.inventory program before table).activationBase + before.nextActivation
        nextHandler := (suspension.inventory program before table).handlerBase + before.nextHandler } ∧
      CopiesSnapshot program before suspension (suspension.inventory program before table) copied) ∨
      SnapshotBlocked program.declarations before.world suspension.roots := by
  have origin := formed.origin id suspension found
  rcases placement_fold (suspension.roots_present formed found active) origin.roots with placed | blocked
  · obtain ⟨table,physical⟩ := placed
    have liveRegions : ∀ region ∈ (suspension.inventory program before table).regions,
        region ∈ before.world.liveRegions := by
      intro region member
      exact admission.regionsLive region (by simpa only [Suspension.inventory] using member)
    have externalFacts : ∀ address value id' loan,
        address.root ∈ suspension.roots → before.world.Resident address value → value.head = .reference id' →
        before.world.loans.get id' = some loan → loan.referent.root ∉ suspension.roots →
        ∀ type, AddressType program.declarations before.world loan.referent type →
        ∀ region ∈ (suspension.inventory program before table).regions,
          ¬ Occurs (.runtimeRegion region) type := by
      intro address value id' loan resident head selected outside type typed region member
      exact admission.externalScoped address value id' loan resident head selected outside type typed region
        (by simpa only [Suspension.inventory] using member)
    refine Or.inl ⟨table,_,rfl,?_⟩
    exact
      { replayable := admission.replayable
        controlReplayable := admission.controlReplayable
        frames := admission.frames
        relocation := suspension.inventory_snapshotMap well physical liveRegions externalFacts
        roots := by rw [Suspension.inventory_roots]; exact origin.roots
        owners := Suspension.inventory_owners_nodup
        loans := Suspension.inventory_loans_nodup
        regions := Suspension.inventory_regions_nodup
        activations := Suspension.inventory_activations_nodup
        scopes := Suspension.inventory_scopes_nodup
        handlers := Suspension.inventory_handlers_nodup
        result := rfl }
  · exact Or.inr blocked

end Glorious.Language.Execution
