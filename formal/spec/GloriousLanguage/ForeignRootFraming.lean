import GloriousLanguage.ForeignEvolution

/-! Exact root framing from the existing mutation producers. Vacant private
slots are included: the absence of a resident does not authorize installing
one, retiring the slot or changing its home, generation or lifetime. -/
namespace Glorious.Language

open Kernel Execution Memory

theorem World.write_roots_other {before after : World} {address : Address} {value : Option Value} {id : Identity}
    (written : before.write address value = some after) (outside : id ≠ address.root) :
    after.roots.get id = before.roots.get id := by
  obtain ⟨root,value,_,rfl⟩ := World.write_value_update written
  exact Table.get_set_other _ _ _ _ outside

theorem Allocates.roots_other {program : Program} {before after : World}
    {home region type layout mutable address} {id : Identity}
    (allocated : Allocates program before home region type layout mutable address after) (bound : id < before.nextRoot) :
    after.roots.get id = before.roots.get id := by
  cases allocated
  exact Table.get_set_other _ _ _ _ (Nat.ne_of_lt bound)

theorem Clears.roots_other {before after : World} {addresses : List Address} {id : Identity}
    (cleared : Clears before addresses after) (outside : ∀ address ∈ addresses, id ≠ address.root) :
    after.roots.get id = before.roots.get id := by
  induction cleared with
  | nil => rfl
  | cons written _ ih =>
    exact (ih (fun _ member => outside _ (List.mem_cons_of_mem _ member))).trans
      (World.write_roots_other written (outside _ List.mem_cons_self))

theorem Transfers.roots_other {program : Program} {before after : World} {authority source destination} {id : Identity}
    (moved : Transfers program before authority source destination after)
    (sourceOutside : id ≠ source.root) (destinationOutside : id ≠ destination.root) :
    after.roots.get id = before.roots.get id := by
  cases moved with
  | move _ _ _ _ _ _ cleared installed =>
    exact (World.write_roots_other installed destinationOutside).trans (World.write_roots_other cleared sourceOutside)

theorem Copies.roots_other {program : Program} {before after : World} {authority source destination} {id : Identity}
    (copied : Copies program before authority source destination after) (outside : id ≠ destination.root) :
    after.roots.get id = before.roots.get id := by
  cases copied with
  | copy _ _ _ _ _ _ written => have framed := World.write_roots_other written outside; exact framed

theorem Acquires.roots_other {program : Program} {before after : World} {authority force source destination} {id : Identity}
    (acquired : Acquires program before authority force source destination after)
    (sourceOutside : id ≠ source.root) (destinationOutside : id ≠ destination.root) :
    after.roots.get id = before.roots.get id := by
  cases acquired with
  | explicitMove moved => exact moved.roots_other sourceOutside destinationOutside
  | copy copied => exact copied.roots_other destinationOutside
  | move _ _ _ moved => exact moved.roots_other sourceOutside destinationOutside

theorem NewValue.roots_other {program : Program} {before after : World} {destination type head sources} {id : Identity}
    (constructed : NewValue program before destination type head sources after)
    (destinationOutside : id ≠ destination.root) (sourcesOutside : ∀ source ∈ sources, id ≠ source.address.root) :
    after.roots.get id = before.roots.get id := by
  cases constructed with
  | construct _ _ _ _ _ _ cleared written =>
    refine (World.write_roots_other written destinationOutside).trans (cleared.roots_other ?_)
    intro address member
    obtain ⟨source,present,rfl⟩ := List.mem_map.mp member
    exact sourcesOutside source present

theorem FormsLoan.roots_other {program : Program} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination} {id : Identity}
    (borrowed : FormsLoan program purpose before authority mode region referent destination after)
    (outside : id ≠ destination.root) : after.roots.get id = before.roots.get id := by
  cases borrowed with
  | borrow _ _ _ _ _ _ _ _ _ written => have framed := World.write_roots_other written outside; exact framed

theorem Memory.InstallsResidents.roots_other {program : Program} {before after : World}
    {addresses : List Address} {values : List (Option Value)} {id : Identity}
    (installed : InstallsResidents program before addresses values after)
    (outside : ∀ address ∈ addresses, id ≠ address.root) : after.roots.get id = before.roots.get id := by
  induction installed with
  | nil => rfl
  | hole _ _ ih => exact ih (fun _ member => outside _ (List.mem_cons_of_mem _ member))
  | resident _ _ written _ ih =>
    exact (ih (fun _ member => outside _ (List.mem_cons_of_mem _ member))).trans
      (World.write_roots_other written (outside _ List.mem_cons_self))

theorem Memory.BulkMove.roots_other {program : Program} {before after : World} {sources destinations} {id : Identity}
    (moved : BulkMove program before sources destinations after)
    (sourcesOutside : ∀ address ∈ sources, id ≠ address.root)
    (destinationsOutside : ∀ address ∈ destinations, id ≠ address.root) : after.roots.get id = before.roots.get id := by
  obtain ⟨_,_,_,_,_,_,_,_,cleared,installed⟩ := moved
  exact (installed.roots_other destinationsOutside).trans (cleared.roots_other sourcesOutside)

theorem Memory.AllocatesBuffer.roots_other {program : Program} {before after : World}
    {domain element count base pointer} {id : Identity}
    (allocated : AllocatesBuffer program before domain element count base pointer after) (bound : id < before.nextRoot) :
    after.roots.get id = before.roots.get id := by
  cases allocated
  exact Table.get_set_other _ _ _ _ (Nat.ne_of_lt bound)

namespace Foreign

/-- Allocation/external objects can be explicitly shared with a host.
Internal logical homes require an actual source handoff instead. -/
def InternalHome (root : Root) : Prop :=
  ∀ domain, root.home ≠ .allocation domain ∧ root.home ≠ .external domain

theorem InternalHome.temporary {root : Root} {activation scope : Identity}
    (home : root.home = .temporary activation scope) : InternalHome root := by
  intro domain
  simp [home]

theorem InternalHome.no_raw {program : Language.Program} {world : World} {id : Identity} {root : Root}
    (selected : world.roots.get id = some root) (internalHome : InternalHome root)
    {pointer : RawPointer} {address : Address} {type : Term}
    (points : PointsTo program world pointer address type) : address.root ≠ id := by
  intro same
  obtain ⟨other,_,found,_,_,domain,_,home⟩ := points.2.2.2
  have identity := Option.some.inj ((World.root_found found).1.symm.trans (same ▸ selected))
  subst other
  exact home.elim (internalHome domain).1 (internalHome domain).2

end Foreign

theorem World.HomeExtension.internal_root {before after : World} {id : Identity} {root : Root}
    (changed : before.HomeExtension after) (bound : id < before.nextRoot)
    (selected : before.roots.get id = some root) (internalHome : Foreign.InternalHome root) :
    ∃ current, after.roots.get id = some current ∧ Foreign.InternalHome current := by
  have homes := changed.homes id bound
  rw [selected] at homes
  obtain ⟨current,found,home⟩ := Option.map_eq_some_iff.mp homes
  exact ⟨current,found,fun domain => by simpa only [home] using internalHome domain⟩

theorem Memory.ReleasesBuffer.avoids_internal {program : Program} {before after : World}
    {pointer : RawPointer} {domain allocation id : Identity} {root : Root}
    (released : ReleasesBuffer program before pointer domain after) (selected : before.roots.get id = some root)
    (internalHome : Foreign.InternalHome root) (origin : pointer.allocation = some allocation) : allocation ≠ id := by
  cases released with
  | release allocated _ _ found _ home _ _ _ _ _ _ _ _ _ =>
    have same := Option.some.inj (origin.symm.trans allocated)
    subst allocation
    intro same
    have identity := Option.some.inj (found.symm.trans (same ▸ selected))
    subst root
    exact (internalHome domain).1 home

theorem Memory.ReleasesBuffer.roots_other {program : Program} {before after : World}
    {pointer : RawPointer} {domain allocation id : Identity}
    (released : ReleasesBuffer program before pointer domain after)
    (origin : pointer.allocation = some allocation) (outside : id ≠ allocation) :
    after.roots.get id = before.roots.get id := by
  cases released with
  | release allocated _ _ _ _ _ _ _ _ _ _ _ written retired ended =>
    have same := Option.some.inj (origin.symm.trans allocated)
    subst allocation
    rcases ended with ⟨_,_,_,rfl⟩
    exact (retired.roots_other outside).trans (World.write_roots_other written outside)

theorem Memory.ReallocatesBuffer.private_root {program : Program} {before after : World}
    {old domain element count base result} {id : Identity} {root : Root}
    (reallocated : ReallocatesBuffer program before old domain element count base result after)
    (bound : id < before.nextRoot) (selected : before.roots.get id = some root) (internalHome : Foreign.InternalHome root) :
    after.roots.get id = before.roots.get id := by
  obtain ⟨oldId,oldRoot,value,allocated,newId,moved,oldCount,oldOrigin,_,_,_,_,_,_,_,allocation,newOrigin,move,release⟩ := reallocated
  obtain ⟨current,currentAt,currentInternal⟩ :=
    (allocation.authorityStable.homes.trans move.authorityStable.homes).internal_root bound selected internalHome
  have oldOutside := (release.avoids_internal currentAt currentInternal oldOrigin).symm
  have newOutside : id ≠ newId := by
    cases allocation
    simp only [Option.some.injEq] at newOrigin
    exact newOrigin ▸ Nat.ne_of_lt bound
  have slots (address : Address) (outside : id ≠ address.root) :
      ∀ slot ∈ Slots address 0 oldCount, id ≠ slot.root := by
    intro slot member
    obtain ⟨index,_,rfl⟩ := List.mem_map.mp member
    exact outside
  exact (release.roots_other oldOrigin oldOutside).trans
    ((move.roots_other (slots _ oldOutside) (slots _ newOutside)).trans (allocation.roots_other bound))

end Glorious.Language
