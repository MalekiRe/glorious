import GloriousLanguage.BulkMovePreservation
import GloriousLanguage.StorageWrites

/-! Constructibility of the actual snapshot-clear-install raw move. The
snapshot and pre-world storage contracts determine successful writes; a
completed movement is never an input to progress. -/
namespace Glorious.Language

theorem ListRel.map_left {α β γ : Type} {relation : β → γ → Prop} {left : List α} {right : List γ}
    (function : α → β) (related : ListRel (fun a b => relation (function a) b) left right) :
    ListRel relation (left.map function) right := by
  induction related with
  | nil => exact .nil
  | cons head rest ih => exact .cons head ih

theorem ListRel.imp_mem {α β : Type} {first second : α → β → Prop} {left : List α} {right : List β}
    (related : ListRel first left right)
    (implies : ∀ a ∈ left, ∀ b ∈ right, first a b → second a b) : ListRel second left right := by
  induction related with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons (implies _ (by simp) _ (by simp) head)
        (ih (fun a member b present proof => implies a (by simp [member]) b (by simp [present]) proof))

theorem World.Vacant.write_disjoint {before after : World} {mutation address : Address} {value : Option Value}
    (vacant : before.Vacant address) (written : before.write mutation value = some after)
    (apart : ¬ mutation.Overlaps address) : after.Vacant address := by
  have located := World.write_located written (fun included => apart included.1.overlaps) (Or.inr vacant)
  rcases located with ⟨resident,stored⟩ | vacant
  · have absent := (World.write_disjoint written apart).trans vacant.read_none
    rw [stored] at absent
    cases absent
  · exact vacant

theorem Clears.exists {before : World} {addresses : List Address}
    (apart : addresses.Pairwise (fun first last => ¬ first.Overlaps last))
    (located : ∀ address ∈ addresses, before.Located address) : ∃ after, Clears before addresses after := by
  induction addresses generalizing before with
  | nil => exact ⟨before,.nil⟩
  | cons address addresses ih =>
      obtain ⟨middle,written⟩ := (located address (by simp)).write_exists none
      obtain ⟨after,cleared⟩ := ih (List.pairwise_cons.mp apart).2 (before := middle) (by
        intro next member
        exact World.write_located written
          (fun included => (List.pairwise_cons.mp apart).1 next member included.1.overlaps)
          (located next (by simp [member])))
      exact ⟨after,.cons written cleared⟩

namespace Memory

theorem InstallsResidents.exists {program : Program} {before : World}
    {addresses : List Address} {values : List (Option Value)}
    (apart : addresses.Pairwise (fun first last => ¬ first.Overlaps last))
    (prepared : ListRel (fun address resident => before.Vacant address ∧
      ∀ value, resident = some value → AddressType program before address value.type) addresses values) :
    ∃ after, InstallsResidents program before addresses values after := by
  induction addresses generalizing before values with
  | nil => cases prepared; exact ⟨before,.nil⟩
  | cons address addresses ih =>
      cases prepared with
      | @cons _ resident _ values head rest =>
          cases resident with
          | none =>
              obtain ⟨after,installed⟩ := ih (List.pairwise_cons.mp apart).2 rest
              exact ⟨after,.hole head.1 installed⟩
          | some value =>
              obtain ⟨middle,written⟩ := head.1.write_exists (some value)
              have pending : ListRel (fun address resident => middle.Vacant address ∧
                  ∀ value, resident = some value → AddressType program middle address value.type) addresses values := by
                apply rest.imp_mem
                intro next member resident present ready
                have separate := (List.pairwise_cons.mp apart).1 next member
                exact ⟨ready.1.write_disjoint written separate,fun value found =>
                  (World.write_address_types written (fun included => separate included.1.overlaps)).mp (ready.2 value found)⟩
              obtain ⟨after,installed⟩ := ih (List.pairwise_cons.mp apart).2 pending
              exact ⟨after,.resident head.1 (head.2 value rfl) written installed⟩

/-- A disjoint destination range receives the exact evaluated source snapshot.
Holes remain holes and nonempty subtrees retain their complete values, including
resources. The more general actual BulkMove also permits source overlap. -/
theorem BulkMove.disjoint_exists {program : RuntimeProgram} {before : World}
    {sources destinations : List ResolvedPlace} {values : List (Option Value)}
    (sourceApart : sources.Pairwise (fun first last => ¬ first.address.Overlaps last.address))
    (destinationApart : destinations.Pairwise (fun first last => ¬ first.address.Overlaps last.address))
    (apart : ∀ source ∈ sources, ∀ destination ∈ destinations, ¬ source.address.Overlaps destination.address)
    (snapshot : ListRel (fun source value => before.read source.address = value) sources values)
    (located : ∀ source ∈ sources, before.Located source.address)
    (permissions : ∀ source ∈ sources, Permitted before source.authority .owned source.address ∧
      ∀ value, before.Stores source.address value → value.MoveReady program before ((sources ++ destinations).map ResolvedPlace.address))
    (writable : ∀ destination ∈ destinations, Permitted before destination.authority .unique destination.address)
    (prepared : ListRel (fun destination resident => before.Vacant destination.address ∧
      ∀ value, resident = some value → AddressType program.declarations before destination.address value.type) destinations values) :
    ∃ after, BulkMove program before sources destinations after := by
  obtain ⟨cleared,clears⟩ := Clears.exists (List.pairwise_map.mpr sourceApart) (by
    intro address member
    obtain ⟨source,present,equal⟩ := List.mem_map.mp member
    exact equal ▸ located source present)
  have ready : ListRel (fun destination resident => cleared.Vacant destination.address ∧
      ∀ value, resident = some value → AddressType program.declarations cleared destination.address value.type) destinations values := by
    apply prepared.imp_mem
    intro destination present resident member ready
    have outside : ∀ address ∈ sources.map ResolvedPlace.address, ¬ address.ProperPrefix destination.address := by
      intro address member
      obtain ⟨source,selected,equal⟩ := List.mem_map.mp member
      exact equal ▸ (fun included => apart source selected destination present included.1.overlaps)
    exact ⟨clears.vacant ready.1 outside,fun value found => clears.address_type (ready.2 value found) outside⟩
  have readyAddresses : ListRel (fun address resident => cleared.Vacant address ∧
      ∀ value, resident = some value → AddressType program.declarations cleared address value.type)
      (destinations.map ResolvedPlace.address) values := ListRel.map_left ResolvedPlace.address ready
  obtain ⟨after,installed⟩ := InstallsResidents.exists (List.pairwise_map.mpr destinationApart) readyAddresses
  refine ⟨after,values,cleared,snapshot.length_eq.trans prepared.length_eq.symm,sourceApart,destinationApart,
    snapshot,permissions,?_,clears,installed⟩
  intro destination member
  obtain ⟨resident,present,ready⟩ := prepared.member_left member
  exact ⟨writable destination member,Or.inr ready.1⟩

end Memory
end Glorious.Language
