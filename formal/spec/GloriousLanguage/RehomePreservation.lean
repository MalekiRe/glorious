import GloriousLanguage.BorrowPreservation
import GloriousLanguage.RehomeFraming

/-! Root ownership changes retain physical storage and resident typing.
Shared by suspension capture, final replay and cancellation cleanup. -/
namespace Glorious.Language


theorem World.rehome_addressOffset {program : Program} {before : World} (select : Identity → Root → Home)
    {address : Address} {type : Term} {offset : Nat} (located : AddressOffset program before address type offset) :
    AddressOffset program { before with roots := before.roots.map (fun (id,root) =>
      (id,{ root with home := select id root })) } address type offset := by
  induction located with
  | @root id root found live =>
    exact .root (root := { root with home := select id root }) (by rw [World.rehome_get,found]; rfl) live
  | child _ field ih => exact .child ih (field.transport (by rw [World.rehome_read]))

theorem World.rehome_addressType {program : Program} {before : World} (select : Identity → Root → Home)
    {address : Address} {type : Term} (located : AddressType program before address type) :
    AddressType program { before with roots := before.roots.map (fun (id,root) =>
      (id,{ root with home := select id root })) } address type := by
  obtain ⟨offset,located⟩ := located
  exact ⟨offset,World.rehome_addressOffset select located⟩

theorem World.rehome_worldTyped {program : Kernel.Program} {before : World}
    (typed : Typing.WorldTyped program before) (select : Identity → Root → Home) :
    Typing.WorldTyped program
      { before with roots := before.roots.map (fun (id,root) => (id,{ root with home := select id root })) } := by
  let after : World :=
    { before with roots := before.roots.map (fun (id,root) => (id,{ root with home := select id root })) }
  change Typing.WorldTyped program after
  have selected : ∀ id, after.roots.get id = (before.roots.get id).map (fun root => { root with home := select id root }) :=
    World.rehome_get before select
  have origin : ∀ id root, after.roots.get id = some root →
      ∃ original, before.roots.get id = some original ∧ root = { original with home := select id original } := by
    intro id root found
    rw [selected] at found
    obtain ⟨original,found,same⟩ := Option.map_eq_some_iff.mp found
    exact ⟨original,found,same.symm⟩
  have atRoot : ∀ address, after.root address =
      (before.root address).map (fun root => { root with home := select address.root root }) :=
    World.rehome_root before select
  have reads : ∀ address, after.read address = before.read address := World.rehome_read before select
  have residents : ∀ address value, after.Resident address value ↔ before.Resident address value := by
    intro address value
    rw [World.resident_iff_stores,World.resident_iff_stores]
    exact Iff.of_eq (congrArg (fun found => found = some value) (reads address))
  have vacant : ∀ address, before.Vacant address → after.Vacant address := by
    intro address ⟨root,found,hole⟩
    exact ⟨{ root with home := select address.root root },by rw [atRoot,found]; rfl,hole⟩
  have located : ∀ address, before.Located address → after.Located address := by
    intro address location
    rcases location with ⟨value,found⟩ | hole
    · exact Or.inl ⟨value,by simpa only [World.Stores,reads] using found⟩
    · exact Or.inr (vacant address hole)
  have typedLocations : ∀ address type offset, AddressOffset program.declarations before address type offset →
      AddressOffset program.declarations after address type offset :=
    fun _ _ _ located => World.rehome_addressOffset select located
  have pointers : ∀ pointer : RawPointer, pointer.Origin before → pointer.Origin after := by
    intro pointer valid id allocation
    obtain ⟨root,found,address,bound⟩ := valid id allocation
    exact ⟨{ root with home := select id root },by rw [selected,found]; rfl,address,bound⟩
  have retained : ∀ value, Typing.ValueTyped program before value → Typing.ValueTyped program after value := by
    intro value checked
    apply checked.transport (after := after) ?_ rfl pointers
    intro id loan found live
    exact ⟨found,fun type ⟨offset,location⟩ => ⟨offset,typedLocations _ _ _ location⟩⟩
  rcases typed.1 with ⟨rootUnique,loanUnique,proofUnique,regionUnique,proofs,packs,owners,ownerUnique,
    roots,regions,bases,ranges,loans,references,overlaps,parents,locations,guards⟩
  refine ⟨⟨?_,loanUnique,proofUnique,regionUnique,?_,?_,?_,?_,?_,regions,?_,?_,?_,?_,?_,parents,?_,guards⟩,?_,?_,?_⟩
  · simpa only [after,Table.Unique,List.map_map,Function.comp_def] using rootUnique
  · intro id available found
    obtain ⟨identity,bound,brand,active,recorded⟩ := proofs id available found
    refine ⟨identity,bound,brand,?_,recorded⟩
    intro live
    obtain ⟨region,homes⟩ := active live
    refine ⟨region,?_⟩
    intro place member
    rw [atRoot]
    simpa using homes place member
  · intro address value pack resident head
    exact packs address value pack ((residents address value).mp resident) head
  · intro address value resident
    exact owners address value ((residents address value).mp resident)
  · intro first second left right a b same
    exact ownerUnique first second left right ((residents _ _).mp a) ((residents _ _).mp b) same
  · intro id root found
    obtain ⟨original,oldFound,rfl⟩ := origin id root found
    exact roots id original oldFound
  · intro id root found live
    obtain ⟨original,oldFound,rfl⟩ := origin id root found
    exact bases id original oldFound live
  · intro first second left right a b distinct liveLeft liveRight
    obtain ⟨oldLeft,oldA,rfl⟩ := origin first left a
    obtain ⟨oldRight,oldB,rfl⟩ := origin second right b
    exact ranges first second oldLeft oldRight oldA oldB distinct liveLeft liveRight
  · intro id loan found
    obtain ⟨identity,bound,active⟩ := loans id loan found
    refine ⟨identity,bound,?_⟩
    intro live
    obtain ⟨region,home⟩ := active live
    refine ⟨region,?_⟩
    rw [atRoot]
    simpa using home
  · intro address value id resident head
    exact references address value id ((residents _ _).mp resident) head
  · intro first second left right a b liveLeft liveRight overlap conflict
    exact (overlaps first second left right a b liveLeft liveRight overlap conflict).imp
      (fun ancestor => AncestorLoan.transport (before := before) (after := after) rfl ancestor)
      (fun ancestor => AncestorLoan.transport (before := before) (after := after) rfl ancestor)
  · intro id loan found live
    exact located _ (locations id loan found live)
  · intro address value resident
    exact retained value (typed.2.1 address value ((residents _ _).mp resident))
  · intro id root value found contents
    obtain ⟨original,oldFound,rfl⟩ := origin id root found
    exact typed.2.2.1 id original value oldFound contents
  · intro id root found
    obtain ⟨original,oldFound,rfl⟩ := origin id root found
    exact typed.2.2.2 id original oldFound

namespace Execution

theorem suspendRoots.worldTyped {program : Kernel.Program} {before : World} {roots : List Identity} {id : Identity}
    (typed : Typing.WorldTyped program before) : Typing.WorldTyped program (suspendRoots before roots id) := by
  rw [suspendRoots.eq_rehome]
  exact World.rehome_worldTyped typed (fun root original => if root ∈ roots then .suspended id else original.home)

theorem restoreRoots.worldTyped {program : Kernel.Program} {before : World} {homes : Table Home}
    (typed : Typing.WorldTyped program before) : Typing.WorldTyped program (restoreRoots before homes) :=
  World.rehome_worldTyped typed (fun id root => (homes.get id).getD root.home)

end Execution
end Glorious.Language
