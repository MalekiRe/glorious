import GloriousLanguage.BorrowPreservation

/-! Root ownership changes retain physical storage and resident typing.
Shared by suspension capture, final replay and cancellation cleanup. -/
namespace Glorious.Language


theorem Table.get_map_keyed {α β : Type} (table : Table α) (f : Identity → α → β) (id : Identity) :
    Table.get (table.map (fun (key,value) => (key,f key value))) id = (table.get id).map (f id) := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨key,value⟩ := entry
    by_cases same : key = id
    · simp [Table.get,same]
    · simpa only [List.map_cons,Table.get,List.find?_cons,beq_eq_false_iff_ne.mpr same,
        Bool.false_eq_true,↓reduceIte,Option.map_map] using ih

theorem World.rehome_worldTyped {program : Kernel.Program} {before : World}
    (typed : Typing.WorldTyped program before) (select : Identity → Root → Home) :
    Typing.WorldTyped program
      { before with roots := before.roots.map (fun (id,root) => (id,{ root with home := select id root })) } := by
  let after : World :=
    { before with roots := before.roots.map (fun (id,root) => (id,{ root with home := select id root })) }
  change Typing.WorldTyped program after
  have selected : ∀ id, after.roots.get id = (before.roots.get id).map (fun root => { root with home := select id root }) :=
    fun id => Table.get_map_keyed before.roots (fun id (root : Root) => { root with home := select id root }) id
  have origin : ∀ id root, after.roots.get id = some root →
      ∃ original, before.roots.get id = some original ∧ root = { original with home := select id original } := by
    intro id root found
    rw [selected] at found
    obtain ⟨original,found,same⟩ := Option.map_eq_some_iff.mp found
    exact ⟨original,found,same.symm⟩
  have atRoot : ∀ address, after.root address =
      (before.root address).map (fun root => { root with home := select address.root root }) := by
    intro address
    unfold World.root
    rw [selected]
    cases before.roots.get address.root with
    | none => rfl
    | some root =>
      dsimp
      split <;> rfl
  have reads : ∀ address, after.read address = before.read address := by
    intro address
    unfold World.read
    rw [atRoot]
    cases before.root address <;> rfl
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
      AddressOffset program.declarations after address type offset := by
    intro address type offset location
    induction location with
    | @root id root found live =>
      have found : after.roots.get id = some { root with home := select id root } := by rw [selected,found]; rfl
      exact .root (root := { root with home := select id root }) found live
    | child _ field ih => exact .child ih (field.transport (by rw [reads]))
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
    roots,regions,bases,ranges,loans,references,overlaps,parents,locations⟩
  refine ⟨⟨?_,loanUnique,proofUnique,regionUnique,?_,?_,?_,?_,?_,regions,?_,?_,?_,?_,?_,parents,?_⟩,?_,?_,?_⟩
  · simpa only [after,Table.Unique,List.map_map,Function.comp_def] using rootUnique
  · intro id available found
    obtain ⟨identity,bound,brand,active⟩ := proofs id available found
    refine ⟨identity,bound,brand,?_⟩
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
  have result := World.rehome_worldTyped typed (fun root original => if root ∈ roots then .suspended id else original.home)
  have same : (before.roots.map (fun (key,root) =>
      (key,{ root with home := if key ∈ roots then .suspended id else root.home }))) =
      before.roots.map (fun (key,root) => (key,if key ∈ roots then { root with home := .suspended id } else root)) := by
    apply List.map_congr_left
    intro entry member
    obtain ⟨key,root⟩ := entry
    dsimp
    split <;> rfl
  simpa only [suspendRoots,same] using result

theorem restoreRoots.worldTyped {program : Kernel.Program} {before : World} {homes : Table Home}
    (typed : Typing.WorldTyped program before) : Typing.WorldTyped program (restoreRoots before homes) :=
  World.rehome_worldTyped typed (fun id root => (homes.get id).getD root.home)

end Execution
end Glorious.Language
