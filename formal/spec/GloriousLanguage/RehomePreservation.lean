import GloriousLanguage.BorrowPreservation
import GloriousLanguage.RehomeFraming

/-! Root ownership changes retain physical storage and resident typing.
Shared by suspension capture, final replay and cancellation cleanup. -/
namespace Glorious.Language


theorem World.rehome_stores {world : World} {select : Identity → Root → Home} {address : Address}
    {value : Value} : (world.rehome select).Stores address value ↔ world.Stores address value := by
  unfold World.Stores World.rehome
  rw [World.rehome_read]

theorem World.rehome_initialized {world : World} {select : Identity → Root → Home} {address : Address} :
    (world.rehome select).Initialized address ↔ world.Initialized address := by
  unfold World.Initialized
  exact exists_congr fun value => and_congr World.rehome_stores Iff.rfl

theorem World.rehome_resident {world : World} {select : Identity → Root → Home} {address : Address}
    {value : Value} : (world.rehome select).Resident address value ↔ world.Resident address value := by
  unfold World.rehome
  constructor
  · rintro ⟨root,whole,found,live,generation,contents,located⟩
    obtain ⟨original,originalAt,equal⟩ := Option.map_eq_some_iff.mp (by
      rw [World.rehome_get] at found; exact found)
    subst equal
    exact ⟨original,whole,originalAt,live,generation,contents,located⟩
  · rintro ⟨root,whole,found,live,generation,contents,located⟩
    exact ⟨{ root with home := select address.root root },whole,
      by rw [World.rehome_get,found]; rfl,live,generation,contents,located⟩

/-- The relative index of the reachability graph is a function of the loan table
alone, so rehoming changes no edge. -/
theorem Value.ReachableResident.rehome {before : World} {select : Identity → Root → Home}
    {value resident : Value} {authority current : Authority} {incoming access : Access} :
    value.ReachableResident before authority incoming resident current access ↔
      value.ReachableResident (before.rehome select) authority incoming resident current access := by
  constructor
  · intro reached
    induction reached with
    | resident located => exact .resident located
    | @referent carrier parent parentAuthority parentAccess loan target path resident prior reference found stored located ih =>
        exact Value.ReachableResident.referent ih reference found
          ((World.rehome_stores (world := before) (select := select)).mpr stored) located
    | @resource carrier current access binding target path resident prior member stored located ih =>
        exact Value.ReachableResident.resource ih member
          ((World.rehome_stores (world := before) (select := select)).mpr stored) located
  · intro reached
    induction reached with
    | resident located => exact .resident located
    | @referent carrier parent parentAuthority parentAccess loan target path resident prior reference found stored located ih =>
        exact Value.ReachableResident.referent ih reference found
          ((World.rehome_stores (world := before) (select := select)).mp stored) located
    | @resource carrier current access binding target path resident prior member stored located ih =>
        exact Value.ReachableResident.resource ih member
          ((World.rehome_stores (world := before) (select := select)).mp stored) located

theorem Value.ReachableReference.rehome {before : World} {select : Identity → Root → Home}
    {value : Value} {authority : Authority} {incoming : Access} {identity : Identity}
    {current : Authority} {access : Access} :
    value.ReachableReference before authority incoming identity current access ↔
      value.ReachableReference (before.rehome select) authority incoming identity current access := by
  constructor
  · rintro ⟨resident,reached,head⟩
    exact ⟨resident,(Value.ReachableResident.rehome.mp reached),head⟩
  · rintro ⟨resident,reached,head⟩
    exact ⟨resident,(Value.ReachableResident.rehome.mpr reached),head⟩

theorem Authority.Custodied.rehome {world : World} {select : Identity → Root → Home}
    {custody : ClaimCustody} (authority : Authority) (custodied : authority.Custodied world custody) :
    authority.Custodied (world.rehome select) custody := by
  induction authority with
  | owner => trivial
  | loan id => exact custodied
  | shared backing => simpa only [Authority.Custodied,World.rehome_loans] using custodied
  | guarded backing carrier ih => exact ih custodied

theorem Authority.Recorded.rehome {world : World} {select : Identity → Root → Home}
    {authority : Authority} (recorded : authority.Recorded world.loans) :
    authority.Recorded (world.rehome select).loans := by
  simpa only [World.rehome_loans] using recorded

/-- Rehoming retains allocation claims whose root is not relabelled. Roots
carried by a local, capture, suspended, static or exterior home never carried an
allocation claim, so they cannot lose one. -/
theorem AllocationClaim.rehome {before : World} {select : Identity → Root → Home} {roots : List Identity}
    (outside : ∀ id, id ∉ roots → ∀ root, select id root = root.home)
    (internal : ∀ id ∈ roots, ∀ root, before.roots.get id = some root →
      (∀ domain, root.home ≠ .allocation domain) ∧ (∀ domain, root.home ≠ .external domain))
    {authority : Authority} {address : Address} (claim : AllocationClaim before authority address) :
    AllocationClaim (before.rehome select) authority address := by
  obtain ⟨identity,loan,root,domain,parent,found,live,kind,referent,whole,selected,home,latest⟩ := claim
  have rootAt : before.roots.get address.root = some root := (World.root_found selected).1
  by_cases member : address.root ∈ roots
  · rcases home with same | same
    · exact False.elim ((internal address.root member root rootAt).1 domain same)
    · exact False.elim ((internal address.root member root rootAt).2 domain same)
  · refine ⟨identity,loan,root,domain,parent,found,live,kind,referent,whole,?_,?_,?_⟩
    · unfold World.rehome
      rw [World.rehome_root,selected]
      simp only [Option.map_some]
      rw [outside address.root member root]
    · rcases home with same | same
      · exact Or.inl same
      · exact Or.inr same
    · intro child successor found' live' kind' ancestor
      exact latest child successor found' live' kind'
        (AncestorLoan.transport (World.rehome_loans before select).symm ancestor)

theorem StorageBinding.HeldBy.rehome {before : World} {select : Identity → Root → Home} {roots : List Identity}
    (outside : ∀ id, id ∉ roots → ∀ root, select id root = root.home)
    (internal : ∀ id ∈ roots, ∀ root, before.roots.get id = some root →
      (∀ domain, root.home ≠ .allocation domain) ∧ (∀ domain, root.home ≠ .external domain))
    {owner : Identity} {binding : StorageBinding} (held : binding.HeldBy before owner) :
    binding.HeldBy (before.rehome select) owner := by
  obtain ⟨custody,resources⟩ := held
  refine ⟨Authority.Custodied.rehome _ custody,?_⟩
  rcases resources with ⟨claim,added⟩ | borrow
  · exact Or.inl ⟨AllocationClaim.rehome outside internal claim,added⟩
  · exact Or.inr (by simpa only [World.rehome_loans before select] using borrow)

theorem Value.InvariantClosed.rehome {program : RuntimeProgram} {before : World}
    {select : Identity → Root → Home} {resident : Value}
    (closed : resident.InvariantClosed program before) :
    resident.InvariantClosed program (before.rehome select) := by
  cases resident with
  | resident owner type head live fields resources =>
    dsimp only [Value.InvariantClosed] at closed ⊢
    cases type with
    | nominal identity arguments =>
        obtain ⟨data,found,shape⟩ := closed
        refine ⟨data,found,?_⟩
        cases invariant : data.invariant with
        | none => simpa only [invariant] using shape
        | some declared =>
            obtain ⟨contract,lookup,ownerAt,holds⟩ := by simpa only [invariant] using shape
            exact ⟨contract,lookup,ownerAt,contract.rehomed before select _ holds⟩
    | _ => exact closed

theorem Value.ResourcesClosed.rehome {program : RuntimeProgram} {before : World}
    {select : Identity → Root → Home} {roots : List Identity}
    (outside : ∀ id, id ∉ roots → ∀ root, select id root = root.home)
    (internal : ∀ id ∈ roots, ∀ root, before.roots.get id = some root →
      (∀ domain, root.home ≠ .allocation domain) ∧ (∀ domain, root.home ≠ .external domain))
    {value : Value} (closed : value.ResourcesClosed program before) :
    value.ResourcesClosed program (before.rehome select) := by
  intro resident authority access reached
  have prior := Value.ReachableResident.rehome.mpr reached
  obtain ⟨held,declared⟩ := closed resident authority access prior
  exact ⟨fun binding member => StorageBinding.HeldBy.rehome outside internal (held binding member),
    Value.InvariantClosed.rehome declared⟩

theorem Value.LoansRestored.rehome {program : RuntimeProgram} {before : World}
    {select : Identity → Root → Home} {roots : List Identity}
    (outside : ∀ id, id ∉ roots → ∀ root, select id root = root.home)
    (internal : ∀ id ∈ roots, ∀ root, before.roots.get id = some root →
      (∀ domain, root.home ≠ .allocation domain) ∧ (∀ domain, root.home ≠ .external domain))
    {value : Value} (restored : value.LoansRestored program before) :
    value.LoansRestored program (before.rehome select) := by
  intro identity authority access reached
  have prior := Value.ReachableReference.rehome.mpr reached
  obtain ⟨loan,found,live,initialized,closed⟩ := restored identity authority access prior
  exact ⟨loan,found,live,(World.rehome_initialized (world := before) (select := select)).mpr initialized,
    fun referent stored =>
      Value.ResourcesClosed.rehome outside internal (closed referent ((World.rehome_stores (world := before) (select := select)).mp stored))⟩

theorem World.ResourcesClosed.rehome {program : RuntimeProgram} {before : World}
    {select : Identity → Root → Home} {roots : List Identity}
    (outside : ∀ id, id ∉ roots → ∀ root, select id root = root.home)
    (internal : ∀ id ∈ roots, ∀ root, before.roots.get id = some root →
      (∀ domain, root.home ≠ .allocation domain) ∧ (∀ domain, root.home ≠ .external domain))
    {address : Address} (closed : World.ResourcesClosed program before address) :
    World.ResourcesClosed program (before.rehome select) address := by
  intro value stored
  obtain ⟨resources,restored⟩ := closed value ((World.rehome_stores (world := before) (select := select)).mp stored)
  exact ⟨Value.ResourcesClosed.rehome outside internal resources,
    Value.LoansRestored.rehome outside internal restored⟩

theorem Permitted.rehome {before : World} {select : Identity → Root → Home}
    {authority : Authority} {access : Access} {address : Address}
    (permission : Permitted before authority access address) :
    Permitted (before.rehome select) authority access address := by
  obtain ⟨root,found⟩ := permission.root
  apply permission.of_same_loans (before := before) (after := before.rehome select) rfl
  exact ⟨{ root with home := select address.root root },by
    unfold World.rehome
    rw [World.rehome_root,found]
    rfl⟩

theorem Value.ReferencesAccessible.rehome {before : World} {select : Identity → Root → Home}
    {value : Value} {authority : Authority} {incoming : Access}
    (ready : value.ReferencesAccessible before authority incoming) :
    value.ReferencesAccessible (before.rehome select) authority incoming := by
  intro identity current access reached
  obtain ⟨loan,found,live,permission⟩ := ready identity current access (Value.ReachableReference.rehome.mpr reached)
  exact ⟨loan,found,live,permission.rehome⟩

theorem Value.ResourcesAccessible.rehome {program : RuntimeProgram} {before : World}
    {select : Identity → Root → Home} {roots : List Identity}
    (outside : ∀ id, id ∉ roots → ∀ root, select id root = root.home)
    (internal : ∀ id ∈ roots, ∀ root, before.roots.get id = some root →
      (∀ domain, root.home ≠ .allocation domain) ∧ (∀ domain, root.home ≠ .external domain))
    {value : Value} {access : Access} (ready : value.ResourcesAccessible program before access) :
    value.ResourcesAccessible program (before.rehome select) access := by
  refine ⟨ready.1.rehome outside internal,ready.2.1.rehome outside internal,ready.2.2.1.rehome,?_⟩
  intro resident authority incoming reached binding member
  exact (ready.2.2.2 resident authority incoming (Value.ReachableResident.rehome.mpr reached) binding member).rehome

theorem Value.Support.rehome {before : World} {select : Identity → Root → Home}
    {value : Value} {address : Address} :
    value.Support before address ↔ value.Support (before.rehome select) address := by
  constructor
  · rintro ⟨resident,authority,access,reached,edge⟩
    exact ⟨resident,authority,access,Value.ReachableResident.rehome.mp reached,edge⟩
  · rintro ⟨resident,authority,access,reached,edge⟩
    exact ⟨resident,authority,access,Value.ReachableResident.rehome.mpr reached,edge⟩

/-- Home bookkeeping retains the whole original handoff graph. Only allocation
claims need a source-side restriction: relabelled roots were internal homes. -/
theorem Value.HandoffReady.rehome {program : RuntimeProgram} {before : World}
    {select : Identity → Root → Home} {roots : List Identity}
    (outside : ∀ id, id ∉ roots → ∀ root, select id root = root.home)
    (internal : ∀ id ∈ roots, ∀ root, before.roots.get id = some root →
      (∀ domain, root.home ≠ .allocation domain) ∧ (∀ domain, root.home ≠ .external domain))
    {value : Value} {access : Access} {footprint : List Address}
    (ready : value.HandoffReady program before access footprint) :
    value.HandoffReady program (before.rehome select) access footprint :=
  ⟨ready.1.rehome outside internal,fun source member address supported =>
    ready.2 source member address (Value.Support.rehome.mpr supported)⟩


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

theorem World.rehome_wellFormed {before : World} (valid : before.WellFormed)
    (select : Identity → Root → Home) : (before.rehome select).WellFormed := by
  let after := before.rehome select
  change after.WellFormed
  have atRoot : ∀ address, after.root address =
      (before.root address).map (fun root => { root with home := select address.root root }) :=
    World.rehome_root before select
  have residents : ∀ address value, after.Resident address value ↔ before.Resident address value :=
    fun _ _ => World.rehome_resident
  have located : ∀ address, before.Located address → after.Located address := by
    intro address location
    rcases location with ⟨value,found⟩ | ⟨root,found,hole⟩
    · exact Or.inl ⟨value,World.rehome_stores.mpr found⟩
    · exact Or.inr ⟨{ root with home := select address.root root },by rw [atRoot,found]; rfl,hole⟩
  rcases valid with ⟨rootUnique,loanUnique,proofUnique,regionUnique,proofs,packs,owners,ownerUnique,
    roots,regions,bases,ranges,loans,references,overlaps,parents,locations,guards⟩
  refine ⟨?_,loanUnique,proofUnique,regionUnique,?_,?_,?_,?_,?_,regions,?_,?_,?_,?_,?_,parents,?_,guards⟩
  · simpa only [after,World.rehome,Table.Unique,List.map_map,Function.comp_def] using rootUnique
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
    obtain ⟨original,oldFound,rfl⟩ := World.rehome_origin found
    exact roots id original oldFound
  · intro id root found live
    obtain ⟨original,oldFound,rfl⟩ := World.rehome_origin found
    exact bases id original oldFound live
  · intro first second left right a b distinct liveLeft liveRight
    obtain ⟨oldLeft,oldA,rfl⟩ := World.rehome_origin a
    obtain ⟨oldRight,oldB,rfl⟩ := World.rehome_origin b
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

theorem World.rehome_worldTyped {program : Kernel.Program} {before : World}
    (typed : Typing.WorldTyped program before) (select : Identity → Root → Home) :
    Typing.WorldTyped program
      { before with roots := before.roots.map (fun (id,root) => (id,{ root with home := select id root })) } := by
  change Typing.WorldTyped program (before.rehome select)
  refine ⟨World.rehome_wellFormed typed.1 select,?_,?_,?_,?_⟩
  · intro address value resident
    apply (typed.2.1 address value (World.rehome_resident.mp resident)).transport
      (after := before.rehome select) ?_ rfl ?_
    · intro id loan found _
      exact ⟨found,fun _ located => World.rehome_addressType select located⟩
    · intro pointer origin id allocation
      obtain ⟨root,found,address,bound⟩ := origin id allocation
      exact ⟨{ root with home := select id root },by
        unfold World.rehome
        rw [World.rehome_get,found]
        rfl,address,bound⟩
  · intro id root value found contents
    obtain ⟨original,oldFound,rfl⟩ := World.rehome_origin found
    exact typed.2.2.1 id original value oldFound contents
  · intro id root found
    obtain ⟨original,oldFound,rfl⟩ := World.rehome_origin found
    exact typed.2.2.2.1 id original oldFound
  · intro id root found live
    obtain ⟨original,oldFound,rfl⟩ := World.rehome_origin found
    exact typed.2.2.2.2 id original oldFound live

namespace Execution

theorem restoreRoots.wellFormed {before : World} {homes : Table Home} (valid : before.WellFormed) :
    (restoreRoots before homes).WellFormed := by
  rw [restoreRoots.eq_rehome]
  exact World.rehome_wellFormed valid _

theorem suspendRoots.worldTyped {program : Kernel.Program} {before : World} {roots : List Identity} {id : Identity}
    (typed : Typing.WorldTyped program before) : Typing.WorldTyped program (suspendRoots before roots id) := by
  rw [suspendRoots.eq_rehome]
  exact World.rehome_worldTyped typed (fun root original => if root ∈ roots then .suspended id else original.home)

theorem restoreRoots.worldTyped {program : Kernel.Program} {before : World} {homes : Table Home}
    (typed : Typing.WorldTyped program before) : Typing.WorldTyped program (restoreRoots before homes) :=
  World.rehome_worldTyped typed (fun id root => (homes.get id).getD root.home)

end Execution
end Glorious.Language
