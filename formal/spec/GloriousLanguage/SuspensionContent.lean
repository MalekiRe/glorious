import GloriousLanguage.SuspensionAdmission
import GloriousLanguage.RehomeFraming
import GloriousLanguage.ReferenceTransferPreservation

/-! Captured content is a real product of the actual capture, replay and
cancellation storage operations. Those operations relabel the homes of the
roots they own while leaving every read, every loan row and every resident
value unchanged. This module derives that frame for the source admission of
replay (`Suspensible`, `Replayable`, `Cancelable` and the control authorities),
so the admission established at the operation boundary is retained by the
storage transitions the machine really performs instead of being re-assumed at
replay. -/
namespace Glorious.Language

open Kernel

/-- Relabel the home of every root while leaving values, loans and reads of the
world untouched. `suspendRoots` and `restoreRoots` are both instances; no second
storage inventory is introduced. -/
def World.rehome (world : World) (select : Identity → Root → Home) : World :=
  { world with roots := world.roots.map (fun (key,root) => (key,{ root with home := select key root })) }

theorem World.rehome_loans (world : World) (select : Identity → Root → Home) :
    (world.rehome select).loans = world.loans := rfl

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
        have view := Authority.referenceView_same_loans (World.rehome_loans before select)
          parentAuthority parent (ReferenceAccess parentAccess loan.mode)
        simpa only [view] using
          Value.ReachableResident.referent ih reference found
            ((World.rehome_stores (world := before) (select := select)).mpr stored) located
    | @resource carrier current access binding target path resident prior member stored located ih =>
        have view := Authority.resourceView_same_loans (World.rehome_loans before select)
          current binding access
        simpa only [view] using
          Value.ReachableResident.resource ih member
            ((World.rehome_stores (world := before) (select := select)).mpr stored) located
  · intro reached
    induction reached with
    | resident located => exact .resident located
    | @referent carrier parent parentAuthority parentAccess loan target path resident prior reference found stored located ih =>
        have view := Authority.referenceView_same_loans (World.rehome_loans before select)
          parentAuthority parent (ReferenceAccess parentAccess loan.mode)
        simpa only [view] using
          Value.ReachableResident.referent ih reference found
            ((World.rehome_stores (world := before) (select := select)).mp stored) located
    | @resource carrier current access binding target path resident prior member stored located ih =>
        have view := Authority.resourceView_same_loans (World.rehome_loans before select)
          current binding access
        simpa only [view] using
          Value.ReachableResident.resource ih member
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
theorem AncestorLoan.transport_rehome {before : World} {select : Identity → Root → Home}
    {ancestor child : Identity} (loans : (before.rehome select).loans = before.loans)
    (related : AncestorLoan (before.rehome select) ancestor child) : AncestorLoan before ancestor child := by
  induction related with
  | refl => exact .refl
  | parent found parent _ ih => exact .parent (by simpa only [loans] using found) parent ih

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
        (AncestorLoan.transport_rehome (World.rehome_loans before select).symm ancestor)

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

theorem Suspensible.rehome {program : RuntimeProgram} {before : World} {select : Identity → Root → Home}
    {roots : List Identity}
    (outside : ∀ id, id ∉ roots → ∀ root, select id root = root.home)
    (internal : ∀ id ∈ roots, ∀ root, before.roots.get id = some root →
      (∀ domain, root.home ≠ .allocation domain) ∧ (∀ domain, root.home ≠ .external domain))
    {wanted : List Identity} (suspensible : Suspensible program before wanted) :
    Suspensible program (before.rehome select) wanted := by
  constructor
  · intro id loan found live kind touched
    have foundBefore : before.loans.get id = some loan := by simpa only [World.rehome_loans] using found
    have touchedBefore : loan.referent.root ∈ wanted ∨
        ∃ address value, address.root ∈ wanted ∧ before.Resident address value ∧ value.head = .reference id := by
      rcases touched with member | ⟨address,value,member,resident,head⟩
      · exact Or.inl member
      · exact Or.inr ⟨address,value,member,(World.rehome_resident (world := before) (select := select)).mp resident,head⟩
    obtain ⟨initialized,closed⟩ := suspensible.1 id loan foundBefore live kind touchedBefore
    exact ⟨(World.rehome_initialized (world := before) (select := select)).mpr initialized,
      World.ResourcesClosed.rehome outside internal closed⟩
  · intro address value member resident
    obtain ⟨closed,restored⟩ := suspensible.2 address value member ((World.rehome_resident (world := before) (select := select)).mp resident)
    exact ⟨Value.ResourcesClosed.rehome outside internal closed,
      Value.LoansRestored.rehome outside internal restored⟩

theorem Cancelable.rehome {program : RuntimeProgram} {before : World} {select : Identity → Root → Home}
    {roots : List Identity}
    (outside : ∀ id, id ∉ roots → ∀ root, select id root = root.home)
    (internal : ∀ id ∈ roots, ∀ root, before.roots.get id = some root →
      (∀ domain, root.home ≠ .allocation domain) ∧ (∀ domain, root.home ≠ .external domain))
    {wanted : List Identity} (cancelable : Cancelable program before wanted) :
    Cancelable program (before.rehome select) wanted := by
  refine ⟨Suspensible.rehome outside internal cancelable.1,?_⟩
  intro address value member resident
  exact cancelable.2 address value member ((World.rehome_resident (world := before) (select := select)).mp resident)

theorem Authority.Replayable.rehome {world : World} {select : Identity → Root → Home}
    (authority : Authority) (replayable : authority.Replayable world) :
    authority.Replayable (world.rehome select) := by
  cases authority with
  | owner => trivial
  | loan id => exact replayable
  | shared backing => simpa only [Authority.Replayable,World.rehome_loans] using replayable
  | guarded backing carrier =>
      exact ⟨Authority.Replayable.rehome backing replayable.1,replayable.2⟩

theorem Replayable.rehome {program : RuntimeProgram} {before : World} {select : Identity → Root → Home}
    {roots : List Identity}
    (outside : ∀ id, id ∉ roots → ∀ root, select id root = root.home)
    (internal : ∀ id ∈ roots, ∀ root, before.roots.get id = some root →
      (∀ domain, root.home ≠ .allocation domain) ∧ (∀ domain, root.home ≠ .external domain))
    {wanted : List Identity} (replayable : Replayable program before wanted) :
    Replayable program (before.rehome select) wanted := by
  refine ⟨Suspensible.rehome outside internal replayable.1,?_,?_,?_⟩
  · intro address value member resident
    exact replayable.2.1 address value member ((World.rehome_resident (world := before) (select := select)).mp resident)
  · intro address value id loan member resident head found
    exact replayable.2.2.1 address value id loan member ((World.rehome_resident (world := before) (select := select)).mp resident) head
      (by simpa only [World.rehome_loans] using found)
  · intro id loan found live member
    exact replayable.2.2.2 id loan (by simpa only [World.rehome_loans] using found) live member

namespace Execution

open Kernel

theorem HomeOwnedByActivation.shape {home : Home} {activation : Identity}
    (owned : HomeOwnedByActivation home activation) :
    ∃ scope, home = .localSlot activation scope ∨ home = .temporary activation scope := by
  rcases owned with ⟨scope,same⟩ | ⟨scope,same⟩
  · exact ⟨scope,Or.inl same⟩
  · exact ⟨scope,Or.inr same⟩

/-- A home that a captured frame owns is a local or temporary home; capture never
relabels allocation or exterior storage. -/
theorem CapturedHome.local_or_temporary {handler : InstalledHandler} {inner : List Frame} {home : Home}
    (owned : CapturedHome handler inner home) :
    ∃ activation scope, home = .localSlot activation scope ∨ home = .temporary activation scope := by
  rcases owned with scope | ⟨frame,member,owned⟩
  · exact ⟨_,_,scope⟩
  · cases frame with
    | activation caller activation region =>
        obtain ⟨scope,shape⟩ := HomeOwnedByActivation.shape owned
        exact ⟨activation,scope,shape⟩
    | scope caller scope region => exact ⟨_,_,owned⟩
    | handler installed owns =>
        rcases owned with owned | ⟨_,owned⟩
        · exact ⟨_,_,owned⟩
        · obtain ⟨scope,shape⟩ := HomeOwnedByActivation.shape owned
          exact ⟨_,_,shape⟩
    | serviced installed owns clause continuation =>
        rcases owned with owned | ⟨_,owned⟩
        · obtain ⟨scope,shape⟩ := HomeOwnedByActivation.shape owned
          exact ⟨_,_,shape⟩
        · obtain ⟨scope,shape⟩ := HomeOwnedByActivation.shape owned
          exact ⟨_,_,shape⟩
    | completion installed owns clause =>
        rcases owned with owned | ⟨_,owned⟩
        · obtain ⟨scope,shape⟩ := HomeOwnedByActivation.shape owned
          exact ⟨_,_,shape⟩
        · obtain ⟨scope,shape⟩ := HomeOwnedByActivation.shape owned
          exact ⟨_,_,shape⟩
    | _ => exact False.elim owned

/-- The roots a capture selects carry local or temporary homes, so their home
is never an allocation or exterior domain. -/
theorem DelimitedRoots.home_not_allocation {world : World} {handler : InstalledHandler}
    {inner : List Frame} {kept roots : List Identity} (selected : DelimitedRoots world handler inner kept roots) :
    ∀ id ∈ roots, ∀ root, world.roots.get id = some root →
      (∀ domain, root.home ≠ .allocation domain) ∧ (∀ domain, root.home ≠ .external domain) := by
  intro id member root found
  obtain ⟨actual,actualAt,_,_,captured⟩ := (selected.2 id).mp member
  obtain ⟨activation,scope,shape⟩ := CapturedHome.local_or_temporary captured
  have same : root = actual := Option.some.inj (found.symm.trans actualAt)
  subst same
  rcases shape with shape | shape <;>
    (constructor <;> (intro domain equal; rw [shape] at equal; cases equal))

theorem suspendRoots.eq_rehome' (world : World) (roots : List Identity) (id : Identity) :
    suspendRoots world roots id = world.rehome (fun key root => if key ∈ roots then .suspended id else root.home) :=
  suspendRoots.eq_rehome world roots id

theorem restoreRoots.eq_rehome (world : World) (homes : Table Home) :
    restoreRoots world homes = world.rehome (fun key root => (homes.get key).getD root.home) := rfl

/-- The actual capture relabels the selected roots to the suspension; it moves
no value, creates no loan and changes no read, so the replay admission the
operation boundary granted for those roots is retained by the capture itself. -/
theorem DelimitedRoots.replayable_suspendRoots {program : Kernel.Program} {world : World}
    {handler : InstalledHandler} {inner : List Frame} {kept roots : List Identity}
    {quantity : Quantity} {bound id : Identity}
    (permission : SuspendPermission program world roots quantity inner)
    (upper : quantity.upper = some bound) (multi : 1 < bound)
    (selected : DelimitedRoots world handler inner kept roots) :
    Replayable program (suspendRoots world roots id) roots ∧ ∀ frame ∈ inner, SnapshotFrame frame := by
  obtain ⟨replayable,frames⟩ := SuspendPermission.replayable_frames permission upper multi
  constructor
  · rw [suspendRoots.eq_rehome']
    refine Replayable.rehome (roots := roots)
      (select := fun key root => if key ∈ roots then .suspended id else root.home) ?_ ?_ replayable
    · intro key outside root
      simp only [outside,↓reduceIte]
    · exact DelimitedRoots.home_not_allocation selected
  · exact frames

/-- Restoring the saved homes of one suspension relabels only roots that the
suspension currently owns, so the captured admission is retained by final
replay and cancellation as well. -/
theorem Suspension.restore_replayable {program : Kernel.Program} {before : State}
    {id : Identity} {suspension : Suspension}
    (formed : before.SuspensionsWellFormed) (found : before.resumptions.get id = some suspension)
    (active : suspension.active = true)
    (replayable : Replayable program before.world suspension.roots) :
    Replayable program (restoreRoots before.world suspension.homes) suspension.roots := by
  have origin := formed.origin id suspension found
  refine Replayable.rehome (roots := suspension.roots)
    (select := fun key root => (suspension.homes.get key).getD root.home) ?_ ?_ replayable
  · intro key outside root
    have absent : suspension.homes.get key = none := by
      cases saved : suspension.homes.get key with
      | none => rfl
      | some home => exact False.elim (outside ((origin.domain key).mp ⟨home,saved⟩))
    rw [absent]
    rfl
  · intro key member root rootAt
    obtain ⟨actual,actualAt,_,suspended⟩ := (formed.active id suspension found active key).mp member
    have same : root = actual := Option.some.inj (rootAt.symm.trans actualAt)
    rw [same,suspended]
    constructor <;> (intro domain equal; cases equal)



open Kernel

/-- Read agreement at every address outside one fresh root: the fresh root has
its own identity, so every previously existing row is untouched. -/
theorem World.root_of_rows {before after : World} {fresh : Identity}
    (rows : ∀ id, id ≠ fresh → after.roots.get id = before.roots.get id)
    {address : Address} (outside : address.root ≠ fresh) : after.root address = before.root address := by
  unfold World.root
  rw [rows address.root outside]

theorem World.stores_of_rows {before after : World} {fresh : Identity}
    (rows : ∀ id, id ≠ fresh → after.roots.get id = before.roots.get id)
    {address : Address} {value : Value} (outside : address.root ≠ fresh) :
    after.Stores address value ↔ before.Stores address value := by
  have reads : after.read address = before.read address := by
    unfold World.read
    rw [World.root_of_rows rows outside]
  unfold World.Stores
  rw [reads]

theorem Authority.Custodied.fresh {before after : World} {custody : ClaimCustody}
    (loans : after.loans = before.loans) (authority : Authority)
    (custodied : authority.Custodied before custody) : authority.Custodied after custody := by
  induction authority with
  | owner => trivial
  | loan id => obtain ⟨loan,found,kind⟩ := custodied; exact ⟨loan,by simpa only [← loans] using found,kind⟩
  | shared backing => simpa only [Authority.Custodied,loans] using custodied
  | guarded backing carrier ih => exact ih custodied

theorem AllocationClaim.fresh {before after : World} {fresh : Identity}
    (rows : ∀ id, id ≠ fresh → after.roots.get id = before.roots.get id)
    (loans : after.loans = before.loans)
    {authority : Authority} {address : Address} (outside : address.root ≠ fresh)
    (claim : AllocationClaim before authority address) : AllocationClaim after authority address := by
  obtain ⟨identity,loan,root,domain,parent,found,live,kind,referent,whole,selected,home,latest⟩ := claim
  have replaced : after.root address = some root := by
    rw [World.root_of_rows rows outside]
    exact selected
  refine ⟨identity,loan,root,domain,parent,by rw [loans]; exact found,live,kind,referent,whole,replaced,home,?_⟩
  intro child successor found' live' kind' ancestor
  exact latest child successor (by rw [← loans]; exact found') live' kind'
    (AncestorLoan.transport loans.symm ancestor)

theorem StorageBinding.HeldBy.referent_recorded {world : World} {owner : Identity} {binding : StorageBinding}
    (held : binding.HeldBy world owner) :
    ∃ identity loan, world.loans.get identity = some loan ∧ loan.live = true ∧ loan.referent = binding.address := by
  obtain ⟨custody,resources⟩ := held
  rcases resources with ⟨claim,_⟩ | borrow
  · obtain ⟨identity,loan,root,domain,parent,found,live,kind,referent,whole,selected,home,latest⟩ := claim
    exact ⟨identity,loan,found,live,referent⟩
  · obtain ⟨identity,loan,parent,found,live,kind,referent,shared⟩ := borrow
    exact ⟨identity,loan,found,live,referent⟩

theorem StorageBinding.HeldBy.fresh {before after : World} {fresh : Identity}
    (rows : ∀ id, id ≠ fresh → after.roots.get id = before.roots.get id)
    (loans : after.loans = before.loans) {owner : Identity} {binding : StorageBinding}
    (outside : binding.address.root ≠ fresh) (held : binding.HeldBy before owner) :
    binding.HeldBy after owner := by
  obtain ⟨custody,resources⟩ := held
  refine ⟨Authority.Custodied.fresh loans _ custody,?_⟩
  rcases resources with ⟨claim,added⟩ | borrow
  · exact Or.inl ⟨AllocationClaim.fresh rows loans outside claim,added⟩
  · exact Or.inr (by simpa only [loans] using borrow)

/-- A declared invariant of a resident is retained when an unrelated fresh root
is added: no support address of the resident is the fresh root, so every read and
every location the invariant observes is untouched. -/
theorem Value.InvariantClosed.fresh {program : RuntimeProgram} {before after : World} {fresh : Identity}
    {resident : Value}
    (rows : ∀ id, id ≠ fresh → after.roots.get id = before.roots.get id)
    (support : ∀ address, resident.Support before address → address.root ≠ fresh)
    (closed : resident.InvariantClosed program before) :
    resident.InvariantClosed program after := by
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
            refine ⟨contract,lookup,ownerAt,contract.framed before after _ ?_ holds⟩
            intro address supported
            have outside := support address supported
            exact ⟨by unfold World.read; rw [World.root_of_rows rows outside],
              by rw [rows address.root outside]⟩
    | _ => exact closed

/-- Reachability in the enlarged world maps back to the source world: no edge of
the graph names the fresh root. Both kinds of edge carry the machine's own
provenance for their loan: a reference head is covered by the value's
`LoansRestored` closure, which the real loan-ending rules maintain by requiring
that no resident names the loan being ended, and a resource binding is covered
by `HeldBy`, which records a live loan. A dead row therefore never appears as an
edge and needs no referent bound of its own. -/
theorem Value.ReachableResident.outside {program : RuntimeProgram} {before after : World}
    {fresh : Identity} {value : Value}
    (rows : ∀ id, id ≠ fresh → after.roots.get id = before.roots.get id)
    (loans : after.loans = before.loans)
    (avoid : ∀ id loan, before.loans.get id = some loan → loan.live = true → loan.referent.root ≠ fresh)
    (closed : value.ResourcesClosed program before)
    (restored : value.LoansRestored program before) :
    ∀ {resident : Value} {current : Authority} {access : Access},
      value.ReachableResident after .owner .shared resident current access →
      value.ReachableResident before .owner .shared resident current access := by
  intro resident current access reached
  induction reached with
  | resident located => exact .resident located
  | @referent carrier parent parentAuthority parentAccess loan target path resident prior reference found stored located ih =>
      have foundBefore : before.loans.get parent = some loan := by simpa only [← loans] using found
      obtain ⟨liveLoan,liveAt,liveLive,_⟩ :=
        restored parent parentAuthority parentAccess ⟨carrier,ih,reference⟩
      have same : liveLoan = loan := Option.some.inj (liveAt.symm.trans foundBefore)
      have outside : loan.referent.root ≠ fresh := by
        rw [← same]
        exact avoid parent liveLoan liveAt liveLive
      have view := Authority.referenceView_same_loans loans parentAuthority parent
        (ReferenceAccess parentAccess loan.mode)
      simpa only [view] using
        Value.ReachableResident.referent ih reference foundBefore
          ((World.stores_of_rows rows outside).mp stored) located
  | @resource carrier current accessAt binding target path resident prior member stored located ih =>
      have held := (closed carrier current accessAt ih).1 binding member
      obtain ⟨identity,loan,found,live,referent⟩ := StorageBinding.HeldBy.referent_recorded held
      have outside : binding.address.root ≠ fresh := by
        rw [← referent]
        exact avoid identity loan found live
      have view := Authority.resourceView_same_loans loans current binding accessAt
      simpa only [view] using
        Value.ReachableResident.resource ih member ((World.stores_of_rows rows outside).mp stored) located

theorem Value.ReachableResident.nested {world : World} {value carrier resident : Value}
    {authority current : Authority} {incoming access : Access} {path : List Nat}
    (reached : value.ReachableResident world authority incoming carrier current access)
    (located : ResidentAt carrier path resident) :
    value.ReachableResident world authority incoming resident current access := by
  induction reached with
  | resident initial => exact .resident (initial.append located)
  | referent prior reference found stored initial _ => exact .referent prior reference found stored (initial.append located)
  | resource prior member stored initial _ => exact .resource prior member stored (initial.append located)

theorem Value.ReachableResident.trans {world : World} {value carrier resident : Value}
    {authority current final : Authority} {incoming access finalAccess : Access}
    (prior : value.ReachableResident world authority incoming carrier current access)
    (next : carrier.ReachableResident world current access resident final finalAccess) :
    value.ReachableResident world authority incoming resident final finalAccess := by
  induction next with
  | resident located => exact prior.nested located
  | referent _ reference found stored located ih => exact .referent ih reference found stored located
  | resource _ member stored located ih => exact .resource ih member stored located

theorem Value.ResourcesClosed.reachable {program : RuntimeProgram} {world : World}
    {value resident : Value} {authority current : Authority} {incoming access : Access}
    (closed : value.ResourcesClosed program world)
    (reached : value.ReachableResident world authority incoming resident current access) :
    resident.ResourcesClosed program world := by
  intro child next requested nested
  obtain ⟨base,acc,prior⟩ := reached.rebase .owner .shared
  obtain ⟨final,finalAccess,nested⟩ := nested.rebase base acc
  exact closed child final finalAccess (prior.trans nested)

/-- The restoration closure of a value is inherited by every reachable
resident: a reference view of a resident reachable from the value is a reference
view of the value, after rebasing both to the same base authority. -/
theorem Value.LoansRestored.reachable {program : RuntimeProgram} {world : World}
    {value resident : Value} {authority current : Authority} {incoming access : Access}
    (restored : value.LoansRestored program world)
    (reached : value.ReachableResident world authority incoming resident current access) :
    resident.LoansRestored program world := by
  intro identity target targetAccess view
  obtain ⟨carrier,reachedAt,head⟩ := view
  obtain ⟨base,acc,prior⟩ := reached.rebase .owner .shared
  obtain ⟨mid,midAccess,nested⟩ := reachedAt.rebase base acc
  exact restored identity mid midAccess ⟨carrier,prior.trans nested,head⟩

theorem World.resident_of_rows {before after : World} {fresh : Identity}
    (rows : ∀ id, id ≠ fresh → after.roots.get id = before.roots.get id)
    {address : Address} {value : Value} (outside : address.root ≠ fresh) :
    after.Resident address value ↔ before.Resident address value := by
  constructor
  · rintro ⟨root,whole,found,live,generation,contents,located⟩
    exact ⟨root,whole,by rw [← rows address.root outside]; exact found,live,generation,contents,located⟩
  · rintro ⟨root,whole,found,live,generation,contents,located⟩
    exact ⟨root,whole,by rw [rows address.root outside]; exact found,live,generation,contents,located⟩

/-- Closed resources are retained when an unrelated fresh root is added, provided
every live recorded loan avoids that root. The reference-head arm of an
invariant's support uses the resident's own restoration closure, so no dead row
referent is ever consumed. -/
theorem Value.ResourcesClosed.fresh {program : RuntimeProgram} {before after : World} {value : Value}
    {fresh : Identity}
    (rows : ∀ id, id ≠ fresh → after.roots.get id = before.roots.get id)
    (loans : after.loans = before.loans)
    (avoid : ∀ id loan, before.loans.get id = some loan → loan.live = true → loan.referent.root ≠ fresh)
    (closed : value.ResourcesClosed program before)
    (restored : value.LoansRestored program before) :
    value.ResourcesClosed program after := by
  intro resident current access reached
  have reachedBefore := Value.ReachableResident.outside rows loans avoid closed restored reached
  obtain ⟨held,declared⟩ := closed resident current access reachedBefore
  have residentClosed : resident.ResourcesClosed program before := closed.reachable reachedBefore
  have residentRestored : resident.LoansRestored program before := restored.reachable reachedBefore
  have support : ∀ address, resident.Support before address → address.root ≠ fresh := by
    intro address supported
    obtain ⟨carrier,authorityAt,accessAt,reachedAt,reference | ⟨binding,member,same⟩⟩ := supported
    · obtain ⟨identity,loan,headAt,found,referent⟩ := reference
      obtain ⟨currentLoan,currentAt,currentLive,_⟩ :=
        residentRestored identity authorityAt accessAt ⟨carrier,reachedAt,headAt⟩
      have sameLoan : currentLoan = loan := Option.some.inj (currentAt.symm.trans found)
      subst sameLoan
      rw [← referent]
      exact avoid identity currentLoan currentAt currentLive
    · have carrierClosed : carrier.ResourcesClosed program before :=
        Value.ResourcesClosed.reachable (closed := residentClosed) (reached := reachedAt)
      obtain ⟨identity,loan,found,live,referent⟩ := StorageBinding.HeldBy.referent_recorded
        ((carrierClosed carrier .owner .shared (.resident .root)).1 binding member)
      rw [← same,← referent]
      exact avoid identity loan found live
  refine ⟨fun binding member => StorageBinding.HeldBy.fresh rows loans ?_ (held binding member),?_⟩
  · obtain ⟨identity,loan,found,live,referent⟩ := StorageBinding.HeldBy.referent_recorded (held binding member)
    rw [← referent]
    exact avoid identity loan found live
  · exact Value.InvariantClosed.fresh rows support declared

theorem Value.LoansRestored.fresh {program : RuntimeProgram} {before after : World} {value : Value}
    {fresh : Identity}
    (rows : ∀ id, id ≠ fresh → after.roots.get id = before.roots.get id)
    (loans : after.loans = before.loans)
    (avoid : ∀ id loan, before.loans.get id = some loan → loan.live = true → loan.referent.root ≠ fresh)
    (closed : value.ResourcesClosed program before)
    (restored : value.LoansRestored program before) :
    value.LoansRestored program after := by
  intro identity authority access reached
  obtain ⟨resident,reachedAt,head⟩ := reached
  have carrierBefore := Value.ReachableResident.outside rows loans avoid closed restored reachedAt
  obtain ⟨loan,found,live,initialized,referentClosed⟩ :=
    restored identity authority access ⟨resident,carrierBefore,head⟩
  have outside : loan.referent.root ≠ fresh := avoid identity loan found live
  obtain ⟨target,stored,ready⟩ := initialized
  refine ⟨loan,by rw [loans]; exact found,live,⟨target,(World.stores_of_rows rows outside).mpr stored,ready⟩,?_⟩
  intro referent referentStored
  have referentBefore : before.Stores loan.referent referent :=
    (World.stores_of_rows rows outside).mp referentStored
  have referentRestored : referent.LoansRestored program before :=
    restored.reachable (Value.ReachableResident.referent carrierBefore head found referentBefore ResidentAt.root)
  exact Value.ResourcesClosed.fresh rows loans avoid
    (referentClosed referent referentBefore) referentRestored

theorem World.ResourcesClosed.fresh {program : RuntimeProgram} {before after : World} {fresh : Identity}
    {address : Address}
    (rows : ∀ id, id ≠ fresh → after.roots.get id = before.roots.get id)
    (loans : after.loans = before.loans)
    (avoid : ∀ id loan, before.loans.get id = some loan → loan.live = true → loan.referent.root ≠ fresh)
    (outside : address.root ≠ fresh) (closed : World.ResourcesClosed program before address) :
    World.ResourcesClosed program after address := by
  intro value stored
  obtain ⟨resources,restored⟩ := closed value ((World.stores_of_rows rows outside).mp stored)
  exact ⟨Value.ResourcesClosed.fresh rows loans avoid resources restored,
    Value.LoansRestored.fresh rows loans avoid resources restored⟩

theorem Suspensible.fresh {program : RuntimeProgram} {before after : World} {fresh : Identity}
    {roots : List Identity}
    (rows : ∀ id, id ≠ fresh → after.roots.get id = before.roots.get id)
    (loans : after.loans = before.loans)
    (avoid : ∀ id loan, before.loans.get id = some loan → loan.live = true → loan.referent.root ≠ fresh)
    (outside : fresh ∉ roots)
    (suspensible : Suspensible program before roots) :
    Suspensible program after roots := by
  constructor
  · intro id loan found live kind touched
    have foundBefore : before.loans.get id = some loan := by simpa only [← loans] using found
    have touchedBefore : loan.referent.root ∈ roots ∨
        ∃ address value, address.root ∈ roots ∧ before.Resident address value ∧ value.head = .reference id := by
      rcases touched with member | ⟨address,value,member,resident,head⟩
      · exact Or.inl member
      · exact Or.inr ⟨address,value,member,
          (World.resident_of_rows rows (fun same => outside (same ▸ member))).mp resident,head⟩
    obtain ⟨initialized,closed⟩ := suspensible.1 id loan foundBefore live kind touchedBefore
    have referentOutside : loan.referent.root ≠ fresh := avoid id loan foundBefore live
    obtain ⟨value,stored,ready⟩ := initialized
    exact ⟨⟨value,(World.stores_of_rows rows referentOutside).mpr stored,ready⟩,
      World.ResourcesClosed.fresh rows loans avoid referentOutside closed⟩
  · intro address value member resident
    have outside' : address.root ≠ fresh := fun same => outside (same ▸ member)
    obtain ⟨closed,restored⟩ := suspensible.2 address value member
      ((World.resident_of_rows rows outside').mp resident)
    exact ⟨Value.ResourcesClosed.fresh rows loans avoid closed restored,
      Value.LoansRestored.fresh rows loans avoid closed restored⟩

theorem Replayable.fresh {program : RuntimeProgram} {before after : World} {fresh : Identity}
    {roots : List Identity}
    (rows : ∀ id, id ≠ fresh → after.roots.get id = before.roots.get id)
    (loans : after.loans = before.loans)
    (avoid : ∀ id loan, before.loans.get id = some loan → loan.live = true → loan.referent.root ≠ fresh)
    (outside : fresh ∉ roots)
    (replayable : Replayable program before roots) :
    Replayable program after roots := by
  refine ⟨Suspensible.fresh rows loans avoid outside replayable.1,?_,?_,?_⟩
  · intro address value member resident
    exact replayable.2.1 address value member
      ((World.resident_of_rows rows (fun same => outside (same ▸ member))).mp resident)
  · intro address value id loan member resident head found
    exact replayable.2.2.1 address value id loan member
      ((World.resident_of_rows rows (fun same => outside (same ▸ member))).mp resident) head
      (by rw [← loans]; exact found)
  · intro id loan found live member
    exact replayable.2.2.2 id loan (by rw [← loans]; exact found) live member

-- The three lemmas below are the row facts the fresh-root frame consumes: rows
-- above the frontier are absent, and the machine's own allocation and write move
-- no other identity. ForeignRootFraming proves the same two framing lemmas, but
-- that module does not currently build in main, so they are reproved here.

/-- A live root read is backed by a row of the actual root table; this is the
only projection the loan law needs. -/
theorem World.exists_root_of_root {world : World} {address : Address} {value : Root}
    (found : world.root address = some value) : ∃ root, world.roots.get address.root = some root := by
  unfold World.root at found
  exact (Option.bind_eq_some_iff.mp found).imp fun _ selected => selected.1

/-- The machine's own loan law, consumed as the fresh frame's side condition: a
live recorded loan has a stored referent, hence a referent root below the current
frontier. Dead rows carry no frontier law, and none is needed: neither kind of
edge of a closed value's graph names one. -/
theorem World.loan_referent_bound {world : World} (well : world.WellFormed)
    {id : Identity} {loan : Loan} (found : world.loans.get id = some loan) (live : loan.live = true) :
    loan.referent.root < world.nextRoot := by
  obtain ⟨value,rooted⟩ := Option.isSome_iff_exists.mp
    ((well.2.2.2.2.2.2.2.2.2.2.2.2.1 id loan found).2.2 live).2
  obtain ⟨root,rootAt⟩ := World.exists_root_of_root rooted
  exact World.root_bound well rootAt

/-- A live loan's referent also avoids every identity at or above the frontier,
which is exactly the side condition of the fresh-root frame. -/
theorem World.loan_referent_ne {world : World} (well : world.WellFormed)
    {id : Identity} {loan : Loan} (found : world.loans.get id = some loan) (live : loan.live = true)
    {fresh : Identity} (above : world.nextRoot ≤ fresh) : loan.referent.root ≠ fresh :=
  Nat.ne_of_lt (Nat.lt_of_lt_of_le (World.loan_referent_bound well found live) above)

/-- Rows above the allocation frontier are absent, so adding the fresh root
leaves every other identity untouched. -/
theorem World.roots_none_of_frontier {world : World} (well : world.WellFormed) {id : Identity}
    (frontier : world.nextRoot ≤ id) : world.roots.get id = none := by
  cases found : world.roots.get id with
  | none => rfl
  | some root => exact False.elim (Nat.not_lt_of_ge frontier (World.root_bound well found))

theorem World.write_roots_other' {before after : World} {address : Address} {value : Option Value}
    {id : Identity} (written : before.write address value = some after) (outside : id ≠ address.root) :
    after.roots.get id = before.roots.get id := by
  obtain ⟨root,replacement,found,rfl⟩ := World.write_value_update written
  exact Table.get_set_other _ _ _ _ outside

theorem Allocates.roots_other' {program : Program} {before after : World}
    {home region type layout mutable address} {id : Identity}
    (allocated : Allocates program before home region type layout mutable address after)
    (bound : id < before.nextRoot) : after.roots.get id = before.roots.get id := by
  cases allocated
  exact Table.get_set_other _ _ _ _ (Nat.ne_of_lt bound)

end Execution
end Glorious.Language
