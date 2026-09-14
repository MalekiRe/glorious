import GloriousLanguage.RelocationPreservation
import GloriousLanguage.ReferenceTransferPreservation

/-! Snapshot relocation preserves the actual mixed resident graph: captured
storage is renamed while edges into external storage retain that storage.
The declared invariant relocation law is consumed at copied nominal nodes;
ordinary support framing handles the unchanged external nodes. -/
namespace Glorious.Language

theorem World.Resident.nested {world : World} {address : Address} {value child : Value}
    {path : List Nat} (resident : world.Resident address value) (located : ResidentAt value path child) :
    world.Resident { address with fields := address.fields ++ path } child := by
  obtain ⟨root,whole,found,live,generation,contents,inside⟩ := resident
  exact ⟨root,whole,found,live,generation,contents,inside.append located⟩

theorem StorageBinding.HeldBy.root {world : World} {binding : StorageBinding} {owner : Identity}
    (valid : world.WellFormed) (held : binding.HeldBy world owner) :
    ∃ root, world.root binding.address = some root := by
  rcases held.2 with ⟨⟨_,_,root,_,_,_,_,_,_,_,found,_⟩,_⟩ | ⟨id,loan,_,found,live,_,referent,_⟩
  · exact ⟨root,found⟩
  · rw [← referent]
    exact Option.isSome_iff_exists.mp (((valid.2.2.2.2.2.2.2.2.2.2.2.2.1 id loan found).2.2 live).2)

theorem Value.ResourcesClosed.support_root {program : RuntimeProgram} {world : World} {value : Value}
    (valid : world.WellFormed) (closed : value.ResourcesClosed program world)
    (restored : value.LoansRestored program world) {address : Address} (supported : value.Support world address) :
    ∃ root, world.root address = some root := by
  obtain ⟨resident,authority,access,reached,support⟩ := supported
  rcases support with ⟨id,loan,head,found,rfl⟩ | ⟨binding,member,rfl⟩
  · obtain ⟨current,selected,live,_⟩ := restored id authority access ⟨resident,reached,head⟩
    have same := Option.some.inj (found.symm.trans selected)
    subst current
    exact Option.isSome_iff_exists.mp (((valid.2.2.2.2.2.2.2.2.2.2.2.2.1 id loan found).2.2 live).2)
  · exact ((closed resident authority access reached).1 binding member).root valid

namespace Execution

theorem CopiesSnapshot.storageReady {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} (copied : CopiesSnapshot program before suspension map after) :
    Relocation.StorageReady before.world map.roots suspension.controlAuthoritySupport := by
  have roots := copied.relocation.roots
  refine ⟨?_,?_,?_,copied.controlReplayable⟩
  · intro address value included resident binding member
    have captured : address.root ∈ suspension.roots := roots ▸ included
    exact ⟨(copied.replayable.2.1 address value captured resident).2.2.2 binding member,
      ((copied.replayable.1.2 address value captured resident).1 value .owner .shared (.resident .root)).1 binding member⟩
  · intro address value id loan included resident head found
    exact copied.replayable.2.2.1 address value id loan (roots ▸ included) resident head found
  · intro id loan found live included
    exact copied.replayable.2.2.2 id loan found live (roots ▸ included)

theorem Relocation.authority_parent (map : Relocation) (authority : Authority) :
    (map.authority authority).parentLoan = authority.parentLoan.map map.loan := by
  induction authority with
  | owner => rfl
  | loan id => rfl
  | shared backing ih => exact ih
  | guarded backing carrier ih => exact ih

theorem Relocation.binding_readOnly {map : Relocation} {binding : StorageBinding}
    (shared : binding.ReadOnly) : (map.binding binding).ReadOnly := by
  obtain ⟨backing,same⟩ := shared
  exact ⟨map.authority backing,by simp [Relocation.binding,same,Relocation.authority]⟩

theorem SnapshotMap.loan_lookup {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} {homes : Table Home} {id : Identity} {loan : Loan}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (found : before.world.loans.get id = some loan) :
    ∃ current, (map.copyWorld before.world homes).loans.get (map.loan id) = some current := by
  by_cases included : id ∈ map.loans
  · exact ⟨map.loanValue loan,selected.copied_loan valid found included⟩
  · exact ⟨loan,by simpa [Relocation.loan,relocateId,included] using Relocation.old_loan (map := map) (homes := homes) found⟩

theorem SnapshotMap.authority_recorded {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} {homes : Table Home} {authority : Authority}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (recorded : authority.Recorded before.world.loans) :
    (map.authority authority).Recorded (map.copyWorld before.world homes).loans := by
  induction authority with
  | owner => trivial
  | loan id =>
      obtain ⟨loan,found⟩ := recorded
      exact selected.loan_lookup valid found
  | shared backing ih => exact ih recorded
  | guarded backing carrier ih =>
      obtain ⟨loan,found⟩ := recorded.2
      exact ⟨ih recorded.1,selected.loan_lookup valid found⟩

theorem SnapshotMap.old_loan_lookup {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} {homes : Table Home} {id : Identity}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (bound : id < before.world.nextLoan) :
    (map.copyWorld before.world homes).loans.get id = before.world.loans.get id := by
  cases found : (map.copyWorld before.world homes).loans.get id with
  | none =>
      cases original : before.world.loans.get id with
      | none => rfl
      | some loan => have conflict := Relocation.old_loan (map := map) (homes := homes) original; rw [found] at conflict; contradiction
  | some loan =>
      rcases Relocation.loan_origin valid.2.1 found with original | ⟨old,previous,_,included,same,_⟩
      · exact original.symm
      · have : id = before.world.nextLoan + old := by simpa [Relocation.loan,relocateId,included,selected.loanBase] using same
        exact False.elim ((Nat.not_lt_of_ge (Nat.le_add_right _ _)) (this ▸ bound))

/-- Old loan permissions survive the actual copy table when every selected
new row is compatible with their original overlap and guard observations. -/
theorem Relocation.old_loanPermission {world : World} {map : Relocation} {homes : Table Home}
    {identity : Identity} {requested : Access} {address : Address}
    (valid : world.WellFormed) (permission : LoanPermission world identity requested address)
    (compatible : ∀ id loan, world.loans.get id = some loan → id ∈ map.loans →
      (Authority.loan identity).LoanCompatible world requested address
        (map.loanValue loan).referent (map.loanValue loan).mode (map.loanValue loan).guards) :
    LoanPermission (map.copyWorld world homes) identity requested address := by
  obtain ⟨active,found,live,root,generation,path,mode,excluded,guards,dependent⟩ := permission
  refine ⟨active,Relocation.old_loan found,live,root,generation,path,mode,?_,?_,?_⟩
  · intro other loan selected alive different overlap conflict
    rcases Relocation.loan_origin valid.2.1 selected with original | ⟨old,previous,present,included,rfl,rfl⟩
    · exact (excluded other loan original alive different overlap conflict).weaken
        (fun _ _ => Relocation.old_loan)
    · exact False.elim ((compatible old previous present included).1 overlap conflict)
  · intro guard member
    obtain ⟨loan,selected,alive⟩ := guards guard member
    exact ⟨loan,Relocation.old_loan selected,alive⟩
  · intro other loan selected alive member
    rcases Relocation.loan_origin valid.2.1 selected with original | ⟨old,previous,present,included,rfl,rfl⟩
    · exact dependent other loan original alive member
    · exact (compatible old previous present included).2 member

/-- Copy permission framing consumes original selected-row compatibility, not
an assumed permission in an arbitrary copied world. -/
theorem Relocation.old_permitted {world : World} {map : Relocation} {homes : Table Home}
    {authority : Authority} {requested : Access} {address : Address}
    (valid : world.WellFormed) (permission : Permitted world authority requested address)
    (compatible : ∀ id loan, world.loans.get id = some loan → id ∈ map.loans →
      authority.LoanCompatible world requested address
        (map.loanValue loan).referent (map.loanValue loan).mode (map.loanValue loan).guards) :
    Permitted (map.copyWorld world homes) authority requested address := by
  obtain ⟨root,selected⟩ := permission.root
  induction authority with
  | owner =>
    refine ⟨⟨root,Relocation.old_selected_root selected⟩,?_⟩
    intro identity loan found live overlap conflict
    rcases Relocation.loan_origin valid.2.1 found with original | ⟨old,previous,present,included,rfl,rfl⟩
    · exact permission.2 identity loan original live overlap conflict
    · exact compatible old previous present included overlap conflict
  | loan identity =>
    exact ⟨⟨root,Relocation.old_selected_root selected⟩,Relocation.old_loanPermission valid permission.2 compatible⟩
  | shared backing ih =>
    exact ⟨⟨root,Relocation.old_selected_root selected⟩,permission.2.1,ih permission.2.2 compatible⟩
  | guarded backing carrier ih =>
    obtain ⟨loan,found,allowed⟩ := permission.2.2
    exact ⟨⟨root,Relocation.old_selected_root selected⟩,
      ih permission.2.1 (fun id loan found included => (compatible id loan found included).1),
      loan,Relocation.old_loan found,Relocation.old_loanPermission valid allowed
        (fun id previous present included => (compatible id previous present included).2 loan found)⟩


/-- A fresh relocated referent cannot overlap an old root. Thus every overlap
observed by an original permission comes from an unchanged source referent. -/
theorem SnapshotMap.old_overlap {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} {address referent : Address} (selected : SnapshotMap program before suspension map)
    (bound : address.root < before.world.nextRoot) (overlap : address.Overlaps (map.address referent)) :
    address.Overlaps referent := by
  by_cases included : referent.root ∈ map.roots
  · have fresh : before.world.nextRoot ≤ address.root := by
      rw [overlap.1]
      simp only [Relocation.address,Relocation.root,relocateId,if_pos included,selected.rootBase]
      exact Nat.le_add_right _ _
    exact False.elim (Nat.not_lt_of_ge fresh bound)
  · simpa only [Relocation.address_unselected included] using overlap

/-- A shared source row cannot conflict with an admitted old unique use: the
only ancestry exemption would put a shared ancestor above a unique descendant,
which the world's actual parent-mode invariant excludes. Copied guards either
retain their old identity or are fresh and cannot name an old carrier. -/
theorem SnapshotMap.old_loan_compatible {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} {identity old : Identity} {requested : Access} {address : Address} {loan : Loan}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (permission : LoanPermission before.world identity requested address)
    (present : before.world.loans.get old = some loan) (included : old ∈ map.loans) :
    (Authority.loan identity).LoanCompatible before.world requested address
      (map.loanValue loan).referent (map.loanValue loan).mode (map.loanValue loan).guards := by
  obtain ⟨active,found,live,root,generation,path,mode,excluded,guards,dependent⟩ := permission
  have source := selected.selected_loan included present
  constructor
  · intro overlap conflict
    have bound : address.root < before.world.nextRoot := root ▸ World.live_loan_root_bound valid found live
    have originalOverlap := selected.old_overlap bound overlap
    have notShared : requested ≠ .shared := by
      rcases conflict with requested | unique
      · exact requested
      · change loan.mode = .unique at unique
        cases source.2.symm.trans unique
    have unique := mode notShared
    by_cases same : old = identity
    · subst old
      have equal : loan = active := Option.some.inj (present.symm.trans found)
      subst loan
      cases source.2.symm.trans unique
    · have ancestry := excluded old loan present source.1 same originalOverlap conflict
      have ancestorUnique := ancestry.unique_ancestor (World.loanParents valid) present found unique
      cases source.2.symm.trans ancestorUnique
  · intro member
    change identity ∈ loan.guards.map map.loan at member
    obtain ⟨guard,guardMember,equal⟩ := List.mem_map.mp member
    by_cases copied : guard ∈ map.loans
    · have fresh : before.world.nextLoan ≤ identity := by
        rw [← equal]
        simp only [Relocation.loan,relocateId,if_pos copied,selected.loanBase]
        exact Nat.le_add_right _ _
      exact False.elim (Nat.not_lt_of_ge fresh (World.loanBounds valid found))
    · have same : guard = identity := by simpa only [Relocation.loan,relocateId,if_neg copied] using equal
      exact dependent old loan present source.1 (same ▸ guardMember)

/-- The authoritative snapshot selector copies only shared rows. It therefore
produces, rather than assumes, compatibility with every original permission. -/
theorem SnapshotMap.old_compatible {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} {authority : Authority} {requested : Access} {address : Address}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (permission : Permitted before.world authority requested address) :
    ∀ id loan, before.world.loans.get id = some loan → id ∈ map.loans →
      authority.LoanCompatible before.world requested address
        (map.loanValue loan).referent (map.loanValue loan).mode (map.loanValue loan).guards := by
  obtain ⟨root,rootAt⟩ := permission.root
  induction authority with
  | owner =>
    intro id loan found included overlap conflict
    exact permission.2 id loan found (selected.selected_loan included found).1
      (selected.old_overlap (World.root_bound valid (World.root_found rootAt).1) overlap) conflict
  | loan identity =>
    exact fun _ _ found included => selected.old_loan_compatible valid permission.2 found included
  | shared backing ih => exact ih permission.2.2
  | guarded backing carrier ih =>
    intro id loan found included
    refine ⟨ih permission.2.1 id loan found included,?_⟩
    intro original originalAt
    obtain ⟨current,currentAt,allowed⟩ := permission.2.2
    have same : current = original := Option.some.inj (currentAt.symm.trans originalAt)
    subst current
    exact selected.old_loan_compatible valid allowed found included

theorem SnapshotMap.old_permitted {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} {homes : Table Home} {authority : Authority} {requested : Access} {address : Address}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (permission : Permitted before.world authority requested address) :
    Permitted (map.copyWorld before.world homes) authority requested address :=
  Relocation.old_permitted valid permission (selected.old_compatible valid permission)


theorem SnapshotMap.ancestor_old {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} {homes : Table Home} {ancestor child : Identity}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (ancestry : AncestorLoan (map.copyWorld before.world homes) ancestor child)
    (bound : child < before.world.nextLoan) : AncestorLoan before.world ancestor child := by
  induction ancestry with
  | refl => exact .refl
  | parent found parentEq previous ih =>
      have original := (selected.old_loan_lookup valid bound).symm.trans found
      obtain ⟨parent,atParent,_,_⟩ := World.loanParents valid _ _ _ original parentEq
      exact .parent original parentEq (ih (World.loanBounds valid atParent))

theorem SnapshotMap.owning_old {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} {homes : Table Home} {id : Identity} {loan : Loan}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (found : (map.copyWorld before.world homes).loans.get id = some loan) (owning : loan.kind = .owning) :
    before.world.loans.get id = some loan := by
  rcases Relocation.loan_origin valid.2.1 found with original | ⟨old,previous,present,included,_,rfl⟩
  · exact original
  · exact False.elim (World.shared_loan_nonowning valid present (selected.selected_loan included present).2 owning)

theorem SnapshotMap.old_allocationClaim {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} {homes : Table Home} {authority : Authority} {address : Address}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (claim : AllocationClaim before.world authority address) :
    AllocationClaim (map.copyWorld before.world homes) authority address := by
  obtain ⟨identity,loan,root,domain,parent,found,live,kind,referent,whole,atRoot,home,latest⟩ := claim
  refine ⟨identity,loan,root,domain,parent,Relocation.old_loan found,live,kind,referent,whole,
    Relocation.old_selected_root atRoot,home,?_⟩
  intro child successor atChild active owning ancestry
  have original := selected.owning_old valid atChild owning
  exact latest child successor original active owning
    (selected.ancestor_old valid ancestry (World.loanBounds valid original))

theorem Relocation.old_custodied {map : Relocation} {world : World} {homes : Table Home}
    {authority : Authority} {custody : ClaimCustody} (held : authority.Custodied world custody) :
    authority.Custodied (map.copyWorld world homes) custody := by
  induction authority with
  | owner => trivial
  | loan id =>
      obtain ⟨loan,found,kind⟩ := held
      exact ⟨loan,Relocation.old_loan found,kind⟩
  | shared backing => exact held.transport (fun _ loan found => ⟨loan,Relocation.old_loan found⟩)
  | guarded backing carrier ih => exact ih held

theorem SnapshotMap.old_heldBy {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} {homes : Table Home} {binding : StorageBinding} {owner : Identity}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (held : binding.HeldBy before.world owner) : binding.HeldBy (map.copyWorld before.world homes) owner := by
  refine ⟨Relocation.old_custodied held.1,?_⟩
  rcases held.2 with ⟨claim,writable⟩ | ⟨id,loan,parent,found,live,kind,referent,shared⟩
  · exact Or.inl ⟨selected.old_allocationClaim valid claim,writable⟩
  · exact Or.inr ⟨id,loan,parent,Relocation.old_loan found,live,kind,referent,shared⟩

/-- The existing old-row, claim and custody proofs supply the common resource
frame used by the original argument's reachable graph. -/
theorem SnapshotMap.old_resourceRows {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} {homes : Table Home} (valid : before.world.WellFormed)
    (selected : SnapshotMap program before suspension map) :
    before.world.ResourceRowsRetained (map.copyWorld before.world homes) :=
  ⟨fun _ loan found => ⟨loan,Relocation.old_loan found,rfl⟩,
    fun _ _ claim => selected.old_allocationClaim valid claim,
    fun _ _ held => Relocation.old_custodied held⟩


theorem SnapshotMap.copied_heldBy {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} {homes : Table Home} {address : Address} {value : Value} {binding : StorageBinding}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (included : address.root ∈ map.roots) (resident : before.world.Resident address value)
    (member : binding ∈ value.resources) (shared : binding.ReadOnly)
    (held : binding.HeldBy before.world value.owner) :
    (map.binding binding).HeldBy (map.copyWorld before.world homes) (map.value value).owner := by
  have readOnly := Relocation.binding_readOnly (map := map) shared
  refine ⟨?_,?_⟩
  · obtain ⟨backing,same⟩ := shared
    have recorded : backing.Recorded before.world.loans := by simpa [same,Authority.Custodied] using held.1
    simpa [Relocation.binding,same,Relocation.authority,Authority.Custodied] using selected.authority_recorded (homes := homes) valid recorded
  · rcases held.2 with ⟨_,writable⟩ | ⟨id,loan,parent,found,live,kind,referent,mode⟩
    · exact False.elim (writable shared)
    · have copied : id ∈ map.loans := (selected.loans id).mpr (.resource found live (mode shared) included resident member
        (List.mem_append_left _ (by simp [parent])))
      refine Or.inr ⟨map.loan id,map.loanValue loan,?_,selected.copied_loan valid found copied,live,kind,?_,fun _ => mode shared⟩
      · change (map.authority binding.authority).parentLoan = some (map.loan id)
        rw [map.authority_parent,parent]; rfl
      · exact congrArg map.address referent

theorem Relocation.value_resources (map : Relocation) (value : Value) :
    (map.value value).resources = value.resources.map map.binding := by cases value; rfl

theorem CopiesSnapshot.invariantClosed {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} {homes : Table Home} {address : Address} {value : Value}
    (valid : before.world.WellFormed) (copied : CopiesSnapshot program before suspension map after)
    (included : address.root ∈ map.roots) (resident : before.world.Resident address value)
    (closed : value.InvariantClosed program before.world) :
    (map.value value).InvariantClosed program (map.copyWorld before.world homes) := by
  unfold Value.InvariantClosed at closed ⊢
  rw [map.value_type]
  cases type : value.type with
  | nominal identity arguments =>
      simp only [type,Relocation.term,Term.renameRuntimeRegions] at closed ⊢
      obtain ⟨data,found,declared⟩ := closed
      refine ⟨data,found,?_⟩
      cases invariant : data.invariant with
      | none =>
          simp only [invariant] at declared ⊢
          rw [map.value_resources,declared]; rfl
      | some invariant =>
          simp only [invariant] at declared ⊢
          obtain ⟨contract,found,owner,holds⟩ := declared
          exact ⟨contract,found,owner,contract.relocated before.world map _ homes address value valid
            copied.relocation.toStoragePlan copied.storageReady included resident holds⟩
  | _ =>
      simp only [type,Relocation.term,Term.renameRuntimeRegions] at closed ⊢
      rw [map.value_resources,closed]; rfl

theorem Relocation.old_read {map : Relocation} {world : World} {homes : Table Home}
    {address : Address} {root : Root} (selected : world.root address = some root) :
    (map.copyWorld world homes).read address = world.read address := by
  simp [World.read,selected,Relocation.old_selected_root (map := map) (homes := homes) selected]

theorem SnapshotMap.copied_read {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} {homes : Table Home} {address : Address} {root : Root}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (atRoot : before.world.root address = some root) (included : address.root ∈ map.roots) :
    (map.copyWorld before.world homes).read (map.address address) = (before.world.read address).map map.value := by
  unfold World.read
  rw [selected.copied_selected_root valid atRoot included,atRoot]
  change (root.value.map map.value >>= fun value => value.atPath address.fields) =
    (root.value >>= fun value => value.atPath address.fields).map map.value
  cases contents : root.value with
  | none => rfl
  | some value => exact map.value_atPath value address.fields

theorem Relocation.old_supportFramed {program : RuntimeProgram} {map : Relocation}
    {world : World} {homes : Table Home} {value : Value}
    (valid : world.WellFormed) (closed : value.ResourcesClosed program world)
    (restored : value.LoansRestored program world) : value.SupportFramed world (map.copyWorld world homes) := by
  intro address supported
  obtain ⟨root,selected⟩ := closed.support_root valid restored supported
  have found := (World.root_found selected).1
  exact ⟨Relocation.old_read selected,by rw [Relocation.old_root found,found]⟩

/-- The caller's original handoff graph remains ready after the actual copy.
Shared-row selection supplies all permission compatibility; no copied-world
readiness or extra source compatibility assumption is required. -/
theorem CopiesSnapshot.old_handoffReady {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} {value : Value} {access : Access} {footprint : List Address}
    (valid : before.world.WellFormed) (copied : CopiesSnapshot program before suspension map after)
    (ready : value.HandoffReady program before.world access footprint) :
    value.HandoffReady program after.world access footprint := by
  have rows := copied.relocation.old_resourceRows (homes := suspension.homes) valid
  have batch : value.BatchCompatible before.world (map.copyWorld before.world suspension.homes) := by
    apply Value.BatchCompatible.of_rows rows
    intro identity current access reached
    obtain ⟨loan,found,_⟩ := ready.1.2.1 identity current access reached
    exact ⟨loan,found⟩
  have framed := Relocation.old_supportFramed (map := map) (homes := suspension.homes) valid ready.1.1 ready.1.2.1
  rw [copied.result]
  exact ready.frame_batch batch framed
    (fun _ _ _ _ permission => copied.relocation.old_permitted valid permission)


/-- Proof-only provenance for a node of the actual post-copy graph. Each node
is either a captured resident under the one relocation or an unchanged
resident reached in external storage. Source readiness is retained along
the same finite graph derivation, not reconstructed from pointer bits. -/
def Relocation.ReadyOrigin (program : RuntimeProgram) (world : World) (map : Relocation) (current : Value) : Prop :=
  ∃ address value, world.Resident address value ∧ value.ResourcesClosed program world ∧
    value.LoansRestored program world ∧
    (current = value ∨ address.root ∈ map.roots ∧ current = map.value value)

theorem Relocation.residentAt_origin {map : Relocation} {value current : Value} {path : List Nat}
    (located : ResidentAt (map.value value) path current) :
    ∃ original, ResidentAt value path original ∧ current = map.value original := by
  have found := ResidentAt.iff_atPath.mp located
  rw [map.value_atPath] at found
  obtain ⟨original,selected,same⟩ := Option.map_eq_some_iff.mp found
  exact ⟨original,ResidentAt.iff_atPath.mpr selected,same.symm⟩

theorem Relocation.ReadyOrigin.nested {program : RuntimeProgram} {world : World} {map : Relocation}
    {current resident : Value} {path : List Nat}
    (origin : map.ReadyOrigin program world current) (located : ResidentAt current path resident) :
    map.ReadyOrigin program world resident := by
  obtain ⟨address,value,stored,closed,restored,unchanged | ⟨included,renamed⟩⟩ := origin
  · subst current
    exact ⟨{address with fields := address.fields ++ path},resident,stored.nested located,
      closed.reachable (.resident (authority := .owner) (incoming := .shared) located),restored.resident located,Or.inl rfl⟩
  · subst current
    obtain ⟨original,inside,rfl⟩ := Relocation.residentAt_origin located
    exact ⟨{address with fields := address.fields ++ path},original,stored.nested inside,
      closed.reachable (.resident (authority := .owner) (incoming := .shared) inside),restored.resident inside,Or.inr ⟨included,rfl⟩⟩

theorem SnapshotMap.target_origin {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} {homes : Table Home} {address : Address} {root : Root} {target : Value}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (atRoot : before.world.root address = some root)
    (stored : (map.copyWorld before.world homes).Stores (map.address address) target) :
    ∃ original, before.world.Stores address original ∧
      (target = original ∨ address.root ∈ map.roots ∧ target = map.value original) := by
  by_cases included : address.root ∈ map.roots
  · change (map.copyWorld before.world homes).read (map.address address) = some target at stored
    rw [selected.copied_read valid atRoot included] at stored
    obtain ⟨original,found,same⟩ := Option.map_eq_some_iff.mp stored
    exact ⟨original,found,Or.inr ⟨included,same.symm⟩⟩
  · change (map.copyWorld before.world homes).read (map.address address) = some target at stored
    rw [Relocation.address_unselected included,Relocation.old_read atRoot] at stored
    exact ⟨target,stored,Or.inl rfl⟩

theorem Relocation.ReadyOrigin.target {program : RuntimeProgram} {world : World} {map : Relocation}
    {address : Address} {original target : Value}
    (stored : world.Stores address original) (closed : original.ResourcesClosed program world)
    (restored : original.LoansRestored program world)
    (origin : target = original ∨ address.root ∈ map.roots ∧ target = map.value original) :
    map.ReadyOrigin program world target :=
  ⟨address,original,World.resident_iff_stores.mpr stored,closed,restored,origin⟩

theorem Relocation.value_initialized {map : Relocation} {value : Value} (initialized : value.Initialized) :
    (map.value value).Initialized := by
  intro path resident located
  obtain ⟨original,inside,rfl⟩ := Relocation.residentAt_origin located
  obtain ⟨live,fields⟩ := initialized path original inside
  refine ⟨?_,?_⟩
  · cases original
    exact live
  · intro field member
    have copied : field.isSome ∈ (map.value original).fields.map Option.isSome := List.mem_map.mpr ⟨field,member,rfl⟩
    rw [relocation_preserves_holes map original] at copied
    obtain ⟨old,member,equal⟩ := List.mem_map.mp copied
    exact equal.symm.trans (fields old member)

/-- One reference-edge proof is used both by graph preservation and by the
transitive restoration consumer. It constructs the actual live target and
its source provenance, including an unchanged external target. -/
theorem CopiesSnapshot.reference_origin {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} {homes : Table Home} {value : Value} {identity : Identity}
    (valid : before.world.WellFormed) (copied : CopiesSnapshot program before suspension map after)
    (origin : map.ReadyOrigin program before.world value) (reference : value.head = .reference identity) :
    ∃ loan, (map.copyWorld before.world homes).loans.get identity = some loan ∧ loan.live = true ∧
      (map.copyWorld before.world homes).Initialized loan.referent ∧
      ∀ target, (map.copyWorld before.world homes).Stores loan.referent target →
        map.ReadyOrigin program before.world target := by
  obtain ⟨address,source,resident,closed,restored,unchanged | ⟨included,renamed⟩⟩ := origin
  · subst value
    obtain ⟨loan,selected,live,⟨target,targetStored,initialized⟩,_⟩ :=
      restored identity .owner .shared ⟨source,.resident .root,reference⟩
    refine ⟨loan,Relocation.old_loan selected,live,
      ⟨target,World.resident_iff_stores.mp (Relocation.old_resident (World.resident_iff_stores.mpr targetStored)),initialized⟩,?_⟩
    intro target stored
    obtain ⟨root,atRoot⟩ := Option.isSome_iff_exists.mp
      (((valid.2.2.2.2.2.2.2.2.2.2.2.2.1 _ loan selected).2.2 live).2)
    have oldStored : before.world.Stores loan.referent target := (Relocation.old_read atRoot).symm.trans stored
    have child := Value.ReachableResident.referent (authority := .owner) (incoming := .shared)
      (.resident (.root (value := source))) reference selected oldStored (.root)
    exact Relocation.ReadyOrigin.target oldStored (closed.reachable child) (restored.reachable child) (Or.inl rfl)
  · subst value
    obtain ⟨previous,head,equal⟩ := Relocation.reference_origin reference
    subst identity
    obtain ⟨loan,selected,live,⟨target,targetStored,initialized⟩,_⟩ :=
      restored previous .owner .shared ⟨source,.resident .root,head⟩
    have shared := copied.storageReady.references address source previous loan included resident head selected
    have selectedLoan := copied.relocation.reference_loan included resident head selected live shared
    refine ⟨map.loanValue loan,copied.relocation.copied_loan valid selected selectedLoan,live,?_,?_⟩
    · by_cases captured : loan.referent.root ∈ map.roots
      · exact ⟨map.value target,World.resident_iff_stores.mp
          (copied.relocation.copied_resident valid (World.resident_iff_stores.mpr targetStored) captured),
          Relocation.value_initialized initialized⟩
      · change (map.copyWorld before.world homes).Initialized (map.address loan.referent)
        rw [Relocation.address_unselected captured]
        exact ⟨target,World.resident_iff_stores.mp (Relocation.old_resident (World.resident_iff_stores.mpr targetStored)),initialized⟩
    · intro target stored
      obtain ⟨root,atRoot⟩ := Option.isSome_iff_exists.mp
        (((valid.2.2.2.2.2.2.2.2.2.2.2.2.1 _ loan selected).2.2 live).2)
      obtain ⟨original,oldStored,node⟩ := copied.relocation.target_origin valid atRoot stored
      have child := Value.ReachableResident.referent (authority := .owner) (incoming := .shared)
        (.resident (.root (value := source))) head selected oldStored (.root)
      exact Relocation.ReadyOrigin.target oldStored (closed.reachable child) (restored.reachable child) node

theorem CopiesSnapshot.reachable_origin {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} {homes : Table Home} {value resident : Value}
    {authority current : Authority} {incoming access : Access}
    (valid : before.world.WellFormed) (copied : CopiesSnapshot program before suspension map after)
    (origin : map.ReadyOrigin program before.world value)
    (reached : value.ReachableResident (map.copyWorld before.world homes) authority incoming resident current access) :
    map.ReadyOrigin program before.world resident := by
  induction reached with
  | resident located => exact origin.nested located
  | referent prior reference found stored located ih =>
      obtain ⟨loan,selected,_,_,targets⟩ := copied.reference_origin (homes := homes) valid ih reference
      have same := Option.some.inj (selected.symm.trans found)
      subst loan
      exact (targets _ stored).nested located
  | resource prior member stored located ih =>
      obtain ⟨address,source,resident,closed,restored,unchanged | ⟨included,renamed⟩⟩ := ih
      · subst_vars
        have held := (closed source .owner .shared (.resident .root)).1 _ member
        obtain ⟨root,atRoot⟩ := held.root valid
        have oldStored := (Relocation.old_read atRoot).symm.trans stored
        have child := Value.ReachableResident.resource (authority := .owner) (incoming := .shared)
          (.resident (.root (value := source))) member oldStored (.root)
        exact (Relocation.ReadyOrigin.target oldStored (closed.reachable child) (restored.reachable child) (Or.inl rfl)).nested located
      · subst_vars
        rw [map.value_resources] at member
        obtain ⟨binding,sourceMember,equal⟩ := List.mem_map.mp member
        subst_vars
        have held := (closed source .owner .shared (.resident .root)).1 binding sourceMember
        obtain ⟨root,atRoot⟩ := held.root valid
        obtain ⟨original,oldStored,node⟩ := copied.relocation.target_origin valid atRoot stored
        have child := Value.ReachableResident.resource (authority := .owner) (incoming := .shared)
          (.resident (.root (value := source))) sourceMember oldStored (.root)
        exact (Relocation.ReadyOrigin.target oldStored (closed.reachable child) (restored.reachable child) node).nested located

theorem CopiesSnapshot.resourcesClosed_origin {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} {homes : Table Home} {value : Value}
    (valid : before.world.WellFormed) (copied : CopiesSnapshot program before suspension map after)
    (origin : map.ReadyOrigin program before.world value) :
    value.ResourcesClosed program (map.copyWorld before.world homes) := by
  intro resident authority access reached
  obtain ⟨address,source,located,closed,restored,unchanged | ⟨included,renamed⟩⟩ := copied.reachable_origin valid origin reached
  · subst resident
    obtain ⟨held,declared⟩ := closed source .owner .shared (.resident .root)
    exact ⟨fun binding member => copied.relocation.old_heldBy valid (held binding member),
      declared.framed (Relocation.old_supportFramed valid closed restored)⟩
  · subst resident
    obtain ⟨held,declared⟩ := closed source .owner .shared (.resident .root)
    refine ⟨?_,copied.invariantClosed valid included located declared⟩
    intro binding member
    rw [map.value_resources] at member
    obtain ⟨original,sourceMember,rfl⟩ := List.mem_map.mp member
    exact copied.relocation.copied_heldBy valid included located sourceMember
      (copied.storageReady.resources address source included located original sourceMember).1 (held original sourceMember)

theorem CopiesSnapshot.resourcesClosed {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} {address : Address} {value : Value}
    (valid : before.world.WellFormed) (copied : CopiesSnapshot program before suspension map after)
    (included : address.root ∈ map.roots) (resident : before.world.Resident address value) :
    (map.value value).ResourcesClosed program after.world := by
  have captured := copied.relocation.roots ▸ included
  obtain ⟨closed,restored⟩ := copied.replayable.1.2 address value captured resident
  rw [copied.result]
  exact copied.resourcesClosed_origin valid ⟨address,value,resident,closed,restored,Or.inr ⟨included,rfl⟩⟩

theorem CopiesSnapshot.loansRestored_origin {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} {homes : Table Home} {value : Value}
    (valid : before.world.WellFormed) (copied : CopiesSnapshot program before suspension map after)
    (origin : map.ReadyOrigin program before.world value) :
    value.LoansRestored program (map.copyWorld before.world homes) := by
  rintro identity authority access ⟨resident,reached,head⟩
  obtain ⟨loan,found,live,initialized,targets⟩ := copied.reference_origin (homes := homes) valid
    (copied.reachable_origin valid origin reached) head
  exact ⟨loan,found,live,initialized,fun target stored => copied.resourcesClosed_origin valid (targets target stored)⟩

theorem CopiesSnapshot.loansRestored {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} {address : Address} {value : Value}
    (valid : before.world.WellFormed) (copied : CopiesSnapshot program before suspension map after)
    (included : address.root ∈ map.roots) (resident : before.world.Resident address value) :
    (map.value value).LoansRestored program after.world := by
  have captured := copied.relocation.roots ▸ included
  obtain ⟨closed,restored⟩ := copied.replayable.1.2 address value captured resident
  rw [copied.result]
  exact copied.loansRestored_origin valid ⟨address,value,resident,closed,restored,Or.inr ⟨included,rfl⟩⟩

theorem SnapshotMap.fresh_root {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} {identity : Identity} (selected : SnapshotMap program before suspension map)
    (included : identity ∈ map.roots.map map.root) : before.world.nextRoot ≤ identity := by
  obtain ⟨old,member,rfl⟩ := List.mem_map.mp included
  simp only [Relocation.root,relocateId,if_pos member,selected.rootBase]
  exact Nat.le_add_right _ _

theorem SnapshotMap.captured_origin {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} {homes : Table Home} {address : Address} {value : Value}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (included : address.root ∈ map.roots.map map.root)
    (resident : (map.copyWorld before.world homes).Resident address value) :
    ∃ original source, original.root ∈ map.roots ∧ before.world.Resident original source ∧
      address = map.address original ∧ value = map.value source := by
  rcases Relocation.resident_origin valid.1 resident with old | copied
  · obtain ⟨root,_,found,_⟩ := old
    exact False.elim (Nat.not_le_of_gt (World.root_bound valid found) (selected.fresh_root included))
  · exact copied

theorem CopiesSnapshot.captured_readyOrigin {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} {homes : Table Home} {address : Address} {value : Value}
    (valid : before.world.WellFormed) (copied : CopiesSnapshot program before suspension map after)
    (included : address.root ∈ map.roots.map map.root)
    (resident : (map.copyWorld before.world homes).Resident address value) :
    map.ReadyOrigin program before.world value := by
  obtain ⟨original,source,selected,located,_,rfl⟩ := copied.relocation.captured_origin valid included resident
  obtain ⟨closed,restored⟩ := copied.replayable.1.2 original source (copied.relocation.roots ▸ selected) located
  exact ⟨original,source,located,closed,restored,Or.inr ⟨selected,rfl⟩⟩

theorem SnapshotMap.initialized {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} {homes : Table Home} {address : Address}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (initialized : before.world.Initialized address) :
    (map.copyWorld before.world homes).Initialized (map.address address) := by
  obtain ⟨value,stored,initialized⟩ := initialized
  by_cases included : address.root ∈ map.roots
  · exact ⟨map.value value,World.resident_iff_stores.mp
      (selected.copied_resident valid (World.resident_iff_stores.mpr stored) included),
      Relocation.value_initialized initialized⟩
  · rw [Relocation.address_unselected included]
    exact ⟨value,World.resident_iff_stores.mp (Relocation.old_resident (World.resident_iff_stores.mpr stored)),initialized⟩

theorem CopiesSnapshot.worldResourcesClosed {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} {homes : Table Home} {address : Address} {root : Root}
    (valid : before.world.WellFormed) (copied : CopiesSnapshot program before suspension map after)
    (atRoot : before.world.root address = some root) (closed : before.world.ResourcesClosed program address) :
    (map.copyWorld before.world homes).ResourcesClosed program (map.address address) := by
  intro target stored
  obtain ⟨original,oldStored,node⟩ := copied.relocation.target_origin valid atRoot stored
  obtain ⟨ready,restored⟩ := closed original oldStored
  have origin := Relocation.ReadyOrigin.target oldStored ready restored node
  exact ⟨copied.resourcesClosed_origin valid origin,copied.loansRestored_origin valid origin⟩

theorem SnapshotMap.captured_loan_origin {program : Kernel.Program} {before : State} {suspension : Suspension}
    {map : Relocation} {homes : Table Home} {identity : Identity} {loan : Loan}
    (valid : before.world.WellFormed) (selected : SnapshotMap program before suspension map)
    (found : (map.copyWorld before.world homes).loans.get identity = some loan) (live : loan.live = true)
    (included : loan.referent.root ∈ map.roots.map map.root) :
    ∃ previous original, before.world.loans.get previous = some original ∧ previous ∈ map.loans ∧
      original.referent.root ∈ map.roots ∧ loan = map.loanValue original := by
  have fresh := selected.fresh_root included
  rcases Relocation.loan_origin valid.2.1 found with old | ⟨previous,original,present,member,_,rfl⟩
  · exact False.elim (Nat.not_le_of_gt (World.live_loan_root_bound valid old live) fresh)
  · refine ⟨previous,original,present,member,?_,rfl⟩
    by_cases captured : original.referent.root ∈ map.roots
    · exact captured
    · change before.world.nextRoot ≤ (map.address original.referent).root at fresh
      rw [Relocation.address_unselected captured] at fresh
      exact False.elim (Nat.not_le_of_gt (World.live_loan_root_bound valid present live) fresh)

/-- The actual suspension admission boundary for the copied roots: every
resident is closed and restored, and every retained restoring/destructor
loan has an initialized, recursively closed target. No post-state
suspensibility premise is used by CopiesSnapshot. -/
theorem CopiesSnapshot.suspensible {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation}
    (valid : before.world.WellFormed) (copied : CopiesSnapshot program before suspension map after) :
    Suspensible program after.world (map.roots.map map.root) := by
  rw [copied.result]
  constructor
  · intro identity loan found live kind relevant
    rcases relevant with included | ⟨address,value,included,resident,head⟩
    · obtain ⟨previous,original,present,_,captured,rfl⟩ := copied.relocation.captured_loan_origin valid found live included
      have obligation := copied.replayable.1.1 previous original present live kind (Or.inl (copied.relocation.roots ▸ captured))
      obtain ⟨root,atRoot⟩ := Option.isSome_iff_exists.mp
        (((valid.2.2.2.2.2.2.2.2.2.2.2.2.1 previous original present).2.2 live).2)
      exact ⟨copied.relocation.initialized valid obligation.1,copied.worldResourcesClosed valid atRoot obligation.2⟩
    · have origin := copied.captured_readyOrigin valid included resident
      obtain ⟨actual,selected,_,initialized,targets⟩ := copied.reference_origin (homes := suspension.homes) valid origin head
      have same := Option.some.inj (selected.symm.trans found)
      subst loan
      exact ⟨initialized,fun target stored =>
        ⟨copied.resourcesClosed_origin valid (targets target stored),copied.loansRestored_origin valid (targets target stored)⟩⟩
  · intro address value included resident
    have origin := copied.captured_readyOrigin valid included resident
    exact ⟨copied.resourcesClosed_origin valid origin,copied.loansRestored_origin valid origin⟩

end Execution
end Glorious.Language
