import GloriousLanguage.LifecyclePreservation
import GloriousLanguage.LoanPreservation

/-! The two admission products the actual post-cancellation cleanup consumes.

*Reference freeness* is the closed stored-value inventory of one loan identity:
no stored resident anywhere still carries that reference handle, and no stored
resident's erased resources name that loan. `ReturnsStorageLoan` and `EndsLoan`
both require exactly this pair, and it is read here from the real `Stores`
relation of every address rather than admitted per ending step.

*Custody discharge* is the inventory of the live owning claims of one custody
and their actual successors. `World.CustodyHandedOff` quantifies over the whole
loan table; a discharge enumerates those claims and carries the successor row
each of them actually received through `ClaimsAllocation`, which is the step the
entry binder performs. This is what `RelinquishesCustody` (and therefore
`finishShell`/`shellDone`) consumes.
-/
namespace Glorious.Language

open Kernel

/-! ## Reference freeness -/

/-- The closed stored-value inventory of one identity: nothing stored anywhere
still names it, neither as an ordinary reference handle nor as an erased
resource authority. -/
def World.ReferenceFree (world : World) (identity : Identity) : Prop :=
  (∀ address value, world.Stores address value → value.head ≠ .reference identity) ∧
  (∀ address value binding, world.Stores address value → binding ∈ value.resources →
    binding.authority.parentLoan ≠ some identity)

theorem World.ReferenceFree.not_references {world : World} {identity : Identity}
    (free : world.ReferenceFree identity) : ¬ world.References identity := by
  rintro ⟨address, value, resident, head⟩
  exact free.1 address value (World.resident_iff_stores.mp resident) head

theorem World.ReferenceFree.not_resourceReferences {world : World} {identity : Identity}
    (free : world.ReferenceFree identity) : ¬ world.ResourceReferences identity := by
  rintro ⟨address, value, binding, resident, member, parent⟩
  exact free.2 address value binding (World.resident_iff_stores.mp resident) member parent

/-- The inventory is exactly the pair of premises the ending transitions
consume: nothing else about a world is used. -/
theorem World.referenceFree_iff {world : World} {identity : Identity} :
    world.ReferenceFree identity ↔ ¬ world.References identity ∧ ¬ world.ResourceReferences identity := by
  constructor
  · intro free
    exact ⟨free.not_references,free.not_resourceReferences⟩
  · rintro ⟨free,resources⟩
    constructor
    · intro address value stored head
      exact free ⟨address,value,World.resident_iff_stores.mpr stored,head⟩
    · intro address value binding stored member parent
      exact resources ⟨address,value,binding,World.resident_iff_stores.mpr stored,member,parent⟩

/-- Retirement only removes one root's liveness, so a cleared identity stays
cleared. -/
theorem World.ReferenceFree.of_retires {before after : World} {retired identity : Identity}
    (free : before.ReferenceFree identity) (retirement : Retires before retired after) :
    after.ReferenceFree identity := by
  have lift : ∀ {address value}, after.Stores address value → before.Stores address value :=
    fun stored => World.resident_iff_stores.mp
      ((retirement.resident).mp (World.resident_iff_stores.mpr stored))
  exact ⟨fun address value stored => free.1 address value (lift stored),
    fun address value binding stored member => free.2 address value binding (lift stored) member⟩

/-- Closing a region only removes it from the live set, so a cleared identity
stays cleared. -/
theorem World.ReferenceFree.of_regionEnds {before after : World} {region identity : Identity}
    (free : before.ReferenceFree identity) (ended : Execution.RegionEnds before region after) :
    after.ReferenceFree identity := by
  have lift : ∀ {address value}, after.Stores address value → before.Stores address value := by
    intro address value stored
    cases ended with
    | intro safe rows => simpa only [World.Stores,World.read,World.root,rows] using stored
  exact ⟨fun address value stored => free.1 address value (lift stored),
    fun address value binding stored member => free.2 address value binding (lift stored) member⟩

/-- The storage-return transition of one requested, unreferenced loan. The
reference inventory, which the machine's own cleanup keeps, discharges the two
`¬ References` premises of the actual rule. -/
theorem ReturnsStorageLoan.of_referenceFree {before : World} {id : Identity} {loan : Loan}
    (found : before.loans.get id = some loan) (live : loan.live = true) (kind : loan.kind = .storageBorrow)
    (requested : loan.returnRequested = true) (free : before.ReferenceFree id)
    (children : ∀ child, before.loans.get child.identity = some child →
      child.parent = some id ∨ id ∈ child.guards → child.live = false) :
    ReturnsStorageLoan before id { before with loans := before.loans.set id { loan with live := false } } :=
  .returned found live kind requested free.not_references free.not_resourceReferences children

/-- The restored-referent loan ending. The reference inventory discharges the
same two premises; initialization and resource closure remain the actual
referent facts they always were. -/
theorem EndsLoan.of_referenceFree {program : RuntimeProgram} {before : World} {id : Identity} {loan : Loan}
    (found : before.loans.get id = some loan) (live : loan.live = true)
    (kind : loan.kind = .restoring ∨ loan.kind = .destructor)
    (initialized : before.Initialized loan.referent)
    (closed : loan.kind = .restoring → before.ResourcesClosed program loan.referent)
    (free : before.ReferenceFree id)
    (children : ∀ child, before.loans.get child.identity = some child →
      child.parent = some id ∨ id ∈ child.guards → child.live = false) :
    EndsLoan program before id { before with loans := before.loans.set id { loan with live := false } } :=
  .restored found live kind initialized closed free.not_references free.not_resourceReferences children

/-! ## Custody discharge -/

/-- One live owning claim of a custody together with the successor row it
actually received: a live owning child with the same referent and a different
recipient. This is the existential `World.CustodyHandedOff` needs, per claim. -/
def World.HandedOffClaim (world : World) (identity : Identity) (custody : ClaimCustody) : Prop :=
  ∃ (original : Loan) (child : Identity) (successor : Loan),
    world.loans.get identity = some original ∧
    world.loans.get child = some successor ∧
    successor.parent = some identity ∧ successor.live = true ∧ successor.kind = .owning ∧
    successor.referent = original.referent ∧
    ∃ recipient : ClaimCustody, successor.custody = some recipient ∧ recipient ≠ custody

/-- The claim inventory of one custody: the identities the exit hands over,
each with its successor. A discharge is what makes the whole-table
`CustodyHandedOff` checkable, since the enumeration is the exit's own resource
interface rather than the full loan table. -/
def World.CustodyDischarge (world : World) (custody : ClaimCustody) : Prop :=
  ∃ claims : List Identity,
    (∀ identity loan, world.loans.get identity = some loan → loan.live = true →
      loan.kind = .owning → loan.custody = some custody → identity ∈ claims) ∧
    ∀ identity ∈ claims, world.HandedOffClaim identity custody

/-- A discharge produces the whole-table custody condition the actual
relinquishment rule consumes. -/
theorem World.CustodyHandedOff.of_discharge {world : World} {custody : ClaimCustody}
    (discharge : world.CustodyDischarge custody) : world.CustodyHandedOff custody := by
  obtain ⟨claims,complete,handed⟩ := discharge
  intro identity loan found live owning custodied
  obtain ⟨original,child,successor,rowFound,childFound,parent,childLive,childOwning,referent,
    recipient,custodiedRow,different⟩ :=
    handed identity (complete identity loan found live owning custodied)
  have same : original = loan := Option.some.inj (rowFound.symm.trans found)
  exact ⟨child,successor,childFound,parent,childLive,childOwning,same ▸ referent,recipient,
    custodiedRow,different⟩

/-- The successor an actual allocation claim creates is exactly the handoff
witness of the claim's owning row: the entry binder's `ClaimsAllocation` step
makes the fresh row a live owning child with the new custody and the same
referent. -/
theorem World.HandedOffClaim.of_claimsAllocation {before after : World} {custody recipient : ClaimCustody}
    {identity : Identity} {authority : Authority} {address : Address}
    (valid : before.WellFormed) (claim : AllocationClaim before authority address)
    (parentEq : authority.parentLoan = some identity)
    (claimed : ClaimsAllocation recipient before authority address before.nextLoan after)
    (different : recipient ≠ custody) : after.HandedOffClaim identity custody := by
  obtain ⟨owner, claimLoan, root, domain, parentRow, claimFound, live, owning, referent, latest⟩ := claim
  have same : identity = owner := Option.some.inj (parentEq.symm.trans parentRow)
  have bound : identity < before.nextLoan := same.symm ▸ World.loanBounds valid claimFound
  cases claimed with
  | claim permission rooted =>
      refine ⟨claimLoan,before.nextLoan,_,?_,Table.get_set _ _ _,parentEq,rfl,rfl,referent.symm,
        recipient,rfl,different⟩
      rw [Table.get_set_other _ _ _ _ (Nat.ne_of_lt bound),same]
      exact claimFound

/-- A later row insertion at another index keeps an already-created successor
valid, so a chain of handoff steps composes. -/
theorem World.HandedOffClaim.retained {before after : World} {identity : Identity}
    {custody : ClaimCustody} {original : Loan} {child : Identity} {successor : Loan}
    {index : Identity} {inserted : Loan}
    (rows : after.loans = before.loans.set index inserted)
    (found : before.loans.get identity = some original)
    (childFound : before.loans.get child = some successor)
    (parent : successor.parent = some identity) (childLive : successor.live = true)
    (childOwning : successor.kind = .owning) (referent : successor.referent = original.referent)
    {recipient : ClaimCustody} (custodied : successor.custody = some recipient)
    (different : recipient ≠ custody) (newIdentity : index ≠ identity) (newChild : index ≠ child) :
    after.HandedOffClaim identity custody :=
  ⟨original,child,successor,
    by rw [rows,Table.get_set_other _ _ _ _ (Ne.symm newIdentity)]; exact found,
    by rw [rows,Table.get_set_other _ _ _ _ (Ne.symm newChild)]; exact childFound,
    parent,childLive,childOwning,referent,recipient,custodied,different⟩


/-! ## Region readiness from the discharges the cleanup performs -/

/-- Region readiness derived from the actual outcomes of the cleanup steps. The
retirements only remove liveness (`liveBefore`), and the enumerated region roots
are exactly the ones they kill; the loan endings do the same for the region's
live loans. What is left is the reservation and binding-pack freedom. So the
`RegionCanEnd` obligation of the region-closing step is read from what the
retirement and ending steps actually produced instead of being assumed. -/
theorem Execution.RegionCanEnd.of_discharged {before after : World} {region : Identity}
    {retired ended : List Identity}
    (roots : ∀ id root, before.roots.get id = some root → root.live = true →
      root.region = region → id ∈ retired)
    (liveBefore : ∀ id root, after.roots.get id = some root → root.live = true →
      before.roots.get id = some root)
    (deadRoots : ∀ id ∈ retired, ∀ root, after.roots.get id = some root → root.live = false)
    (loans : ∀ id loan, before.loans.get id = some loan → loan.live = true →
      loan.region = region → id ∈ ended)
    (liveLoanBefore : ∀ id loan, after.loans.get id = some loan → loan.live = true →
      before.loans.get id = some loan)
    (deadLoans : ∀ id ∈ ended, ∀ loan, after.loans.get id = some loan → loan.live = false)
    (reservations : ∀ id available, after.availability.get id = some available →
      available.active = true → available.region ≠ region)
    (packings : ∀ address value pack, after.Resident address value →
      value.head = .bindings pack → pack.region ≠ region) :
    Execution.RegionCanEnd after region :=
  ⟨fun id root found live same =>
      absurd (deadRoots id (roots id root (liveBefore id root found live) live same) root found) (by simp [live]),
   fun id loan found live same =>
      absurd (deadLoans id (loans id loan (liveLoanBefore id loan found live) live same) loan found) (by simp [live]),
   reservations,packings⟩

end Glorious.Language
