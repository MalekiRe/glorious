import GloriousLanguage.LifecyclePreservation
import GloriousLanguage.LoanPreservation
import GloriousLanguage.LoanResourceRows
import GloriousLanguage.InputLending

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

theorem World.HandedOffClaim.successor {world : World} {identity : Identity} {custody : ClaimCustody} {loan : Loan}
    (handed : world.HandedOffClaim identity custody) (found : world.loans.get identity = some loan) :
    ∃ child successor, world.loans.get child = some successor ∧ successor.parent = some identity ∧
      successor.live = true ∧ successor.kind = .owning ∧ successor.referent = loan.referent ∧
      ∃ recipient, successor.custody = some recipient ∧ recipient ≠ custody := by
  obtain ⟨original,child,successor,rowFound,childFound,parent,childLive,childOwning,referent,
    recipient,custodied,different⟩ := handed
  have same : original = loan := Option.some.inj (rowFound.symm.trans found)
  exact ⟨child,successor,childFound,parent,childLive,childOwning,same ▸ referent,recipient,custodied,different⟩


/-- A discharge produces the whole-table custody condition the actual
relinquishment rule consumes. -/
theorem World.CustodyHandedOff.of_discharge {world : World} {custody : ClaimCustody}
    (discharge : world.CustodyDischarge custody) : world.CustodyHandedOff custody := by
  obtain ⟨claims,complete,handed⟩ := discharge
  intro identity loan found live owning custodied
  exact (handed identity (complete identity loan found live owning custodied)).successor found

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


/-! ## Caller custody through the actual ordered input binder -/

/-- Every live owning claim of the outgoing custody is either already handed
off or names an original allocation port still to be bound. This is finite
input-interface coverage, not a post-entry relinquishment promise. -/
def World.CustodyCovered (world : World) (custody : ClaimCustody) (inputs : List Kernel.InvocationInput) : Prop :=
  ∀ id loan, world.loans.get id = some loan → loan.live = true → loan.kind = .owning → loan.custody = some custody →
    world.HandedOffClaim id custody ∨ ∃ input ∈ inputs, ∃ identity type,
      input.formal = .allocation identity type ∧ input.authority.parentLoan = some id

theorem Kernel.LendsResident.custodyFrame {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {address : Address} {authority result : Authority} {access : Access}
    {lease : Option Kernel.InvocationLease} {recipient : ClaimCustody}
    (lent : Kernel.LendsResident program activation scope region before address authority access lease result after)
    (valid : before.WellFormed) : before.CustodyTransferFrame after recipient := by
  cases lent with
  | owned => exact .of_loans rfl
  | lent _ _ _ allocated formed =>
      apply (World.CustodyTransferFrame.of_loans allocated.loans).trans
      cases formed
      exact .of_fresh (Allocates.wellFormed valid allocated) rfl (Or.inl rfl)

theorem Kernel.BindsInputAt.custodyFrame {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {before after : World} {input : Kernel.InvocationInput} {binding : Kernel.Binding}
    (bound : Kernel.BindsInputAt program recipient activation scope region before input binding after)
    (valid : before.WellFormed) : before.CustodyTransferFrame after recipient := by
  cases bound with
  | lent _ _ _ _ _ _ _ lent => exact lent.custodyFrame valid
  | owned _ _ _ _ _ allocated moved => exact .of_loans (moved.loans.trans allocated.loans)
  | storage _ _ _ claimed => cases claimed; exact .of_fresh valid rfl (Or.inr rfl)
  | allocation _ _ _ _ moved =>
      obtain ⟨_,_,row⟩ := moved.rowCustodyTransferred
      exact row.frame
  | guardedAllocation _ _ _ _ _ claimed => cases claimed; exact .of_fresh valid rfl (Or.inr rfl)
  | loan _ _ _ _ moved =>
      rcases moved.rows with same | ⟨_,_,row⟩
      · exact .of_loans (congrArg World.loans same)
      · exact row.frame

theorem Kernel.BindsInputsAttemptFor.custodyFrame {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {footprint : List Address} {before after : World}
    {inputs : List Kernel.InvocationInput} {bindings : Kernel.Environment} {outcome : Kernel.PreparationOutcome}
    (bound : Kernel.BindsInputsAttemptFor program recipient activation scope region footprint before inputs bindings after outcome)
    (valid : before.WellFormed) : before.CustodyTransferFrame after recipient := by
  induction bound with
  | nil | exhausted => exact .of_loans rfl
  | cons _ head _ ih => exact (head.custodyFrame valid).trans (ih (head.wellFormed valid))


theorem World.HandedOffClaim.custodyFrame {before after : World} {id : Identity} {custody recipient : ClaimCustody}
    (handed : before.HandedOffClaim id custody) (frame : before.CustodyTransferFrame after recipient)
    (different : recipient ≠ custody) : after.HandedOffClaim id custody := by
  obtain ⟨original,child,successor,originalAt,childAt,parent,live,kind,referent,owner,custodied,ownerDifferent⟩ := handed
  obtain ⟨current,selected,changed⟩ := frame.rows id original originalAt
  obtain ⟨next,nextAt,nextChanged⟩ := frame.rows child successor childAt
  have originalShape : current.permissionState = original.permissionState := by rcases changed with rfl | rfl <;> rfl
  have childShape : next.permissionState = successor.permissionState := by rcases nextChanged with rfl | rfl <;> rfl
  refine ⟨current,child,next,selected,nextAt,(congrArg Loan.parent childShape).trans parent,
    (congrArg Loan.live childShape).trans live,(congrArg Loan.kind childShape).trans kind,
    (congrArg Loan.referent childShape).trans (referent.trans (congrArg Loan.referent originalShape).symm),?_⟩
  rcases nextChanged with rfl | rfl
  · exact ⟨owner,custodied,ownerDifferent⟩
  · exact ⟨recipient,rfl,different⟩

theorem World.CustodyCovered.custodyFrame {before after : World} {custody recipient : ClaimCustody}
    {inputs : List Kernel.InvocationInput} (covered : before.CustodyCovered custody inputs)
    (frame : before.CustodyTransferFrame after recipient) (different : recipient ≠ custody) :
    after.CustodyCovered custody inputs := by
  intro id loan found live kind held
  rcases covered id loan (frame.outside id loan custody different found held) live kind held with handed | input
  · exact Or.inl (handed.custodyFrame frame different)
  · exact Or.inr input

/-- A real allocation port either moves its owning row to the recipient or
creates the fresh guarded owning child. Both discharge the old custodian. -/
theorem Kernel.BindsInputAt.handoff_claim {program : RuntimeProgram} {recipient custody : ClaimCustody}
    {activation scope region : Identity} {before after : World} {input : Kernel.InvocationInput} {binding : Kernel.Binding}
    {identity name : Identity} {type : Term} {loan : Loan}
    (bound : Kernel.BindsInputAt program recipient activation scope region before input binding after)
    (valid : before.WellFormed) (different : recipient ≠ custody)
    (formal : input.formal = .allocation name type) (parent : input.authority.parentLoan = some identity)
    (found : after.loans.get identity = some loan) (held : loan.custody = some custody) :
    after.HandedOffClaim identity custody := by
  cases bound with
  | lent _ _ resident _ _ _ _ _ | owned _ _ resident _ _ _ _ => simp [formal,Kernel.InputFormal.IsResident] at resident
  | storage _ selected _ _ | loan _ selected _ _ _ => cases selected.symm.trans formal
  | allocation _ _ _ _ moved =>
      cases moved with
      | @transfer key original authority _ _ =>
          change input.authority = .loan key at authority
          have same : key = identity := by simpa only [authority,Authority.parentLoan,Option.some.injEq] using parent
          subst identity
          have same : { original with custody := some recipient } = loan := by
            simpa only [Table.get_set,Option.some.injEq] using found
          subst loan
          exact False.elim (different (Option.some.inj held))
  | guardedAllocation _ _ _ _ _ claimed =>
      cases claimed with
      | claim claim permission rooted =>
          exact World.HandedOffClaim.of_claimsAllocation valid claim parent (.claim claim permission rooted) different

theorem World.CustodyCovered.bindInput {program : RuntimeProgram} {recipient custody : ClaimCustody}
    {activation scope region : Identity} {before after : World} {head : Kernel.InvocationInput}
    {rest : List Kernel.InvocationInput} {binding : Kernel.Binding}
    (covered : before.CustodyCovered custody (head :: rest)) (valid : before.WellFormed)
    (bound : Kernel.BindsInputAt program recipient activation scope region before head binding after)
    (different : recipient ≠ custody) : after.CustodyCovered custody rest := by
  intro id loan found live kind held
  rcases (covered.custodyFrame (bound.custodyFrame valid) different) id loan found live kind held with handed |
    ⟨input,member,name,type,formal,parent⟩
  · exact Or.inl handed
  · rcases List.mem_cons.mp member with same | remaining
    · subst input
      exact Or.inl (bound.handoff_claim valid different formal parent found held)
    · exact Or.inr ⟨input,remaining,name,type,formal,parent⟩

/-- All pending allocation ports are consumed by the successful real fold.
The outgoing custody's owning obligations are discharged without assuming a
successful relinquishment or an invariant of an arbitrary future world. -/
theorem Kernel.BindsInputsFor.custody_handedOff {program : RuntimeProgram} {recipient custody : ClaimCustody}
    {activation scope region : Identity} {footprint : List Address} {before after : World}
    {inputs : List Kernel.InvocationInput} {bindings : Kernel.Environment}
    (bound : Kernel.BindsInputsFor program recipient activation scope region footprint before inputs bindings after)
    (valid : before.WellFormed) (different : recipient ≠ custody) (covered : before.CustodyCovered custody inputs) :
    after.CustodyHandedOff custody := by
  induction bound using Kernel.BindsInputsFor.inductionOn with
  | nil world =>
      intro id loan found live kind held
      rcases covered id loan found live kind held with handed | ⟨input,member,_⟩
      · exact handed.successor found
      · cases member
  | cons _ head _ ih => exact ih (head.wellFormed valid) (covered.bindInput valid head different)


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
