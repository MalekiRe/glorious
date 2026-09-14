import GloriousLanguage.ReceiverPreservation
import GloriousLanguage.CleanupPreservation
import GloriousLanguage.StorageFraming
import GloriousLanguage.InvocationLending
import GloriousLanguage.CapabilityModels

/-! Invocation lease cleanup uses the actual reference destruction and
releaseLoan machine path.

This module keeps the two products of that path that other checked modules
consume: the loan-release frame law (`World.LoanReleaseFrame`, its transport
through the actual `EndsLoan` transition and its `CanEndStorage` clause, used by
`PrivateStorage`) and the invocation-lending resident projection
(`Kernel.LendsResident.lease_resident`, used by `ForeignAuthority`).

The earlier draft of the parent/guard release cascade that lived here
(`World.InitializedAncestors`, `releaseLoan_cleanup`, `referenceRoot_cleanup`,
`activationReference_cleanup`, `lendsResident_cleanup`) is superseded rather
than re-established: its `EndsLoan.restored` premise now carries
`ResourcesClosed program loan.referent` for restoring loans, which the old
`Initialized`-only ancestor obligation does not supply, and no checked module
consumed those statements. The actual pending-return drain of the destructor
chain is executed in `CleanupDrain`, against the world invariant the machine's
own `releaseLoan` rules consume. -/
namespace Glorious.Language

/-- The real release cascade retains all rows and metadata, may only turn
liveness off, and creates no live authority. Dead bookkeeping remains readable. -/
structure World.LoanReleaseFrame (before after : World) : Prop where
  rest : after = { before with loans := after.loans }
  live_origin : ∀ id loan, after.loans.get id = some loan → loan.live = true → before.loans.get id = some loan
  rows : ∀ id loan, before.loans.get id = some loan →
    ∃ current, after.loans.get id = some current ∧ (current = loan ∨ current = { loan with live := false })

theorem World.LoanReleaseFrame.refl (world : World) : world.LoanReleaseFrame world :=
  ⟨rfl,fun _ _ found _ => found,fun _ loan found => ⟨loan,found,Or.inl rfl⟩⟩

theorem World.LoanReleaseFrame.trans {before middle after : World}
    (first : before.LoanReleaseFrame middle) (last : middle.LoanReleaseFrame after) :
    before.LoanReleaseFrame after := by
  refine ⟨?_,fun _ _ found live => first.live_origin _ _ (last.live_origin _ _ found live) live,?_⟩
  · calc
      after = { middle with loans := after.loans } := last.rest
      _ = { before with loans := after.loans } := by rw [first.rest]
  · intro id loan found
    obtain ⟨current,currentAt,changed⟩ := first.rows id loan found
    obtain ⟨final,finalAt,ending⟩ := last.rows id current currentAt
    refine ⟨final,finalAt,?_⟩
    rcases changed with rfl | rfl <;> rcases ending with rfl | rfl
    · exact Or.inl rfl
    all_goals exact Or.inr rfl

theorem World.loanReleaseFrame_set_dead {world : World} {id : Identity} {loan : Loan}
    (found : world.loans.get id = some loan) :
    world.LoanReleaseFrame { world with loans := world.loans.set id { loan with live := false } } := by
  refine ⟨rfl,?_,?_⟩
  · intro other row selected live
    by_cases same : other = id
    · subst other
      have equal : ({ loan with live := false } : Loan) = row :=
        Option.some.inj ((Table.get_set _ _ _).symm.trans selected)
      exact absurd (equal ▸ rfl : row.live = false) (by simp [live])
    · simpa only [Table.get_set_other _ _ _ _ same] using selected
  · intro other row selected
    by_cases same : other = id
    · subst other
      have same := Option.some.inj (selected.symm.trans found)
      subst row
      exact ⟨_,Table.get_set _ _ _,Or.inr rfl⟩
    · exact ⟨row,(Table.get_set_other _ _ _ _ same).trans selected,Or.inl rfl⟩

theorem EndsLoan.releaseFrame {program : RuntimeProgram} {before after : World} {id : Identity}
    (ended : EndsLoan program before id after) : before.LoanReleaseFrame after := by
  cases ended with
  | restored found _ _ _ _ _ _ _ => exact World.loanReleaseFrame_set_dead found

theorem World.LoanReleaseFrame.dead_retained {before after : World} {id : Identity} {loan : Loan}
    (frame : before.LoanReleaseFrame after) (found : before.loans.get id = some loan) (dead : loan.live = false) :
    after.loans.get id = some loan := by
  obtain ⟨current,selected,unchanged | ended⟩ := frame.rows id loan found
  · exact unchanged ▸ selected
  · have same : { loan with live := false } = loan := by cases loan; simp_all
    exact (ended.trans same) ▸ selected

theorem AncestorLoan.loanReleaseFrame {before after : World} {parent child : Identity}
    (related : AncestorLoan before parent child) (frame : before.LoanReleaseFrame after) :
    AncestorLoan after parent child := by
  apply related.transport_parents
  intro id loan found
  obtain ⟨current,selected,same⟩ := frame.rows id loan found
  exact ⟨current,selected,by rcases same with rfl | rfl <;> rfl⟩

theorem World.Stores.loanReleaseFrame {before after : World} {address : Address} {value : Value}
    (stored : before.Stores address value) (frame : before.LoanReleaseFrame after) : after.Stores address value := by
  rw [frame.rest]
  exact stored

theorem Permitted.of_loanReleaseFrame {world after : World} {requested : Access} {address : Address}
    (permission : Permitted world .owner requested address)
    (frame : world.LoanReleaseFrame after) (existence : ∃ root, after.root address = some root) :
    Permitted after .owner requested address :=
  ⟨existence,fun id loan found live overlap conflict =>
    permission.2 id loan (frame.live_origin id loan found live) live overlap conflict⟩



/-- A retained resident handle remains a live row by the produced world's
structural invariant. Release framing identifies it with its original row. -/
theorem World.LoanReleaseFrame.reference_retained {before after : World} {id : Identity} {loan : Loan}
    (frame : before.LoanReleaseFrame after) (well : after.WellFormed)
    (referenced : before.References id) (found : before.loans.get id = some loan) : after.loans.get id = some loan := by
  have retained := referenced.roots_congr (congrArg World.roots frame.rest)
  obtain ⟨address,value,resident,head⟩ := retained
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,references,_,_,_,_,_⟩ := well
  obtain ⟨current,selected,live⟩ := references address value id resident head
  exact Option.some.inj ((frame.live_origin id current selected live).symm.trans found) ▸ selected

theorem LoanPermission.loanReleaseFrame {before after : World} {id : Identity} {access : Access} {address : Address}
    (permission : LoanPermission before id access address) (frame : before.LoanReleaseFrame after)
    (well : after.WellFormed) (referenced : before.References id) : LoanPermission after id access address := by
  obtain ⟨active,found,live,root,generation,path,mode,excluded,_,dependent⟩ := permission
  have retained := frame.reference_retained well referenced found
  refine ⟨active,retained,live,root,generation,path,mode,?_,?_,?_⟩
  · intro other loan selected living different overlap conflict
    exact (excluded other loan (frame.live_origin other loan selected living) living different overlap conflict).loanReleaseFrame frame
  · intro guard member
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,guards,_⟩ := well
    obtain ⟨carrier,selected,_,living⟩ := guards id active guard retained member
    exact ⟨carrier,selected,living live⟩
  · intro other loan selected living member
    exact dependent other loan (frame.live_origin other loan selected living) living member

/-- Only actual resident carriers justify preserving loan or guarded
permissions. There is deliberately no permission claim for arbitrary ended loans. -/
theorem World.LoanReleaseFrame.permitted {before after : World} {authority : Authority}
    {access : Access} {address : Address} (frame : before.LoanReleaseFrame after) (well : after.WellFormed)
    (permission : Permitted before authority access address)
    (held : ∀ id ∈ authority.carriers, before.References id) : Permitted after authority access address := by
  have root : ∃ root, after.root address = some root := by rw [frame.rest]; exact permission.root
  induction authority with
  | owner => exact permission.of_loanReleaseFrame frame root
  | loan id => exact ⟨root,permission.2.loanReleaseFrame frame well (held id (by simp [Authority.carriers]))⟩
  | shared backing ih => exact ⟨root,permission.2.1,ih permission.2.2 held⟩
  | guarded backing carrier ih =>
      have referenced := held carrier (by simp [Authority.carriers])
      obtain ⟨loan,found,allowed⟩ := permission.2.2
      exact ⟨root,ih permission.2.1 (fun id member => held id (by simp [Authority.carriers,member])),
        loan,frame.reference_retained well referenced found,allowed.loanReleaseFrame frame well referenced⟩


theorem World.LoanReleaseFrame.canEndStorage {before after : World} {id : Identity}
    (frame : before.LoanReleaseFrame after) (safe : CanEndStorage before id) : CanEndStorage after id := by
  refine ⟨fun key loan found live => safe.1 key loan (frame.live_origin key loan found live) live,?_,?_⟩
  · intro key available found active address member
    have old : before.availability.get key = some available := by
      simpa only [congrArg World.availability frame.rest] using found
    exact safe.2.1 key available old active address member
  · simpa only [congrArg World.roots frame.rest] using safe.2.2

/-- Cleanup consumes the resident projection of the same lease-origin
product used by retained invocation contexts. -/
theorem Kernel.LendsResident.lease_resident {program : RuntimeProgram} {before after : World}
    {activation scope region address authority access lease permission}
    (lent : Kernel.LendsResident program activation scope region before address authority access lease permission after)
    (borrowed : access ≠ .owned) :
    ∃ witness owner mode type sourceRegion, lease = some witness ∧ witness.handle.fields = [] ∧
      after.Stores witness.handle (.resident owner (.reference mode (.runtimeRegion sourceRegion) type)
        (.reference witness.loan) true []) := by
  obtain ⟨witness,root,owner,mode,type,sourceRegion,selected,_,whole,found,home,atRegion,borrowedRegion,stored,_⟩ :=
    lent.lease_origin borrowed
  exact ⟨witness,owner,mode,type,sourceRegion,selected,whole,stored⟩

end Glorious.Language
