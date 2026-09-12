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

/-- Proof view of a release cascade: only loan liveness changes, and every
remaining live loan is an unchanged pre-existing authority. -/
def World.LoanReleaseFrame (before after : World) : Prop :=
  after = { before with loans := after.loans } ∧
  ∀ id loan, after.loans.get id = some loan → loan.live = true → before.loans.get id = some loan

theorem World.LoanReleaseFrame.refl (world : World) : world.LoanReleaseFrame world :=
  ⟨rfl,fun _ _ found _ => found⟩

theorem World.LoanReleaseFrame.trans {before middle after : World}
    (first : before.LoanReleaseFrame middle) (last : middle.LoanReleaseFrame after) :
    before.LoanReleaseFrame after := by
  refine ⟨?_,fun _ _ found live => first.2 _ _ (last.2 _ _ found live) live⟩
  calc
    after = { middle with loans := after.loans } := last.1
    _ = { before with loans := after.loans } := by rw [first.1]

theorem EndsLoan.releaseFrame {program : RuntimeProgram} {before after : World} {id : Identity}
    (ended : EndsLoan program before id after) : before.LoanReleaseFrame after := by
  refine ⟨?_,fun _ _ found live => ended.live_origin found live⟩
  cases ended
  rfl

theorem World.LoanReleaseFrame.canEndStorage {before after : World} {id : Identity}
    (frame : before.LoanReleaseFrame after) (safe : CanEndStorage before id) : CanEndStorage after id := by
  refine ⟨fun key loan found live => safe.1 key loan (frame.2 key loan found live) live,?_,?_⟩
  · intro key available found active address member
    have old : before.availability.get key = some available := by
      simpa only [congrArg World.availability frame.1] using found
    exact safe.2.1 key available old active address member
  · simpa only [congrArg World.roots frame.1] using safe.2.2

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
