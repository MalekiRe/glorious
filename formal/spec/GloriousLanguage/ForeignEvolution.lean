import GloriousLanguage.ForeignPreservation

/-! Authority metadata of the actual host mutation producers. Fresh roots do
not replace an existing storage home. A producer may add loan rows (exterior
allocation, buffer allocation, reference formation) or rewrite existing rows
in place (claim release, return, loan end); it never drops a recorded row, and
it never turns a dead row into a live one. -/
namespace Glorious.Language

open Kernel Execution Memory

structure World.HomeExtension (before after : World) : Prop where
  counter : before.nextRoot ≤ after.nextRoot
  homes : ∀ id, id < before.nextRoot →
    (after.roots.get id).map Root.home = (before.roots.get id).map Root.home

theorem World.HomeExtension.refl (world : World) : world.HomeExtension world :=
  ⟨Nat.le_refl _,fun _ _ => rfl⟩

theorem World.HomeExtension.trans {before middle after : World}
    (first : before.HomeExtension middle) (last : middle.HomeExtension after) : before.HomeExtension after :=
  ⟨Nat.le_trans first.counter last.counter,fun id bound =>
    (last.homes id (Nat.lt_of_lt_of_le bound first.counter)).trans (first.homes id bound)⟩

theorem World.HomeExtension.of_locations {before after : World}
    (counter : before.nextRoot ≤ after.nextRoot)
    (locations : ∀ id, (after.roots.get id).map Root.location = (before.roots.get id).map Root.location) :
    before.HomeExtension after := by
  refine ⟨counter,?_⟩
  intro id _
  have same := congrArg (Option.map Root.home) (locations id)
  simpa only [Option.map_map,Function.comp_def,Root.location] using same

/-- Home extension depends only on the root table and the root frontier, so an
administrative loan-table update transports it unchanged. -/
theorem World.HomeExtension.congr_roots {before middle after : World}
    (extended : before.HomeExtension middle) (roots : after.roots = middle.roots)
    (nextRoot : after.nextRoot = middle.nextRoot) : before.HomeExtension after := by
  refine ⟨?_,?_⟩
  · rw [nextRoot]; exact extended.counter
  · intro id bound
    rw [roots]; exact extended.homes id bound

structure World.AuthorityStable (before after : World) : Prop where
  homes : before.HomeExtension after
  loans : after.loans = before.loans

theorem World.AuthorityStable.refl (world : World) : world.AuthorityStable world :=
  ⟨.refl world,rfl⟩

theorem World.AuthorityStable.trans {before middle after : World}
    (first : before.AuthorityStable middle) (last : middle.AuthorityStable after) : before.AuthorityStable after :=
  ⟨first.homes.trans last.homes,last.loans.trans first.loans⟩

theorem World.AuthorityStable.recorded {before after : World} (stable : before.AuthorityStable after)
    (authority : Authority) (recorded : authority.Recorded before.loans) : authority.Recorded after.loans :=
  stable.loans.symm ▸ recorded

theorem World.write_authorityStable {before after : World} {address : Address} {value : Option Value}
    (written : before.write address value = some after) : before.AuthorityStable after :=
  ⟨.of_locations (Nat.le_of_eq (congrArg World.nextRoot (World.write_rest written)).symm)
      (World.write_locations written),World.write_loans written⟩

/-- A row-preserving loan relation keeps every recorded authority: the actual
claim-release, relinquishment and return producers rewrite rows in place. -/
theorem Authority.Recorded.rewrite_loans {authority : Authority} {before after : Table Loan}
    (records : ∀ id loan, before.get id = some loan → ∃ current, after.get id = some current)
    (recorded : authority.Recorded before) : authority.Recorded after :=
  recorded.transport records

theorem Allocates.authorityStable {program : Program} {before after : World}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) : before.AuthorityStable after := by
  cases allocated
  exact ⟨⟨Nat.le_succ _,fun id bound => by
    simp only [Table.get_set_other _ _ _ _ (Nat.ne_of_lt bound)]⟩,rfl⟩

theorem Transfers.authorityStable {program : RuntimeProgram} {before after : World} {authority source destination}
    (transferred : Transfers program before authority source destination after) : before.AuthorityStable after := by
  cases transferred with
  | move _ _ _ _ _ _ _ clear install =>
    exact (World.write_authorityStable clear).trans (World.write_authorityStable install)

theorem Copies.authorityStable {program : RuntimeProgram} {before after : World} {authority source destination}
    (copied : Copies program before authority source destination after) : before.AuthorityStable after := by
  cases copied with
  | copy _ _ _ _ _ _ _ written =>
    have stable := World.write_authorityStable written
    exact ⟨⟨stable.homes.counter,stable.homes.homes⟩,stable.loans⟩

theorem Acquires.authorityStable {program : RuntimeProgram} {before after : World} {authority force source destination}
    (acquired : Acquires program before authority force source destination after) : before.AuthorityStable after := by
  cases acquired with
  | explicitMove moved => exact moved.authorityStable
  | copy copied => exact copied.authorityStable
  | move _ _ _ moved => exact moved.authorityStable

theorem NewValue.authorityStable {program : RuntimeProgram} {before after : World} {destination type head sources}
    (constructed : NewValue program before destination type head sources after) : before.AuthorityStable after :=
  ⟨.of_locations (Nat.le_of_eq (congrArg World.nextRoot constructed.rest).symm) constructed.locations,
    by have same := congrArg World.loans constructed.rest; exact same⟩

theorem FormsLoan.homeExtension {program : RuntimeProgram} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination}
    (borrowed : FormsLoan program purpose before authority mode region referent destination after) :
    before.HomeExtension after := by
  apply World.HomeExtension.of_locations ?_ borrowed.locations
  cases borrowed with
  | borrow _ _ _ _ _ _ _ _ _ _ written => exact (World.write_authorityStable written).homes.counter

theorem FormsLoan.recorded {program : RuntimeProgram} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination}
    (borrowed : FormsLoan program purpose before authority mode region referent destination after)
    (saved : Authority) (recorded : saved.Recorded before.loans) : saved.Recorded after.loans := by
  cases borrowed
  exact recorded.set _ _

theorem FormsLoan.loan_origin {program : RuntimeProgram} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination} {id : Identity} {loan : Loan}
    (borrowed : FormsLoan program purpose before authority mode region referent destination after)
    (found : after.loans.get id = some loan) :
    before.loans.get id = some loan ∨ loan.referent = referent := by
  cases borrowed
  by_cases same : id = before.nextLoan
  · subst id
    simp only [Table.get_set,Option.some.injEq] at found
    subst loan
    exact Or.inr rfl
  · exact Or.inl (by simpa only [Table.get_set_other _ _ _ _ same] using found)

theorem EndsLoan.homeExtension {program : RuntimeProgram} {before after : World} {id : Identity}
    (ended : EndsLoan program before id after) : before.HomeExtension after := by
  cases ended
  exact ⟨Nat.le_refl _,fun _ _ => rfl⟩

theorem EndsLoan.recorded {program : RuntimeProgram} {before after : World} {id : Identity}
    (ended : EndsLoan program before id after)
    (authority : Authority) (recorded : authority.Recorded before.loans) : authority.Recorded after.loans := by
  cases ended
  exact recorded.set _ _

/-- Ending a loan removes only that row's liveness, so a live row after the
transition is the same row of the pre-state. -/
theorem EndsLoan.loan_live_before {program : RuntimeProgram} {before after : World} {id : Identity}
    (ended : EndsLoan program before id after) {key : Identity} {loan : Loan}
    (found : after.loans.get key = some loan) (live : loan.live = true) :
    before.loans.get key = some loan := by
  cases ended with
  | restored selected _ _ _ _ _ _ _ =>
    by_cases same : key = id
    · subst key
      rw [Table.get_set] at found
      cases found
      exact absurd live (by simp)
    · exact by simpa only [Table.get_set_other _ _ _ _ same] using found

theorem ReturnsStorageLoan.homeExtension {before after : World} {id : Identity}
    (returned : ReturnsStorageLoan before id after) : before.HomeExtension after := by
  cases returned
  exact ⟨Nat.le_refl _,fun _ _ => rfl⟩

theorem ReturnsStorageLoan.recorded {before after : World} {id : Identity}
    (returned : ReturnsStorageLoan before id after)
    (authority : Authority) (recorded : authority.Recorded before.loans) : authority.Recorded after.loans := by
  cases returned
  exact recorded.set _ _

theorem ReleasesStorageClaims.homeExtension {before after : World} {place : ResolvedPlace}
    (released : ReleasesStorageClaims before place after) : before.HomeExtension after := by
  cases released
  exact .of_locations (Nat.le_refl _) (by intro id; rfl)

/-- The released loan table is the pre-state table with the rows of the
retired root's closure marked dead; this is the same map as `as_liveness`,
written with the projection shape used by lookup lemmas. -/
theorem ReleasesStorageClaims.get_map {before after : World} {place : ResolvedPlace}
    (released : ReleasesStorageClaims before place after) (id : Identity) :
    after.loans.get id = (before.loans.get id).map
      (fun loan => { loan with live := decide (loan.referent.root ≠ place.address.root) && loan.live }) := by
  rw [released.as_liveness]
  exact Table.get_map_values before.loans
    (fun loan => { loan with live := decide (loan.referent.root ≠ place.address.root) && loan.live }) id

theorem ReleasesStorageClaims.recorded {before after : World} {place : ResolvedPlace}
    (released : ReleasesStorageClaims before place after) (authority : Authority)
    (recorded : authority.Recorded before.loans) : authority.Recorded after.loans :=
  Authority.Recorded.rewrite_loans (fun id loan found => by
    rw [released.get_map,found]
    exact ⟨_,rfl⟩) recorded

/-- Claim release marks only the retired root's rows dead, so a live row keeps
its pre-state referent. -/
theorem ReleasesStorageClaims.loan_live_before {before after : World} {place : ResolvedPlace}
    (released : ReleasesStorageClaims before place after) {id : Identity} {loan : Loan}
    (found : after.loans.get id = some loan) (live : loan.live = true) :
    ∃ original, before.loans.get id = some original ∧ original.live = true ∧
      loan.referent = original.referent := by
  rw [released.get_map] at found
  cases original : before.loans.get id with
  | none => rw [original] at found; exact absurd found (by simp)
  | some row =>
    rw [original] at found
    simp only [Option.map_some,Option.some.injEq] at found
    cases found
    by_cases same : row.referent.root = place.address.root
    · simp only [same,ne_eq,not_true_eq_false,decide_false,Bool.false_and] at live
      exact absurd live Bool.false_ne_true
    · have decided : decide (row.referent.root ≠ place.address.root) = true := by
        simp only [decide_eq_true_eq]; exact same
      exact ⟨row,rfl,(by simpa only [decided,Bool.true_and] using live),rfl⟩

theorem Retires.authorityStable {before after : World} {id : Identity} (retired : Retires before id after) :
    before.AuthorityStable after := by
  cases retired with
  | vacant found _ _ _ =>
    refine ⟨⟨Nat.le_refl _,?_⟩,rfl⟩
    intro key _
    by_cases same : key = id
    · subst key
      simp only [Table.get_set,found,Option.map_some]
    · simp only [Table.get_set_other _ _ _ _ same]

theorem Execution.RegionEnds.authorityStable {before after : World} {region : Identity}
    (ended : RegionEnds before region after) : before.AuthorityStable after := by
  rcases ended with ⟨_,_,_,_,rfl⟩
  exact ⟨⟨Nat.le_refl _,fun _ _ => rfl⟩,rfl⟩

theorem Clears.authorityStable {before after : World} {addresses : List Address}
    (cleared : Clears before addresses after) : before.AuthorityStable after :=
  ⟨.of_locations (Nat.le_of_eq (congrArg World.nextRoot cleared.rest).symm) cleared.locations,cleared.loans⟩

theorem Memory.InstallsResidents.authorityStable {program : Program} {before after : World}
    {addresses : List Address} {values : List (Option Value)}
    (installed : InstallsResidents program before addresses values after) : before.AuthorityStable after :=
  ⟨.of_locations (Nat.le_of_eq (congrArg World.nextRoot installed.rest).symm) installed.locations,
    by have same := congrArg World.loans installed.rest; exact same⟩

theorem Memory.BulkMove.authorityStable {program : RuntimeProgram} {before after : World} {sources destinations}
    (moved : BulkMove program before sources destinations after) : before.AuthorityStable after := by
  obtain ⟨_,_,_,_,_,_,_,_,cleared,installed⟩ := moved
  exact cleared.authorityStable.trans installed.authorityStable

/-- Buffer allocation installs a fresh owning row for its physical extent, so
it preserves every recorded authority and the home of every earlier root
without claiming the loan table is literally unchanged. -/
theorem Memory.AllocatesBuffer.homeExtension {program : Program} {custody : ClaimCustody}
    {before after : World} {domain element count base pointer allocation}
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after) :
    before.HomeExtension after := by
  cases allocated with
  | fresh request extent =>
    exact ⟨Nat.le_succ _,fun id bound => by
      simp only [Table.get_set_other _ _ _ _ (Nat.ne_of_lt bound)]⟩

theorem Memory.AllocatesBuffer.recorded {program : Program} {custody : ClaimCustody}
    {before after : World} {domain element count base pointer allocation}
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    (authority : Authority) (recorded : authority.Recorded before.loans) : authority.Recorded after.loans := by
  cases allocated
  exact recorded.set _ _

/-- A live buffer-allocation row is either an earlier live row or the claim on
the freshly allocated root. -/
theorem Memory.AllocatesBuffer.loan_live_before {program : Program} {custody : ClaimCustody}
    {before after : World} {domain element count base pointer allocation} {id : Identity} {loan : Loan}
    (allocated : AllocatesBuffer program custody before domain element count base pointer allocation after)
    (found : after.loans.get id = some loan) (live : loan.live = true) :
    (∃ original, before.loans.get id = some original ∧ original.live = true ∧
      loan.referent = original.referent) ∨ before.nextRoot ≤ loan.referent.root := by
  cases allocated with
  | fresh request extent =>
    by_cases same : id = before.nextLoan
    · subst id
      simp only [Table.get_set,Option.some.injEq] at found
      cases found
      exact Or.inr (Nat.le_refl _)
    · exact Or.inl ⟨loan,by simpa only [Table.get_set_other _ _ _ _ same] using found,live,rfl⟩

theorem Memory.ReleasesBuffer.homeExtension {program : Program} {before after : World}
    {allocation : ResolvedPlace} {pointer : RawPointer} {domain : Identity}
    (released : ReleasesBuffer program before allocation pointer domain after) : before.HomeExtension after := by
  cases released with
  | release ready rootAt shellLive resources fields claims canEnd written retiredRel endedRel =>
    exact claims.homeExtension.trans
      ((World.write_authorityStable written).homes.trans
        (retiredRel.authorityStable.homes.trans endedRel.authorityStable.homes))

theorem Memory.ReleasesBuffer.recorded {program : Program} {before after : World}
    {allocation : ResolvedPlace} {pointer : RawPointer} {domain : Identity}
    (released : ReleasesBuffer program before allocation pointer domain after) (authority : Authority)
    (recorded : authority.Recorded before.loans) : authority.Recorded after.loans := by
  cases released with
  | release ready rootAt shellLive resources fields claims canEnd written retiredRel endedRel =>
    exact ((World.write_authorityStable written).trans
      (retiredRel.authorityStable.trans endedRel.authorityStable)).recorded authority
      (claims.recorded authority recorded)

/-- Buffer release only removes liveness from the retired allocation's claim. -/
theorem Memory.ReleasesBuffer.loan_live_before {program : Program} {before after : World}
    {allocation : ResolvedPlace} {pointer : RawPointer} {domain : Identity}
    (released : ReleasesBuffer program before allocation pointer domain after) {id : Identity} {loan : Loan}
    (found : after.loans.get id = some loan) (live : loan.live = true) :
    ∃ original, before.loans.get id = some original ∧ original.live = true ∧
      loan.referent = original.referent := by
  cases released with
  | release ready rootAt shellLive resources fields claims canEnd written retiredRel endedRel =>
    rename_i unclaimed cleared retired
    have same : after.loans = unclaimed.loans := by
      rw [endedRel.authorityStable.loans,retiredRel.authorityStable.loans,
        (World.write_authorityStable written).loans]
    rw [same] at found
    exact claims.loan_live_before found live

theorem Memory.ReallocatesBuffer.homeExtension {program : RuntimeProgram} {custody : ClaimCustody}
    {before after : World} {oldAllocation : ResolvedPlace} {old : RawPointer} {domain : Identity}
    {element : Term} {newCount : Nat} {base : Nat} {result : RawPointer} {allocation : ResolvedPlace}
    (reallocated : ReallocatesBuffer program custody before oldAllocation old domain element newCount base result
      allocation after) : before.HomeExtension after := by
  cases reallocated with
  | grow ready allocatedRel movedRel releasedRel =>
    exact allocatedRel.homeExtension.trans (movedRel.authorityStable.homes.trans releasedRel.homeExtension)

theorem Memory.ReallocatesBuffer.recorded {program : RuntimeProgram} {custody : ClaimCustody}
    {before after : World} {oldAllocation : ResolvedPlace} {old : RawPointer} {domain : Identity}
    {element : Term} {newCount : Nat} {base : Nat} {result : RawPointer} {allocation : ResolvedPlace}
    (reallocated : ReallocatesBuffer program custody before oldAllocation old domain element newCount base result
      allocation after) (authority : Authority) (recorded : authority.Recorded before.loans) :
    authority.Recorded after.loans := by
  cases reallocated with
  | grow ready allocatedRel movedRel releasedRel =>
    exact releasedRel.recorded authority
      (movedRel.authorityStable.recorded authority (allocatedRel.recorded authority recorded))

/-- Reallocation composes buffer allocation, the physical move and the old
allocation's release; only the fresh root's claim is new. -/
theorem Memory.ReallocatesBuffer.loan_live_before {program : RuntimeProgram} {custody : ClaimCustody}
    {before after : World} {oldAllocation : ResolvedPlace} {old : RawPointer} {domain : Identity}
    {element : Term} {newCount : Nat} {base : Nat} {result : RawPointer} {allocation : ResolvedPlace}
    (reallocated : ReallocatesBuffer program custody before oldAllocation old domain element newCount base result
      allocation after) {id : Identity} {loan : Loan}
    (found : after.loans.get id = some loan) (live : loan.live = true) :
    (∃ original, before.loans.get id = some original ∧ original.live = true ∧
      loan.referent = original.referent) ∨ before.nextRoot ≤ loan.referent.root := by
  cases reallocated with
  | grow ready allocatedRel movedRel releasedRel =>
    obtain ⟨original,liveInMoved,originalLive,referent⟩ := releasedRel.loan_live_before found live
    rename_i allocated moved
    have inAllocated : allocated.loans.get id = some original := by
      simpa only [movedRel.authorityStable.loans] using liveInMoved
    rcases allocatedRel.loan_live_before inAllocated originalLive with earlier | fresh
    · obtain ⟨older,olderAt,olderLive,olderReferent⟩ := earlier
      exact Or.inl ⟨older,olderAt,olderLive,referent.trans olderReferent⟩
    · exact Or.inr (by rw [referent]; exact fresh)

theorem Memory.RawRead.authorityStable {program : RuntimeProgram} {before after : World}
    {source : ResolvedPlace} {pointer : RawPointer} {type : Term} {copy : Bool} {destination : Address}
    (read : RawRead program before source pointer type copy destination after) : before.AuthorityStable after := by
  cases read with
  | read _ _ _ action =>
    rcases action with ⟨_,copied⟩ | ⟨_,moved⟩
    · exact copied.authorityStable
    · exact moved.authorityStable

theorem Memory.RawWrite.authorityStable {program : RuntimeProgram} {before after : World}
    {source destination : ResolvedPlace} {pointer : RawPointer} {type : Term}
    (written : RawWrite program before source destination pointer type after) : before.AuthorityStable after := by
  cases written with
  | write _ _ _ _ _ _ moved => exact moved.authorityStable

namespace Foreign

/-- Every recorded authority of the actual host mutation survives that
mutation. Exterior allocation and buffer allocation add rows; nothing removes
one. -/
theorem Mutation.recorded {program : Kernel.Program} {policy : AuthorityPolicy} {before after : World}
    {action : MutationAction}
    (changed : Mutation program policy before action after) (authority : Authority)
    (recorded : authority.Recorded before.loans) : authority.Recorded after.loans := by
  cases changed with
  | allocate _ _ allocated => exact allocated.authorityStable.recorded authority recorded
  | scalar _ stored => exact stored.2.2.authorityStable.recorded authority recorded
  | unit _ stored => exact stored.2.authorityStable.recorded authority recorded
  | pointer _ _ _ _ stored => exact stored.2.authorityStable.recorded authority recorded
  | aggregate _ _ _ _ constructed => exact constructed.authorityStable.recorded authority recorded
  | acquire _ _ acquired => exact acquired.authorityStable.recorded authority recorded
  | borrow _ _ borrowed => exact borrowed.recorded authority recorded
  | allocateBuffer _ allocated => exact allocated.recorded authority recorded
  | reallocateBuffer _ _ _ reallocated => exact reallocated.recorded authority recorded
  | releaseBuffer _ _ _ released => exact released.recorded authority recorded
  | rawRead _ _ _ read => exact read.authorityStable.recorded authority recorded
  | rawWrite _ _ _ written => exact written.authorityStable.recorded authority recorded
  | rawBorrow _ _ _ borrowed => cases borrowed with | borrow _ _ _ _ formed => exact formed.recorded authority recorded
  | bulkMove _ _ moved => exact moved.authorityStable.recorded authority recorded
  | retire _ _ retired => exact retired.authorityStable.recorded authority recorded
  | endLoan ended => exact ended.recorded authority recorded
  | allocateExterior _ _ allocated =>
      exact (allocated.authorityStable.recorded authority recorded).set _ _

theorem Mutation.homeExtension {program : Kernel.Program} {policy : AuthorityPolicy} {before after : World}
    {action : MutationAction}
    (changed : Mutation program policy before action after) : before.HomeExtension after := by
  cases changed with
  | allocate _ _ allocated => exact allocated.authorityStable.homes
  | scalar _ stored => exact stored.2.2.authorityStable.homes
  | unit _ stored => exact stored.2.authorityStable.homes
  | pointer _ _ _ _ stored => exact stored.2.authorityStable.homes
  | aggregate _ _ _ _ constructed => exact constructed.authorityStable.homes
  | acquire _ _ acquired => exact acquired.authorityStable.homes
  | borrow _ _ borrowed => exact borrowed.homeExtension
  | allocateBuffer _ allocated => exact allocated.homeExtension
  | reallocateBuffer _ _ _ reallocated => exact reallocated.homeExtension
  | releaseBuffer _ _ _ released => exact released.homeExtension
  | rawRead _ _ _ read => exact read.authorityStable.homes
  | rawWrite _ _ _ written => exact written.authorityStable.homes
  | rawBorrow _ _ _ borrowed => cases borrowed with | borrow _ _ _ _ formed => exact formed.homeExtension
  | bulkMove _ _ moved => exact moved.authorityStable.homes
  | retire _ _ retired => exact retired.authorityStable.homes
  | endLoan ended => exact ended.homeExtension
  | allocateExterior _ _ allocated => exact (allocated.authorityStable.homes).congr_roots rfl rfl

theorem Mutations.homeExtension {program : Kernel.Program} {custody : ClaimCustody}
    {policy : List ProducedResource → AuthorityPolicy} {before after : World} {produced actions}
    (changed : Mutations program custody policy before produced actions after) : before.HomeExtension after := by
  induction changed with
  | refl => exact .refl _
  | cons first _ last => exact first.homeExtension.trans last

/-- A live loan after an actual host mutation traces to a pre-state live loan of
the same referent, a place published by the same mutation's authority policy, a
raw pointer origin, or a claim on a root the mutation itself freshly allocated.
Liveness-removing producers (loan end, claim release) introduce no live row. -/
theorem Mutation.liveLoan_origin {program : Kernel.Program} {policy : AuthorityPolicy} {before after : World}
    {action : MutationAction} {id : Identity} {loan : Loan} (changed : Mutation program policy before action after)
    (found : after.loans.get id = some loan) (live : loan.live = true) :
    (∃ original, before.loans.get id = some original ∧ original.live = true ∧
        loan.referent = original.referent) ∨
      (∃ authority, policy.place before ⟨loan.referent,authority⟩) ∨
      (∃ pointer type, PointsTo program.declarations before pointer loan.referent type) ∨
      before.nextRoot ≤ loan.referent.root := by
  have kept (stable : before.AuthorityStable after) :
      before.loans.get id = some loan := by simpa only [stable.loans] using found
  have recorded (stable : before.AuthorityStable after) :
      ∃ original, before.loans.get id = some original ∧ original.live = true ∧
        loan.referent = original.referent := ⟨loan,kept stable,live,rfl⟩
  cases changed with
  | allocate _ _ allocated => exact Or.inl (recorded allocated.authorityStable)
  | scalar _ stored => exact Or.inl (recorded stored.2.2.authorityStable)
  | unit _ stored => exact Or.inl (recorded stored.2.authorityStable)
  | pointer _ _ _ _ stored => exact Or.inl (recorded stored.2.authorityStable)
  | aggregate _ _ _ _ constructed => exact Or.inl (recorded constructed.authorityStable)
  | acquire _ _ acquired => exact Or.inl (recorded acquired.authorityStable)
  | rawRead _ _ _ read => exact Or.inl (recorded read.authorityStable)
  | rawWrite _ _ _ written => exact Or.inl (recorded written.authorityStable)
  | bulkMove _ _ moved => exact Or.inl (recorded moved.authorityStable)
  | retire _ _ retired => exact Or.inl (recorded retired.authorityStable)
  | borrow accessible _ borrowed =>
    rcases borrowed.loan_origin found with original | referent
    · exact Or.inl ⟨loan,original,live,rfl⟩
    · exact Or.inr (Or.inl ⟨_,by simpa only [referent] using accessible⟩)
  | rawBorrow _ _ _ borrowed =>
    cases borrowed with
    | borrow points _ _ _ borrowed =>
      rcases borrowed.loan_origin found with original | referent
      · exact Or.inl ⟨loan,original,live,rfl⟩
      · exact Or.inr (Or.inr (Or.inl ⟨_,_,by simpa only [referent] using points⟩))
  | allocateBuffer _ allocated =>
    rcases allocated.loan_live_before found live with earlier | fresh
    · exact Or.inl earlier
    · exact Or.inr (Or.inr (Or.inr fresh))
  | allocateExterior _ _ allocated =>
    cases allocated with
    | fresh request extent =>
      by_cases same : id = before.nextLoan
      · subst id
        simp only [Table.get_set,Option.some.injEq] at found
        cases found
        exact Or.inr (Or.inr (Or.inr (Nat.le_refl _)))
      · refine Or.inl ?_
        rw [Table.get_set_other _ _ _ _ same] at found
        exact ⟨loan,(by simpa only [(Allocates.authorityStable (Allocates.fresh request extent)).loans]
          using found),live,rfl⟩
  | reallocateBuffer _ _ _ reallocated =>
    rcases reallocated.loan_live_before found live with earlier | fresh
    · exact Or.inl earlier
    · exact Or.inr (Or.inr (Or.inr fresh))
  | releaseBuffer _ _ _ released =>
    obtain ⟨original,found',originalLive,referent⟩ := released.loan_live_before found live
    exact Or.inl ⟨original,found',originalLive,referent⟩
  | endLoan ended =>
    exact Or.inl ⟨loan,ended.loan_live_before found live,live,rfl⟩

/-- Every place a host mutation publishes is a destination that mutation really
allocated, so it lies at or above the mutation's initial root frontier. A caller
with a private root below that frontier can conclude that no actual published
place names it. -/
theorem Mutation.produced_fresh {program : Kernel.Program} {policy : AuthorityPolicy}
    {before after : World} {action : MutationAction} {custody : ClaimCustody}
    (changed : Mutation program policy before action after) {resource : ProducedResource}
    (member : resource ∈ action.produced custody) :
    before.nextRoot ≤ resource.place.address.root := by
  cases changed with
  | allocate _ _ allocated =>
      simp only [MutationAction.produced,List.mem_singleton] at member
      subst member
      cases allocated
      exact Nat.le_refl _
  | allocateExterior _ _ allocated =>
      simp only [MutationAction.produced,List.mem_singleton] at member
      subst member
      cases allocated
      exact Nat.le_refl _
  | allocateBuffer _ allocated =>
      simp only [MutationAction.produced,List.mem_singleton] at member
      subst member
      cases allocated
      exact Nat.le_refl _
  | reallocateBuffer _ _ _ reallocated =>
      simp only [MutationAction.produced,List.mem_singleton] at member
      subst member
      cases reallocated with
      | grow _ allocated _ _ =>
        cases allocated
        exact Nat.le_refl _
  | scalar => simp only [MutationAction.produced,List.not_mem_nil] at member
  | unit => simp only [MutationAction.produced,List.not_mem_nil] at member
  | pointer => simp only [MutationAction.produced,List.not_mem_nil] at member
  | aggregate => simp only [MutationAction.produced,List.not_mem_nil] at member
  | acquire => simp only [MutationAction.produced,List.not_mem_nil] at member
  | borrow => simp only [MutationAction.produced,List.not_mem_nil] at member
  | releaseBuffer => simp only [MutationAction.produced,List.not_mem_nil] at member
  | rawRead => simp only [MutationAction.produced,List.not_mem_nil] at member
  | rawWrite => simp only [MutationAction.produced,List.not_mem_nil] at member
  | rawBorrow => simp only [MutationAction.produced,List.not_mem_nil] at member
  | bulkMove => simp only [MutationAction.produced,List.not_mem_nil] at member
  | retire => simp only [MutationAction.produced,List.not_mem_nil] at member
  | endLoan => simp only [MutationAction.produced,List.not_mem_nil] at member

/-- The accumulated published places of an actual host transaction are all at or
above the transaction's initial root frontier, along the whole fold. -/
theorem Mutations.published_fresh {program : Kernel.Program} {custody : ClaimCustody}
    {policy : List ProducedResource → AuthorityPolicy} {initial : World} {produced : List ProducedResource}
    {actions : List MutationAction} {after : World}
    (changed : Mutations program custody policy initial produced actions after) {resource : ProducedResource}
    (member : resource ∈ TransactionOutputs custody actions) :
    initial.nextRoot ≤ resource.place.address.root := by
  induction changed with
  | refl => simp only [TransactionOutputs,List.flatMap_nil,List.not_mem_nil] at member
  | cons first _ ih =>
      simp only [TransactionOutputs,List.flatMap_cons,List.mem_append] at member
      rcases member with own | published
      · exact first.produced_fresh own
      · exact Nat.le_trans first.homeExtension.counter (ih published)

theorem _root_.Glorious.Language.Memory.AllocatesBuffer.root_bound {program : Language.Program}
    {custody : ClaimCustody} {before after : World} {domain element count base pointer allocation}
    (allocated : Memory.AllocatesBuffer program custody before domain element count base pointer allocation after) :
    allocation.address.root < after.nextRoot := by
  cases allocated
  exact Nat.lt_succ_self _

theorem _root_.Glorious.Language.Memory.ReallocatesBuffer.root_bound {program : RuntimeProgram}
    {custody : ClaimCustody} {before after : World} {oldAllocation : ResolvedPlace} {old : RawPointer}
    {domain element count base pointer allocation}
    (reallocated : Memory.ReallocatesBuffer program custody before oldAllocation old domain element count base pointer allocation after) :
    allocation.address.root < after.nextRoot := by
  cases reallocated with
  | grow ready allocated moved released =>
    exact Nat.lt_of_lt_of_le allocated.root_bound
      (Nat.le_trans moved.authorityStable.homes.counter released.homeExtension.counter)

theorem Mutation.produced_root_bound {program : Kernel.Program} {policy : AuthorityPolicy}
    {before after : World} {action : MutationAction} {custody : ClaimCustody}
    (changed : Mutation program policy before action after) {resource : ProducedResource}
    (member : resource ∈ action.produced custody) : resource.place.address.root < after.nextRoot := by
  cases changed <;> simp only [MutationAction.produced,List.mem_singleton,List.not_mem_nil] at member
  case allocate allocated | allocateExterior allocated =>
    subst member
    cases allocated
    exact Nat.lt_succ_self _
  case allocateBuffer allocated | reallocateBuffer allocated =>
    subst member
    exact allocated.root_bound

theorem Mutations.published_root_bound {program : Kernel.Program} {custody : ClaimCustody}
    {policy : List ProducedResource → AuthorityPolicy} {before after : World} {produced actions}
    (changed : Mutations program custody policy before produced actions after) {resource : ProducedResource}
    (member : resource ∈ TransactionOutputs custody actions) : resource.place.address.root < after.nextRoot := by
  induction changed with
  | refl => simp only [TransactionOutputs,List.flatMap_nil,List.not_mem_nil] at member
  | cons first rest ih =>
    simp only [TransactionOutputs,List.flatMap_cons,List.mem_append] at member
    rcases member with own | published
    · exact Nat.lt_of_lt_of_le (first.produced_root_bound own) rest.homeExtension.counter
    · exact ih published


theorem _root_.Glorious.Language.Memory.AllocatesBuffer.authority_recorded {program : Language.Program}
    {custody : ClaimCustody} {before after : World} {domain element count base pointer allocation}
    (allocated : Memory.AllocatesBuffer program custody before domain element count base pointer allocation after) :
    allocation.authority.Recorded after.loans := by
  cases allocated
  exact ⟨_,Table.get_set _ _ _⟩

theorem _root_.Glorious.Language.Memory.ReallocatesBuffer.authority_recorded {program : RuntimeProgram}
    {custody : ClaimCustody} {before after : World} {oldAllocation : ResolvedPlace} {old : RawPointer}
    {domain element count base pointer allocation}
    (reallocated : Memory.ReallocatesBuffer program custody before oldAllocation old domain element count base pointer allocation after) :
    allocation.authority.Recorded after.loans := by
  cases reallocated with
  | grow ready allocated moved released =>
    exact released.recorded _ (moved.authorityStable.recorded _ allocated.authority_recorded)


/-- Published authority belongs to the actual allocating action, including
fresh exterior and buffer claims. It is not inferred from endpoint roots. -/
theorem Mutation.produced_recorded {program : Kernel.Program} {policy : AuthorityPolicy}
    {before after : World} {action : MutationAction} {custody : ClaimCustody}
    (changed : Mutation program policy before action after) {resource : ProducedResource}
    (member : resource ∈ action.produced custody) : resource.place.authority.Recorded after.loans := by
  cases changed <;> simp only [MutationAction.produced,List.mem_singleton,List.not_mem_nil] at member
  all_goals subst resource
  case allocate => trivial
  case allocateExterior allocated => cases allocated; exact ⟨_,Table.get_set _ _ _⟩
  case allocateBuffer allocated => exact allocated.authority_recorded
  case reallocateBuffer reallocated => exact reallocated.authority_recorded

/-- Every actual transaction suffix retains the authority produced earlier in
that same transaction, even if its loan becomes inactive. -/
theorem Mutations.recorded {program : Kernel.Program} {custody : ClaimCustody}
    {policy : List ProducedResource → AuthorityPolicy} {before after : World} {produced actions}
    (changed : Mutations program custody policy before produced actions after) (authority : Authority)
    (recorded : authority.Recorded before.loans) : authority.Recorded after.loans := by
  induction changed with
  | refl => exact recorded
  | cons first _ ih => exact ih (first.recorded authority recorded)

theorem Mutations.published_recorded {program : Kernel.Program} {custody : ClaimCustody}
    {policy : List ProducedResource → AuthorityPolicy} {before after : World} {produced actions}
    (changed : Mutations program custody policy before produced actions after) {resource : ProducedResource}
    (member : resource ∈ TransactionOutputs custody actions) : resource.place.authority.Recorded after.loans := by
  induction changed with
  | refl => simp only [TransactionOutputs,List.flatMap_nil,List.not_mem_nil] at member
  | cons first rest ih =>
    simp only [TransactionOutputs,List.flatMap_cons,List.mem_append] at member
    rcases member with own | later
    · exact rest.recorded _ (first.produced_recorded own)
    · exact ih later


end Foreign
end Glorious.Language
