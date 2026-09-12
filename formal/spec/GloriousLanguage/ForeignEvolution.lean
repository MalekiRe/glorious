import GloriousLanguage.ForeignPreservation

/-! Authority metadata of the actual host mutation producers. Fresh roots do
not replace an existing storage home. Existing loan records are unchanged
except for ordinary release; new loans originate in the selected source. -/
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

theorem Allocates.authorityStable {program : Program} {before after : World}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) : before.AuthorityStable after := by
  cases allocated
  exact ⟨⟨Nat.le_succ _,fun id bound => by
    simp only [Table.get_set_other _ _ _ _ (Nat.ne_of_lt bound)]⟩,rfl⟩

theorem Transfers.authorityStable {program : Program} {before after : World} {authority source destination}
    (transferred : Transfers program before authority source destination after) : before.AuthorityStable after := by
  cases transferred with
  | move _ _ _ _ _ _ clear install => exact (World.write_authorityStable clear).trans (World.write_authorityStable install)

theorem Copies.authorityStable {program : Program} {before after : World} {authority source destination}
    (copied : Copies program before authority source destination after) : before.AuthorityStable after := by
  cases copied with
  | copy _ _ _ _ _ _ written =>
    have stable := World.write_authorityStable written
    exact ⟨⟨stable.homes.counter,stable.homes.homes⟩,stable.loans⟩

theorem Acquires.authorityStable {program : Program} {before after : World} {authority force source destination}
    (acquired : Acquires program before authority force source destination after) : before.AuthorityStable after := by
  cases acquired with
  | explicitMove moved => exact moved.authorityStable
  | copy copied => exact copied.authorityStable
  | move _ _ _ moved => exact moved.authorityStable

theorem NewValue.authorityStable {program : Program} {before after : World} {destination type head sources}
    (constructed : NewValue program before destination type head sources after) : before.AuthorityStable after :=
  ⟨.of_locations (Nat.le_of_eq (congrArg World.nextRoot constructed.rest).symm) constructed.locations,
    by have same := congrArg World.loans constructed.rest; exact same⟩

theorem FormsLoan.homeExtension {program : Program} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination}
    (borrowed : FormsLoan program purpose before authority mode region referent destination after) :
    before.HomeExtension after := by
  apply World.HomeExtension.of_locations ?_ borrowed.locations
  cases borrowed with
  | borrow _ _ _ _ _ _ _ _ _ written => exact (World.write_authorityStable written).homes.counter

theorem FormsLoan.recorded {program : Program} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination}
    (borrowed : FormsLoan program purpose before authority mode region referent destination after)
    (saved : Authority) (recorded : saved.Recorded before.loans) : saved.Recorded after.loans := by
  cases borrowed
  exact recorded.set _ _

theorem FormsLoan.loan_origin {program : Program} {purpose : LoanPurpose} {before after : World}
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

theorem EndsLoan.homeExtension {before after : World} {id : Identity} (ended : EndsLoan before id after) :
    before.HomeExtension after := by
  cases ended
  exact ⟨Nat.le_refl _,fun _ _ => rfl⟩

theorem EndsLoan.recorded {before after : World} {id : Identity} (ended : EndsLoan before id after)
    (authority : Authority) (recorded : authority.Recorded before.loans) : authority.Recorded after.loans := by
  cases ended
  exact recorded.set _ _

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
  rcases ended with ⟨_,_,_,rfl⟩
  exact ⟨⟨Nat.le_refl _,fun _ _ => rfl⟩,rfl⟩

theorem Clears.authorityStable {before after : World} {addresses : List Address}
    (cleared : Clears before addresses after) : before.AuthorityStable after :=
  ⟨.of_locations (Nat.le_of_eq (congrArg World.nextRoot cleared.rest).symm) cleared.locations,cleared.loans⟩

theorem Memory.InstallsResidents.authorityStable {program : Program} {before after : World}
    {addresses : List Address} {values : List (Option Value)}
    (installed : InstallsResidents program before addresses values after) : before.AuthorityStable after :=
  ⟨.of_locations (Nat.le_of_eq (congrArg World.nextRoot installed.rest).symm) installed.locations,
    by have same := congrArg World.loans installed.rest; exact same⟩

theorem Memory.BulkMove.authorityStable {program : Program} {before after : World} {sources destinations}
    (moved : BulkMove program before sources destinations after) : before.AuthorityStable after := by
  obtain ⟨_,_,_,_,_,_,_,_,cleared,installed⟩ := moved
  exact cleared.authorityStable.trans installed.authorityStable

theorem Memory.AllocatesBuffer.authorityStable {program : Program} {before after : World}
    {domain element count base pointer}
    (allocated : AllocatesBuffer program before domain element count base pointer after) : before.AuthorityStable after := by
  cases allocated
  exact ⟨⟨Nat.le_succ _,fun id bound => by
    simp only [Table.get_set_other _ _ _ _ (Nat.ne_of_lt bound)]⟩,rfl⟩

theorem Memory.ReleasesBuffer.authorityStable {program : Program} {before after : World} {pointer domain}
    (released : ReleasesBuffer program before pointer domain after) : before.AuthorityStable after := by
  cases released with
  | release _ _ _ _ _ _ _ _ _ _ _ _ written retired ended =>
    exact (World.write_authorityStable written).trans (retired.authorityStable.trans ended.authorityStable)

theorem Memory.ReallocatesBuffer.authorityStable {program : Program} {before after : World}
    {old domain element count base result}
    (reallocated : ReallocatesBuffer program before old domain element count base result after) : before.AuthorityStable after := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,allocated,_,moved,released⟩ := reallocated
  exact allocated.authorityStable.trans (moved.authorityStable.trans released.authorityStable)

theorem Memory.RawRead.authorityStable {program : Program} {before after : World} {pointer type copy destination}
    (read : RawRead program before pointer type copy destination after) : before.AuthorityStable after := by
  cases read with
  | read _ _ _ action =>
    rcases action with ⟨_,copied⟩ | ⟨_,moved⟩
    · exact copied.authorityStable
    · exact moved.authorityStable

theorem Memory.RawWrite.authorityStable {program : Program} {before after : World} {authority source pointer type}
    (written : RawWrite program before authority source pointer type after) : before.AuthorityStable after := by
  cases written with
  | write _ _ _ _ _ moved => exact moved.authorityStable

namespace Foreign

theorem Mutation.recorded {program : Kernel.Program} {policy : AuthorityPolicy} {before after : World}
    (changed : Mutation program policy before after) (authority : Authority)
    (recorded : authority.Recorded before.loans) : authority.Recorded after.loans := by
  cases changed with
  | allocate _ allocated => exact allocated.authorityStable.recorded authority recorded
  | scalar _ stored => exact stored.2.2.authorityStable.recorded authority recorded
  | unit _ stored => exact stored.2.authorityStable.recorded authority recorded
  | pointer _ _ _ _ stored => exact stored.2.authorityStable.recorded authority recorded
  | aggregate _ _ _ _ constructed => exact constructed.authorityStable.recorded authority recorded
  | acquire _ _ acquired => exact acquired.authorityStable.recorded authority recorded
  | borrow _ _ borrowed => exact borrowed.recorded authority recorded
  | allocateBuffer _ allocated => exact allocated.authorityStable.recorded authority recorded
  | reallocateBuffer _ _ reallocated => exact reallocated.authorityStable.recorded authority recorded
  | releaseBuffer _ _ released => exact released.authorityStable.recorded authority recorded
  | rawRead _ _ read => exact read.authorityStable.recorded authority recorded
  | rawWrite _ _ written => exact written.authorityStable.recorded authority recorded
  | rawBorrow _ _ borrowed => cases borrowed with | borrow _ _ _ _ formed => exact formed.recorded authority recorded
  | bulkMove _ _ moved => exact moved.authorityStable.recorded authority recorded
  | retire _ _ retired => exact retired.authorityStable.recorded authority recorded
  | endLoan ended => exact ended.recorded authority recorded

theorem Mutation.homeExtension {program : Kernel.Program} {policy : AuthorityPolicy} {before after : World}
    (changed : Mutation program policy before after) : before.HomeExtension after := by
  cases changed with
  | allocate _ allocated => exact allocated.authorityStable.homes
  | scalar _ stored => exact stored.2.2.authorityStable.homes
  | unit _ stored => exact stored.2.authorityStable.homes
  | pointer _ _ _ _ stored => exact stored.2.authorityStable.homes
  | aggregate _ _ _ _ constructed => exact constructed.authorityStable.homes
  | acquire _ _ acquired => exact acquired.authorityStable.homes
  | borrow _ _ borrowed => exact borrowed.homeExtension
  | allocateBuffer _ allocated => exact allocated.authorityStable.homes
  | reallocateBuffer _ _ reallocated => exact reallocated.authorityStable.homes
  | releaseBuffer _ _ released => exact released.authorityStable.homes
  | rawRead _ _ read => exact read.authorityStable.homes
  | rawWrite _ _ written => exact written.authorityStable.homes
  | rawBorrow _ _ borrowed => cases borrowed with | borrow _ _ _ _ formed => exact formed.homeExtension
  | bulkMove _ _ moved => exact moved.authorityStable.homes
  | retire _ _ retired => exact retired.authorityStable.homes
  | endLoan ended => exact ended.homeExtension

theorem Mutations.homeExtension {program : Kernel.Program} {policy : AuthorityPolicy} {before after : World}
    (changed : Mutations program policy before after) : before.HomeExtension after := by
  induction changed with
  | refl => exact .refl _
  | cons first _ last => exact first.homeExtension.trans last

theorem Mutation.liveLoan_origin {program : Kernel.Program} {policy : AuthorityPolicy} {before after : World}
    {id : Identity} {loan : Loan} (changed : Mutation program policy before after)
    (found : after.loans.get id = some loan) (live : loan.live = true) :
    before.loans.get id = some loan ∨
      (∃ authority, policy.place before ⟨loan.referent,authority⟩) ∨
      ∃ pointer type, PointsTo program.declarations before pointer loan.referent type := by
  have unchanged (stable : before.AuthorityStable after) : before.loans.get id = some loan := by
    simpa only [stable.loans] using found
  cases changed with
  | allocate _ allocated => exact Or.inl (unchanged allocated.authorityStable)
  | scalar _ stored => exact Or.inl (unchanged stored.2.2.authorityStable)
  | unit _ stored => exact Or.inl (unchanged stored.2.authorityStable)
  | pointer _ _ _ _ stored => exact Or.inl (unchanged stored.2.authorityStable)
  | aggregate _ _ _ _ constructed => exact Or.inl (unchanged constructed.authorityStable)
  | acquire _ _ acquired => exact Or.inl (unchanged acquired.authorityStable)
  | allocateBuffer _ allocated => exact Or.inl (unchanged allocated.authorityStable)
  | reallocateBuffer _ _ reallocated => exact Or.inl (unchanged reallocated.authorityStable)
  | releaseBuffer _ _ released => exact Or.inl (unchanged released.authorityStable)
  | rawRead _ _ read => exact Or.inl (unchanged read.authorityStable)
  | rawWrite _ _ written => exact Or.inl (unchanged written.authorityStable)
  | bulkMove _ _ moved => exact Or.inl (unchanged moved.authorityStable)
  | retire _ _ retired => exact Or.inl (unchanged retired.authorityStable)
  | borrow accessible _ borrowed =>
    rcases borrowed.loan_origin found with original | referent
    · exact Or.inl original
    · exact Or.inr (Or.inl ⟨_,by simpa only [referent] using accessible⟩)
  | rawBorrow _ _ borrowed =>
    cases borrowed with
    | borrow points _ _ _ borrowed =>
      rcases borrowed.loan_origin found with original | referent
      · exact Or.inl original
      · exact Or.inr (Or.inr ⟨_,_,by simpa only [referent] using points⟩)
  | endLoan ended =>
    rename_i key
    cases ended with
    | restored original _ _ _ _ =>
      by_cases same : id = key
      · subst id
        simp only [Table.get_set,Option.some.injEq] at found
        subst loan
        cases live
      · exact Or.inl (by simpa only [Table.get_set_other _ _ _ _ same] using found)

end Foreign
end Glorious.Language
