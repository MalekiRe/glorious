import GloriousLanguage.ForeignSuspension

/-! The preservation projection shared by ordinary storage producers and
whole-machine suspension ownership. It is proved from their executable
relations; it neither stores a second inventory nor admits a post-state. -/
namespace Glorious.Language

open Kernel Execution Memory

structure World.SuspensionExtension (before after : World) : Prop extends before.HomeExtension after where
  retained : ∀ id root suspension, id < before.nextRoot → before.roots.get id = some root →
    root.home = .suspended suspension → (after.roots.get id).map Root.location = some root.location
  origin : ∀ id root suspension, after.roots.get id = some root → root.home = .suspended suspension →
    ∃ original, before.roots.get id = some original ∧ root.location = original.location
  recorded : ∀ (authority : Authority), authority.Recorded before.loans → authority.Recorded after.loans

theorem World.SuspensionExtension.refl (world : World) : world.SuspensionExtension world :=
  ⟨.refl _,fun _ _ _ _ found _ => by rw [found]; rfl,fun _ root _ found _ => ⟨root,found,rfl⟩,
    fun _ recorded => recorded⟩

theorem World.SuspensionExtension.trans {before middle after : World}
    (first : before.SuspensionExtension middle) (last : middle.SuspensionExtension after) :
    before.SuspensionExtension after := by
  refine ⟨first.toHomeExtension.trans last.toHomeExtension,?_,?_,
    fun authority recorded => last.recorded authority (first.recorded authority recorded)⟩
  · intro id root suspension bound found home
    obtain ⟨current,currentAt,location⟩ := Option.map_eq_some_iff.mp (first.retained id root suspension bound found home)
    have currentHome : current.home = .suspended suspension := by
      have same : current.home = root.home := by simpa only [Root.location] using congrArg Root.home location
      exact same.trans home
    exact (last.retained id current suspension (Nat.lt_of_lt_of_le bound first.counter) currentAt currentHome).trans
      (congrArg some location)
  · intro id root suspension found home
    obtain ⟨current,currentAt,location⟩ := last.origin id root suspension found home
    have currentHome : current.home = .suspended suspension := by
      have same : root.home = current.home := by simpa only [Root.location] using congrArg Root.home location
      exact same.symm.trans home
    obtain ⟨original,originalAt,oldLocation⟩ := first.origin id current suspension currentAt currentHome
    exact ⟨original,originalAt,location.trans oldLocation⟩

theorem World.SuspensionExtension.of_locations {before after : World}
    (counter : before.nextRoot ≤ after.nextRoot)
    (locations : ∀ id, (after.roots.get id).map Root.location = (before.roots.get id).map Root.location)
    (recorded : ∀ (authority : Authority), authority.Recorded before.loans → authority.Recorded after.loans) :
    before.SuspensionExtension after := by
  refine ⟨.of_locations counter locations,?_,?_,recorded⟩
  · intro id root _ _ found _
    simpa only [found,Option.map_some] using locations id
  · intro id root _ found _
    obtain ⟨original,originalAt,location⟩ := World.root_origin_of_locations (locations id) found
    exact ⟨original,originalAt,location.symm⟩

theorem World.SuspensionExtension.of_roots {before after : World}
    (counter : before.nextRoot ≤ after.nextRoot) (roots : after.roots = before.roots)
    (recorded : ∀ (authority : Authority), authority.Recorded before.loans → authority.Recorded after.loans) :
    before.SuspensionExtension after := .of_locations counter (by intro id; rw [roots]) recorded

/-- A step that only rewrites or extends the loan table retains the suspension
extension: the roots and every location are literally untouched. -/
theorem World.SuspensionExtension.of_loans {before after : World}
    (counter : before.nextRoot ≤ after.nextRoot) (roots : after.roots = before.roots)
    (retained : ∀ id loan, before.loans.get id = some loan → ∃ current, after.loans.get id = some current) :
    before.SuspensionExtension after :=
  .of_roots counter roots (fun _ recorded => recorded.transport retained)

theorem World.write_suspensionExtension {before after : World} {address : Address} {value : Option Value}
    (written : before.write address value = some after) : before.SuspensionExtension after :=
  .of_locations (Nat.le_of_eq (congrArg World.nextRoot (World.write_rest written)).symm) (World.write_locations written)
    (World.write_authorityStable written).recorded

theorem Allocates.suspensionExtension {program : Program} {before after : World}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after)
    (ordinary : ∀ id, home ≠ .suspended id) : before.SuspensionExtension after := by
  refine ⟨allocated.authorityStable.homes,?_,?_,allocated.authorityStable.recorded⟩
  · intro id root suspension bound found home
    rw [allocated.roots_other bound,found]; rfl
  · intro id root suspension found homeEq
    obtain ⟨original,originalAt,location⟩ := allocated.suspended_origin (ordinary suspension) found homeEq
    exact ⟨original,originalAt,location.symm⟩

theorem Retires.suspensionExtension {before after : World} {retiredId : Identity}
    (retired : Retires before retiredId after) : before.SuspensionExtension after := by
  refine ⟨retired.authorityStable.homes,?_,?_,retired.authorityStable.recorded⟩
  · intro id root suspension _ selected home
    exact retired.suspended_location selected home
  · intro id root suspension found home
    obtain ⟨original,originalAt,location⟩ := retired.suspended_origin found home
    exact ⟨original,originalAt,location.symm⟩

theorem Transfers.suspensionExtension {program : RuntimeProgram} {before after : World} {authority source destination}
    (transferred : Transfers program before authority source destination after) : before.SuspensionExtension after :=
  .of_locations transferred.authorityStable.homes.counter transferred.locations transferred.authorityStable.recorded

theorem Copies.suspensionExtension {program : RuntimeProgram} {before after : World} {authority source destination}
    (copied : Copies program before authority source destination after) : before.SuspensionExtension after :=
  .of_locations copied.authorityStable.homes.counter copied.locations copied.authorityStable.recorded

theorem Acquires.suspensionExtension {program : RuntimeProgram} {before after : World} {authority force source destination}
    (acquired : Acquires program before authority force source destination after) : before.SuspensionExtension after := by
  cases acquired with
  | explicitMove moved => exact moved.suspensionExtension
  | copy copied => exact copied.suspensionExtension
  | move _ _ _ moved => exact moved.suspensionExtension

theorem NewValue.suspensionExtension {program : RuntimeProgram} {before after : World} {destination type head sources}
    (constructed : NewValue program before destination type head sources after) : before.SuspensionExtension after :=
  .of_locations constructed.authorityStable.homes.counter constructed.locations constructed.authorityStable.recorded

theorem FormsLoan.suspensionExtension {program : RuntimeProgram} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination}
    (borrowed : FormsLoan program purpose before authority mode region referent destination after) :
    before.SuspensionExtension after := .of_locations borrowed.homeExtension.counter borrowed.locations borrowed.recorded

theorem EndsLoan.suspensionExtension {program : RuntimeProgram} {before after : World} {id : Identity}
    (ended : EndsLoan program before id after) : before.SuspensionExtension after :=
  World.SuspensionExtension.of_loans (by cases ended; exact Nat.le_refl _) (by cases ended; rfl)
    (by
      intro key loan found
      cases ended
      by_cases same : key = id
      · subst same; exact ⟨_,Table.get_set _ _ _⟩
      · exact ⟨loan,by rw [Table.get_set_other _ _ _ _ same]; exact found⟩)

theorem FreshRegion.suspensionExtension {before after : World} {id : Identity}
    (fresh : FreshRegion before id after) : before.SuspensionExtension after := by
  rcases fresh with ⟨_,rfl⟩
  exact .of_roots (Nat.le_refl _) rfl (fun _ recorded => recorded)

theorem Execution.RegionEnds.suspensionExtension {before after : World} {id : Identity}
    (ended : RegionEnds before id after) : before.SuspensionExtension after := by
  rcases ended with ⟨_,rfl⟩
  exact .of_roots (Nat.le_refl _) rfl (fun _ recorded => recorded)

theorem Execution.Temporary.suspensionExtension {program : Kernel.Program} {context : Context} {type : Term}
    {before after : World} {address : Address} (allocated : Temporary program context type before address after) :
    before.SuspensionExtension after :=
  allocated.choose_spec.suspensionExtension (by intro id; simp)

theorem Execution.Protect.suspensionExtension {program : Kernel.Program} {context : Context}
    {before after : World} {source destination : Address} {authority : Authority}
    (kept : Protect program context before source authority destination after) : before.SuspensionExtension after := by
  obtain ⟨value,allocated,stored,allocation,transfer⟩ := kept
  exact allocation.suspensionExtension.trans transfer.suspensionExtension

theorem Execution.Protects.suspensionExtension {program : Kernel.Program} {context : Context}
    {before after : World} {sources : List ResolvedPlace} {destinations : List Address}
    (kept : Protects program context before sources destinations after) : before.SuspensionExtension after := by
  exact ProtectsFor.inductionOn
    (motive := fun before sources destinations after _ => before.SuspensionExtension after)
    (nil := fun world => .refl world)
    (cons := fun _ head _ ih => head.suspensionExtension.trans ih) kept

theorem Execution.StartsClause.suspensionExtension {before : State} {handler context after}
    (started : StartsClause before handler context after) : before.world.SuspensionExtension after :=
  started.1.suspensionExtension

theorem Execution.StartsResumptionClause.suspensionExtension {before : State} {handler lexical context localSlot after}
    (started : StartsResumptionClause before handler lexical context localSlot after) :
    before.world.SuspensionExtension after := by
  obtain ⟨outer,brand,started,_⟩ := started
  exact started.suspensionExtension

theorem Execution.CreatesContinuation.suspensionExtension {program : Kernel.Program} {context : Context}
    {before after : World} {id signature answer effects quantity localSlot address}
    (created : CreatesContinuation program context before id signature answer effects quantity localSlot address after) :
    before.SuspensionExtension after := by
  obtain ⟨allocated,layout,type,allocation,constructed⟩ := created
  exact (allocation.suspensionExtension (by intro id; simp)).trans constructed.suspensionExtension

theorem Kernel.LendsResident.suspensionExtension {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {source : Address} {authority result : Authority} {access : Access} {lease : Option InvocationLease}
    (lent : LendsResident program activation scope region before source authority access lease result after) :
    before.SuspensionExtension after := by
  cases lent with
  | owned => exact .refl _
  | lent _ _ _ allocated borrowed =>
    exact (allocated.suspensionExtension (by intro id; simp)).trans borrowed.suspensionExtension

theorem Execution.ConsumesReceiver.suspensionExtension {before after : World}
    {address : Address} {authority : Authority} {access : Access}
    (consumed : ConsumesReceiver before address authority access after) : before.SuspensionExtension after := by
  cases consumed with
  | lent => exact .refl _
  | owned _ _ _ _ written => exact World.write_suspensionExtension written

/-- A row that exists before a table update still has a row afterwards: either
the rewritten row or the original one. -/
theorem Table.get_set_some {α : Type} {table : Table α} {id key : Identity} {value row : α}
    (found : table.get id = some row) : ∃ after, (table.set key value).get id = some after := by
  by_cases same : id = key
  · subst same; exact ⟨value,Table.get_set _ _ _⟩
  · exact ⟨row,by rw [Table.get_set_other _ _ _ _ same]; exact found⟩

theorem ClaimsStorage.suspensionExtension {custody : ClaimCustody} {before after : World}
    {authority : Authority} {access : Access} {referent : Address} {loan : Identity}
    (claimed : ClaimsStorage custody before authority access referent loan after) :
    before.SuspensionExtension after := by
  cases claimed
  refine World.SuspensionExtension.of_locations ?_ ?_ ?_
  · exact Nat.le_refl _
  · intro id; rfl
  · intro current recorded
    refine Authority.Recorded.transport recorded ?_
    intro key row found
    exact Table.get_set_some found

theorem ClaimsAllocation.suspensionExtension {recipient : ClaimCustody} {before after : World}
    {authority : Authority} {address : Address} {loan : Identity}
    (claimed : ClaimsAllocation recipient before authority address loan after) :
    before.SuspensionExtension after := by
  cases claimed
  refine World.SuspensionExtension.of_locations ?_ ?_ ?_
  · exact Nat.le_refl _
  · intro id; rfl
  · intro current recorded
    refine Authority.Recorded.transport recorded ?_
    intro key row found
    exact Table.get_set_some found

theorem TransfersAllocation.suspensionExtension {recipient : ClaimCustody} {before after : World}
    {place : ResolvedPlace} (transferred : TransfersAllocation recipient before place after) :
    before.SuspensionExtension after := by
  cases transferred
  rename_i identity placeEq claim loanAt
  refine World.SuspensionExtension.of_locations ?_ ?_ ?_
  · exact Nat.le_refl _
  · intro id; rfl
  · intro current recorded
    refine Authority.Recorded.transport recorded ?_
    intro key row found
    exact Table.get_set_some found

theorem TransfersStorageLoan.suspensionExtension {recipient : ClaimCustody} {before after : World}
    {place : ResolvedPlace} (transferred : TransfersStorageLoan recipient before place after) :
    before.SuspensionExtension after := by
  cases transferred with
  | shared => exact World.SuspensionExtension.refl before
  | unique =>
    rename_i identity loanAt
    refine World.SuspensionExtension.of_locations ?_ ?_ ?_
    · exact Nat.le_refl _
    · intro id; rfl
    · intro current recorded
      refine Authority.Recorded.transport recorded ?_
      intro key row found
      exact Table.get_set_some found

theorem Kernel.BindsInput.suspensionExtension {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {input : InvocationInput} {binding : Binding}
    (bound : BindsInput program activation scope region before input binding after) : before.SuspensionExtension after := by
  cases bound with
  | lent _ _ _ _ _ _ _ borrowed => exact borrowed.suspensionExtension
  | owned _ _ _ _ _ allocated transferred =>
    exact (allocated.suspensionExtension (by intro id; simp)).trans transferred.suspensionExtension
  | storage _ _ _ claimed => exact claimed.suspensionExtension
  | allocation _ _ _ _ transferred => exact transferred.suspensionExtension
  | guardedAllocation _ _ _ _ _ claimed => exact claimed.suspensionExtension
  | loan _ _ _ _ transferred => exact transferred.suspensionExtension

/-- The general binder: the same preservation as `BindsInput`, for an arbitrary
recipient custody, so the outcome-indexed fold can consume it directly. -/
theorem Kernel.BindsInputAt.suspensionExtension {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {before after : World} {input : InvocationInput} {binding : Binding}
    (bound : BindsInputAt program recipient activation scope region before input binding after) :
    before.SuspensionExtension after := by
  cases bound with
  | lent _ _ _ _ _ _ _ borrowed => exact borrowed.suspensionExtension
  | owned _ _ _ _ _ allocated transferred =>
    exact (allocated.suspensionExtension (by intro id; simp)).trans transferred.suspensionExtension
  | storage _ _ _ claimed => exact claimed.suspensionExtension
  | allocation _ _ _ _ transferred => exact transferred.suspensionExtension
  | guardedAllocation _ _ _ _ _ claimed => exact claimed.suspensionExtension
  | loan _ _ _ _ transferred => exact transferred.suspensionExtension

theorem Kernel.BindsInputsAttemptFor.suspensionExtension {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {footprint : List Address} {before after : World}
    {inputs : List InvocationInput} {bindings : Environment} {outcome : PreparationOutcome}
    (bound : BindsInputsAttemptFor program recipient activation scope region footprint before inputs bindings after outcome) :
    before.SuspensionExtension after := by
  induction bound with
  | nil => exact .refl _
  | cons _ head _ ih => exact head.suspensionExtension.trans ih
  | exhausted _ _ => exact .refl _

theorem Kernel.BindsPattern.suspensionExtension {program : RuntimeProgram} {activation scope region : Identity}
    {before after : World} {localSlot : Local} {source : Address} {authority : Authority} {access : Access} {binding : Binding}
    (bound : BindsPattern program activation scope region before localSlot source authority access binding after) :
    before.SuspensionExtension after := by
  cases bound with
  | owned bound => exact bound.suspensionExtension
  | borrowed _ _ allocated borrowed =>
    exact (allocated.suspensionExtension (by intro id; simp)).trans borrowed.suspensionExtension

theorem Deconstructs.suspensionExtension {program : RuntimeProgram} {context : Language.Context}
    {before after : World} {authority : Authority} {address : Address}
    (consumed : Deconstructs program context before authority address after) : before.SuspensionExtension after := by
  cases consumed with
  | shell _ _ _ _ _ written => exact World.write_suspensionExtension written

theorem Execution.ConsumesAvailability.suspensionExtension {before after : World}
    {address : Address} {authority : Authority} {id : Identity} {access : Access}
    (consumed : ConsumesAvailability before address authority id access after) :
    before.SuspensionExtension after := by
  cases consumed with
  | lent => exact .refl _
  | owned _ _ _ _ _ _ written =>
    exact (World.write_suspensionExtension written).trans
      (.of_roots (Nat.le_refl _) rfl (fun _ recorded => recorded))

theorem Execution.PreparesEntryAttempt.suspensionExtension {program : Kernel.Program} {callee : Context} {function : Kernel.Function}
    {before after : World} {source : EntrySource} {inputs : List InvocationInput} {outcome : PreparationOutcome}
    (prepared : PreparesEntryAttempt program callee function before source inputs after outcome) : before.SuspensionExtension after := by
  cases prepared with
  | supplied => exact .refl _
  | resident _ _ lent _ consumed => exact lent.suspensionExtension.trans consumed.suspensionExtension
  | contextual _ _ _ _ lends lendsWitness _ consumed finished =>
    have step1 := lends.suspensionExtension
    have step2 := lendsWitness.suspensionExtension
    have step3 := consumed.suspensionExtension
    have step4 := finished.suspensionExtension
    exact ((step1.trans step2).trans step3).trans step4
  | residentExhausted | contextualReceiverExhausted => exact .refl _
  | contextualWitnessExhausted _ _ _ _ lent _ => exact lent.suspensionExtension

theorem Execution.FinishesReceiver.suspensionExtension {before after : World} {receiver : ResolvedPlace}
    {access : Access} (finished : FinishesReceiver before receiver access after) :
    before.SuspensionExtension after := by
  cases finished with
  | lent => exact .refl _
  | owned _ _ _ _ _ _ written => exact World.write_suspensionExtension written

theorem Execution.FinishesEntry.suspensionExtension {before after : World} {source : EntrySource}
    (finished : FinishesEntry before source after) : before.SuspensionExtension after := by
  cases finished with
  | supplied => exact .refl _
  | resident inner => exact inner.suspensionExtension
  | contextual inner => exact inner.suspensionExtension

theorem Execution.EnterWorldAttempt.suspensionExtension {program : Kernel.Program} {before : State} {after : World}
    {caller context : Context} {function : Kernel.Function} {source : EntrySource} {outcome : PreparationOutcome}
    (attempted : EnterWorldAttempt program before caller function source context after outcome) :
    before.world.SuspensionExtension after := by
  cases attempted with
  | inputs _ fresh entryPrep _ attempt finished _ _ =>
    have chain := fresh.suspensionExtension.trans (entryPrep.suspensionExtension.trans attempt.suspensionExtension)
    cases outcome with
    | complete => exact chain.trans finished.suspensionExtension
    | exhausted => rw [finished]; exact chain
  | preparationExhausted _ fresh preparation _ _ =>
    exact fresh.suspensionExtension.trans preparation.suspensionExtension

theorem Execution.Captures.suspensionExtension {program : Kernel.Program} {context : Context}
    {before after : World} {captures : List Capture} {addresses : List Address}
    (captured : Captures program context before captures addresses after) : before.SuspensionExtension after := by
  induction captured with
  | nil => exact .refl _
  | owned _ _ temporary acquired _ ih =>
    exact (temporary.choose_spec.suspensionExtension (by intro id; simp)).trans
      (acquired.suspensionExtension.trans ih)
  | borrowed _ _ _ allocated borrowed _ ih => exact allocated.suspensionExtension.trans (borrowed.suspensionExtension.trans ih)

theorem Execution.RetiresEmpty.suspensionExtension {before after : World} {addresses : List Address}
    (retired : RetiresEmpty before addresses after) : before.SuspensionExtension after := by
  induction retired with
  | nil => exact .refl _
  | cons _ retired _ ih => exact retired.suspensionExtension.trans ih

theorem Execution.Installs.suspensionExtension {program : Kernel.Program} {before : State}
    {outer : Context} {syntaxNode : Handler} {handler : InstalledHandler} {after : World}
    (installed : Installs program before outer syntaxNode handler after) : before.world.SuspensionExtension after := by
  obtain ⟨_,_,_,_,_,_,_,_,one,two,_,captured,bound,retired,rfl,_⟩ := installed
  exact one.suspensionExtension.trans (two.suspensionExtension.trans
    (captured.suspensionExtension.trans (bound.suspensionExtension.trans retired.suspensionExtension)))

theorem Execution.CopiesObservations.suspensionExtension {program : Kernel.Program} {context : Context}
    {before after : World} {observations : List (Local × Address × Authority)} {bindings : List (Local × Address)}
    (copied : CopiesObservations program context before observations bindings after) : before.SuspensionExtension after := by
  induction copied with
  | nil => exact .refl _
  | copy _ _ allocated copied _ ih => exact allocated.suspensionExtension.trans (copied.suspensionExtension.trans ih)
  | borrow _ _ allocated borrowed _ ih => exact allocated.suspensionExtension.trans (borrowed.suspensionExtension.trans ih)

theorem Execution.PacksBindings.suspensionExtension {program : Kernel.Program} {context : Context}
    {before after : World} {pattern resultOrigin positive bindings pack}
    (packed : PacksBindings program context before pattern resultOrigin positive bindings pack after) :
    before.SuspensionExtension after := by
  obtain ⟨allocated,created,type,_,temporary,_,constructed,rfl⟩ := packed
  exact (temporary.suspensionExtension.trans constructed.suspensionExtension).trans
    (.of_roots (Nat.le_refl _) rfl (fun _ recorded => recorded))

theorem Execution.UnitFields.suspensionExtension {program : Kernel.Program} {context : Context}
    {before after : World} {types : List Term} {index : Option Nat} {pack : Address} {fields : List Address}
    (assembled : UnitFields program context before types index pack fields after) : before.SuspensionExtension after := by
  induction assembled with
  | done => exact .refl _
  | selected _ _ _ ih => exact ih
  | unitBefore allocated created _ ih | unitAfter allocated created _ ih =>
    exact allocated.suspensionExtension.trans (created.2.suspensionExtension.trans ih)

theorem Execution.TestResult.suspensionExtension {program : Kernel.Program} {context : Context}
    {before after : World} {destination type pattern positive observations}
    (tested : TestResult program context before destination type pattern positive observations after) :
    before.SuspensionExtension after := by
  cases tested with
  | result _ _ copied packed fields constructed =>
    exact copied.suspensionExtension.trans (packed.suspensionExtension.trans
      (fields.choose_spec.2.2.2.2.suspensionExtension.trans constructed.suspensionExtension))



end Glorious.Language
