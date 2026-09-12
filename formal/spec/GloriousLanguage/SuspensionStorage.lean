import GloriousLanguage.ForeignSuspension

/-! The preservation projection shared by ordinary storage producers and
whole-machine suspension ownership. It is proved from their executable
relations; it neither stores a second inventory nor admits a post-state. -/
namespace Glorious.Language

open Kernel Execution Memory

structure World.SuspensionExtension (before after : World) : Prop where
  counter : before.nextRoot ≤ after.nextRoot
  retained : ∀ id root suspension, id < before.nextRoot → before.roots.get id = some root →
    root.home = .suspended suspension → (after.roots.get id).map Root.location = some root.location
  origin : ∀ id root suspension, after.roots.get id = some root → root.home = .suspended suspension →
    ∃ original, before.roots.get id = some original ∧ root.location = original.location
  recorded : ∀ (authority : Authority), authority.Recorded before.loans → authority.Recorded after.loans

theorem World.SuspensionExtension.refl (world : World) : world.SuspensionExtension world :=
  ⟨Nat.le_refl _,fun _ _ _ _ found _ => by rw [found]; rfl,fun _ root _ found _ => ⟨root,found,rfl⟩,
    fun _ recorded => recorded⟩

theorem World.SuspensionExtension.trans {before middle after : World}
    (first : before.SuspensionExtension middle) (last : middle.SuspensionExtension after) :
    before.SuspensionExtension after := by
  refine ⟨Nat.le_trans first.counter last.counter,?_,?_,
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
  refine ⟨counter,?_,?_,recorded⟩
  · intro id root _ _ found _
    simpa only [found,Option.map_some] using locations id
  · intro id root _ found _
    obtain ⟨original,originalAt,location⟩ := World.root_origin_of_locations (locations id) found
    exact ⟨original,originalAt,location.symm⟩

theorem World.SuspensionExtension.of_roots {before after : World}
    (counter : before.nextRoot ≤ after.nextRoot) (roots : after.roots = before.roots)
    (recorded : ∀ (authority : Authority), authority.Recorded before.loans → authority.Recorded after.loans) :
    before.SuspensionExtension after := .of_locations counter (by intro id; rw [roots]) recorded

theorem World.write_suspensionExtension {before after : World} {address : Address} {value : Option Value}
    (written : before.write address value = some after) : before.SuspensionExtension after :=
  .of_locations (Nat.le_of_eq (congrArg World.nextRoot (World.write_rest written)).symm) (World.write_locations written)
    (World.write_authorityStable written).recorded

theorem Allocates.suspensionExtension {program : Program} {before after : World}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after)
    (ordinary : ∀ id, home ≠ .suspended id) : before.SuspensionExtension after := by
  refine ⟨allocated.authorityStable.homes.counter,?_,?_,allocated.authorityStable.recorded⟩
  · intro id root suspension bound found home
    rw [allocated.roots_other bound,found]; rfl
  · intro id root suspension found homeEq
    obtain ⟨original,originalAt,location⟩ := allocated.suspended_origin (ordinary suspension) found homeEq
    exact ⟨original,originalAt,location.symm⟩

theorem Retires.suspensionExtension {before after : World} {retiredId : Identity}
    (retired : Retires before retiredId after) : before.SuspensionExtension after := by
  refine ⟨retired.authorityStable.homes.counter,?_,?_,retired.authorityStable.recorded⟩
  · intro id root suspension _ selected home
    exact retired.suspended_location selected home
  · intro id root suspension found home
    obtain ⟨original,originalAt,location⟩ := retired.suspended_origin found home
    exact ⟨original,originalAt,location.symm⟩

theorem Transfers.suspensionExtension {program : Program} {before after : World} {authority source destination}
    (transferred : Transfers program before authority source destination after) : before.SuspensionExtension after :=
  .of_locations transferred.authorityStable.homes.counter transferred.locations transferred.authorityStable.recorded

theorem Copies.suspensionExtension {program : Program} {before after : World} {authority source destination}
    (copied : Copies program before authority source destination after) : before.SuspensionExtension after :=
  .of_locations copied.authorityStable.homes.counter copied.locations copied.authorityStable.recorded

theorem Acquires.suspensionExtension {program : Program} {before after : World} {authority force source destination}
    (acquired : Acquires program before authority force source destination after) : before.SuspensionExtension after := by
  cases acquired with
  | explicitMove moved => exact moved.suspensionExtension
  | copy copied => exact copied.suspensionExtension
  | move _ _ _ moved => exact moved.suspensionExtension

theorem NewValue.suspensionExtension {program : Program} {before after : World} {destination type head sources}
    (constructed : NewValue program before destination type head sources after) : before.SuspensionExtension after :=
  .of_locations constructed.authorityStable.homes.counter constructed.locations constructed.authorityStable.recorded

theorem FormsLoan.suspensionExtension {program : Program} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination}
    (borrowed : FormsLoan program purpose before authority mode region referent destination after) :
    before.SuspensionExtension after := .of_locations borrowed.homeExtension.counter borrowed.locations borrowed.recorded

theorem EndsLoan.suspensionExtension {before after : World} {id : Identity} (ended : EndsLoan before id after) :
    before.SuspensionExtension after := by
  exact .of_roots (by cases ended; exact Nat.le_refl _) (by cases ended; rfl) ended.recorded

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
  induction kept with
  | nil => exact .refl _
  | cons first _ ih => exact first.suspensionExtension.trans ih

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

theorem Kernel.LendsResident.suspensionExtension {program : Language.Program} {activation scope region : Identity}
    {before after : World} {source : Address} {authority result : Authority} {access : Access} {lease : Option InvocationLease}
    (lent : LendsResident program activation scope region before source authority access lease result after) :
    before.SuspensionExtension after := by
  cases lent with
  | owned => exact .refl _
  | lent _ _ allocated borrowed =>
    exact (allocated.suspensionExtension (by intro id; simp)).trans borrowed.suspensionExtension

theorem Execution.ConsumesReceiver.suspensionExtension {before after : World}
    {address : Address} {authority : Authority} {access : Access}
    (consumed : ConsumesReceiver before address authority access after) : before.SuspensionExtension after := by
  cases consumed with
  | lent => exact .refl _
  | owned _ _ _ _ written => exact World.write_suspensionExtension written

theorem Kernel.BindsInput.suspensionExtension {program : Language.Program} {activation scope region : Identity}
    {before after : World} {input : InvocationInput} {binding : Binding}
    (bound : BindsInput program activation scope region before input binding after) : before.SuspensionExtension after := by
  cases bound with
  | lent _ _ _ _ _ borrowed => exact borrowed.suspensionExtension
  | owned _ _ _ allocated transferred =>
    exact (allocated.suspensionExtension (by intro id; simp)).trans transferred.suspensionExtension

theorem Kernel.BindsInputs.suspensionExtension {program : Language.Program} {activation scope region : Identity}
    {before after : World} {inputs : List InvocationInput} {bindings : Environment}
    (bound : BindsInputs program activation scope region before inputs bindings after) : before.SuspensionExtension after := by
  induction bound with
  | nil => exact .refl _
  | cons first _ ih => exact first.suspensionExtension.trans ih

theorem Kernel.BindsPattern.suspensionExtension {program : Language.Program} {activation scope region : Identity}
    {before after : World} {localSlot : Local} {source : Address} {authority : Authority} {access : Access} {binding : Binding}
    (bound : BindsPattern program activation scope region before localSlot source authority access binding after) :
    before.SuspensionExtension after := by
  cases bound with
  | owned bound => exact bound.suspensionExtension
  | borrowed _ _ allocated borrowed =>
    exact (allocated.suspensionExtension (by intro id; simp)).trans borrowed.suspensionExtension

theorem Deconstructs.suspensionExtension {program : Program} {context : Language.Context}
    {before after : World} {authority : Authority} {address : Address}
    (consumed : Deconstructs program context before authority address after) : before.SuspensionExtension after := by
  cases consumed with
  | shell _ _ _ _ written => exact World.write_suspensionExtension written

theorem Execution.PreparesEntry.suspensionExtension {program : Kernel.Program} {callee : Context} {function : Kernel.Function}
    {before after : World} {source : EntrySource} {inputs : List InvocationInput}
    (prepared : PreparesEntry program callee function before source inputs after) : before.SuspensionExtension after := by
  cases prepared with
  | supplied => exact .refl _
  | resident lent _ => exact lent.suspensionExtension
  | contextual receiver witness => exact receiver.suspensionExtension.trans witness.suspensionExtension

theorem Execution.EnterWorld.suspensionExtension {program : Kernel.Program} {before : State} {after : World}
    {caller context : Context} {function : Kernel.Function} {source : EntrySource}
    (entered : EnterWorld program before caller function source context after) : before.world.SuspensionExtension after := by
  obtain ⟨_,_,_,_,_,_,fresh,prepared,bound,_,_⟩ := entered
  exact fresh.suspensionExtension.trans (prepared.suspensionExtension.trans bound.suspensionExtension)

theorem Execution.Captures.suspensionExtension {program : Kernel.Program} {context : Context}
    {before after : World} {captures : List Capture} {addresses : List Address}
    (captured : Captures program context before captures addresses after) : before.SuspensionExtension after := by
  induction captured with
  | nil => exact .refl _
  | owned _ _ allocated acquired _ ih => exact allocated.suspensionExtension.trans (acquired.suspensionExtension.trans ih)
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

theorem Execution.ConsumesAvailability.suspensionExtension {before after : World}
    {address : Address} {id : Identity} {access : Access}
    (consumed : ConsumesAvailability before address id access after) : before.SuspensionExtension after := by
  cases consumed with
  | lent => exact .refl _
  | owned _ written =>
    exact (World.write_suspensionExtension written).trans
      (.of_roots (Nat.le_refl _) rfl (fun _ recorded => recorded))

end Glorious.Language
