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

theorem World.SuspensionExtension.refl (world : World) : world.SuspensionExtension world :=
  ⟨Nat.le_refl _,fun _ _ _ _ found _ => by rw [found]; rfl,fun _ root _ found _ => ⟨root,found,rfl⟩⟩

theorem World.SuspensionExtension.trans {before middle after : World}
    (first : before.SuspensionExtension middle) (last : middle.SuspensionExtension after) :
    before.SuspensionExtension after := by
  refine ⟨Nat.le_trans first.counter last.counter,?_,?_⟩
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
    (locations : ∀ id, (after.roots.get id).map Root.location = (before.roots.get id).map Root.location) :
    before.SuspensionExtension after := by
  refine ⟨counter,?_,?_⟩
  · intro id root _ _ found _
    simpa only [found,Option.map_some] using locations id
  · intro id root _ found _
    obtain ⟨original,originalAt,location⟩ := World.root_origin_of_locations (locations id) found
    exact ⟨original,originalAt,location.symm⟩

theorem World.SuspensionExtension.of_roots {before after : World}
    (counter : before.nextRoot ≤ after.nextRoot) (roots : after.roots = before.roots) :
    before.SuspensionExtension after := .of_locations counter (by intro id; rw [roots])

theorem World.write_suspensionExtension {before after : World} {address : Address} {value : Option Value}
    (written : before.write address value = some after) : before.SuspensionExtension after :=
  .of_locations (Nat.le_of_eq (congrArg World.nextRoot (World.write_rest written)).symm) (World.write_locations written)

theorem Allocates.suspensionExtension {program : Program} {before after : World}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after)
    (ordinary : ∀ id, home ≠ .suspended id) : before.SuspensionExtension after := by
  refine ⟨allocated.authorityStable.homes.counter,?_,?_⟩
  · intro id root suspension bound found home
    rw [allocated.roots_other bound,found]; rfl
  · intro id root suspension found homeEq
    obtain ⟨original,originalAt,location⟩ := allocated.suspended_origin (ordinary suspension) found homeEq
    exact ⟨original,originalAt,location.symm⟩

theorem Retires.suspensionExtension {before after : World} {retiredId : Identity}
    (retired : Retires before retiredId after) : before.SuspensionExtension after := by
  refine ⟨retired.authorityStable.homes.counter,?_,?_⟩
  · intro id root suspension _ selected home
    exact retired.suspended_location selected home
  · intro id root suspension found home
    obtain ⟨original,originalAt,location⟩ := retired.suspended_origin found home
    exact ⟨original,originalAt,location.symm⟩

theorem Transfers.suspensionExtension {program : Program} {before after : World} {authority source destination}
    (transferred : Transfers program before authority source destination after) : before.SuspensionExtension after :=
  .of_locations transferred.authorityStable.homes.counter transferred.locations

theorem Copies.suspensionExtension {program : Program} {before after : World} {authority source destination}
    (copied : Copies program before authority source destination after) : before.SuspensionExtension after :=
  .of_locations copied.authorityStable.homes.counter copied.locations

theorem Acquires.suspensionExtension {program : Program} {before after : World} {authority force source destination}
    (acquired : Acquires program before authority force source destination after) : before.SuspensionExtension after := by
  cases acquired with
  | explicitMove moved => exact moved.suspensionExtension
  | copy copied => exact copied.suspensionExtension
  | move _ _ _ moved => exact moved.suspensionExtension

theorem NewValue.suspensionExtension {program : Program} {before after : World} {destination type head sources}
    (constructed : NewValue program before destination type head sources after) : before.SuspensionExtension after :=
  .of_locations constructed.authorityStable.homes.counter constructed.locations

theorem FormsLoan.suspensionExtension {program : Program} {purpose : LoanPurpose} {before after : World}
    {authority mode region referent destination}
    (borrowed : FormsLoan program purpose before authority mode region referent destination after) :
    before.SuspensionExtension after := .of_locations borrowed.homeExtension.counter borrowed.locations

theorem EndsLoan.suspensionExtension {before after : World} {id : Identity} (ended : EndsLoan before id after) :
    before.SuspensionExtension after := by
  cases ended
  exact .of_roots (Nat.le_refl _) rfl

theorem FreshRegion.suspensionExtension {before after : World} {id : Identity}
    (fresh : FreshRegion before id after) : before.SuspensionExtension after := by
  rcases fresh with ⟨_,rfl⟩
  exact .of_roots (Nat.le_refl _) rfl

theorem RegionEnds.suspensionExtension {before after : World} {id : Identity}
    (ended : RegionEnds before id after) : before.SuspensionExtension after := by
  rcases ended with ⟨_,rfl⟩
  exact .of_roots (Nat.le_refl _) rfl

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

end Glorious.Language
