import GloriousLanguage.HandoffPreservation
import GloriousLanguage.RehomeFraming

/-! An already-constructed plan retains its exact reference views when a
transition preserves old residents and the loan table. This includes fresh
continuation construction; it does not inspect unrelated newly stored values. -/
namespace Glorious.Language

theorem Permitted.of_same_loans {before after : World} {address : Address}
    {authority : Authority} {access : Access}
    (loans : after.loans = before.loans) (root : ∃ root, after.root address = some root)
    (permitted : Permitted before authority access address) : Permitted after authority access address := by
  induction authority with
  | owner => exact ⟨root,by simpa only [loans] using permitted.2⟩
  | loan identity => exact ⟨root,permitted.2.transport loans⟩
  | shared backing ih => exact ⟨root,permitted.2.1,ih permitted.2.2⟩
  | guarded backing carrier ih =>
      obtain ⟨loan,selected,guard⟩ := permitted.2.2
      exact ⟨root,ih permitted.2.1,loan,by simpa only [loans] using selected,guard.transport loans⟩

theorem Permitted.stores_iff {before after : World} {address : Address} {value : Value}
    {authority : Authority} {access : Access}
    (loans : after.loans = before.loans) (stored : before.Stores address value)
    (retained : after.Stores address value) :
    Permitted before authority access address ↔ Permitted after authority access address := by
  obtain ⟨first,firstRoot,_⟩ := Option.bind_eq_some_iff.mp stored
  obtain ⟨last,lastRoot,_⟩ := Option.bind_eq_some_iff.mp retained
  exact ⟨fun permitted => permitted.of_same_loans loans ⟨last,lastRoot⟩,
    fun permitted => permitted.of_same_loans loans.symm ⟨first,firstRoot⟩⟩

theorem Kernel.PatternPlan.transport {program : Language.Program} {before after : World}
    {address : Address} {authority : Authority} {access : Access} {pattern : Kernel.Pattern}
    {actions : Kernel.PatternActions}
    (planned : Kernel.PatternPlan program before address authority access pattern actions)
    (stores : ∀ address value, before.Stores address value → after.Stores address value)
    (loans : after.loans = before.loans) :
    Kernel.PatternPlan program after address authority access pattern actions := by
  refine Kernel.PatternPlan.rec
    (motive_1 := fun address authority access pattern actions _ =>
      Kernel.PatternPlan program after address authority access pattern actions)
    (motive_2 := fun address authority access offset patterns actions _ =>
      Kernel.PatternPlans program after address authority access offset patterns actions)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ planned
  · intro address authority; exact .wildcardOwned
  · intro address authority access borrowed; exact .wildcardBorrowed borrowed
  · intro address authority access localSlot; exact .bind
  · intro address authority scalar; exact .scalarOwned
  · intro address authority access scalar borrowed; exact .scalarBorrowed borrowed
  · intro address authority; exact .unitOwned
  · intro address authority access borrowed; exact .unitBorrowed borrowed
  · intro address authority access pattern fields actions shape _ ih
    exact .aggregate shape ih
  · intro address authority access pattern mode value identity loan actions view nestedAccess
      stored head selected modeEq live initialized permitted viewed _ ih
    have retained := stores address value stored
    have permission (authority : Authority) (access : Access) :=
      Permitted.stores_iff (authority := authority) (access := access) loans stored retained
    refine .reference retained head (by simpa only [loans] using selected) modeEq live initialized
      ((permission _ _).mp permitted) ?_ ih
    simpa only [ReferenceView,Authority.referenceView_same_loans loans,← permission _ .unique] using viewed
  · intro address authority access offset; exact .nil
  · intro address authority access offset pattern rest first later _ _ ihFirst ihRest
    exact .cons ihFirst ihRest

theorem NewValue.empty_loans {program : RuntimeProgram} {before after : World}
    {destination : Address} {type : Term} {head : ValueHead}
    (created : NewValue program before destination type head [] after) : after.loans = before.loans := by
  cases created with
  | construct _ _ _ _ cleared written =>
      cases cleared
      have loans := World.write_loans written
      exact loans

theorem NewValue.empty_preserves_stored {program : RuntimeProgram} {before after : World}
    {destination observed : Address} {type : Term} {head : ValueHead} {value : Value}
    (created : NewValue program before destination type head [] after)
    (stored : before.Stores observed value) (outside : ¬ destination.Overlaps observed) :
    after.Stores observed value := by
  cases created with
  | construct _ _ _ _ cleared written =>
      cases cleared
      exact (World.write_disjoint written outside).trans stored

theorem Allocates.newValue_preserves_stored {program : RuntimeProgram} {before allocated after : World}
    {home region type layout mutable destination} {head : ValueHead} {observed : Address} {value : Value}
    (valid : before.WellFormed)
    (allocation : Allocates program.declarations before home region type layout mutable destination allocated)
    (created : NewValue program allocated destination type head [] after)
    (stored : before.Stores observed value) : after.Stores observed value := by
  apply created.empty_preserves_stored ((allocation.read valid observed).trans stored)
  intro overlap
  obtain ⟨root,selected,_⟩ := Option.bind_eq_some_iff.mp stored
  have bound := World.root_bound valid (World.root_found selected).1
  have same : before.nextRoot = observed.root := allocation.fresh_root.1.symm.trans overlap.1
  exact Nat.lt_irrefl _ (same ▸ bound)

namespace Execution

theorem PayloadPlan.transport {program : Program} {before after : World}
    {addresses : List Address} {patterns : List Kernel.Pattern} {actions : Kernel.PatternActions}
    (planned : PayloadPlan program before addresses patterns actions)
    (stores : ∀ address value, before.Stores address value → after.Stores address value)
    (loans : after.loans = before.loans) : PayloadPlan program after addresses patterns actions := by
  induction planned with
  | nil => exact .nil
  | cons first _ ih => exact .cons (first.transport stores loans) ih

theorem PayloadPlan.suspend {program : Program} {world : World}
    {addresses : List Address} {patterns : List Kernel.Pattern} {actions : Kernel.PatternActions}
    (planned : PayloadPlan program world addresses patterns actions) (roots : List Identity) (identity : Identity) :
    PayloadPlan program (suspendRoots world roots identity) addresses patterns actions := by
  rw [suspendRoots.eq_rehome]
  exact planned.transport (fun address _ stored =>
    (World.rehome_read world (fun key root => if key ∈ roots then .suspended identity else root.home) address).trans stored) rfl

theorem PayloadPlan.fresh_value {program : RuntimeProgram} {before allocated after : World}
    {home region type layout mutable destination} {head : ValueHead}
    {addresses : List Address} {patterns : List Kernel.Pattern} {actions : Kernel.PatternActions}
    (planned : PayloadPlan program.declarations before addresses patterns actions)
    (valid : before.WellFormed)
    (allocation : Allocates program.declarations before home region type layout mutable destination allocated)
    (created : NewValue program allocated destination type head [] after) :
    PayloadPlan program.declarations after addresses patterns actions :=
  planned.transport (fun _ _ stored => allocation.newValue_preserves_stored valid created stored)
    (created.empty_loans.trans allocation.loans)

end Execution
end Glorious.Language
