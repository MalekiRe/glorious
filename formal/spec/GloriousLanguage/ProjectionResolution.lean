import GloriousLanguage.Kernel
import GloriousLanguage.PatternPlanTransport

/-! Projection resolution retains the one lexical environment through every
dynamic index and reference hop. Its result is a unique address/authority pair. -/
namespace Glorious.Language

theorem ReferenceView.deterministic {world : World} {handle : Address} {authority : Authority}
    {id : Identity} {mode : Mutability} {left right : Authority} {firstAccess secondAccess : Access}
    (first : ReferenceView world handle authority id mode left firstAccess)
    (second : ReferenceView world handle authority id mode right secondAccess) :
    left = right ∧ firstAccess = secondAccess := by
  rcases first with ⟨_,rfl,rfl⟩ | ⟨_,_,rfl,rfl⟩ | ⟨_,_,rfl,rfl⟩ <;>
    rcases second with ⟨_,rfl,rfl⟩ | ⟨_,_,rfl,rfl⟩ | ⟨_,_,rfl,rfl⟩ <;> simp_all

namespace Kernel

theorem Environment.Selects.deterministic {environment : Environment} {localSlot : Identity}
    {left right : Binding} (first : environment.Selects localSlot left)
    (second : environment.Selects localSlot right) : left = right :=
  second.2.2 left first.1 first.2.1

theorem ResolvesProjections.deterministic {world : World} {environment : Environment}
    {base left right : Address} {authority firstPermission secondPermission : Authority} {projections : List Projection}
    (first : ResolvesProjections world environment base authority projections left firstPermission)
    (second : ResolvesProjections world environment base authority projections right secondPermission) :
    left = right ∧ firstPermission = secondPermission := by
  induction first generalizing right secondPermission with
  | nil => cases second; exact ⟨rfl,rfl⟩
  | field stored field rest ih =>
      cases second with
      | field otherStored otherField otherRest =>
          have same := Option.some.inj (stored.symm.trans otherStored)
          subst_vars
          exact ih otherRest
      | vacantField otherStored otherField =>
          have same := Option.some.inj (stored.symm.trans otherStored)
          subst_vars
          simp_all
  | vacantField stored field =>
      cases second with
      | field otherStored otherField otherRest =>
          have same := Option.some.inj (stored.symm.trans otherStored)
          subst_vars
          simp_all
      | vacantField => exact ⟨rfl,rfl⟩
  | index selected stored head initialized readable nonnegative rest ih =>
      cases second with
      | index otherSelected otherStored otherHead otherInitialized otherReadable otherNonnegative otherRest =>
          have bindingEqual := selected.deterministic otherSelected
          subst_vars
          have valueEqual := Option.some.inj (stored.symm.trans otherStored)
          subst_vars
          have integerEqual := ScalarValue.integer.inj (ValueHead.scalar.inj (head.symm.trans otherHead))
          obtain ⟨_,_,rfl⟩ := integerEqual
          exact ih otherRest
  | dereference stored head initialized readable found live view rest ih =>
      cases second with
      | dereference otherStored otherHead otherInitialized otherReadable otherFound otherLive otherView otherRest =>
          have valueEqual := Option.some.inj (stored.symm.trans otherStored)
          subst_vars
          have idEqual := ValueHead.reference.inj (head.symm.trans otherHead)
          subst_vars
          have loanEqual := Option.some.inj (found.symm.trans otherFound)
          subst_vars
          obtain ⟨rfl,_⟩ := view.deterministic otherView
          exact ih otherRest

theorem ResolvesPlace.deterministic {world : World} {environment : Environment} {place : Place}
    {left right : Address} {firstPermission secondPermission : Authority}
    (first : ResolvesPlace world environment place left firstPermission)
    (second : ResolvesPlace world environment place right secondPermission) :
    left = right ∧ firstPermission = secondPermission := by
  cases first with
  | localSlot selected resolved =>
      cases second with
      | localSlot otherSelected otherResolved =>
          have same := selected.deterministic otherSelected
          subst_vars
          exact resolved.deterministic otherResolved

theorem ResolvesProjections.transport {before after : World} {environment nextEnvironment : Environment}
    {base result : Address} {authority permission : Authority} {projections : List Projection}
    (resolved : ResolvesProjections before environment base authority projections result permission)
    (bindings : ∀ id binding, environment.Selects id binding → nextEnvironment.Selects id binding)
    (stores : ∀ address value, before.Stores address value → after.Stores address value)
    (loans : after.loans = before.loans) :
    ResolvesProjections after nextEnvironment base authority projections result permission := by
  induction resolved with
  | nil => exact .nil
  | field stored field _ ih => exact .field (stores _ _ stored) field ih
  | vacantField stored field => exact .vacantField (stores _ _ stored) field
  | index selected stored head initialized readable nonnegative _ ih =>
      exact .index (bindings _ _ selected) (stores _ _ stored) head initialized
        ((Permitted.stores_iff loans stored (stores _ _ stored)).mp readable) nonnegative ih
  | dereference stored head initialized readable found live view _ ih =>
      have retained := stores _ _ stored
      have permission (authority : Authority) (access : Access) :=
        Permitted.stores_iff (authority := authority) (access := access) loans stored retained
      simp only [ReferenceView, permission _ .unique] at view
      exact .dereference retained head initialized ((permission _ _).mp readable)
        (by simpa only [loans] using found) live view ih

theorem ResolvesPlace.transport {before after : World} {environment nextEnvironment : Environment}
    {place : Place} {address : Address} {authority : Authority}
    (resolved : ResolvesPlace before environment place address authority)
    (bindings : ∀ id binding, environment.Selects id binding → nextEnvironment.Selects id binding)
    (stores : ∀ address value, before.Stores address value → after.Stores address value)
    (loans : after.loans = before.loans) :
    ResolvesPlace after nextEnvironment place address authority := by
  cases resolved with
  | localSlot selected projections =>
      exact .localSlot (bindings _ _ selected) (projections.transport bindings stores loans)

end Kernel
end Glorious.Language
