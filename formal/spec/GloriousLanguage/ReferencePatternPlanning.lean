import GloriousLanguage.HandoffAccess
import GloriousLanguage.PatternTransport

/-! Actual match-to-plan construction uses the common reachable-reference
readiness contract, preserving the authority that reached each handle. -/
namespace Glorious.Language

private theorem storedChild {world : World} {address : Address} {value child : Value} {index : Nat}
    (stored : world.Stores address value) (field : value.fields[index]? = some (some child)) :
    world.Stores (address.child index) child := by
  change world.read { address with fields := address.fields ++ [index] } = some child
  rw [World.read_append,stored]
  simp [Value.atPath,field]

namespace Kernel

/-- Planning follows the already selected match. Initialization and each
derived reference view come from the same general value-handoff contract used
by moves, copies and invocation inputs; no pattern-specific readiness walk or
preconstructed plan is assumed. -/
theorem Matches.plan {program : RuntimeProgram} {world : World} {address : Address}
    {pattern : Pattern} {value : Value} {authority : Authority} {access : Access}
    (matched : Matches program.declarations world address pattern)
    (stored : world.Stores address value) (initialized : value.Initialized)
    (restored : value.LoansRestored program world)
    (references : value.ReferencesAccessible world authority access)
    (permitted : Permitted world authority access address) :
    ∃ actions, PatternPlan program.declarations world address authority access pattern actions := by
  refine Matches.rec
    (motive_1 := fun address pattern _ => ∀ value authority access,
      world.Stores address value → value.Initialized → value.LoansRestored program world →
      value.ReferencesAccessible world authority access → Permitted world authority access address →
      ∃ actions, PatternPlan program.declarations world address authority access pattern actions)
    (motive_2 := fun address offset patterns _ => ∀ value authority access,
      world.Stores address value → value.Initialized → value.LoansRestored program world →
      value.ReferencesAccessible world authority access → Permitted world authority access address →
      offset + patterns.length ≤ value.fields.length →
      ∃ actions, PatternPlans program.declarations world address authority access offset patterns actions)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ matched value authority access stored initialized restored references permitted
  · intro address value authority access _ _ _ _ _
    by_cases owned : access = .owned
    · subst access; exact ⟨_,.wildcardOwned⟩
    · exact ⟨_,.wildcardBorrowed owned⟩
  · intro address localSlot matchedValue _ _ value authority access _ _ _ _ _
    exact ⟨_,.bind⟩
  · intro address expected matchedValue _ _ _ _ value authority access _ _ _ _ _
    by_cases owned : access = .owned
    · subst access; exact ⟨_,.scalarOwned⟩
    · exact ⟨_,.scalarBorrowed owned⟩
  · intro address matchedValue _ _ _ value authority access _ _ _ _ _
    by_cases owned : access = .owned
    · subst access; exact ⟨_,.unitOwned⟩
    · exact ⟨_,.unitBorrowed owned⟩
  · intro address matchedValue fields selected _ _ length _ ih value authority access stored initialized restored references permitted
    have same := Option.some.inj (selected.symm.trans stored)
    subst matchedValue
    obtain ⟨actions,planned⟩ := ih _ _ _ stored initialized restored references permitted (by omega)
    exact ⟨_,.aggregate (Or.inl rfl) planned⟩
  · intro address matchedValue fields selected _ _ length _ ih value authority access stored initialized restored references permitted
    have same := Option.some.inj (selected.symm.trans stored)
    subst matchedValue
    obtain ⟨actions,planned⟩ := ih _ _ _ stored initialized restored references permitted (by omega)
    exact ⟨_,.aggregate (Or.inr (Or.inl rfl)) planned⟩
  · intro address matchedValue variant fields selected _ _ length _ ih value authority access stored initialized restored references permitted
    have same := Option.some.inj (selected.symm.trans stored)
    subst matchedValue
    obtain ⟨actions,planned⟩ := ih _ _ _ stored initialized restored references permitted (by omega)
    exact ⟨_,.aggregate (Or.inr (Or.inr ⟨_,rfl⟩)) planned⟩
  · intro address matchedValue id loan mode pattern selected head found live modeEq _ ih value authority access stored initialized restored references permitted
    have same := Option.some.inj (selected.symm.trans stored)
    subst matchedValue
    have reached : value.ReachableReference world authority access id authority access := .resident .root head
    obtain ⟨actual,selected,_,target,targetStored,targetInitialized⟩ := restored.direct .root head
    have sameLoan := Option.some.inj (found.symm.trans selected)
    subst actual
    obtain ⟨actual,selected,_,referentPermission⟩ := references id authority access reached
    have sameLoan := Option.some.inj (found.symm.trans selected)
    subst actual
    obtain ⟨actions,planned⟩ := ih _ _ _ targetStored targetInitialized
      (restored.referent reached found targetStored) (references.referent reached found targetStored) referentPermission
    subst mode
    exact ⟨_,.reference stored head found rfl live initialized permitted.lend_shared
      (ReferenceView.of_permitted permitted id loan.mode) planned⟩
  · intro address offset value authority access _ _ _ _ _ _
    exact ⟨_,.nil⟩
  · intro address offset first rest _ _ ihFirst ihRest value authority access stored initialized restored references permitted bound
    have inBounds : offset < value.fields.length := by simp only [List.length_cons] at bound; omega
    have present := List.getElem?_eq_getElem inBounds
    obtain ⟨child,field⟩ := Option.isSome_iff_exists.mp
      ((initialized [] value .root).2 _ (List.getElem_mem inBounds))
    have selected : value.fields[offset]? = some (some child) := by rw [present,field]
    have located : ResidentAt value [offset] child := .field selected .root
    obtain ⟨firstActions,firstPlanned⟩ := ihFirst _ _ _ (storedChild stored selected)
      (initialized.resident located) (restored.resident located) (references.resident located) (permitted.child offset)
    obtain ⟨restActions,restPlanned⟩ := ihRest _ _ _ stored initialized restored references permitted (by
      simp only [List.length_cons] at bound
      omega)
    exact ⟨_,.cons firstPlanned restPlanned⟩

/-- Relocating an initialized payload preserves its selected match when the
actual reference graph is framed. Only loans reached from that payload are
consulted; the moved source may be vacant and unrelated residents may change. -/
theorem Matches.transport_value {program : RuntimeProgram} {before after : World}
    {source destination : Address} {pattern : Pattern} {value : Value}
    (matched : Matches program.declarations before source pattern)
    (stored : before.Stores source value) (relocated : after.Stores destination value)
    (initialized : value.Initialized) (restored : value.LoansRestored program before)
    (framed : ∀ identity authority access,
      value.ReachableReference before .owner .shared identity authority access →
      ∀ loan, before.loans.get identity = some loan →
        after.loans.get identity = some loan ∧
        ∀ target, before.Stores loan.referent target → after.Stores loan.referent target) :
    Matches program.declarations after destination pattern := by
  refine Matches.rec
    (motive_1 := fun source pattern _ => ∀ destination value,
      before.Stores source value → after.Stores destination value → value.Initialized →
      value.LoansRestored program before →
      (∀ identity authority access,
        value.ReachableReference before .owner .shared identity authority access →
        ∀ loan, before.loans.get identity = some loan →
          after.loans.get identity = some loan ∧
          ∀ target, before.Stores loan.referent target → after.Stores loan.referent target) →
      Matches program.declarations after destination pattern)
    (motive_2 := fun source offset patterns _ => ∀ destination value,
      before.Stores source value → after.Stores destination value → value.Initialized →
      value.LoansRestored program before →
      (∀ identity authority access,
        value.ReachableReference before .owner .shared identity authority access →
        ∀ loan, before.loans.get identity = some loan →
          after.loans.get identity = some loan ∧
          ∀ target, before.Stores loan.referent target → after.Stores loan.referent target) →
      offset + patterns.length ≤ value.fields.length →
      MatchesFields program.declarations after destination offset patterns)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ matched destination value stored relocated initialized restored framed
  · intro source destination value _ _ _ _ _; exact .wildcard
  · intro source localSlot matchedValue _ _ destination value _ relocated initialized _ _
    exact .bind relocated initialized
  · intro source expected matchedValue selected _ head notFloat destination value stored relocated initialized _ _
    have same := Option.some.inj (selected.symm.trans stored)
    subst matchedValue
    exact .scalar relocated initialized head notFloat
  · intro source matchedValue selected head _ destination value stored relocated initialized _ _
    have same := Option.some.inj (selected.symm.trans stored)
    subst matchedValue
    exact .unit relocated head initialized
  · intro source matchedValue fields selected head live length _ ih destination value stored relocated initialized restored framed
    have same := Option.some.inj (selected.symm.trans stored)
    subst matchedValue
    exact .tuple relocated head live length (ih _ _ stored relocated initialized restored framed (by omega))
  · intro source matchedValue fields selected head _ length _ ih destination value stored relocated initialized restored framed
    have same := Option.some.inj (selected.symm.trans stored)
    subst matchedValue
    exact .array relocated head initialized length (ih _ _ stored relocated initialized restored framed (by omega))
  · intro source matchedValue variant fields selected head live length _ ih destination value stored relocated initialized restored framed
    have same := Option.some.inj (selected.symm.trans stored)
    subst matchedValue
    exact .constructor relocated head live length (ih _ _ stored relocated initialized restored framed (by omega))
  · intro source matchedValue id loan mode pattern selected head found live modeEq _ ih destination value stored relocated initialized restored framed
    have same := Option.some.inj (selected.symm.trans stored)
    subst matchedValue
    have reached : value.ReachableReference before .owner .shared id .owner .shared := .resident .root head
    obtain ⟨actual,selected,_,target,targetStored,targetInitialized⟩ := restored.direct .root head
    have sameLoan := Option.some.inj (found.symm.trans selected)
    subst actual
    obtain ⟨loanAfter,targetAfter⟩ := framed id .owner .shared reached loan found
    apply Matches.reference relocated head loanAfter live modeEq
    refine ih _ _ targetStored (targetAfter target targetStored) targetInitialized
      (restored.referent reached found targetStored) ?_
    intro next nextAuthority nextAccess nested actual selected
    obtain ⟨view,requested,nested⟩ := nested.rebase
      (Authority.owner.referenceView id (ReferenceAccess .shared loan.mode)) (ReferenceAccess .shared loan.mode)
    exact framed next view requested (Value.ReachableReference.referent_prefix reached found targetStored nested) actual selected
  · intro source offset destination value _ _ _ _ _ _; exact .nil
  · intro source offset first rest _ _ ihFirst ihRest destination value stored relocated initialized restored framed bound
    have inBounds : offset < value.fields.length := by simp only [List.length_cons] at bound; omega
    have present := List.getElem?_eq_getElem inBounds
    obtain ⟨child,field⟩ := Option.isSome_iff_exists.mp
      ((initialized [] value .root).2 _ (List.getElem_mem inBounds))
    have selected : value.fields[offset]? = some (some child) := by rw [present,field]
    have located : ResidentAt value [offset] child := .field selected .root
    refine .cons (ihFirst _ _ (storedChild stored selected) (storedChild relocated selected)
      (initialized.resident located) (restored.resident located) ?_)
      (ihRest _ _ stored relocated initialized restored framed (by simp only [List.length_cons] at bound; omega))
    intro identity authority access reachable loan found
    exact framed identity authority access (reachable.resident_prefix located) loan found

end Kernel

end Glorious.Language
