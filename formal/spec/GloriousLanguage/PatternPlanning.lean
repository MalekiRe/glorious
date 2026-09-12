import GloriousLanguage.Effects
import GloriousLanguage.ReferencePatternPlanning

/-! Clause planning consumes the selected structural match. Closing a clause's
type annotations does not rerun selection or change the payload it matched. -/
namespace Glorious.Language.Kernel

theorem Matches.mapTerms {program : Language.Program} {world : World}
    {address : Address} {pattern : Pattern} (matched : Matches program world address pattern)
    (close : Term → Term) : Matches program world address (pattern.mapTerms close) := by
  refine Matches.rec
    (motive_1 := fun address pattern _ => Matches program world address (pattern.mapTerms close))
    (motive_2 := fun address offset patterns _ => MatchesFields program world address offset
      (patterns.map (Pattern.mapTerms close)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ matched
  all_goals simp only [Pattern.mapTerms,List.map_nil,List.map_cons]
  · intro address; exact .wildcard
  · intro address localSlot value stored initialized; exact .bind stored initialized
  · intro address expected value stored initialized head notFloat; exact .scalar stored initialized head notFloat
  · intro address value stored head initialized; exact .unit stored head initialized
  · intro address value fields stored head live length _ ih
    exact .tuple stored head live (by simpa only [List.length_map] using length) ih
  · intro address value fields stored head initialized length _ ih
    exact .array stored head initialized (by simpa only [List.length_map] using length) ih
  · intro address value variant fields stored head live length _ ih
    exact .constructor stored head live (by simpa only [List.length_map] using length) ih
  · intro address value id loan mode pattern stored head found live modeEq _ ih
    exact .reference stored head found live modeEq ih
  · intro address offset; exact .nil
  · intro address offset first rest _ _ ihFirst ihRest; exact .cons ihFirst ihRest

theorem Matches.of_mapTerms {program : Language.Program} {world : World}
    {address : Address} {pattern : Pattern} {close : Term → Term}
    (matched : Matches program world address (pattern.mapTerms close)) : Matches program world address pattern := by
  have recover {address mapped} (matched : Matches program world address mapped) :
      ∀ pattern, mapped = pattern.mapTerms close → Matches program world address pattern := by
    refine Matches.rec
      (motive_1 := fun address mapped _ => ∀ pattern, mapped = pattern.mapTerms close → Matches program world address pattern)
      (motive_2 := fun address offset mapped _ => ∀ patterns, mapped = patterns.map (Pattern.mapTerms close) →
        MatchesFields program world address offset patterns)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ matched
    · intro address pattern same
      cases pattern <;> simp only [Pattern.mapTerms] at same <;> cases same
      exact .wildcard
    · intro address localSlot value stored initialized pattern same
      cases pattern <;> simp only [Pattern.mapTerms] at same <;> cases same
      exact .bind stored initialized
    · intro address expected value stored initialized head notFloat pattern same
      cases pattern <;> simp only [Pattern.mapTerms] at same <;> cases same
      exact .scalar stored initialized head notFloat
    · intro address value stored head initialized pattern same
      cases pattern <;> simp only [Pattern.mapTerms] at same <;> cases same
      exact .unit stored head initialized
    · intro address value fields stored head live length _ ih pattern same
      cases pattern <;> simp only [Pattern.mapTerms] at same <;> cases same
      exact .tuple stored head live (by simpa only [List.length_map] using length) (ih _ rfl)
    · intro address value fields stored head initialized length _ ih pattern same
      cases pattern <;> simp only [Pattern.mapTerms] at same <;> cases same
      exact .array stored head initialized (by simpa only [List.length_map] using length) (ih _ rfl)
    · intro address value variant fields stored head live length _ ih pattern same
      cases pattern <;> simp only [Pattern.mapTerms] at same <;> cases same
      exact .constructor stored head live (by simpa only [List.length_map] using length) (ih _ rfl)
    · intro address value id loan mode mapped stored head found live modeEq _ ih pattern same
      cases pattern <;> simp only [Pattern.mapTerms] at same <;> cases same
      exact .reference stored head found live modeEq (ih _ rfl)
    · intro address offset patterns same
      cases patterns with
      | nil => exact .nil
      | cons first rest => simp only [List.map_cons] at same; cases same
    · intro address offset first rest _ _ ihFirst ihRest patterns same
      cases patterns with
      | nil => simp only [List.map_nil] at same; cases same
      | cons pattern patterns =>
        simp only [List.map_cons,List.cons.injEq] at same
        exact .cons (ihFirst _ same.1) (ihRest _ same.2)
  exact recover matched pattern rfl

theorem Matches.mapTerms_iff {program : Language.Program} {world : World}
    {address : Address} {pattern : Pattern} {close : Term → Term} :
    Matches program world address (pattern.mapTerms close) ↔ Matches program world address pattern :=
  ⟨Matches.of_mapTerms,fun matched => matched.mapTerms close⟩

end Glorious.Language.Kernel

namespace Glorious.Language.Execution

open Kernel

/-- The common handoff output supplies actual resident readiness. Planning
then consumes the transported matches in the same payload order. -/
theorem PayloadPlan.of_handoff {program : RuntimeProgram} {world : World}
    {addresses : List Address} {patterns : List Pattern} {values : List Value}
    (matched : ListRel (Matches program.declarations world) addresses patterns)
    (ready : ResidentHandoffReady program world
      (addresses.map (fun address => ⟨address,.owner⟩)) values []) :
    ∃ actions, PayloadPlan program.declarations world addresses patterns actions := by
  induction addresses generalizing patterns values with
  | nil => cases matched; exact ⟨_,.nil⟩
  | cons address addresses ih =>
    cases matched with
    | cons first rest =>
      obtain ⟨stored,valuesReady,distinct,permitted⟩ := ready
      cases stored with
      | @cons source value sources values selected stored =>
        obtain ⟨initialized,resources,_⟩ := valuesReady value List.mem_cons_self
        obtain ⟨firstActions,firstPlanned⟩ := first.plan selected initialized resources.2.1 resources.references
          (permitted _ List.mem_cons_self)
        obtain ⟨restActions,restPlanned⟩ := ih rest ⟨stored,
          fun value member => valuesReady value (List.mem_cons_of_mem _ member),
          (List.pairwise_cons.mp distinct).2,
          fun source member => permitted source (List.mem_cons_of_mem _ member)⟩
        exact ⟨_,.cons firstPlanned restPlanned⟩

/-- The selected header's binder annotations are lexical. Closing them for
the fresh clause leaves every actual payload match intact, including the
reference path chosen by `Matches`. No selection decision is repeated. -/
theorem SelectsOperation.payload_matches {program : Kernel.Program} {world : World}
    {handler : InstalledHandler} {id : DeclId} {arguments : List Term}
    {payload : List ResolvedPlace} {arm : OperationArm}
    (selected : SelectsOperation program world handler id arguments payload arm)
    (close : Term → Term) :
    ListRel (fun source pattern => Permitted world source.authority .shared source.address ∧
      Matches program.declarations world source.address pattern)
      payload (arm.patterns.map (Pattern.mapTerms close)) := by
  obtain ⟨skipped,rest,sourceArms,accepted,earlier⟩ := selected
  have matched := accepted.2.2
  have header : (arm.closeHead handler.environment.instantiation).patterns =
      arm.patterns.map (Pattern.mapTerms handler.environment.instantiation.term) := by
    cases arm; rfl
  rw [header] at matched
  clear accepted earlier header sourceArms skipped rest
  generalize arm.patterns = patterns at matched ⊢
  induction patterns generalizing payload with
  | nil => cases matched; exact .nil
  | cons pattern patterns ih =>
    cases matched with
    | cons first rest =>
      exact .cons ⟨first.1,first.2.of_mapTerms.mapTerms close⟩ (ih rest)

end Glorious.Language.Execution
