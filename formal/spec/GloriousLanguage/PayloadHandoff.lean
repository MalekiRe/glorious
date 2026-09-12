import GloriousLanguage.HandoffPreservation
import GloriousLanguage.PatternPlanning

/-! Selected payload matching survives the common ordered handoff. Clause
planning is constructed from the resulting actual residents and permissions;
it is not supplied as an admission premise for the relocation being proved. -/
namespace Glorious.Language.Execution
open Kernel

private theorem matches_snapshot {program : RuntimeProgram} {before after : World}
    {sources : List ResolvedPlace} {destinations footprint : List Address}
    {values : List Value} {patterns : List Pattern}
    (stored : ListRel (fun source value => before.Stores source.address value) sources values)
    (relocated : ListRel (fun (source : ResolvedPlace) value => after.Stores source.address value)
      (destinations.map (fun address => ⟨address,.owner⟩)) values)
    (ready : Values.MoveReady program before values footprint)
    (framed : ∀ value ∈ values, value.SupportFramed before after)
    (loans : after.loans = before.loans)
    (matched : ListRel (fun source pattern => Matches program.declarations before source.address pattern) sources patterns) :
    ListRel (Matches program.declarations after) destinations patterns := by
  induction stored generalizing destinations patterns with
  | nil =>
      cases destinations with
      | nil => cases matched; exact .nil
      | cons _ _ => cases relocated
  | @cons source value sources values selected stored ih =>
      cases destinations with
      | nil => cases relocated
      | cons destination destinations =>
        cases relocated with
        | cons relocated restRelocated =>
          cases matched with
          | cons matched restMatched =>
            have firstReady := ready value List.mem_cons_self
            have firstFramed := framed value List.mem_cons_self
            refine .cons (matched.transport_value selected relocated firstReady.1 firstReady.2.1.2.1 ?_)
              (ih restRelocated (fun value member => ready value (List.mem_cons_of_mem _ member))
                (fun value member => framed value (List.mem_cons_of_mem _ member)) restMatched)
            intro identity authority access reached loan found
            exact ⟨by simpa only [loans] using found,fun _ stored =>
              (firstFramed _ (Value.Support.reference reached found)).1.trans stored⟩

theorem ProtectsFor.matches {program : Kernel.Program} {context : Context} {before after : World}
    {footprint destinations : List Address} {sources : List ResolvedPlace} {patterns : List Pattern}
    (valid : before.WellFormed) (kept : ProtectsFor program context footprint before sources destinations after)
    (matched : ListRel (fun source pattern => Matches program.declarations before source.address pattern) sources patterns) :
    ListRel (Matches program.declarations after) destinations patterns := by
  obtain ⟨values,ready⟩ := kept.ready
  have relocated := kept.resident_snapshot valid ready.1
  exact matches_snapshot ready.1 relocated.1 ready.2.1
    (fun value member => kept.supportFramed valid (ready.2.1 value member).2) kept.loans matched

theorem ProtectsFor.payloadPlan {program : Kernel.Program} {context : Context} {before after : World}
    {footprint destinations : List Address} {sources : List ResolvedPlace} {patterns : List Pattern}
    (valid : before.WellFormed) (kept : ProtectsFor program context footprint before sources destinations after)
    (matched : ListRel (fun source pattern => Matches program.declarations before source.address pattern) sources patterns) :
    ∃ actions, PayloadPlan program.declarations after destinations patterns actions := by
  obtain ⟨values,ready⟩ := kept.ready
  have relocated := kept.resident_snapshot valid ready.1
  apply PayloadPlan.of_handoff (kept.matches valid matched)
    (values := values)
  exact ⟨relocated.1,fun value member => ⟨(relocated.2.1 value member).1,
    (relocated.2.1 value member).2.restrict (by simp)⟩,relocated.2.2⟩

/-- Closing the selected arm's annotations and entering its fresh region do
not repeat dispatch. The exact selected match feeds the actual handoff fold. -/
theorem SelectsOperation.handoff_payloadPlan {program : Kernel.Program} {before withRegion after : World}
    {handler : InstalledHandler} {id : DeclId} {arguments : List Term}
    {payload : List ResolvedPlace} {arm : OperationArm} {context : Context}
    {region : Identity} {destinations footprint : List Address}
    (selected : SelectsOperation program before handler id arguments payload arm)
    (fresh : FreshRegion before region withRegion) (valid : withRegion.WellFormed)
    (kept : ProtectsFor program context footprint withRegion payload destinations after)
    (close : Term → Term) :
    ∃ actions, PayloadPlan program.declarations after destinations
      (arm.patterns.map (Pattern.mapTerms close)) actions := by
  apply kept.payloadPlan valid
  apply (selected.payload_matches close).imp
  intro source pattern matched
  apply matched.2.transport
  · obtain ⟨_,rfl⟩ := fresh
    intro address
    rfl
  · obtain ⟨_,rfl⟩ := fresh
    intro identity
    rfl

end Glorious.Language.Execution
