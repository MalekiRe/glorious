import GloriousLanguage.OrderedHandoff
import GloriousLanguage.AllocationOutcomes
import GloriousLanguage.HandoffPreservation

/-! Exhaustion is an outcome of the actual ordered preparation, not a
separate walk over a successful prefix. Every earlier pending-batch guard
remains present, and the world at the first failed allocation is retained. -/
namespace Glorious.Language
open Kernel

theorem Kernel.BindsInputsAttemptFor.ready {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {footprint : List Address} {before after : World}
    {inputs : List InvocationInput} {bindings : Environment} {outcome : PreparationOutcome}
    (attempted : BindsInputsAttemptFor program recipient activation scope region footprint
      before inputs bindings after outcome) : InvocationInputsReadyFor program before footprint inputs := by
  cases attempted with
  | nil => exact ⟨by simp,.nil,by intro input member; cases member⟩
  | cons ready _ _ | exhausted ready _ => exact ready

/-- The actual failure derivation exposes its complete successful front and
the positively ready failing head, at exactly the retained partial world. -/
theorem Kernel.BindsInputsAttemptFor.exhausted_prefix {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {footprint : List Address} {before after : World}
    {inputs : List InvocationInput} {bindings : Environment}
    (attempted : BindsInputsAttemptFor program recipient activation scope region footprint
      before inputs bindings after .exhausted) :
    ∃ front input rest, inputs = front ++ input :: rest ∧
      BindsInputsFor program recipient activation scope region footprint before front bindings after ∧
      InvocationInputsReadyFor program after footprint (input :: rest) ∧
      BindsInputExhausted program region after input := by
  induction inputs generalizing before bindings with
  | nil => cases attempted
  | cons head pending ih =>
    cases attempted with
    | cons ready bound tail =>
      obtain ⟨front,input,rest,equation,beginning,remaining,failed⟩ := ih tail
      refine ⟨head :: front,input,rest,congrArg (head :: ·) equation,?_,remaining,failed⟩
      rw [equation] at ready
      exact .cons (InvocationInputsReadyFor.prefix (front := head :: front) ready) bound beginning
    | exhausted ready failed => exact ⟨[],head,pending,rfl,.nil,ready,failed⟩

namespace Execution

theorem ProtectsAttemptFor.ready {program : Kernel.Program} {context : Context}
    {footprint : List Address} {before after : World} {sources : List ResolvedPlace}
    {destinations : List Address} {outcome : PreparationOutcome}
    (attempted : ProtectsAttemptFor program context footprint before sources destinations after outcome) :
    ∃ values, ResidentHandoffReady program before sources values footprint ∧
      ∀ source ∈ sources, source.address ∈ footprint := by
  cases attempted with
  | nil =>
    refine ⟨[],⟨.nil,?_,.nil,?_⟩,?_⟩
    · intro value member; cases member
    · intro source member; cases member
    · intro source member; cases member
  | cons ready _ _ | exhausted ready _ => exact ready

theorem ProtectsAttemptFor.exhausted_prefix {program : Kernel.Program} {context : Context}
    {footprint : List Address} {before after : World} {sources : List ResolvedPlace}
    {destinations : List Address}
    (attempted : ProtectsAttemptFor program context footprint before sources destinations after .exhausted) :
    ∃ front source rest, sources = front ++ source :: rest ∧
      ProtectsFor program context footprint before front destinations after ∧
      (∃ values, ResidentHandoffReady program after (source :: rest) values footprint ∧
        ∀ place ∈ source :: rest, place.address ∈ footprint) ∧
      ProtectExhausted program context after source.address source.authority := by
  induction sources generalizing before destinations with
  | nil => cases attempted
  | cons head pending ih =>
    cases attempted with
    | cons ready kept tail =>
      obtain ⟨front,source,rest,equation,beginning,remaining,failed⟩ := ih tail
      refine ⟨head :: front,source,rest,congrArg (head :: ·) equation,?_,remaining,failed⟩
      obtain ⟨values,residents,coverage⟩ := ready
      rw [equation] at residents coverage
      obtain ⟨keptValues,keptResidents⟩ := ResidentHandoffReady.prefix (front := head :: front) residents
      exact .cons ⟨keptValues,keptResidents,fun place member =>
        coverage place (List.mem_append_left _ member)⟩ kept beginning
    | exhausted ready failed => exact ⟨[],head,pending,rfl,.nil,ready,failed⟩

/-- A terminal failed handoff keeps the well-formed partial world produced by
its actual successful prefix; exhaustion performs no destruction or rollback. -/
theorem ProtectsAttemptFor.wellFormed {program : Kernel.Program} {context : Context}
    {footprint : List Address} {before after : World} {sources : List ResolvedPlace}
    {destinations : List Address} {outcome : PreparationOutcome}
    (valid : before.WellFormed)
    (attempted : ProtectsAttemptFor program context footprint before sources destinations after outcome) :
    after.WellFormed := by
  cases outcome with
  | complete => exact ProtectsFor.wellFormed valid attempted
  | exhausted =>
    obtain ⟨_,_,_,_,beginning,_,_⟩ := attempted.exhausted_prefix
    exact ProtectsFor.wellFormed valid beginning

end Execution
end Glorious.Language
