import GloriousLanguage.Machine

namespace Glorious.Language
open Kernel

/-- Restrict the pending inputs, never the original write footprint. This is
the readiness consumed by a successful front of the actual invocation fold. -/
theorem Kernel.InvocationInputsReadyFor.prefix {program : RuntimeProgram} {world : World}
    {footprint : List Address} {front suffix : List InvocationInput}
    (ready : InvocationInputsReadyFor program world footprint (front ++ suffix)) :
    InvocationInputsReadyFor program world footprint front := by
  refine ⟨?_,?_,?_⟩
  · intro address member
    exact ready.1 address (by simpa only [List.flatMap_append] using List.mem_append_left _ member)
  · have separated := ready.2.1
    rw [List.flatMap_append] at separated
    exact (List.pairwise_append.mp separated).1
  · intro input member
    exact ready.2.2 input (List.mem_append_left _ member)

/-- Decompose the successful producer itself. No second success relation is
introduced, and both halves retain the footprint selected by the caller. -/
theorem Kernel.BindsInputsFor.split {program : RuntimeProgram} {recipient : ClaimCustody}
    {activation scope region : Identity} {footprint : List Address} {before after : World}
    {front suffix : List InvocationInput} {bindings : Environment}
    (bound : BindsInputsFor program recipient activation scope region footprint
      before (front ++ suffix) bindings after) :
    ∃ middle first last, bindings = first ++ last ∧
      BindsInputsFor program recipient activation scope region footprint before front first middle ∧
      BindsInputsFor program recipient activation scope region footprint middle suffix last after := by
  induction front generalizing before bindings with
  | nil => exact ⟨before,[],bindings,rfl,.nil,bound⟩
  | cons input front ih =>
    cases bound with
    | cons ready head tail =>
      obtain ⟨middle,first,last,equation,beginning,ending⟩ := ih tail
      exact ⟨middle, _ :: first,last,congrArg (_ :: ·) equation,
        .cons (InvocationInputsReadyFor.prefix (front := input :: front) ready) head beginning,ending⟩

private theorem listRel_split_left {α β : Type} {relation : α → β → Prop}
    {front suffix : List α} {values : List β}
    (paired : ListRel relation (front ++ suffix) values) :
    ∃ first last, values = first ++ last ∧ ListRel relation front first ∧
      ListRel relation suffix last := by
  induction front generalizing values with
  | nil => exact ⟨[],values,rfl,.nil,paired⟩
  | cons source front ih =>
    cases paired with
    | cons head tail =>
      obtain ⟨first,last,equation,beginning,ending⟩ := ih tail
      exact ⟨_ :: first,last,congrArg (_ :: ·) equation,.cons head beginning,ending⟩

/-- The front snapshot comes from the same actual source reads; reference
and raw-resource readiness remain indexed by the full original footprint. -/
theorem ResidentHandoffReady.prefix {program : RuntimeProgram} {world : World}
    {footprint : List Address} {front suffix : List ResolvedPlace} {values : List Value}
    (ready : ResidentHandoffReady program world (front ++ suffix) values footprint) :
    ∃ kept, ResidentHandoffReady program world front kept footprint := by
  obtain ⟨first,last,equation,beginning,_⟩ := listRel_split_left ready.1
  refine ⟨first,beginning,?_,(List.pairwise_append.mp ready.2.2.1).1,?_⟩
  · intro value member
    exact ready.2.1 value (equation ▸ List.mem_append_left _ member)
  · intro source member
    exact ready.2.2.2 source (List.mem_append_left _ member)

/-- A failed later allocation can expose this genuine successful front and
its intermediate world. The original footprint survives on both derivations. -/
theorem Execution.ProtectsFor.split {program : Kernel.Program} {context : Execution.Context}
    {footprint : List Address} {before after : World} {front suffix : List ResolvedPlace}
    {destinations : List Address}
    (handoff : Execution.ProtectsFor program context footprint
      before (front ++ suffix) destinations after) :
    ∃ middle first last, destinations = first ++ last ∧
      Execution.ProtectsFor program context footprint before front first middle ∧
      Execution.ProtectsFor program context footprint middle suffix last after := by
  induction front generalizing before destinations with
  | nil => exact ⟨before,[],destinations,rfl,.nil,handoff⟩
  | cons source front ih =>
    cases handoff with
    | cons ready head tail =>
      obtain ⟨middle,first,last,equation,beginning,ending⟩ := ih tail
      obtain ⟨values,residents,coverage⟩ := ready
      obtain ⟨kept,residents⟩ := ResidentHandoffReady.prefix (front := source :: front) residents
      refine ⟨middle, _ :: first,last,congrArg (_ :: ·) equation,?_,ending⟩
      exact .cons ⟨kept,residents,fun place member =>
        coverage place (List.mem_append_left _ member)⟩ head beginning

end Glorious.Language
