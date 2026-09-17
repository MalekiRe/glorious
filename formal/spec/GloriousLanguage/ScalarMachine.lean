import GloriousLanguage.ScalarStorageProgress
import GloriousLanguage.MemoryPreservation

/-! The scalar machine boundary combines actual resident reads, unique
calculation outcomes and unique result installation with storage preservation. -/
namespace Glorious.Language

theorem NewValue.empty_deterministic {program : RuntimeProgram} {before left right : World}
    {destination : Address} {type : Term} {head : ValueHead}
    (first : NewValue program before destination type head [] left)
    (second : NewValue program before destination type head [] right) : left = right := by
  cases first with
  | construct vacant typed ready distinct clears written =>
      cases ready.1
      cases clears
      cases second with
      | construct vacant typed ready distinct clears rewritten =>
          cases ready.1
          cases clears
          have same := Option.some.inj (written.symm.trans rewritten)
          subst_vars
          rfl

end Glorious.Language

namespace Glorious.Language.Execution

theorem ScalarAt.deterministic {world : World} {source : ResolvedPlace} {left right : ScalarValue}
    (first : ScalarAt world source left) (second : ScalarAt world source right) : left = right := by
  obtain ⟨_,firstValue,firstStored,firstHead,_⟩ := first
  obtain ⟨_,secondValue,secondStored,secondHead,_⟩ := second
  have same := Option.some.inj (firstStored.symm.trans secondStored)
  subst secondValue
  exact ValueHead.scalar.inj (firstHead.symm.trans secondHead)

theorem ScalarValues.deterministic {world : World} {sources : List ResolvedPlace}
    {left right : List ScalarValue} (first : ScalarValues world sources left)
    (second : ScalarValues world sources right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons first rest ih =>
      cases second with
      | cons second remaining => rw [first.deterministic second,ih remaining]

theorem StoresScalar.deterministic {program : Kernel.Program} {before left right : World}
    {destination : Address} {scalar : ScalarValue}
    (first : StoresScalar program before destination scalar left)
    (second : StoresScalar program before destination scalar right) : left = right :=
  first.2.2.empty_deterministic second.2.2

theorem PrimitiveStep.scalar_cases {program : Kernel.Program} {before after : State} {event : Option Event}
    {context : Context} {destination : Address} {binding : RuntimeBinding}
    {arguments : List Term} {operands : List ResolvedPlace} {next : Kernel.Code} {primitive : Primitive}
    (task : before.task = .primitive context destination binding arguments operands next)
    (identity : binding.primitive = some primitive) (scalar : primitive.IsScalar)
    (step : PrimitiveStep program before event after) :
    (∃ values result written, ScalarValues before.world operands values ∧
      PrimitiveCalculation program.declarations.input.target primitive arguments values (.ok result) ∧
      StoresScalar program before.world destination result written ∧ event = none ∧
      after = { before with world := written, task := .run context next }) ∨
    (∃ values reason, ScalarValues before.world operands values ∧
      PrimitiveCalculation program.declarations.input.target primitive arguments values (.error reason) ∧
      event = some (.fatal reason) ∧ after = { before with task := .fatal reason }) := by
  cases step <;> simp_all [Primitive.IsScalar]
  · exact ⟨_,by assumption,_,by assumption,by assumption⟩
  · exact ⟨_,by assumption,by assumption⟩

theorem PrimitiveStep.scalar_deterministic {program : Kernel.Program} {before left right : State}
    {firstEvent secondEvent : Option Event} {context : Context} {destination : Address}
    {binding : RuntimeBinding} {arguments : List Term} {operands : List ResolvedPlace}
    {next : Kernel.Code} {primitive : Primitive}
    (task : before.task = .primitive context destination binding arguments operands next)
    (identity : binding.primitive = some primitive) (scalar : primitive.IsScalar)
    (first : PrimitiveStep program before firstEvent left) (second : PrimitiveStep program before secondEvent right) :
    firstEvent = secondEvent ∧ left = right := by
  obtain ⟨firstValues,firstResult,firstWorld,firstObserved,firstCalculated,firstStored,rfl,rfl⟩ |
      ⟨firstValues,firstReason,firstObserved,firstCalculated,rfl,rfl⟩ := first.scalar_cases task identity scalar
  · obtain ⟨secondValues,secondResult,secondWorld,secondObserved,secondCalculated,secondStored,rfl,rfl⟩ |
        ⟨secondValues,secondReason,secondObserved,secondCalculated,rfl,rfl⟩ := second.scalar_cases task identity scalar
    · have valuesEqual := firstObserved.deterministic secondObserved
      subst secondValues
      have resultEqual := Except.ok.inj (firstCalculated.deterministic secondCalculated)
      subst secondResult
      have worldEqual := firstStored.deterministic secondStored
      subst secondWorld
      exact ⟨rfl,rfl⟩
    · have valuesEqual := firstObserved.deterministic secondObserved
      subst secondValues
      have impossible := firstCalculated.deterministic secondCalculated
      cases impossible
  · obtain ⟨secondValues,secondResult,secondWorld,secondObserved,secondCalculated,secondStored,rfl,rfl⟩ |
        ⟨secondValues,secondReason,secondObserved,secondCalculated,rfl,rfl⟩ := second.scalar_cases task identity scalar
    · have valuesEqual := firstObserved.deterministic secondObserved
      subst secondValues
      have impossible := firstCalculated.deterministic secondCalculated
      cases impossible
    · have valuesEqual := firstObserved.deterministic secondObserved
      subst secondValues
      have reasonEqual := Except.error.inj (firstCalculated.deterministic secondCalculated)
      subst secondReason
      exact ⟨rfl,rfl⟩

/-- Lawful scalar tasks have a unique real transition, and its resulting
world retains the complete storage invariant. -/
theorem PrimitiveStep.scalar_safe_unique_progress {program : Kernel.Program} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding}
    {arguments : List Term} {operands : List ResolvedPlace} {next : Kernel.Code}
    {primitive : Primitive} {signature : Signature}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding arguments operands next)
    (identity : binding.primitive = some primitive)
    (bound : binding.ScalarSignature program.declarations.input.target arguments signature)
    (scalar : primitive.IsScalar)
    (inputs : ListRel (fun source type => Permitted before.world source.authority .shared source.address ∧
      ∃ value, before.world.Stores source.address value ∧ value.Initialized ∧ value.type = type)
      operands signature.parameters)
    (destinationType : DestinationType before.world destination signature.result) :
    ∃ event after, PrimitiveStep program before event after ∧ Typing.WorldTyped program after.world ∧
      ∀ otherEvent other, PrimitiveStep program before otherEvent other → otherEvent = event ∧ other = after := by
  obtain ⟨event,after,step⟩ := PrimitiveStep.scalar_task_progress worldTyped task identity bound scalar inputs destinationType
  exact ⟨event,after,step,step.worldTyped valid inventory worldTyped,
    fun _ _ other => other.scalar_deterministic task identity scalar step⟩

end Glorious.Language.Execution
