import GloriousLanguage.ScalarMachine

/-! Scalar soundness at the sole executable transition relation. Other
dispatch families cannot compete with an admitted scalar primitive identity. -/
namespace Glorious.Language.Execution

theorem Step.scalar_iff_primitive {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event} {context : Context} {destination : Address}
    {binding : RuntimeBinding} {arguments : List Term} {operands : List ResolvedPlace}
    {next : Kernel.Code} {primitive : Primitive}
    (task : before.task = .primitive context destination binding arguments operands next)
    (identity : binding.primitive = some primitive) (scalar : primitive.IsScalar) :
    Step program host before event after ↔ PrimitiveStep program before event after := by
  constructor
  · intro step
    rcases step with localStep | atom | effect | control | primitiveStep | foreign
    · cases localStep <;> simp_all
    · cases atom <;> simp_all
    · cases effect <;> simp_all
    · cases control <;> simp_all [Primitive.IsScalar]
    · exact primitiveStep
    · cases foreign <;> simp_all [Foreign.Selected]
  · exact fun step => .inr (.inr (.inr (.inr (.inl step))))

/-- Every lawful scalar task has exactly one executable normal/fatal
transition, and its actual post-world preserves storage typing. No law about
the foreign host is needed because scalar identity excludes host dispatch. -/
theorem Step.scalar_safe_unique_progress {program : Kernel.Program} {host : Foreign.Model} {before : State}
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
    ∃ event after, Step program host before event after ∧ Typing.WorldTyped program after.world ∧
      ∀ otherEvent other, Step program host before otherEvent other → otherEvent = event ∧ other = after := by
  obtain ⟨event,after,step,typed,unique⟩ := PrimitiveStep.scalar_safe_unique_progress
    valid inventory worldTyped task identity bound scalar inputs destinationType
  exact ⟨event,after,(Step.scalar_iff_primitive task identity scalar).mpr step,typed,
    fun _ _ other => unique _ _ ((Step.scalar_iff_primitive task identity scalar).mp other)⟩

end Glorious.Language.Execution
