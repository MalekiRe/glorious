import GloriousLanguage.ScalarDeterminism
import GloriousLanguage.ConstructionPreservation

/-! Scalar progress reaches the actual destination write. Vacant storage
supplies an existing writable path; successful calculation supplies the value
and its type. Neither a resulting world nor its typing is assumed. -/
namespace Glorious.Language

theorem Value.replace_extension_exists {before container changed : Value}
    {parent suffix : List Nat} {replacement : Option Value}
    (located : before.atPath parent = some container)
    (written : container.replace suffix replacement = some changed) :
    ∃ after, before.replace (parent ++ suffix) replacement = some after := by
  induction parent generalizing before with
  | nil =>
      have same : before = container := Option.some.inj located
      subst container
      exact ⟨changed,written⟩
  | cons index rest ih =>
      simp only [Value.atPath] at located
      cases found : before.fields[index]? with
      | none => simp [found] at located
      | some slot =>
          cases slot with
          | none => simp [found] at located
          | some child =>
              have nested : child.atPath rest = some container := by simpa [found] using located
              obtain ⟨after,replaced⟩ := ih nested
              exact ⟨_,Value.replace_cons found replaced⟩

/-- Every actual hole is writable, including a field beneath a resident
ancestor. This proves totality of the existing partial write at its contract. -/
theorem World.Vacant.write_exists {world : World} {address : Address}
    (vacant : world.Vacant address) (replacement : Option Value) :
    ∃ after, world.write address replacement = some after := by
  obtain ⟨root,selected,⟨empty,_⟩ | ⟨parent,index,value,path,contents,container,located,slot⟩⟩ := vacant
  · exact ⟨{ world with roots := world.roots.set address.root { root with value := replacement } },
      by simp [World.write,selected,empty]⟩
  · have written : container.replace [index] replacement =
        some (container.withFields (container.fields.set index replacement)) := by
      simp [Value.replace,slot]
    obtain ⟨changed,changedAt⟩ := Value.replace_extension_exists located written
    exact ⟨{ world with roots := world.roots.set address.root { root with value := some changed } },
      by simp [World.write,selected,path,contents,changedAt]⟩

theorem NewValue.empty_exists {program : Program} {before : World} {destination : Address}
    {type : Term} (head : ValueHead) (vacant : before.Vacant destination)
    (typed : AddressType program before destination type) :
    ∃ after, NewValue program before destination type head [] after := by
  obtain ⟨after,written⟩ := vacant.write_exists (some (.resident before.nextOwner type head true []))
  refine ⟨_,NewValue.construct vacant typed .nil ?_ ?_ ?_ .nil written⟩
  · simp
  · exact .nil
  · simp

theorem Typing.ValueTyped.scalar_type {program : Kernel.Program} {world : World} {value : Value}
    {scalar : Scalar} (typed : Typing.ValueTyped program world value) (type : value.type = .scalar scalar) :
    ∃ result, value.head = .scalar result ∧ result.type = scalar ∧ result.Valid program.declarations.input.target := by
  cases typed <;> simp_all [Value.head,Value.type,Execution.ConstructorHead]

theorem ScalarPrimitiveSignature.parameters_scalar {target : TargetProfile} {primitive : Primitive}
    {arguments parameters : List Term} {result : Term}
    (signature : ScalarPrimitiveSignature target primitive arguments parameters result) :
    ∀ type ∈ parameters, ∃ scalar, type = .scalar scalar := by
  cases signature <;> simp_all

end Glorious.Language

namespace Glorious.Language.Execution

theorem StoresScalar.exists {program : Kernel.Program} {before : World} {destination : Address}
    {scalar : ScalarValue} (valid : scalar.Valid program.declarations.input.target)
    (destinationType : DestinationType before destination (.scalar scalar.type)) :
    ∃ after, StoresScalar program before destination scalar after := by
  obtain ⟨after,constructed⟩ := NewValue.empty_exists (.scalar scalar)
    destinationType.vacant destinationType.addressType
  exact ⟨after,valid,destinationType,constructed⟩

theorem ScalarValues.exists {program : Kernel.Program} {world : World} {sources : List ResolvedPlace}
    {types : List Term} (worldTyped : Typing.WorldTyped program world)
    (inputs : ListRel (fun source type => Permitted world source.authority .shared source.address ∧
      ∃ value, world.Stores source.address value ∧ value.Initialized ∧ value.type = type) sources types)
    (scalarTypes : ∀ type ∈ types, ∃ scalar, type = .scalar scalar) :
    ∃ values, ScalarValues world sources values ∧ ScalarOperandsTyped program.declarations.input.target values types := by
  induction inputs with
  | nil => exact ⟨[],.nil,.nil⟩
  | @cons source type sources types input rest ih =>
      obtain ⟨permission,value,stored,initialized,typeEqual⟩ := input
      obtain ⟨scalar,scalarType⟩ := scalarTypes type (by simp)
      have residentType := worldTyped.2.1 _ _ (World.resident_iff_stores.mpr stored)
      obtain ⟨result,head,resultType,valid⟩ := residentType.scalar_type (typeEqual.trans scalarType)
      obtain ⟨values,observed,typed⟩ := ih (fun type member => scalarTypes type (by simp [member]))
      exact ⟨result :: values,.cons ⟨permission,value,stored,head,initialized⟩ observed,
        .cons ⟨valid,(congrArg Term.scalar resultType).trans scalarType.symm⟩ typed⟩

/-- An admitted scalar call either produces its correctly typed resident in
the real vacant destination, or takes the authoritative fatal transition. -/
theorem PrimitiveStep.scalar_progress {program : Kernel.Program} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding}
    {arguments : List Term} {operands : List ResolvedPlace} {next : Kernel.Code}
    {primitive : Primitive} {values : List ScalarValue} {signature : Signature}
    (task : before.task = .primitive context destination binding arguments operands next)
    (identity : binding.primitive = some primitive)
    (bound : binding.ScalarSignature program.declarations.input.target arguments signature)
    (scalar : primitive.IsScalar) (observed : ScalarValues before.world operands values)
    (inputs : ScalarOperandsTyped program.declarations.input.target values signature.parameters)
    (destinationType : DestinationType before.world destination signature.result) :
    ∃ event after, PrimitiveStep program before event after := by
  obtain ⟨outcome,calculated,typed⟩ := (bound primitive identity scalar).progress inputs
  cases outcome with
  | error reason => exact ⟨_,_,.scalarFault task identity observed calculated⟩
  | ok result =>
      obtain ⟨valid,resultType⟩ := typed result rfl
      obtain ⟨after,stored⟩ := StoresScalar.exists valid (resultType ▸ destinationType)
      exact ⟨none,_,.scalar task identity observed calculated stored⟩

/-- The input validity premise is discharged by typing the values actually
read from the shared world, not by a separate scalar-value inventory. -/
theorem PrimitiveStep.scalar_resident_progress {program : Kernel.Program} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding}
    {arguments : List Term} {operands : List ResolvedPlace} {next : Kernel.Code}
    {primitive : Primitive} {values : List ScalarValue} {signature : Signature}
    (worldTyped : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding arguments operands next)
    (identity : binding.primitive = some primitive)
    (bound : binding.ScalarSignature program.declarations.input.target arguments signature)
    (scalar : primitive.IsScalar) (observed : ScalarValues before.world operands values)
    (sourceTypes : ListRel (fun source type =>
      ∃ value, before.world.Stores source.address value ∧ value.type = type) operands signature.parameters)
    (destinationType : DestinationType before.world destination signature.result) :
    ∃ event after, PrimitiveStep program before event after :=
  PrimitiveStep.scalar_progress task identity bound scalar observed
    (observed.typed worldTyped sourceTypes) destinationType

/-- A manifest-admitted scalar task with lawful live inputs and a vacant
result slot takes a machine step. All scalar observations and the written
post-state are constructed from those input contracts. -/
theorem PrimitiveStep.scalar_task_progress {program : Kernel.Program} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding}
    {arguments : List Term} {operands : List ResolvedPlace} {next : Kernel.Code}
    {primitive : Primitive} {signature : Signature}
    (worldTyped : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding arguments operands next)
    (identity : binding.primitive = some primitive)
    (bound : binding.ScalarSignature program.declarations.input.target arguments signature)
    (scalar : primitive.IsScalar)
    (inputs : ListRel (fun source type => Permitted before.world source.authority .shared source.address ∧
      ∃ value, before.world.Stores source.address value ∧ value.Initialized ∧ value.type = type)
      operands signature.parameters)
    (destinationType : DestinationType before.world destination signature.result) :
    ∃ event after, PrimitiveStep program before event after := by
  obtain ⟨values,observed,typed⟩ := ScalarValues.exists worldTyped inputs
    (bound primitive identity scalar).parameters_scalar
  exact PrimitiveStep.scalar_progress task identity bound scalar observed typed destinationType

end Glorious.Language.Execution
