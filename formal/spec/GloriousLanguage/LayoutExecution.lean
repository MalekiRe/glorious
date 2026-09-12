import GloriousLanguage.RepresentationCoherence
import GloriousLanguage.MemoryPreservation
import GloriousLanguage.StorageConstruction

/-! The executable layout query uses the same conversion-coherent LayoutOf
producer as memory representation. Its scalar-tuple result has deterministic
resident identities; no normalization or layout-existence oracle is
part of this result. -/
namespace Glorious.Language.Execution

theorem ConstantValues.scalar_exists {program : Language.Program} {context : Language.Context}
    {scalars : List ScalarValue} (valid : ∀ scalar ∈ scalars, scalar.Valid program.input.target)
    (next : Nat) : ∃ finish residents,
      ConstantValues program context next (scalars.map Term.constant) finish residents ∧
      residents.map Value.type = scalars.map (fun scalar => Term.scalar scalar.type) := by
  induction scalars generalizing next with
  | nil => exact ⟨next,[],.nil,rfl⟩
  | cons scalar rest ih =>
    obtain ⟨finish,residents,constructed,types⟩ := ih
      (fun scalar member => valid scalar (List.mem_cons_of_mem _ member)) (next+1)
    exact ⟨finish,_,.cons (.scalar (valid scalar (by simp))) constructed,
      by simp [Value.type,types]⟩

theorem ConstantValue.scalar_tuple_exists {program : Language.Program} {context : Language.Context}
    {scalars : List ScalarValue} (nonempty : scalars ≠ [])
    (valid : ∀ scalar ∈ scalars, scalar.Valid program.input.target) (next : Nat) :
    ∃ finish value,
      ConstantValue program context next (.constantTuple (scalars.map Term.constant)) finish value ∧
      value.type = .tuple (scalars.map (fun scalar => Term.scalar scalar.type)) := by
  obtain ⟨finish,residents,constructed,types⟩ := ConstantValues.scalar_exists (context := context) valid (next+1)
  exact ⟨finish,_,.tuple (by simpa using nonempty) constructed,by simp [Value.type,types]⟩

theorem ConstantValues.scalar_unique {program : Language.Program} {context : Language.Context}
    {next leftFinish rightFinish : Nat} {scalars : List ScalarValue} {left right : List Value}
    (first : ConstantValues program context next (scalars.map Term.constant) leftFinish left)
    (second : ConstantValues program context next (scalars.map Term.constant) rightFinish right) :
    leftFinish = rightFinish ∧ left = right := by
  induction scalars generalizing next leftFinish rightFinish left right with
  | nil => cases first; cases second; exact ⟨rfl,rfl⟩
  | cons scalar rest ih =>
    cases first with
    | cons value values =>
      cases second with
      | cons other others =>
        cases value
        cases other
        obtain ⟨rfl,rfl⟩ := ih values others
        exact ⟨rfl,rfl⟩

theorem ConstantValue.scalar_tuple_unique {program : Language.Program} {context : Language.Context}
    {next leftFinish rightFinish : Nat} {scalars : List ScalarValue} {left right : Value}
    (first : ConstantValue program context next (.constantTuple (scalars.map Term.constant)) leftFinish left)
    (second : ConstantValue program context next (.constantTuple (scalars.map Term.constant)) rightFinish right) :
    leftFinish = rightFinish ∧ left = right := by
  cases scalars with
  | nil =>
    cases first with
    | unit =>
      cases second with
      | unit => exact ⟨rfl,rfl⟩
      | tuple nonempty _ => exact False.elim (nonempty rfl)
    | tuple nonempty _ => exact False.elim (nonempty rfl)
  | cons scalar rest =>
    cases first with
    | tuple _ values =>
      cases second with
      | tuple _ others =>
        obtain ⟨rfl,rfl⟩ := ConstantValues.scalar_unique values others
        exact ⟨rfl,rfl⟩

theorem PrimitiveStep.layout_deterministic {program : Kernel.Program}
    (valid : ProgramWellFormed program.declarations) {before left right : State}
    {leftEvent rightEvent : Option Event} {context : Context} {destination : Address}
    {binding : RuntimeBinding} {type : Term} {next : Kernel.Code}
    (task : before.task = .primitive context destination binding [type] [] next)
    (identity : binding.primitive = some .layout)
    (first : PrimitiveStep program before leftEvent left)
    (second : PrimitiveStep program before rightEvent right) : leftEvent = rightEvent ∧ left = right := by
  cases first <;> simp_all
  case scalar => rename_i _ calculation _; cases calculation <;> simp_all
  case scalarFault => rename_i calculation; cases calculation <;> simp_all
  case layout =>
    rename_i derived constructed _ written aligned
    cases second <;> simp_all
    case scalar => rename_i _ calculation _; cases calculation <;> simp_all
    case scalarFault => rename_i calculation; cases calculation <;> simp_all
    case layout =>
      rename_i otherDerived otherConstructed _ otherWritten _
      have layouts := derived.unique valid rfl otherDerived
      subst layouts
      obtain ⟨finish,values⟩ := ConstantValue.scalar_tuple_unique
        (scalars := [.integer false .pointer _,.integer false .pointer _]) constructed otherConstructed
      subst values
      have worlds := Option.some.inj (written.symm.trans otherWritten)
      simp_all

/-- Layout production, pointer-integer representability and a real vacant
result destination suffice for the existing primitive rule. Size/alignment
bounds are explicit: layout uniqueness alone does not imply representability. -/
theorem PrimitiveStep.layout_safe_unique_progress {program : Kernel.Program}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    {before : State} (typed : Typing.WorldTyped program before.world)
    {context : Context} {destination : Address} {binding : RuntimeBinding}
    {type : Term} {next : Kernel.Code} {layout : Layout}
    (task : before.task = .primitive context destination binding [type] [] next)
    (identity : binding.primitive = some .layout)
    (derived : LayoutOf program.declarations context.static type layout)
    (representable : IntegerRange program.declarations.input.target false .pointer layout.size ∧
      IntegerRange program.declarations.input.target false .pointer layout.alignment)
    (destinationType : DestinationType before.world destination
      (.tuple [.scalar (.integer false .pointer),.scalar (.integer false .pointer)])) :
    ∃ after, PrimitiveStep program before none after ∧ Typing.WorldTyped program after.world ∧
      ∀ event other, PrimitiveStep program before event other → event = none ∧ other = after := by
  have pointerValid : (Scalar.integer false .pointer).Valid program.declarations.input.target :=
    valid.1.1.2.2.2.2.1.1
  have literalsValid : ∀ scalar ∈ [ScalarValue.integer false .pointer layout.size,
      .integer false .pointer layout.alignment], scalar.Valid program.declarations.input.target := by
    intro scalar member
    simp at member
    rcases member with rfl | rfl
    · exact ⟨pointerValid,representable.1⟩
    · exact ⟨pointerValid,representable.2⟩
  obtain ⟨finish,value,constructed,resultType⟩ := ConstantValue.scalar_tuple_exists
    (context := context.static) (by simp) literalsValid before.world.nextOwner
  have actualDestination : DestinationType before.world destination value.type := by
    simpa only [resultType,List.map_cons,List.map_nil,ScalarValue.type] using destinationType
  obtain ⟨written,write⟩ := actualDestination.vacant.write_exists (some value)
  have step : PrimitiveStep program before none
      { before with world := { written with nextOwner := finish }, task := .run context next } :=
    .layout task identity derived constructed actualDestination write rfl
  exact ⟨_,step,step.worldTyped valid inventory typed,
    fun _ _ other => other.layout_deterministic valid task identity step⟩

theorem Step.layout_iff_primitive {program : Kernel.Program} {host : Foreign.Model}
    {before after : State} {event : Option Event} {context : Context} {destination : Address}
    {binding : RuntimeBinding} {type : Term} {next : Kernel.Code}
    (task : before.task = .primitive context destination binding [type] [] next)
    (identity : binding.primitive = some .layout) :
    Step program host before event after ↔ PrimitiveStep program before event after := by
  constructor
  · intro step
    rcases step with localStep | atom | effect | control | primitiveStep | foreign
    · cases localStep <;> simp_all
    · cases atom <;> simp_all
    · cases effect <;> simp_all
    · cases control <;> simp_all
    · exact primitiveStep
    · cases foreign <;> simp_all [Foreign.Selected]
  · exact fun step => .inr (.inr (.inr (.inr (.inl step))))

theorem Step.layout_deterministic {program : Kernel.Program} {host : Foreign.Model}
    (valid : ProgramWellFormed program.declarations) {before left right : State}
    {leftEvent rightEvent : Option Event} {context : Context} {destination : Address}
    {binding : RuntimeBinding} {type : Term} {next : Kernel.Code}
    (task : before.task = .primitive context destination binding [type] [] next)
    (identity : binding.primitive = some .layout)
    (first : Step program host before leftEvent left) (second : Step program host before rightEvent right) :
    leftEvent = rightEvent ∧ left = right :=
  PrimitiveStep.layout_deterministic valid task identity
    ((Step.layout_iff_primitive task identity).mp first) ((Step.layout_iff_primitive task identity).mp second)

theorem Step.layout_safe_unique_progress {program : Kernel.Program} {host : Foreign.Model}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    {before : State} (typed : Typing.WorldTyped program before.world)
    {context : Context} {destination : Address} {binding : RuntimeBinding}
    {type : Term} {next : Kernel.Code} {layout : Layout}
    (task : before.task = .primitive context destination binding [type] [] next)
    (identity : binding.primitive = some .layout)
    (derived : LayoutOf program.declarations context.static type layout)
    (representable : IntegerRange program.declarations.input.target false .pointer layout.size ∧
      IntegerRange program.declarations.input.target false .pointer layout.alignment)
    (destinationType : DestinationType before.world destination
      (.tuple [.scalar (.integer false .pointer),.scalar (.integer false .pointer)])) :
    ∃ after, Step program host before none after ∧ Typing.WorldTyped program after.world ∧
      ∀ event other, Step program host before event other → event = none ∧ other = after := by
  obtain ⟨after,step,afterTyped,unique⟩ := PrimitiveStep.layout_safe_unique_progress valid inventory typed
    task identity derived representable destinationType
  exact ⟨after,(Step.layout_iff_primitive task identity).mpr step,afterTyped,
    fun _ _ other => unique _ _ ((Step.layout_iff_primitive task identity).mp other)⟩

end Glorious.Language.Execution
