import GloriousLanguage.LayoutExecution

/-! Executable literal views. `Elaboration.literalView` admits `literalText`
and `literalBytes` bindings and emits the octet tuple as the primitive's
argument; this module supplies the machine side of that rule.

Static data is materialized in the existing value vocabulary: the ordinary
constant-value construction of one u8 scalar leaf per octet, in exactly the
`(.constantTuple bytes)` term the elaborator emits. No static-segment
descriptor, second value form or parallel reader is introduced, and the
manifest binding stays authoritative: `AtomStep.primitive` reaches a literal
task only through an admitted binding, and the literal step below requires
that binding's identity and its declared result type.

Scope limit (honest). The constant-value vocabulary materializes static octets
only as that scalar tuple, and the elaborated destination slot is typed at
`binding.signature.result`, so the step applies exactly when the manifest
binds the literal view's result type to the materialized type — the octet
tuple, or `unit` for the empty octet string (the existing empty-constant-tuple
case). A manifest that binds a literal view to a nominal text type has no
transition in this model: no rule installs a `Home.staticData` root and no
relation ties a root's byte image to the contents of a nominal value. That
gap is a property of the current model, reported here rather than papered over
with a second representation. -/
namespace Glorious.Language.Execution

/-- The ordinary machine leaves of an octet string: one u8 constant per octet,
the scalar family `Elaboration.literalView` emits. -/
def OctetScalars (bytes : List Nat) : List ScalarValue :=
  bytes.map (fun byte => .integer false (.fixed 8) (Int.ofNat byte))

/-- The type the constant-value vocabulary assigns to that data: the tuple of
u8 scalar leaves, or `unit` for the empty octet string. -/
def OctetType : List Nat → Term
  | [] => .unit
  | byte :: rest => .tuple ((byte :: rest).map (fun _ => .scalar (.integer false (.fixed 8))))

/-- The immediate machine leaves of that data, octet values included: one u8
constant resident per octet, in order. -/
def OctetLeaves : List Nat → List (Option ValueHead)
  | [] => []
  | byte :: rest => some (.scalar (.integer false (.fixed 8) (Int.ofNat byte))) :: OctetLeaves rest

/-- One octet is a valid u8 machine leaf whenever it fits the width. Signedness
and width are static, so only the value bound is a premise. -/
theorem octet_valid {target : TargetProfile} {byte : Nat} (bound : byte < 256) :
    (ScalarValue.integer false (.fixed 8) (Int.ofNat byte)).Valid target := by
  refine ⟨?_,?_⟩
  · show (8 : Nat) ∈ [8,16,32,64,128]
    decide
  refine ⟨Int.natCast_nonneg byte,?_⟩
  have cast : (byte : Int) < ((2^8 : Nat) : Int) := Int.ofNat_lt.mpr bound
  simpa [integerLimit,Width.bits,Int.natCast_pow] using cast

theorem OctetScalars.terms (bytes : List Nat) :
    (OctetScalars bytes).map Term.constant =
      bytes.map (fun byte => Term.constant (.integer false (.fixed 8) (Int.ofNat byte))) := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
      show Term.constant (.integer false (.fixed 8) (Int.ofNat byte)) :: (OctetScalars rest).map Term.constant =
        Term.constant (.integer false (.fixed 8) (Int.ofNat byte)) ::
          rest.map (fun byte => Term.constant (.integer false (.fixed 8) (Int.ofNat byte)))
      rw [ih]

/-- The resident octet leaves the emitted term constructs: one constant value
per octet with the octet's own scalar type and value, and the same order. -/
theorem OctetScalars.exists {program : Kernel.Program} {context : Language.Context} {bytes : List Nat}
    (octets : ∀ byte ∈ bytes, byte < 256) (next : Nat) :
    ∃ finish residents, ConstantValues program.declarations context next
        ((OctetScalars bytes).map Term.constant) finish residents ∧
      residents.map Value.type = bytes.map (fun _ => Term.scalar (.integer false (.fixed 8))) ∧
      residents.map (fun value => some value.head) = OctetLeaves bytes := by
  induction bytes generalizing next with
  | nil => exact ⟨next,[],.nil,rfl,rfl⟩
  | cons byte rest ih =>
      obtain ⟨finish,residents,constructed,types,heads⟩ := ih
        (fun current member => octets current (List.mem_cons_of_mem _ member)) (next+1)
      exact ⟨finish,_ :: residents,.cons (ConstantValue.scalar (octet_valid (octets byte (by simp)))) constructed,
        by simp only [List.map_cons,Value.type,ScalarValue.type,types],
        by
          simp only [List.map_cons,heads]
          simp only [Value.head,OctetLeaves]⟩

/-- The machine materialization of an octet string: the constant value the
emitted `.constantTuple` argument actually constructs, its deterministic type,
and its actual octet leaves. -/
theorem octet_materialization {program : Kernel.Program} {context : Language.Context} {bytes : List Nat}
    (octets : ∀ byte ∈ bytes, byte < 256) (next : Nat) :
    ∃ finish value, ConstantValue program.declarations context next
        (.constantTuple (bytes.map (fun byte => .constant (.integer false (.fixed 8) (Int.ofNat byte)))))
        finish value ∧ value.type = OctetType bytes ∧
      value.fields.map (Option.map Value.head) = OctetLeaves bytes := by
  cases bytes with
  | nil => exact ⟨next+1,.resident next .unit .unit true [],.unit,rfl,rfl⟩
  | cons byte rest =>
    obtain ⟨finish,residents,constructed,types,heads⟩ :=
      OctetScalars.exists (bytes := byte :: rest) octets (next+1)
    have fields := OctetScalars.terms (byte :: rest) ▸ constructed
    refine ⟨finish,.resident next (.tuple (residents.map Value.type)) .tuple true (residents.map some),
      .tuple (by simp) fields,?_,?_⟩
    · show Term.tuple (residents.map Value.type) = OctetType (byte :: rest)
      rw [types]
      rfl
    · show (residents.map some).map (Option.map Value.head) = OctetLeaves (byte :: rest)
      rw [List.map_map]
      simp only [Function.comp_def,Option.map_some,heads]

/-- The materialization is determined by the emitted argument: an octet tuple
has exactly one constant value and one consumed owner counter, so the machine
leaves of a literal view are deterministic data. -/
theorem octet_materialization_unique {program : Kernel.Program} {context : Language.Context}
    {bytes : List Nat} {next leftFinish rightFinish : Nat} {left right : Value}
    (first : ConstantValue program.declarations context next
      (.constantTuple (bytes.map (fun byte => .constant (.integer false (.fixed 8) (Int.ofNat byte))))) leftFinish left)
    (second : ConstantValue program.declarations context next
      (.constantTuple (bytes.map (fun byte => .constant (.integer false (.fixed 8) (Int.ofNat byte))))) rightFinish right) :
    leftFinish = rightFinish ∧ left = right := by
  rw [← OctetScalars.terms bytes] at first second
  exact ConstantValue.scalar_tuple_unique first second

/-- A write of an initialized resident into a vacant root address is observable
as that resident: the root is not a hole and has no field path. -/
theorem World.Stores.write_root {before after : World} {address : Address} {value : Value}
    (empty : address.fields = []) (written : before.write address (some value) = some after) :
    after.Stores address value := by
  cases address with
  | mk root generation fields =>
      simp only at empty
      subst empty
      have inside := World.write_read_inside written ([] : List Nat)
      rw [World.Stores]
      exact inside

/-- Progress for a manifest-admitted literal view. The task is exactly the atom
`Elaboration.literalView` emits; the binding's identity and result type are the
manifest's authority; the octets are the source literal's static data. The step
installs the octet tuple in the vacant typed destination, preserves world
typing, and allocates nothing: the write changes only the destination root's
value, so no root, region or loan is created.

`_admitted` records the manifest evidence by which `AtomStep.primitive` reaches
this task, so the theorem is about manifest-admitted views; the transition
itself is determined by the binding's identity, its declared result type, the
octets and the destination contract. -/
theorem PrimitiveStep.literal_typed_progress {program : Kernel.Program} {before : State}
    {context : Context} {destination : Address} {binding : RuntimeBinding}
    {bytes : List Nat} {next : Kernel.Code} {primitive : Primitive}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (task : before.task = .primitive context destination binding
      [.constantTuple (bytes.map (fun byte => .constant (.integer false (.fixed 8) (Int.ofNat byte))))] [] next)
    (_admitted : binding ∈ program.declarations.input.manifest.bindings)
    (identity : binding.primitive = some primitive)
    (view : primitive = .literalText ∨ primitive = .literalBytes)
    (octets : ∀ byte ∈ bytes, byte < 256)
    (resultType : binding.signature.result = OctetType bytes)
    (destinationType : DestinationType before.world destination binding.signature.result) :
    ∃ after value, PrimitiveStep program before none after ∧ after.task = .run context next ∧
      Typing.WorldTyped program after.world ∧ after.world.Stores destination value ∧
      Typing.ValueTyped program after.world value ∧ value.type = OctetType bytes ∧
      value.fields.map (Option.map Value.head) = OctetLeaves bytes ∧
      after.world.nextRoot = before.world.nextRoot ∧
      (∀ id, (after.world.roots.get id).isSome = (before.world.roots.get id).isSome) ∧
      after.world.nextRegion = before.world.nextRegion ∧
      after.world.liveRegions = before.world.liveRegions ∧ after.world.loans = before.world.loans := by
  obtain ⟨finish,value,constructed,valueType,valueLeaves⟩ :=
    octet_materialization (program := program) (context := context.static) octets before.world.nextOwner
  have materialized : DestinationType before.world destination value.type := by
    rw [valueType]
    exact resultType ▸ destinationType
  obtain ⟨written,write⟩ := materialized.vacant.write_exists (some value)
  have typedAfter : Typing.WorldTyped program {written with nextOwner := finish} :=
    ConstantValue.install_worldTyped valid inventory typed constructed materialized.vacant
      materialized.addressType write
  have storedWritten : written.Stores destination value :=
    World.Stores.write_root materialized.1 write
  have storedAfter : ({written with nextOwner := finish} : World).Stores destination value :=
    storedWritten
  have valueTyped : Typing.ValueTyped program ({written with nextOwner := finish} : World) value :=
    ConstantValue.typed constructed _
  have rest : written = {before.world with roots := written.roots} := World.write_rest write
  have frontiers : written.liveRegions = before.world.liveRegions ∧
      written.nextRegion = before.world.nextRegion := by
    constructor <;> rw [rest]
  have nextRoot : written.nextRoot = before.world.nextRoot := by rw [rest]
  have loans : written.loans = before.world.loans := by rw [rest]
  have presence : ∀ id, (({written with nextOwner := finish} : World).roots.get id).isSome =
      (before.world.roots.get id).isSome := by
    obtain ⟨root,replacement,found,shape⟩ := World.write_value_update write
    intro id
    by_cases same : id = destination.root
    · subst same
      rw [show (({written with nextOwner := finish} : World).roots.get destination.root) =
        written.roots.get destination.root from rfl, shape]
      simp only [Table.get_set,found,Option.isSome_some]
    · have retained : written.roots.get id = before.world.roots.get id := by
        rw [shape]
        exact Table.get_set_other _ _ _ _ same
      rw [show (({written with nextOwner := finish} : World).roots.get id) = written.roots.get id from rfl,
        retained]
  rcases view with rfl | rfl
  · exact ⟨_,value,.literalText task identity constructed (resultType.trans valueType.symm) materialized write,
      rfl,typedAfter,storedAfter,valueTyped,valueType,valueLeaves,nextRoot,presence,frontiers.2,frontiers.1,loans⟩
  · exact ⟨_,value,.literalBytes task identity constructed (resultType.trans valueType.symm) materialized write,
      rfl,typedAfter,storedAfter,valueTyped,valueType,valueLeaves,nextRoot,presence,frontiers.2,frontiers.1,loans⟩

/-- Octet constants cannot produce a nominal library value. This is a
representation obstruction, independent of octet bounds or allocation. -/
theorem ConstantValue.tuple_not_nominal {program : Language.Program} {context : Language.Context}
    {start finish : Nat} {fields : List Term} {value : Value} {id : DeclId} {arguments : List Term}
    (constructed : ConstantValue program context start (.constantTuple fields) finish value) :
    value.type ≠ .nominal id arguments := by
  cases constructed <;> simp [Value.type]

private theorem calculation_not_literal {target : TargetProfile} {primitive : Primitive}
    {arguments : List Term} {values : List ScalarValue} {outcome : Except Fatal ScalarValue}
    (calculated : PrimitiveCalculation target primitive arguments values outcome)
    (literal : Primitive.literalText = primitive ∨ Primitive.literalBytes = primitive) : False := by
  cases calculated <;> rcases literal with literal | literal <;> cases literal

/-- The current literal rules have no step at a nominal manifest result,
including the ordinary Str and Slice representations required by §3.3.
Storage typing alone cannot close source-literal progress. -/
theorem PrimitiveStep.literal_nominal_impossible {program : Kernel.Program} {before after : State}
    {event : Option Event} {context : Context} {destination : Address} {binding : RuntimeBinding}
    {bytes : List Nat} {next : Kernel.Code} {id : DeclId} {arguments : List Term}
    (task : before.task = .primitive context destination binding
      [.constantTuple (bytes.map (fun byte => .constant (.integer false (.fixed 8) (Int.ofNat byte))))] [] next)
    (literal : binding.primitive = some .literalText ∨ binding.primitive = some .literalBytes)
    (result : binding.signature.result = .nominal id arguments)
    (step : PrimitiveStep program before event after) : False := by
  have selected : ∀ c d b a o n, before.task = .primitive c d b a o n → b = binding := by
    intro c d b a o n running
    exact (Task.primitive.inj (running.symm.trans task)).2.2.1
  clear task
  cases step
  all_goals
    have same := selected _ _ _ _ _ _ (by assumption)
    cases same
  all_goals clear selected
  all_goals rcases literal with text | bytes
  all_goals simp_all only [Option.some.injEq,reduceCtorEq]
  all_goals
    first
      | (apply calculation_not_literal
         · assumption
         · first | exact Or.inl (by assumption) | exact Or.inr (by assumption))
      | exact ConstantValue.tuple_not_nominal (by assumption) (by simpa using result)

end Glorious.Language.Execution
