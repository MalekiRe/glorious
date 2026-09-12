import GloriousLanguage.SnapshotTyping
import GloriousLanguage.RuntimeEquivariance

/-! The copied world's typing follows from the actual finite copy, lexical
declarations, and the input scope closure of retained external referents. -/
namespace Glorious.Language.Execution

def SnapshotMap.permutation {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    (selected : SnapshotMap program before suspension map) (valid : before.world.WellFormed) : RegionPermutation where
  rename := freshSwap map.regions map.regionBase
  involutive := freshSwap_involutive (fun id member => by
    rw [selected.regionBase]
    exact World.region_bound valid (selected.liveRegions id member))

theorem SnapshotMap.term_permutation {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    (selected : SnapshotMap program before suspension map) (valid : before.world.WellFormed) {term : Term}
    (supported : term.RuntimeRegionsBelow before.world.nextRegion) :
    map.term term = (selected.permutation valid).term term := by
  apply map.term_eq_permutation
  rwa [selected.regionBase]

theorem SnapshotMap.layoutOf {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    (valid : ProgramWellFormed program.declarations) (world : before.world.WellFormed)
    (selected : SnapshotMap program before suspension map) {term : Term} {layout : Layout} {module : ModuleId} {unsafeAllowed : Bool}
    (supported : term.RuntimeRegionsBelow before.world.nextRegion)
    (located : LayoutOf program.declarations ⟨[],[],0,module,unsafeAllowed⟩ term layout) :
    LayoutOf program.declarations ⟨[],[],0,module,unsafeAllowed⟩ (map.term term) layout := by
  rw [selected.term_permutation world supported]
  exact located.permute valid (selected.permutation world)

theorem SnapshotMap.fieldLayouts {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    (valid : ProgramWellFormed program.declarations) (world : before.world.WellFormed)
    (selected : SnapshotMap program before suspension map) {fields : List Term} {layouts : List Layout}
    {module : ModuleId} {unsafeAllowed : Bool}
    (supported : ∀ term ∈ fields, term.RuntimeRegionsBelow before.world.nextRegion)
    (located : ListRel (LayoutOf program.declarations ⟨[],[],0,module,unsafeAllowed⟩) fields layouts) :
    ListRel (LayoutOf program.declarations ⟨[],[],0,module,unsafeAllowed⟩) (fields.map map.term) layouts := by
  induction located with
  | nil => exact .nil
  | cons first _ ih =>
      exact .cons (selected.layoutOf valid world (supported _ List.mem_cons_self) first)
        (ih (fun term member => supported term (List.mem_cons_of_mem _ member)))

theorem Relocation.value_constructor_head (map : Relocation) {value : Value} {id : DeclId}
    (head : value.head = .constructor id) : (map.value value).head = .constructor id := by
  cases value
  simp only [Value.head] at head
  simp only [Relocation.value,Value.head,head]

theorem SnapshotMap.copied_fieldOffset {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    (valid : ProgramWellFormed program.declarations) (world : before.world.WellFormed)
    (selected : SnapshotMap program before suspension map) {homes : Table Home}
    {address : Address} {container type : Term} {index offset : Nat}
    (included : address.root ∈ map.roots) (supported : container.RuntimeRegionsBelow before.world.nextRegion)
    (located : FieldOffset program.declarations before.world address container index type offset) :
    FieldOffset program.declarations (map.copyWorld before.world homes) (map.address address)
      (map.term container) index (map.term type) offset := by
  revert supported
  cases located <;> intro supported <;> simp only [Relocation.term,Term.renameRuntimeRegions]
  case tuple layouts aggregate atType atOffset =>
    exact .tuple (by simp only [List.getElem?_map,atType,Option.map])
      (selected.fieldLayouts valid world (fun _ member => supported.child member) layouts) aggregate atOffset
  case bindings layouts aggregate atType atOffset =>
    exact .bindings (by simp only [List.getElem?_map,atType,Option.map])
      (selected.fieldLayouts valid world (fun _ member => supported.child (by simp [Term.children,member])) layouts) aggregate atOffset
  case callable declared layouts aggregate atType atOffset =>
    exact .callable (CallableFields.relocate valid declared map) (by simp only [List.getElem?_map,atType,Option.map,Relocation.term])
      (selected.fieldLayouts valid world
        (declared.runtimeRegionsBelow valid (fun _ member => supported.child member)) layouts) aggregate atOffset
  case array nonnegative bound layout =>
    exact .array nonnegative bound (selected.layoutOf valid world (supported.child (by simp [Term.children])) layout)
  case nominal constructor identity instantiated substituted layout stored head atType atOffset =>
    refine .nominal constructor identity (Instantiates.relocate instantiated map)
      (map.substitutes_list ?_ substituted) (by simp only [List.getElem?_map,atType,Option.map,Relocation.term])
      (by simpa only [Relocation.term,Term.renameRuntimeRegions] using selected.layoutOf valid world supported layout)
      (World.resident_iff_stores.mp (selected.copied_resident world (World.resident_iff_stores.mpr stored) included))
      (map.value_constructor_head head) atOffset
    · intro term member
      obtain ⟨field,present,rfl⟩ := List.mem_map.mp member
      exact valid.field_lexical constructor.1 constructor.2.1 present

theorem SnapshotMap.copied_addressOffset {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    (valid : ProgramWellFormed program.declarations) (typed : Typing.WorldTyped program before.world)
    (selected : SnapshotMap program before suspension map) {homes : Table Home}
    {address : Address} {type : Term} {offset : Nat}
    (included : address.root ∈ map.roots) (located : AddressOffset program.declarations before.world address type offset) :
    AddressOffset program.declarations (map.copyWorld before.world homes) (map.address address) (map.term type) offset := by
  induction located with
  | root found live => exact .root (selected.copied_root typed.1 found included) live
  | child parent field ih =>
      exact .child (ih included) (selected.copied_fieldOffset valid typed.1 included
        (parent.runtimeRegionsBelow valid typed.2.2.2) field)

theorem SnapshotMap.copied_addressType {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    (valid : ProgramWellFormed program.declarations) (typed : Typing.WorldTyped program before.world)
    (selected : SnapshotMap program before suspension map) {homes : Table Home} {address : Address} {type : Term}
    (included : address.root ∈ map.roots) (located : AddressType program.declarations before.world address type) :
    AddressType program.declarations (map.copyWorld before.world homes) (map.address address) (map.term type) := by
  obtain ⟨offset,located⟩ := located
  exact ⟨offset,selected.copied_addressOffset valid typed included located⟩

theorem Relocation.term_fixed (map : Relocation) {term : Term}
    (closed : ∀ region ∈ map.regions, ¬ Occurs (.runtimeRegion region) term) : map.term term = term := by
  have same : map.term term = term.renameRuntimeRegions id := term.renameRuntimeRegions_congr map.region id (by
    intro region occurs
    have outside : region ∉ map.regions := fun member => closed region member occurs
    simp only [Relocation.region,relocateId,if_neg outside,id_eq])
  exact same.trans term.renameRuntimeRegions_id

theorem SnapshotMap.external_referent_type {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    (selected : SnapshotMap program before suspension map) {address : Address} {value : Value} {id : Identity} {loan : Loan} {type : Term}
    (included : address.root ∈ map.roots) (resident : before.world.Resident address value) (head : value.head = .reference id)
    (found : before.world.loans.get id = some loan) (outside : loan.referent.root ∉ map.roots)
    (located : AddressType program.declarations before.world loan.referent type) : map.term type = type :=
  map.term_fixed (selected.externalReferentsScoped address value id loan included resident head found outside type located)

theorem SnapshotMap.terms_permutation {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    (selected : SnapshotMap program before suspension map) (valid : before.world.WellFormed) {terms : List Term}
    (supported : ∀ term ∈ terms, term.RuntimeRegionsBelow before.world.nextRegion) :
    terms.map map.term = terms.map (selected.permutation valid).term :=
  List.map_congr_left (fun term member => selected.term_permutation valid (supported term member))

theorem SnapshotMap.instance_captures {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program) (world : before.world.WellFormed)
    (selected : SnapshotMap program before suspension map) {id : DeclId} {arguments : List Term} {function : Kernel.Function}
    (instantiated : Kernel.Instance program id arguments function)
    (supported : ∀ term ∈ arguments, term.RuntimeRegionsBelow before.world.nextRegion) :
    ∃ copied, Kernel.Instance program id (arguments.map map.term) copied ∧
      copied.captures.map (·.type) = (function.captures.map (·.type)).map map.term := by
  obtain ⟨copied,instanced,captures⟩ := instantiated.permute_captures valid inventory (selected.permutation world)
  rw [← selected.terms_permutation world supported] at instanced
  rw [← selected.terms_permutation world (instantiated.capture_runtimeRegionsBelow valid inventory supported)] at captures
  exact ⟨copied,instanced,captures⟩

theorem SnapshotMap.operation_instance {program : Kernel.Program} {before : State} {suspension : Suspension} {map : Relocation}
    (valid : ProgramWellFormed program.declarations) (world : before.world.WellFormed)
    (selected : SnapshotMap program before suspension map) {id : DeclId} {arguments : List Term}
    {operation : OperationDefinition} {signature : Signature}
    (instantiated : OperationInstance program id arguments operation signature)
    (supported : ∀ term ∈ arguments, term.RuntimeRegionsBelow before.world.nextRegion) :
    ∃ copiedSignature, OperationInstance program id (arguments.map map.term) operation copiedSignature := by
  obtain ⟨signature,instanced⟩ := instantiated.permute valid (selected.permutation world)
  rw [← selected.terms_permutation world supported] at instanced
  exact ⟨signature,instanced⟩

theorem Relocation.value_type (map : Relocation) (value : Value) : (map.value value).type = map.term value.type := by
  cases value
  simp only [Relocation.value,Value.type]

theorem Relocation.constructor_value (map : Relocation) {program : Program} {owner : Identity} {type : Term}
    {head : ValueHead} {live : Bool} {fields : List (Option Value)} {variant : Option DeclId} {types : List Term}
    (shape : ConstructorHead program type variant types head) :
    map.value (.resident owner type head live fields) =
      .resident (map.ownerBase+owner) (map.term type) head live (map.values fields) := by
  rcases shape with ⟨_,_,rfl⟩ | ⟨_,_,_,_,_,_,rfl,_⟩ | ⟨_,_,_,_,_,_,_,rfl,_⟩ <;>
    simp only [Relocation.value]

theorem Relocation.fieldsTyped {program : Kernel.Program} {before after : World} (map : Relocation)
    {fields : List (Option Value)} {types : List Term} (typed : Typing.FieldsTyped program before fields types)
    (mapped : ∀ value, some value ∈ fields → Typing.ValueTyped program after (map.value value)) :
    Typing.FieldsTyped program after (map.values fields) (types.map map.term) := by
  induction fields generalizing types with
  | nil => cases typed; exact .nil
  | cons first rest ih =>
      cases typed with
      | hole tail => exact .hole (ih tail (fun value member => mapped value (List.mem_cons_of_mem _ member)))
      | resident value same tail =>
          exact .resident (mapped _ List.mem_cons_self) (by rw [map.value_type,same])
            (ih tail (fun value member => mapped value (List.mem_cons_of_mem _ member)))

theorem Value.field_sizeOf {value child : Value} (member : some child ∈ value.fields) : sizeOf child < sizeOf value := by
  cases value
  simp only [Value.fields] at member
  have smaller := List.sizeOf_lt_of_mem member
  change 1 + sizeOf child < _ at smaller
  simp_wf
  omega

theorem World.Resident.child_at {world : World} {address : Address} {value child : Value} {index : Nat}
    (resident : world.Resident address value) (found : value.fields[index]? = some (some child)) :
    world.Resident (address.child index) child := by
  apply World.resident_iff_stores.mpr
  change world.read { address with fields := address.fields ++ [index] } = some child
  rw [World.read_append,World.resident_iff_stores.mp resident]
  simp [Value.atPath,found]

theorem CopiesSnapshot.valueTyped {program : Kernel.Program}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    {before after : State} {suspension : Suspension} {map : Relocation}
    (typed : Typing.WorldTyped program before.world) (copied : CopiesSnapshot program before suspension map after)
    {address : Address} {value : Value} (checked : Typing.ValueTyped program before.world value)
    (resident : before.world.Resident address value) (included : address.root ∈ map.roots) :
    Typing.ValueTyped program (map.copyWorld before.world suspension.homes) (map.value value) := by
  have fields : ∀ child, some child ∈ value.fields →
      Typing.ValueTyped program (map.copyWorld before.world suspension.homes) (map.value child) := by
    intro child member
    obtain ⟨index,bound,atChild⟩ := List.mem_iff_getElem.mp member
    have found : value.fields[index]? = some (some child) := by rw [List.getElem?_eq_getElem bound,atChild]
    exact copied.valueTyped valid inventory typed (checked.child found) (World.Resident.child_at resident found) included
  have supported := typed.resident_runtimeRegionsBelow valid inventory resident
  have captured : address.root ∈ suspension.roots := copied.relocation.roots ▸ included
  cases checked with
  | unit =>
      simp only [Relocation.value,Relocation.term,Term.renameRuntimeRegions,Relocation.values]
      exact .unit
  | scalar valid =>
      simp only [Relocation.value,Relocation.term,Term.renameRuntimeRegions,Relocation.values]
      exact .scalar valid
  | aggregate shape typedFields =>
      rw [map.constructor_value shape]
      exact .aggregate (ConstructorHead.relocate valid shape map) (map.fieldsTyped typedFields fields)
  | @reference owner mode region type id loan live found active modeEq regionEq located =>
      have shared := copied.replayable.2.2.1 address _ id loan captured resident rfl found
      have selectedLoan := copied.relocation.reference_loan included resident rfl found active shared
      simp only [regionEq,Relocation.value,Relocation.term,Term.renameRuntimeRegions,Relocation.values]
      refine .reference (copied.relocation.copied_loan typed.1 found selectedLoan) active modeEq rfl ?_
      change AddressType program.declarations (map.copyWorld before.world suspension.homes)
        (map.address loan.referent) (map.term type)
      by_cases internal : loan.referent.root ∈ map.roots
      · exact copied.relocation.copied_addressType valid typed internal located
      · rw [Relocation.address_unselected internal,
          copied.relocation.external_referent_type included resident rfl found internal located]
        exact Relocation.old_addressType located
  | pointer bound origin =>
      simp only [Relocation.value,Relocation.term,Term.renameRuntimeRegions,Relocation.values]
      exact .pointer (copied.relocation.pointer_bound typed.1 origin bound) (copied.relocation.pointer_origin typed.1 origin)
  | callable instantiated typedFields =>
      obtain ⟨function,instanced,captures⟩ := copied.relocation.instance_captures valid inventory typed.1 instantiated
        (fun term member => supported.child member)
      simp only [Relocation.value,Relocation.term,Term.renameRuntimeRegions]
      refine .callable instanced ?_
      rw [captures]
      exact map.fieldsTyped typedFields fields
  | operation instantiated =>
      obtain ⟨signature,instanced⟩ := copied.relocation.operation_instance valid typed.1 instantiated
        (fun term member => supported.child member)
      simp only [Relocation.value,Relocation.term,Term.renameRuntimeRegions,Relocation.values]
      exact .operation instanced
  | label => exact False.elim ((copied.replayable.2.1 address _ captured resident).2.1 _ rfl)
  | continuation form =>
      obtain ⟨argument,answer,effects,quantity,rfl⟩ := form
      simp only [Relocation.value,Relocation.term,Term.renameRuntimeRegions,Relocation.values]
      exact .continuation ⟨_,_,_,_,rfl⟩
  | available => exact False.elim ((copied.replayable.2.1 address _ captured resident).2.2 _ rfl)
  | bindings typedFields brand region count distinct =>
      simp only [brand,region,Relocation.value,Relocation.term,Term.renameRuntimeRegions]
      exact .bindings (map.fieldsTyped typedFields fields) rfl rfl
        (by simpa only [Relocation.values_length,BindingPack.mapOrigins] using count) distinct
termination_by value
decreasing_by exact Value.field_sizeOf member

theorem CopiesSnapshot.worldTyped {program : Kernel.Program}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    {before after : State} {suspension : Suspension} {map : Relocation}
    (typed : Typing.WorldTyped program before.world) (copied : CopiesSnapshot program before suspension map after) :
    Typing.WorldTyped program after.world := by
  refine ⟨copied.wellFormed typed.1,?_,?_,copied.root_support typed⟩
  · intro address value resident
    rw [copied.result] at resident ⊢
    rcases Relocation.resident_origin typed.1.1 resident with original | ⟨previous,original,included,stored,rfl,rfl⟩
    · exact Relocation.old_valueTyped (typed.2.1 address value original)
    · exact copied.valueTyped valid inventory typed (typed.2.1 previous original stored) stored included
  · intro id root value found contents
    rw [copied.result] at found
    rcases Relocation.root_origin typed.1.1 found with original | ⟨old,original,selected,_,_,rfl⟩
    · exact typed.2.2.1 id root value original contents
    · obtain ⟨previous,oldContents,rfl⟩ := Option.map_eq_some_iff.mp contents
      rw [map.value_type,typed.2.2.1 old original previous selected oldContents]
      rfl

end Glorious.Language.Execution
