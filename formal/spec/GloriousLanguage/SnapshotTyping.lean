import GloriousLanguage.RuntimeSupport
import GloriousLanguage.PointerPreservation

/-! Runtime typing of copied and retained snapshot storage is derived from
the executable copy. Lexical declarations and allocated type identities are
the inputs; neither the copied world's typing nor equivariant declarations
are postulated as permission to execute. -/
namespace Glorious.Language.Execution

theorem Relocation.old_fieldOffset {program : Program} {world : World} {map : Relocation} {homes : Table Home}
    {address : Address} {container type : Term} {index offset : Nat}
    (field : FieldOffset program world address container index type offset) :
    FieldOffset program (map.copyWorld world homes) address container index type offset := by
  cases field with
  | tuple selected layouts layout offset => exact .tuple selected layouts layout offset
  | bindings selected layouts layout offset => exact .bindings selected layouts layout offset
  | callable captures selected layouts layout offset => exact .callable captures selected layouts layout offset
  | array nonnegative bound layout => exact .array nonnegative bound layout
  | nominal constructor identity instantiated substituted selected layout stored head offset =>
      exact .nominal constructor identity instantiated substituted selected layout
        (World.resident_iff_stores.mp (Relocation.old_resident (World.resident_iff_stores.mpr stored))) head offset

theorem Relocation.old_addressOffset {program : Program} {world : World} {map : Relocation} {homes : Table Home}
    {address : Address} {type : Term} {offset : Nat} (typed : AddressOffset program world address type offset) :
    AddressOffset program (map.copyWorld world homes) address type offset := by
  induction typed with
  | root found live => exact .root (Relocation.old_root found) live
  | child _ field ih => exact .child ih (Relocation.old_fieldOffset field)

theorem Relocation.old_addressType {program : Program} {world : World} {map : Relocation} {homes : Table Home}
    {address : Address} {type : Term} (typed : AddressType program world address type) :
    AddressType program (map.copyWorld world homes) address type := by
  obtain ⟨offset,located⟩ := typed
  exact ⟨offset,Relocation.old_addressOffset located⟩

/-- Copying adds new storage and reborrow handles; it cannot invalidate the
typing of any original value, including a pointer to already retired storage. -/
theorem Relocation.old_valueTyped {program : Kernel.Program} {world : World} {map : Relocation} {homes : Table Home}
    {value : Value} (typed : Typing.ValueTyped program world value) :
    Typing.ValueTyped program (map.copyWorld world homes) value := by
  apply typed.transport
  · intro id loan found _
    exact ⟨Relocation.old_loan found,fun _ located => Relocation.old_addressType located⟩
  · rfl
  · intro pointer origin
    exact origin.weaken (fun _ _ found => Relocation.old_root found)

theorem Relocation.root_support {program : Kernel.Program} {world : World} {map : Relocation} {homes : Table Home}
    (typed : Typing.WorldTyped program world) :
    ∀ id root, (map.copyWorld world homes).roots.get id = some root →
      root.type.RuntimeRegionsBelow (map.copyWorld world homes).nextRegion := by
  intro id root found
  rcases Relocation.root_origin typed.1.1 found with original | ⟨old,source,selected,_,rfl,rfl⟩
  · exact (typed.2.2.2 id root original).mono (Nat.le_add_left world.nextRegion map.regionBase)
  · exact map.term_runtimeRegionsBelow (typed.2.2.2 old source selected)

theorem CopiesSnapshot.old_valueTyped {program : Kernel.Program} {before after : State} {suspension : Suspension}
    {map : Relocation} (copied : CopiesSnapshot program before suspension map after) {value : Value}
    (typed : Typing.ValueTyped program before.world value) : Typing.ValueTyped program after.world value := by
  rw [copied.result]
  exact Relocation.old_valueTyped typed

theorem CopiesSnapshot.root_support {program : Kernel.Program} {before after : State} {suspension : Suspension}
    {map : Relocation} (typed : Typing.WorldTyped program before.world)
    (copied : CopiesSnapshot program before suspension map after) :
    ∀ id root, after.world.roots.get id = some root → root.type.RuntimeRegionsBelow after.world.nextRegion := by
  rw [copied.result]
  exact Relocation.root_support typed

end Glorious.Language.Execution

namespace Glorious.Language

theorem Execution.ConstructorHead.runtimeRegionsBelow {program : Program} (valid : ProgramWellFormed program)
    {type : Term} {variant : Option DeclId} {fields : List Term} {head : ValueHead} {bound : Identity}
    (constructed : Execution.ConstructorHead program type variant fields head)
    (supported : type.RuntimeRegionsBelow bound) : ∀ field ∈ fields, field.RuntimeRegionsBelow bound := by
  rcases constructed with ⟨rfl,_,_⟩ | ⟨element,sign,width,length,rfl,_,_,_,homogeneous⟩ |
    ⟨id,arguments,data,constructor,substitution,rfl,_,_,selected,instantiated,substituted⟩
  · intro field member
    exact supported.child member
  · intro field member
    rw [homogeneous field member]
    exact supported.child (by simp [Term.children])
  · intro field member
    rw [ListRel.substitutes_eq_map substituted] at member
    obtain ⟨original,inOriginal,rfl⟩ := List.mem_map.mp member
    obtain ⟨declaration,inFields,rfl⟩ := List.mem_map.mp inOriginal
    exact instantiated.runtimeRegionsBelow (fun argument present => supported.child present)
      (valid.field_lexical selected.1 selected.2.1 inFields)

theorem CallableFields.runtimeRegionsBelow {program : Program} (valid : ProgramWellFormed program)
    {id : DeclId} {arguments fields : List Term} {bound : Identity}
    (declared : CallableFields program id arguments fields)
    (supported : ∀ argument ∈ arguments, argument.RuntimeRegionsBelow bound) :
    ∀ field ∈ fields, field.RuntimeRegionsBelow bound := by
  cases declared with
  | function found instantiated substituted =>
      have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.function_lookup found))
      intro field member
      rw [ListRel.substitutes_eq_map substituted] at member
      obtain ⟨original,inOriginal,rfl⟩ := List.mem_map.mp member
      exact instantiated.runtimeRegionsBelow supported (lexical original (by
        simp only [Definition.terms,List.mem_append]
        exact Or.inl (Or.inr inOriginal)))
  | operation => intro field member; cases member

theorem Kernel.Instance.capture_runtimeRegionsBelow {program : Kernel.Program}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    {id : DeclId} {arguments : List Term} {function : Kernel.Function} {bound : Identity}
    (selected : Kernel.Instance program id arguments function)
    (supported : ∀ argument ∈ arguments, argument.RuntimeRegionsBelow bound) :
    ∀ type ∈ function.captures.map (·.type), type.RuntimeRegionsBelow bound := by
  rcases selected with ⟨template,declaration,substitution,body,signature,_,instantiated,_,_,rfl⟩
  have member : template ∈ program.functions := List.mem_of_find?_eq_some body
  have identity : template.declaration = id := by
    have matching := List.find?_some body
    change (template.declaration.package == id.package && template.declaration.serial == id.serial) = true at matching
    simp only [Bool.and_eq_true,beq_iff_eq] at matching
    cases identity : template.declaration
    cases id
    simp_all
  obtain ⟨other,otherFound,_,_,captures⟩ := inventory.2.1 template member
  have otherEq : other = declaration := Option.some.inj ((identity ▸ otherFound).symm.trans signature)
  subst other
  have lexical := valid.lexical (List.mem_of_find?_eq_some (Program.function_lookup signature))
  intro type inTypes
  change type ∈ (template.captures.map (Kernel.Local.mapTerms (Term.substitute substitution))).map (·.type) at inTypes
  simp only [List.map_map,Function.comp_def,Kernel.Local.mapTerms] at inTypes
  obtain ⟨capture,inCaptures,rfl⟩ := List.mem_map.mp inTypes
  exact instantiated.runtimeRegionsBelow supported (lexical capture.type (by
    simp only [Definition.terms,List.mem_append]
    exact Or.inl (Or.inr (captures ▸ List.mem_map.mpr ⟨capture,inCaptures,rfl⟩))))

theorem Typing.FieldsTyped.runtimeRegionsBelow {program : Kernel.Program} {world : World}
    {fields : List (Option Value)} {types : List Term} {bound : Identity}
    (typed : Typing.FieldsTyped program world fields types)
    (supported : ∀ type ∈ types, type.RuntimeRegionsBelow bound) :
    ∀ value, some value ∈ fields → value.type.RuntimeRegionsBelow bound := by
  induction fields generalizing types with
  | nil => intro value member; cases member
  | cons first rest ih =>
      cases typed with
      | hole tail =>
          intro value member
          apply ih tail (fun type inTypes => supported type (List.mem_cons_of_mem _ inTypes)) value
          simpa using member
      | resident _ same tail =>
          intro value member
          rcases List.mem_cons.mp member with equal | later
          · cases equal
            rw [same]
            exact supported _ List.mem_cons_self
          · exact ih tail (fun type inTypes => supported type (List.mem_cons_of_mem _ inTypes)) value later

theorem Typing.ValueTyped.child_runtimeRegionsBelow {program : Kernel.Program}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    {world : World} {value child : Value} {bound : Identity} (typed : Typing.ValueTyped program world value)
    (supported : value.type.RuntimeRegionsBelow bound) (member : some child ∈ value.fields) :
    child.type.RuntimeRegionsBelow bound := by
  cases typed <;> try { simp only [Value.fields,List.not_mem_nil] at member }
  case aggregate shape fields =>
    exact fields.runtimeRegionsBelow (shape.runtimeRegionsBelow valid supported) child member
  case callable selected fields =>
    exact fields.runtimeRegionsBelow
      (selected.capture_runtimeRegionsBelow valid inventory (fun _ present => supported.child present)) child member
  case bindings fields _ _ _ _ =>
    exact fields.runtimeRegionsBelow (fun type present => supported.child (by simp [Value.type,Term.children,present])) child member

theorem Typing.ValueTyped.resident_runtimeRegionsBelow {program : Kernel.Program}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    {world : World} {value resident : Value} {path : List Nat} {bound : Identity}
    (typed : Typing.ValueTyped program world value) (supported : value.type.RuntimeRegionsBelow bound)
    (inside : ResidentAt value path resident) : resident.type.RuntimeRegionsBelow bound := by
  induction inside with
  | root => exact supported
  | field found _ ih =>
      exact ih (typed.child found)
        (typed.child_runtimeRegionsBelow valid inventory supported (List.mem_of_getElem? found))

/-- Phantom generic arguments and vacant field types cannot evade generativity:
all nested resident types derive support from the actual stored root contract. -/
theorem Typing.WorldTyped.resident_runtimeRegionsBelow {program : Kernel.Program}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    {world : World} (typed : Typing.WorldTyped program world) {address : Address} {value : Value}
    (resident : world.Resident address value) : value.type.RuntimeRegionsBelow world.nextRegion := by
  obtain ⟨root,whole,found,live,_,contents,inside⟩ := resident
  have wholeTyped := typed.2.1 ⟨address.root,root.generation,[]⟩ whole ⟨root,whole,found,live,rfl,contents,.root⟩
  have same := typed.2.2.1 address.root root whole found contents
  exact wholeTyped.resident_runtimeRegionsBelow valid inventory
    (same ▸ typed.2.2.2 address.root root found) inside

/-- The declared type of a vacant location comes from the same byte-layout
derivation as a populated location, including instantiated nominal fields. -/
theorem FieldOffset.runtimeRegionsBelow {program : Program} (valid : ProgramWellFormed program)
    {world : World} {address : Address} {container type : Term} {index offset bound : Nat}
    (located : FieldOffset program world address container index type offset)
    (supported : container.RuntimeRegionsBelow bound) : type.RuntimeRegionsBelow bound := by
  cases located with
  | tuple selected _ _ _ => exact supported.child (List.mem_of_getElem? selected)
  | bindings selected _ _ _ =>
      exact supported.child (by simp [Term.children,List.mem_of_getElem? selected])
  | callable declared selected _ _ _ =>
      exact declared.runtimeRegionsBelow valid (fun _ present => supported.child present)
        type (List.mem_of_getElem? selected)
  | array _ _ _ => exact supported.child (by simp [Term.children])
  | @nominal id arguments data variant substitution types index type layout offset value selected identity
      instantiated substituted atType _ _ _ _ =>
      have constructed : Execution.ConstructorHead program (.nominal id arguments)
          (some variant.header.id) types (.constructor variant.header.id) :=
        Or.inr (Or.inr ⟨variant.header.id,arguments,data,variant,substitution,
          by rw [identity],rfl,rfl,selected,instantiated,substituted⟩)
      exact constructed.runtimeRegionsBelow valid supported type (List.mem_of_getElem? atType)

theorem AddressOffset.runtimeRegionsBelow {program : Program} (valid : ProgramWellFormed program)
    {world : World} {address : Address} {type : Term} {offset bound : Nat}
    (located : AddressOffset program world address type offset)
    (supported : ∀ id root, world.roots.get id = some root → root.type.RuntimeRegionsBelow bound) :
    type.RuntimeRegionsBelow bound := by
  induction located with
  | root found _ => exact supported _ _ found
  | child _ field ih => exact field.runtimeRegionsBelow valid ih

theorem Typing.WorldTyped.address_runtimeRegionsBelow {program : Kernel.Program}
    (valid : ProgramWellFormed program.declarations) {world : World} (typed : Typing.WorldTyped program world)
    {address : Address} {type : Term} (located : AddressType program.declarations world address type) :
    type.RuntimeRegionsBelow world.nextRegion := by
  obtain ⟨offset,located⟩ := located
  exact located.runtimeRegionsBelow valid typed.2.2.2

namespace Execution

theorem CopiesSnapshot.region_permutation_involutive {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} (valid : before.world.WellFormed)
    (copied : CopiesSnapshot program before suspension map after) (term : Term) :
    (term.renameRuntimeRegions (freshSwap map.regions map.regionBase)).renameRuntimeRegions
      (freshSwap map.regions map.regionBase) = term := by
  apply map.permutation_involutive
  intro id member
  rw [copied.relocation.regionBase]
  exact World.region_bound valid (copied.relocation.liveRegions id member)

theorem CopiesSnapshot.resident_type_permutation {program : Kernel.Program}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    {before after : State} {suspension : Suspension} {map : Relocation}
    (typed : Typing.WorldTyped program before.world) (copied : CopiesSnapshot program before suspension map after)
    {address : Address} {value : Value} (resident : before.world.Resident address value) :
    map.term value.type = value.type.renameRuntimeRegions (freshSwap map.regions map.regionBase) := by
  apply map.term_eq_permutation
  rw [copied.relocation.regionBase]
  exact typed.resident_runtimeRegionsBelow valid inventory resident

theorem CopiesSnapshot.address_type_permutation {program : Kernel.Program}
    (valid : ProgramWellFormed program.declarations) {before after : State} {suspension : Suspension} {map : Relocation}
    (typed : Typing.WorldTyped program before.world) (copied : CopiesSnapshot program before suspension map after)
    {address : Address} {type : Term} (located : AddressType program.declarations before.world address type) :
    map.term type = type.renameRuntimeRegions (freshSwap map.regions map.regionBase) := by
  apply map.term_eq_permutation
  rw [copied.relocation.regionBase]
  exact typed.address_runtimeRegionsBelow valid located

end Execution

end Glorious.Language
