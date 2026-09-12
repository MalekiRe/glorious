import GloriousLanguage.Preservation

/-! Structural inversion of the actual Copy traversal. These lemmas retain
its exact copied resident and never reconstruct a second ownership walk. -/
namespace Glorious.Language

theorem CopyTree.type_eq {program : Program} {next finish : Nat} {value copied : Value} {origins : Table Identity}
    (copy : CopyTree program next value finish copied origins) : copied.type = value.type := by
  cases copy; rfl

theorem CopyFields.length {program : Program} {next finish : Nat}
    {fields copied : List (Option Value)} {origins : Table Identity}
    (copy : CopyFields program next fields finish copied origins) : copied.length = fields.length := by
  refine CopyFields.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ fields _ copied _ _ => copied.length = fields.length)
    ?_ ?_ ?_ copy
  · intros; trivial
  · intro; rfl
  · intro next middle finish value copied rest copies first later _ _ _ ih
    simpa using congrArg Nat.succ ih

theorem Value.mapFieldOrigins_eq_map (map : Identity → Identity) (fields : List (Option Value)) :
    Value.mapFieldOrigins map fields = fields.map (Option.map (Value.mapBindingOrigins map)) := by
  induction fields with
  | nil => rfl
  | cons field rest ih => cases field <;> simp [Value.mapFieldOrigins,ih]

theorem Value.mapBindingOrigins_owner (value : Value) (map : Identity → Identity) :
    (value.mapBindingOrigins map).owner = value.owner := by cases value; rfl

theorem Value.mapBindingOrigins_head (value : Value) (map : Identity → Identity) :
    (value.mapBindingOrigins map).head =
      (match value.head with | .bindings pack => .bindings (pack.mapOrigins map) | head => head) := by
  cases value; rfl

theorem Value.mapBindingOrigins_length (value : Value) (map : Identity → Identity) :
    (value.mapBindingOrigins map).fields.length = value.fields.length := by
  cases value
  simp [Value.mapBindingOrigins,Value.fields,Value.mapFieldOrigins_eq_map]

theorem Value.mapBindingOrigins_atPath (value : Value) (map : Identity → Identity) (path : List Nat) :
    (value.mapBindingOrigins map).atPath path = (value.atPath path).map (Value.mapBindingOrigins map) := by
  induction path generalizing value with
  | nil => rfl
  | cons index path ih =>
      cases value with
      | resident owner type head live fields resources =>
          simp only [Value.atPath,Value.mapBindingOrigins,Value.fields,Value.mapFieldOrigins_eq_map,List.getElem?_map]
          cases selected : fields[index]? with
          | none => rfl
          | some field => cases field with
            | none => rfl
            | some child => exact ih child

theorem ResidentAt.mapBindingOrigins_iff {value resident : Value} {path : List Nat} {map : Identity → Identity} :
    ResidentAt (value.mapBindingOrigins map) path resident ↔
      ∃ original, ResidentAt value path original ∧ resident = original.mapBindingOrigins map := by
  rw [ResidentAt.iff_atPath,Value.mapBindingOrigins_atPath,Option.map_eq_some_iff]
  constructor
  · rintro ⟨original,found,same⟩
    exact ⟨original,ResidentAt.iff_atPath.mpr found,same.symm⟩
  · rintro ⟨original,found,same⟩
    exact ⟨original,ResidentAt.iff_atPath.mp found,same.symm⟩


/-- Each structural resident in the result has its own actual subtree Copy
derivation at the same path. This supplies the invariant law for nested
nominals without inferring resource ownership from their representation. -/
theorem CopyTree.resident_copy {program : Program} {next finish : Nat}
    {value copied : Value} {origins : Table Identity}
    (copy : CopyTree program next value finish copied origins) :
    ∀ path resident, ResidentAt copied path resident → ∃ original first last names,
      ResidentAt value path original ∧ CopyTree program first original last resident names := by
  refine CopyTree.rec
    (motive_1 := fun _ value _ copied _ _ => ∀ path resident, ResidentAt copied path resident →
      ∃ original first last names, ResidentAt value path original ∧ CopyTree program first original last resident names)
    (motive_2 := fun _ fields _ copied _ _ => ∀ (index : Nat) resident,
      copied[index]? = some (some resident) → ∃ original, fields[index]? = some (some original) ∧
      ∀ path nested, ResidentAt resident path nested → ∃ old first last names,
        ResidentAt original path old ∧ CopyTree program first old last nested names)
    ?_ ?_ ?_ copy
  · intro next owner type head fields resources copied finish origins duplicable shared traversed ih path resident inside
    cases inside with
    | root => exact ⟨_,next,finish,_,.root,.resident duplicable shared traversed⟩
    | field selected nested =>
        obtain ⟨original,found,origin⟩ := ih _ _ selected
        obtain ⟨old,first,last,names,located,subtree⟩ := origin _ _ nested
        exact ⟨old,first,last,names,.field found located,subtree⟩
  · intro next index resident found
    simp at found
  · intro next middle finish value copied rest copies first later _ _ ih tail index resident found
    cases index with
    | zero =>
        have same := Option.some.inj (Option.some.inj found)
        subst resident
        exact ⟨value,rfl,ih⟩
    | succ index =>
        obtain ⟨original,selected,origin⟩ := tail index resident found
        exact ⟨original,selected,origin⟩

theorem CopyTree.resources_eq {program : Program} {next finish : Nat}
    {value copied : Value} {origins : Table Identity}
    (copy : CopyTree program next value finish copied origins) (map : Identity → Identity) :
    (copied.mapBindingOrigins map).resources = value.resources := by cases copy; rfl

theorem CopyTree.resources_readOnly {program : Program} {next finish : Nat}
    {value copied : Value} {origins : Table Identity}
    (copy : CopyTree program next value finish copied origins) :
    ∀ binding ∈ value.resources, binding.ReadOnly := by cases copy; assumption

theorem CopyTree.reference_iff {program : Program} {next finish : Nat}
    {value copied : Value} {origins : Table Identity}
    (copy : CopyTree program next value finish copied origins) (map : Identity → Identity) (identity : Identity) :
    (copied.mapBindingOrigins map).head = .reference identity ↔ value.head = .reference identity := by
  have same : copied.head = value.head := by cases copy; rfl
  rw [Value.mapBindingOrigins_head,same]
  cases value.head <;> simp

theorem CopyFields.present {program : Program} {next finish : Nat}
    {fields copied : List (Option Value)} {origins : Table Identity}
    (copy : CopyFields program next fields finish copied origins) :
    ∀ field ∈ copied, field.isSome = true := by
  refine CopyFields.rec
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ copied _ _ => ∀ field ∈ copied, field.isSome = true)
    ?_ ?_ ?_ copy
  · intros; trivial
  · intro next field member; simp at member
  · intro next middle finish value copied rest copies first later _ _ _ ih field member
    rcases List.mem_cons.mp member with rfl | member
    · rfl
    · exact ih field member

theorem CopyTree.initialized {program : Program} {next finish : Nat}
    {value copied : Value} {origins : Table Identity}
    (copy : CopyTree program next value finish copied origins) : copied.Initialized := by
  intro path resident inside
  obtain ⟨original,first,last,names,_,subtree⟩ := copy.resident_copy path resident inside
  cases subtree with
  | resident _ _ traversed => exact ⟨rfl,traversed.present⟩

theorem Value.Initialized.mapBindingOrigins {value : Value} (ready : value.Initialized)
    (map : Identity → Identity) : (value.mapBindingOrigins map).Initialized := by
  intro path resident inside
  obtain ⟨original,located,rfl⟩ := ResidentAt.mapBindingOrigins_iff.mp inside
  have initialized := ready path original located
  cases original with
  | resident owner type head live fields resources =>
      refine ⟨initialized.1,?_⟩
      intro field copiedMember
      change field ∈ Value.mapFieldOrigins map fields at copiedMember
      rw [Value.mapFieldOrigins_eq_map] at copiedMember
      obtain ⟨old,originalMember,rfl⟩ := List.mem_map.mp copiedMember
      have present := initialized.2 old originalMember
      cases old <;> simp_all

theorem CopyValue.initialized {program : Program} {next finish : Nat} {value copied : Value}
    (copy : CopyValue program next value finish copied) : copied.Initialized := by
  cases copy with
  | copy tree _ => exact tree.initialized.mapBindingOrigins _

theorem Typing.ValueTyped.owner_change {program : Kernel.Program} {world : World}
    {previous owner : Identity} {type : Term} {head : ValueHead} {live : Bool} {fields : List (Option Value)} {resources : List StorageBinding}
    (typed : Typing.ValueTyped program world (.resident previous type head live fields resources)) :
    Typing.ValueTyped program world (.resident owner type head live fields resources) := by
  cases typed with
  | unit => exact .unit
  | scalar checked => exact .scalar checked
  | aggregate shape fields => exact .aggregate shape fields
  | reference found active mode region located => exact .reference found active mode region located
  | pointer bound origin => exact .pointer bound origin
  | callable selected fields => exact .callable selected fields
  | operation selected => exact .operation selected
  | label => exact .label
  | continuation form => exact .continuation form
  | available found brand id region residents => exact .available found brand id region residents
  | bindings fields brand region length distinct => exact .bindings fields brand region length distinct

theorem Typing.ValueTyped.mapBindingOrigins {program : Kernel.Program} {world : World} {value : Value}
    (typed : Typing.ValueTyped program world value) (map : Identity → Identity) :
    Typing.ValueTyped program world (value.mapBindingOrigins map) := by
  refine Typing.ValueTyped.rec
    (motive_1 := fun value _ => Typing.ValueTyped program world (value.mapBindingOrigins map))
    (motive_2 := fun fields types _ => Typing.FieldsTyped program world (Value.mapFieldOrigins map fields) types)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  · exact fun {_ _} => .unit
  · exact fun {_ _ _} checked => .scalar checked
  · intro owner type head live fields types resources constructed _ checked
    cases head <;> try exact .aggregate constructed checked
    case bindings pack =>
      rcases constructed with ⟨_,_,impossible⟩ | ⟨_,_,_,_,_,_,impossible,_⟩ | ⟨_,_,_,_,_,_,_,impossible,_⟩ <;>
        cases impossible
  · exact fun {_ _ _ _ _ _ _} found active mode region located => .reference found active mode region located
  · exact fun {_ _ _ _ _} bound origin => .pointer bound origin
  · exact fun {_ _ _ _ _ _} selected _ fields => .callable selected fields
  · exact fun {_ _ _ _ _ _} selected => .operation selected
  · exact fun {_ _ _ _ _} => .label
  · exact fun {_ _ _ _} form => .continuation form
  · exact fun {_ _ _ _ _ _ _} found brand id region residents => .available found brand id region residents
  · intro owner brand region live fields types pack _ brandEq regionEq length distinct checked
    exact .bindings checked brandEq regionEq
      (by simpa [Value.mapFieldOrigins_eq_map,BindingPack.mapOrigins] using length) distinct
  · exact .nil
  · exact fun {_ _ _} _ fields => .hole fields
  · intro value fields type types _ same _ checked tail
    exact .resident checked (by simpa only [Value.mapBindingOrigins_type] using same) tail

theorem CopyTree.typed {program : Kernel.Program} {world : World} {next finish : Nat}
    {value copied : Value} {origins : Table Identity}
    (copy : CopyTree program.declarations next value finish copied origins)
    (typed : Typing.ValueTyped program world value) : Typing.ValueTyped program world copied := by
  refine CopyTree.rec
    (motive_1 := fun _ value _ copied _ _ =>
      Typing.ValueTyped program world value → Typing.ValueTyped program world copied)
    (motive_2 := fun _ fields _ copied _ _ => ∀ types,
      Typing.FieldsTyped program world fields types → Typing.FieldsTyped program world copied types)
    ?_ ?_ ?_ copy typed
  · intro next owner type head fields resources copied finish origins _ _ _ ih typed
    obtain ⟨types,fieldsTyped,rebuild⟩ := typed.fields_model
    have rebuilt := rebuild copied (ih types fieldsTyped)
    exact rebuilt.owner_change
  · intro next types typed
    cases typed
    exact .nil
  · intro next middle finish value copied rest copies first later tree _ ih tail types typed
    cases typed with
    | resident checked same fields => exact .resident (ih checked) (tree.type_eq.trans same) (tail _ fields)

theorem CopyValue.typed {program : Kernel.Program} {world : World} {next finish : Nat} {value copied : Value}
    (copy : CopyValue program.declarations next value finish copied) (typed : Typing.ValueTyped program world value) :
    Typing.ValueTyped program world copied := by
  cases copy with
  | copy tree _ => exact (tree.typed typed).mapBindingOrigins _

end Glorious.Language
