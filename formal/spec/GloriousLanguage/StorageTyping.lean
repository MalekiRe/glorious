import GloriousLanguage.Typing

/-! Resident typing agrees with the existing layout/address derivation.
These proofs use declaration well-formedness and the body inventory, not
resource admission or a typed post-state. -/
namespace Glorious.Language

theorem Instantiates.functional {binders : List Binder} {arguments : List Term}
    {left right : Substitution} (a : Instantiates binders arguments left)
    (b : Instantiates binders arguments right) : left = right := a.2.2.trans b.2.2.symm

theorem ListRel.substitutes_eq_map {substitution : Substitution} {before after : List Term}
    (related : ListRel (Substitutes substitution) before after) :
    after = before.map (Term.substitute substitution) := by
  induction related with
  | nil => rfl
  | cons term _ ih => simp [term.2.1,ih]

theorem Program.data_lookup {program : Program} {id : DeclId} {data : DataDefinition}
    (found : program.data id = some data) : program.lookup id = some (.data data) := by
  unfold Program.data at found
  split at found <;> simp_all

theorem Program.function_lookup {program : Program} {id : DeclId} {function : FunctionDefinition}
    (found : program.function id = some function) : program.lookup id = some (.function function) := by
  unfold Program.function at found
  split at found <;> simp_all

theorem Program.operation_lookup {program : Program} {id : DeclId} {operation : OperationDefinition}
    (found : program.operation id = some operation) : program.lookup id = some (.operation operation) := by
  unfold Program.operation at found
  split at found <;> simp_all

theorem Program.Constructor.variant_unique {program : Program} {id : DeclId}
    {data : DataDefinition} {left right : VariantDefinition} (valid : ProgramWellFormed program)
    (a : program.Constructor id data left) (b : program.Constructor id data right) : left = right := by
  have headerEq := valid.2.2.1 left.header right.header
    (Or.inr (Or.inl ⟨data,left,⟨a.1,a.2.1,rfl⟩,rfl⟩))
    (Or.inr (Or.inl ⟨data,right,⟨b.1,b.2.1,rfl⟩,rfl⟩)) (a.2.2.trans b.2.2.symm)
  have member : Definition.data data ∈ program.declarations :=
    List.mem_of_find?_eq_some (Program.data_lookup a.1)
  have distinct := (valid.2.2.2.2.1 _ member).2.2.1
  obtain ⟨i,hi,atLeft⟩ := List.mem_iff_getElem.mp a.2.1
  obtain ⟨j,hj,atRight⟩ := List.mem_iff_getElem.mp b.2.1
  have nameEq := congrArg Header.name headerEq
  have equal : i = j := (List.getElem?_inj (by simpa using hi) distinct).mp (by
    simp only [List.getElem?_map,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,
      Option.map_some,atLeft,atRight,nameEq])
  subst j
  exact atLeft.symm.trans atRight

theorem Kernel.Instance.capture_types {program : Kernel.Program} {id : DeclId}
    {arguments fields : List Term} {function : Kernel.Function}
    (inventory : Kernel.BodyInventory program) (selected : Kernel.Instance program id arguments function)
    (declared : CallableFields program.declarations id arguments fields) :
    function.captures.map (·.type) = fields := by
  rcases selected with ⟨template,declaration,substitution,body,signature,agrees,instantiated,_,rfl⟩
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
  cases declared with
  | function found inst types =>
      have equal := Option.some.inj (signature.symm.trans found)
      subst equal
      have subEq := (agrees ▸ instantiated).functional inst
      subst subEq
      rw [ListRel.substitutes_eq_map types]
      change (template.captures.map (Kernel.Local.mapTerms (Term.substitute substitution))).map (·.type) = _
      simp only [List.map_map,Function.comp_def,Kernel.Local.mapTerms]
      simpa only [List.map_map,Function.comp_def] using
        congrArg (List.map (Term.substitute substitution)) captures
  | operation found _ =>
      have impossible := (Program.function_lookup signature).symm.trans (Program.operation_lookup found)
      cases impossible

theorem Typing.FieldsTyped.length {program : Kernel.Program} {world : World}
    {fields : List (Option Value)} {types : List Term} (typed : Typing.FieldsTyped program world fields types) :
    fields.length = types.length := by
  induction fields generalizing types with
  | nil => cases typed; rfl
  | cons field fields ih =>
      cases typed with
      | hole rest => simpa using congrArg Nat.succ (ih rest)
      | resident _ _ rest => simpa using congrArg Nat.succ (ih rest)

theorem Typing.FieldsTyped.get {program : Kernel.Program} {world : World}
    {fields : List (Option Value)} {types : List Term} {index : Nat} {value : Value}
    (typed : Typing.FieldsTyped program world fields types) (found : fields[index]? = some (some value)) :
    Typing.ValueTyped program world value ∧ types[index]? = some value.type := by
  induction fields generalizing types index with
  | nil => simp at found
  | cons field fields ih =>
      cases typed with
      | hole rest =>
          cases index with
          | zero => simp at found
          | succ index => exact ih (index := index) rest found
      | resident checked type rest =>
          cases index with
          | zero =>
              have same := Option.some.inj (Option.some.inj found)
              subst value
              exact ⟨checked,by simpa using type.symm⟩
          | succ index => exact ih (index := index) rest found

theorem Typing.FieldsTyped.set {program : Kernel.Program} {world : World}
    {fields : List (Option Value)} {types : List Term} {index : Nat} {type : Term} {replacement : Option Value}
    (typed : Typing.FieldsTyped program world fields types) (selected : types[index]? = some type)
    (checked : ∀ value, replacement = some value → Typing.ValueTyped program world value ∧ value.type = type) :
    Typing.FieldsTyped program world (fields.set index replacement) types := by
  induction fields generalizing types index with
  | nil => cases typed; simp at selected
  | cons field fields ih => cases typed with
    | hole rest =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero,Option.some.injEq] at selected
          subst type
          cases replacement with
          | none => exact .hole rest
          | some value => exact .resident (checked value rfl).1 (checked value rfl).2 rest
      | succ index => exact .hole (ih rest selected)
    | resident resident typeEq rest =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero,Option.some.injEq] at selected
          subst type
          cases replacement with
          | none => exact .hole rest
          | some value => exact .resident (checked value rfl).1 (checked value rfl).2 rest
      | succ index => exact .resident resident typeEq (ih rest selected)

theorem Execution.ConstructorHead.field_type {program : Program} {world : World}
    {address : Address} {value : Value} {types : List Term} {index : Nat} {type : Term} {offset : Nat}
    (valid : ProgramWellFormed program)
    (stored : world.Stores address value)
    (constructed : Execution.ConstructorHead program value.type
      (match value.head with | .constructor id => some id | _ => none) types value.head)
    (located : FieldOffset program world address value.type index type offset) : types[index]? = some type := by
  generalize typeEq : value.type = container at constructed located
  cases located with
  | tuple selected _ _ _ =>
      rcases constructed with ⟨same,_,_⟩ | ⟨_,_,_,_,same,_⟩ | ⟨_,_,_,_,_,same,_⟩
      · cases same; exact selected
      · cases same
      · cases same
  | bindings =>
      rcases constructed with ⟨same,_,_⟩ | ⟨_,_,_,_,same,_⟩ | ⟨_,_,_,_,_,same,_⟩ <;> cases same
  | callable =>
      rcases constructed with ⟨same,_,_⟩ | ⟨_,_,_,_,same,_⟩ | ⟨_,_,_,_,_,same,_⟩ <;> cases same
  | array nonnegative bound _ =>
      rcases constructed with ⟨same,_,_⟩ | ⟨element,sign,width,count,same,_,_,length,uniform⟩ | ⟨_,_,_,_,_,same,_⟩
      · cases same
      · cases same
        have inBounds : index < types.length := by omega
        have found := List.getElem?_eq_getElem inBounds
        rw [found,uniform _ (List.getElem_mem inBounds)]
      · cases same
  | nominal constructor identity inst fields selected _ found head _ =>
      rcases constructed with ⟨same,_,_⟩ | ⟨_,_,_,_,same,_⟩ |
        ⟨id,arguments,data,variant,substitution,same,_,residentHead,source,sourceInst,sourceFields⟩
      · cases same
      · cases same
      · have residentEq := Option.some.inj (stored.symm.trans found)
        subst residentEq
        have headEq := ValueHead.constructor.inj (residentHead.symm.trans head)
        have typeSame := Term.nominal.inj same
        have dataId := identity.trans typeSame.1
        have dataEq := Option.some.inj ((dataId ▸ constructor.1).symm.trans source.1)
        subst dataEq
        have argumentsEq := typeSame.2
        subst arguments
        have variantEq := Program.Constructor.variant_unique valid
          ⟨source.1,source.2.1,source.2.2.trans headEq⟩ constructor
        subst variantEq
        have subEq := sourceInst.functional inst
        subst subEq
        have typesEq := sourceFields.substitutes_eq_map.trans fields.substitutes_eq_map.symm
        simpa [typesEq] using selected

/-- Inversion and reconstruction use the field type selected by byte layout.
The returned reconstruction is a proof, not a second resident-shape producer. -/
theorem Typing.ValueTyped.field_model {program : Kernel.Program} {world typingWorld : World}
    {address : Address} {value : Value} {index : Nat} {type : Term} {offset : Nat}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.ValueTyped program typingWorld value) (stored : world.Stores address value)
    (located : FieldOffset program.declarations world address value.type index type offset) :
    ∃ types, Typing.FieldsTyped program typingWorld value.fields types ∧ types[index]? = some type ∧
      ∀ fields, Typing.FieldsTyped program typingWorld fields types →
        Typing.ValueTyped program typingWorld (value.withFields fields) := by
  cases typed with
  | unit => cases located
  | scalar => cases located
  | aggregate constructed fields =>
      exact ⟨_,fields,Execution.ConstructorHead.field_type valid stored constructed located,
        fun _ checked => .aggregate constructed checked⟩
  | reference => cases located
  | pointer => cases located
  | callable selected fields =>
      cases located with
      | callable declared atField _ _ _ =>
          have agrees := selected.capture_types inventory declared
          exact ⟨_,fields,by simpa [agrees] using atField,fun _ checked => .callable selected checked⟩
  | operation operationInstance =>
      cases located with
      | callable declared atField _ _ _ =>
          cases declared with
          | operation => simp at atField
          | function found _ _ =>
              rcases operationInstance with ⟨_,selected,_⟩
              have impossible := (Program.function_lookup found).symm.trans (Program.operation_lookup selected)
              cases impossible
  | label => cases located
  | continuation form =>
      obtain ⟨_,_,_,_,rfl⟩ := form
      cases located
  | available => cases located
  | bindings checked brand region length distinct =>
      cases located with
      | bindings selected _ _ _ =>
          exact ⟨_,checked,selected,fun _ fields => .bindings fields brand region
            (fields.length.trans (checked.length.symm.trans length)) distinct⟩

theorem Typing.ValueTyped.replace_field {program : Kernel.Program} {world typingWorld : World}
    {address : Address} {value : Value} {index : Nat} {type : Term} {offset : Nat} {replacement : Option Value}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.ValueTyped program typingWorld value) (stored : world.Stores address value)
    (located : FieldOffset program.declarations world address value.type index type offset)
    (checked : ∀ resident, replacement = some resident → Typing.ValueTyped program typingWorld resident ∧ resident.type = type) :
    Typing.ValueTyped program typingWorld (value.withFields (value.fields.set index replacement)) := by
  obtain ⟨types,fields,selected,rebuild⟩ := typed.field_model valid inventory stored located
  exact rebuild _ (fields.set selected checked)

theorem Typing.ValueTyped.child {program : Kernel.Program} {world : World}
    {value child : Value} {index : Nat} (typed : Typing.ValueTyped program world value)
    (found : value.fields[index]? = some (some child)) : Typing.ValueTyped program world child := by
  cases typed <;> try { simp [Value.fields] at found }
  · rename_i _ _ _ _ _ _ _ fields
    exact (fields.get found).1
  · rename_i _ _ _ _ _ _ _ fields
    exact (fields.get found).1
  · rename_i _ _ _ _ _ _ _ fields _ _ _ _
    exact (fields.get found).1

theorem Typing.ValueTyped.resident {program : Kernel.Program} {world : World}
    {value resident : Value} {path : List Nat} (typed : Typing.ValueTyped program world value)
    (inside : ResidentAt value path resident) : Typing.ValueTyped program world resident := by
  induction inside with
  | root => exact typed
  | field found _ ih => exact ih (typed.child found)

theorem Typing.ValueTyped.fields_model {program : Kernel.Program} {world : World} {value : Value}
    (typed : Typing.ValueTyped program world value) :
    ∃ types, Typing.FieldsTyped program world value.fields types ∧
      ∀ fields, Typing.FieldsTyped program world fields types → Typing.ValueTyped program world (value.withFields fields) := by
  cases typed with
  | unit => exact ⟨[],.nil,fun _ fields => by cases fields; exact .unit⟩
  | scalar valid => exact ⟨[],.nil,fun _ fields => by cases fields; exact .scalar valid⟩
  | aggregate head fields => exact ⟨_,fields,fun _ checked => .aggregate head checked⟩
  | reference found live mode region located =>
      exact ⟨[],.nil,fun _ fields => by cases fields; exact .reference found live mode region located⟩
  | pointer bound origin => exact ⟨[],.nil,fun _ fields => by cases fields; exact .pointer bound origin⟩
  | callable selected fields => exact ⟨_,fields,fun _ checked => .callable selected checked⟩
  | operation selected => exact ⟨[],.nil,fun _ fields => by cases fields; exact .operation selected⟩
  | label => exact ⟨[],.nil,fun _ fields => by cases fields; exact .label⟩
  | continuation form => exact ⟨[],.nil,fun _ fields => by cases fields; exact .continuation form⟩
  | available found brand identity region residents =>
      exact ⟨[],.nil,fun _ fields => by cases fields; exact .available found brand identity region residents⟩
  | bindings checked brand region length distinct =>
      exact ⟨_,checked,fun _ fields => .bindings fields brand region
        (fields.length.trans (checked.length.symm.trans length)) distinct⟩

theorem Typing.ValueTyped.clear_field {program : Kernel.Program} {world : World} {value : Value} {index : Nat}
    (typed : Typing.ValueTyped program world value) (bound : index < value.fields.length) :
    Typing.ValueTyped program world (value.withFields (value.fields.set index none)) := by
  obtain ⟨types,fields,rebuild⟩ := typed.fields_model
  have inTypes : index < types.length := fields.length ▸ bound
  exact rebuild _ (fields.set (List.getElem?_eq_getElem inTypes) (fun _ impossible => by cases impossible))

theorem Typing.ValueTyped.replace_child {program : Kernel.Program} {world : World} {value child changed : Value}
    {index : Nat} (typed : Typing.ValueTyped program world value) (found : value.fields[index]? = some (some child))
    (checked : Typing.ValueTyped program world changed) (same : changed.type = child.type) :
    Typing.ValueTyped program world (value.withFields (value.fields.set index (some changed))) := by
  obtain ⟨types,fields,rebuild⟩ := typed.fields_model
  apply rebuild _ (fields.set (fields.get found).2 ?_)
  intro resident equal
  cases Option.some.inj equal
  exact ⟨checked,same⟩

end Glorious.Language
