import GloriousLanguage.Preservation
import GloriousLanguage.LayoutCoherence
import GloriousLanguage.LayoutContext

namespace Glorious.Language

/-- An array-shaped declared type is only demanded at an index the physical
array actually has: `FieldOffset.array` requires `index < count`. Every other
structurally headed container is unbounded, so the predicate is vacuous there;
for an array it is exactly the field selection the actual resolution performs. -/
def Term.FrameBound : Term → Nat → Prop
  | .array _ (.constant (.integer _ _ count)), index => index < count.toNat
  | _, _ => True

theorem Term.FrameBound.array {element : Term} {sign : Bool} {width : Width} {count : Int} {index : Nat}
    (bound : index < count.toNat) :
    Term.FrameBound (.array element (.constant (.integer sign width count))) index := bound

/-- A source equality at an ordered head where the other side is a nominal
application exhibits that nominal application. -/
theorem SameHead.nominal_shape {container : Term} {id : DeclId} {arguments : List Term}
    (head : SameHead container (.nominal id arguments)) : ∃ actual, container = .nominal id actual := by
  cases container with
  | nominal declared actual =>
      obtain ⟨idEq,_⟩ := Term.nominal.inj head
      subst idEq
      exact ⟨actual,rfl⟩
  | _ => exact absurd head (by simp only [SameHead,Term.mapChildren]; intro clash; cases clash)

theorem Equal.nominal_shape {program : Language.Program} (valid : ProgramWellFormed program)
    {context : Language.Context} (closed : context.assumptions = [])
    {container : Term} {id : DeclId} {arguments : List Term}
    (equal : Equal program context container (.nominal id arguments)) (structural : container.StructuralHead) :
    ∃ actual, container = .nominal id actual := by
  have kinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement := by
    intro requirement member; rw [closed] at member; cases member
  exact SameHead.nominal_shape ((equal.closed_definitional closed).structural_decomposition
    valid kinded structural True.intro).1

theorem FieldsLayout.length {start : Nat} {fields : List Layout} {offsets : List Nat} {stop : Nat}
    (derived : FieldsLayout start fields offsets stop) : offsets.length = fields.length := by
  induction derived with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons,ih]

theorem AggregateLayout.offsets_length {fields : List Layout} {layout : Layout}
    (derived : AggregateLayout fields layout) : layout.offsets.length = fields.length := by
  obtain ⟨_,fieldsLayout,_,_,_,_,_⟩ := derived
  exact fieldsLayout.length

theorem EnumLayout.variant_offsets {variants : List Layout} {layout : Layout}
    (derived : EnumLayout variants layout) {tag : Nat} {variant : Layout}
    (selected : variants[tag]? = some variant) :
    layout.variants[tag]? = some (variant.offsets.map (· + layout.payloadOffset)) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,rows⟩ := derived
  rw [rows,List.getElem?_map,selected]
  rfl

/-- Ordered layout lists transport along elementwise definitional conversion:
the layout judgment reads source-equal declared storage types at the same
physical layout. -/
theorem ListRel.layout_convert {program : Program} {context : Context} {types others : List Term}
    {layouts : List Layout} (related : ListRel (DefinitionallyEqual program context) types others)
    (located : ListRel (LayoutOf program context) types layouts) :
    ListRel (LayoutOf program context) others layouts := by
  induction related generalizing layouts with
  | nil => cases located; exact .nil
  | cons head tail ih =>
    cases located with
    | cons derived rest => exact .cons (.alias (.definitional head) derived) (ih rest)

def NominalRealization (program : Language.Program) (context : Language.Context) (layout : Layout)
    (data : DataDefinition) (tag : Nat) (types : List Term) : Prop :=
  ∃ fieldLayouts offsets,
    ListRel (LayoutOf program context) types fieldLayouts ∧
    offsets.length = types.length ∧
    (data.isEnum = false → layout.offsets = offsets) ∧
    (data.isEnum = true → layout.variants[tag]? = some offsets)

theorem LayoutOf.nominal_realization {program : Language.Program} (valid : ProgramWellFormed program)
    {context : Language.Context} (closed : context.assumptions = [])
    {id : DeclId} {arguments : List Term} {tag : Nat} {data : DataDefinition} {variant : VariantDefinition}
    {substitution : Substitution} {types : List Term}
    {container : Term} {layout : Layout} (derived : LayoutOf program context container layout)
    (found : program.data id = some data) (selected : data.variants[tag]? = some variant)
    (instantiated : Instantiates data.generics arguments substitution)
    (graph : ListRel (Substitutes substitution) (variant.fields.map (·.type)) types) :
    Equal program context container (.nominal id arguments) →
      NominalRealization program context layout data tag types := by
  have kinded : ∀ requirement ∈ context.assumptions, ConstraintKinded program context requirement := by
    intro requirement member; rw [closed] at member; cases member
  refine LayoutOf.rec
    (motive_1 := fun container layout _ =>
      Equal program context container (.nominal id arguments) → NominalRealization program context layout data tag types)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun container layout _ =>
      Equal program context container (.nominal id arguments) → NominalRealization program context layout data tag types)
    (motive_4 := fun _ _ _ => True) (motive_5 := fun _ _ _ => True) (motive_6 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    derived
  · intro equal; exfalso
    rcases Equal.nominal_shape valid closed equal trivial with ⟨actual,same⟩
    exact nomatch same
  · intro scalar validScalar equal; exfalso
    rcases Equal.nominal_shape valid closed equal trivial with ⟨actual,same⟩
    exact nomatch same
  · intro mode region referent equal; exfalso
    rcases Equal.nominal_shape valid closed equal trivial with ⟨actual,same⟩
    exact nomatch same
  · intro mode referent equal; exfalso
    rcases Equal.nominal_shape valid closed equal trivial with ⟨actual,same⟩
    exact nomatch same
  · intro fields layouts layout related aggregate ih equal; exfalso
    rcases Equal.nominal_shape valid closed equal trivial with ⟨actual,same⟩
    exact nomatch same
  · intro declared arguments fields layouts layout declaredFields related aggregate ih equal; exfalso
    rcases Equal.nominal_shape valid closed equal trivial with ⟨actual,same⟩
    exact nomatch same
  · intro brand argument answer effects quantity equal; exfalso
    rcases Equal.nominal_shape valid closed equal trivial with ⟨actual,same⟩
    exact nomatch same
  · intro brand region result equal; exfalso
    rcases Equal.nominal_shape valid closed equal trivial with ⟨actual,same⟩
    exact nomatch same
  · intro brand region residents equal; exfalso
    rcases Equal.nominal_shape valid closed equal trivial with ⟨actual,same⟩
    exact nomatch same
  · intro brand region fields layouts layout related aggregate ih equal; exfalso
    rcases Equal.nominal_shape valid closed equal trivial with ⟨actual,same⟩
    exact nomatch same
  · intro brand region residents layouts layout related aggregate ih equal; exfalso
    rcases Equal.nominal_shape valid closed equal trivial with ⟨actual,same⟩
    exact nomatch same
  · intro element sign width length elementLayout layout nonnegative range elementDerived arrayDerived ih equal
    exfalso
    rcases Equal.nominal_shape valid closed equal trivial with ⟨actual,same⟩
    exact nomatch same
  · intro declared data' arguments' substitution' variantTypes variantLayouts layout' found'
    intro representation instantiated' relatedVariants relatedLayouts enumOrRecord sizeBound ih
    intro equal
    have defEq := equal.closed_definitional closed
    obtain ⟨head,argumentsRelated⟩ := defEq.structural_decomposition valid kinded True.intro True.intro
    have idEq : declared = id := (Term.nominal.inj head).1
    subst idEq
    have dataEq : data = data' := Option.some.inj (found.symm.trans found')
    subst dataEq
    have tagBound : tag < data.variants.length := (List.getElem?_eq_some_iff.mp selected).1
    have typesBound : tag < variantTypes.length := by
      have lengths := relatedVariants.length_eq
      omega
    have typesAt : variantTypes[tag]? = some variantTypes[tag] := List.getElem?_eq_getElem typesBound
    have relatedType : ListRel (Substitutes substitution') (variant.fields.map (·.type)) variantTypes[tag] :=
      ListRel.at relatedVariants selected typesAt
    have layoutsBound : tag < variantLayouts.length := by
      have lengths := relatedLayouts.length_eq
      omega
    have layoutsAt : variantLayouts[tag]? = some variantLayouts[tag] := List.getElem?_eq_getElem layoutsBound
    have tables : SubstitutionsConvertible program context substitution' substitution :=
      instantiated'.convertible_tables instantiated argumentsRelated
    have typesRelated : ListRel (DefinitionallyEqual program context) variantTypes[tag] types :=
      ListRel.substituted_conversion relatedType graph tables
    have hierarchy : FieldsHaveLayout program context variantTypes[tag] variantLayouts[tag] :=
      ListRel.at relatedLayouts typesAt layoutsAt
    cases hierarchy with
    | @fields fieldTypes fieldLayouts targetLayout relatedFields aggregate =>
    have fieldLayoutsRelated : ListRel (LayoutOf program context) types fieldLayouts :=
      ListRel.layout_convert typesRelated relatedFields
    rcases enumOrRecord with ⟨isEnum,enumLayout⟩ | ⟨notEnum,singleLayout⟩
    · have rows := enumLayout.variant_offsets layoutsAt
      refine ⟨fieldLayouts,variantLayouts[tag].offsets.map (· + layout'.payloadOffset),fieldLayoutsRelated,?_,?_,?_⟩
      · rw [List.length_map,aggregate.offsets_length,← relatedFields.length_eq]
        exact typesRelated.length_eq
      · intro impossible
        rw [isEnum] at impossible
        exact nomatch impossible
      · intro _
        exact rows
    · have tagZero : tag = 0 := by
        have bound : tag < 1 := by simpa [singleLayout] using layoutsBound
        omega
      have sameLayout : variantLayouts[tag] = layout' := by simp [tagZero,singleLayout]
      have aggregateLayout : AggregateLayout fieldLayouts layout' := by
        simpa only [sameLayout] using aggregate
      refine ⟨fieldLayouts,layout'.offsets,fieldLayoutsRelated,?_,?_,?_⟩
      · rw [aggregateLayout.offsets_length,← relatedFields.length_eq]
        exact typesRelated.length_eq
      · intro _
        rfl
      · intro impossible
        rw [impossible] at notEnum
        exact nomatch notEnum
  · intro declared data' arguments' substitution' variant' fields types' layouts distinguished represented
    intro layout' found' representation notEnum singleVariant fieldsEq instantiated' graph' relatedLayouts
    intro selected' representedCompatible positive zeros ihLayout
    intro equal
    have defEq := equal.closed_definitional closed
    obtain ⟨head,argumentsRelated⟩ := defEq.structural_decomposition valid kinded True.intro True.intro
    have idEq : declared = id := (Term.nominal.inj head).1
    subst idEq
    have dataEq : data = data' := Option.some.inj (found.symm.trans found')
    subst dataEq
    have tagBound : tag < data.variants.length := (List.getElem?_eq_some_iff.mp selected).1
    have tagZero : tag = 0 := by
      have bound : tag < 1 := by simpa [singleVariant] using tagBound
      omega
    have variantEq : variant = variant' := by
      have present : data.variants[tag]? = some variant' := by simp [tagZero,singleVariant]
      exact Option.some.inj (selected.symm.trans present)
    have graphRelated : ListRel (Substitutes substitution') (variant.fields.map (·.type)) types' := by
      simpa only [fieldsEq,← variantEq] using graph'
    have typesRelated : ListRel (DefinitionallyEqual program context) types' types :=
      ListRel.substituted_conversion graphRelated graph
        (instantiated'.convertible_tables instantiated argumentsRelated)
    have fieldLayoutsRelated : ListRel (LayoutOf program context) types layouts :=
      ListRel.layout_convert typesRelated relatedLayouts
    refine ⟨layouts,List.replicate types.length 0,fieldLayoutsRelated,List.length_replicate,?_,?_⟩
    · intro _
      have lengths : fields.length = types.length := by
        rw [fieldsEq,← variantEq]
        simpa [List.length_map] using graph.length_eq
      rw [zeros,lengths]
    · intro impossible
      rw [impossible] at notEnum
      exact nomatch notEnum
  · intro declared data' arguments' layout' found' representation compatible ih; exact ih
  · intro a b layout' equal' inner ih equalQueried
    exact ih (equal'.trans equalQueried)
  · intros; exact True.intro
  · intro cscalar mapping equal; exfalso
    rcases Equal.nominal_shape valid closed equal trivial with ⟨actual,same⟩
    exact nomatch same
  · intro mode referent equal; exfalso
    rcases Equal.nominal_shape valid closed equal trivial with ⟨actual,same⟩
    exact nomatch same
  · intro declared data' arguments' substitution' variant' types' layouts layout' found'
    intro representation notEnum singleVariant instantiated' graph' relatedLayouts recordLayout ihList
    intro equal
    have defEq := equal.closed_definitional closed
    obtain ⟨head,argumentsRelated⟩ := defEq.structural_decomposition valid kinded True.intro True.intro
    have idEq : declared = id := (Term.nominal.inj head).1
    subst idEq
    have dataEq : data = data' := Option.some.inj (found.symm.trans found')
    subst dataEq
    have tagBound : tag < data.variants.length := (List.getElem?_eq_some_iff.mp selected).1
    have tagZero : tag = 0 := by
      have bound : tag < 1 := by simpa [singleVariant] using tagBound
      omega
    have variantEq : variant = variant' := by
      have present : data.variants[tag]? = some variant' := by simp [tagZero,singleVariant]
      exact Option.some.inj (selected.symm.trans present)
    have graphRelated : ListRel (Substitutes substitution') (variant.fields.map (·.type)) types' := by
      simpa only [← variantEq] using graph'
    have typesRelated : ListRel (DefinitionallyEqual program context) types' types :=
      ListRel.substituted_conversion graphRelated graph
        (instantiated'.convertible_tables instantiated argumentsRelated)
    have fieldLayoutsRelated : ListRel (LayoutOf program context) types layouts :=
      ListRel.layout_convert typesRelated (relatedLayouts.imp (fun _ _ compatible => compatible.layoutOf))
    refine ⟨layouts,layout'.offsets,fieldLayoutsRelated,?_,?_,?_⟩
    · rw [recordLayout.2.2.2.1,← relatedLayouts.length_eq,typesRelated.length_eq]
    · intro _; rfl
    · intro impossible
      rw [notEnum] at impossible
      exact nomatch impossible
  · intro declared data' arguments' substitution' sign width found' instantiated' representation
    intro isEnum nonempty mapping empty range
    intro equal
    have defEq := equal.closed_definitional closed
    obtain ⟨head,argumentsRelated⟩ := defEq.structural_decomposition valid kinded True.intro True.intro
    have idEq : declared = id := (Term.nominal.inj head).1
    subst idEq
    have dataEq : data = data' := Option.some.inj (found.symm.trans found')
    subst dataEq
    have member : variant ∈ data.variants := List.mem_of_getElem? selected
    have emptyFields : variant.fields = [] := empty variant member
    have typesNil : types = [] := by
      have mapped := graph.substitutes_eq_map
      simpa only [emptyFields,List.map_nil] using mapped
    refine ⟨[],[],?_,?_,?_,?_⟩
    · rw [typesNil]; exact .nil
    · rw [typesNil]; rfl
    · intro impossible
      rw [isEnum] at impossible
    · intro _
      have bound : tag < data.variants.length := (List.getElem?_eq_some_iff.mp selected).1
      have present : (List.replicate data.variants.length [])[tag]? = some ([] : List Nat) := by
        rw [List.getElem?_eq_getElem (by simpa using bound)]
        simp
      simpa [typesNil] using present
  · intro declared data' arguments' variant' substitution' types' layouts index represented
    intro representation layout' derived' found' representationEq singleVariant instantiated' graph' relatedLayouts
    intro selected' representedCompatible positive sizeEq alignmentEq zeros
    intro ihLayout ihList ihRepresented
    exact ihLayout
  · intro a b layout' equal' inner ih equalQueried
    exact ih (equal'.trans equalQueried)
  · intros; exact True.intro
  · intro a b as bs head tail ihHead ihTail; exact True.intro
  · intros; exact True.intro
  · intro a b as bs head tail ihHead ihTail; exact True.intro
  · intros; exact True.intro
  · intro a b as bs head tail ihHead ihTail; exact True.intro


theorem SameHead.tuple_shape {container : Term} {fields : List Term}
    (head : SameHead container (.tuple fields)) : ∃ actual, container = .tuple actual := by
  cases container with
  | tuple actual => exact ⟨actual,rfl⟩
  | _ => exact absurd head (by simp only [SameHead,Term.mapChildren]; intro clash; cases clash)

theorem SameHead.array_shape {container : Term} {element length : Term}
    (head : SameHead container (.array element length)) : ∃ actual actualLength, container = .array actual actualLength := by
  cases container with
  | array actual actualLength => exact ⟨actual,actualLength,rfl⟩
  | _ => exact absurd head (by simp only [SameHead,Term.mapChildren]; intro clash; cases clash)

/-- A source field step is impossible at a container whose ordered head is not one
of the three aggregate heads the field judgment can select. -/
theorem FieldType.absurd {program : Kernel.Program} {context : Language.Context}
    {container selected : Term} {index : Nat} {child : Term}
    (head : SameHead container selected) (physical : Typing.FieldType program.declarations context selected index child true)
    (tupleImpossible : ∀ (fields : List Term), container = .tuple fields → False)
    (arrayImpossible : ∀ (element length : Term), container = .array element length → False)
    (nominalImpossible : ∀ (id : DeclId) (actual : List Term), container = .nominal id actual → False) : False := by
  rcases physical with ⟨fields,same,_⟩ | ⟨element,length,same,_⟩ |
    ⟨id,arguments,data,variant,substitution,types,same,found,notEnum,variants,instantiated,graph,selected,visibility⟩
  · rcases SameHead.tuple_shape (same ▸ head) with ⟨actual,shape⟩
    exact tupleImpossible actual shape
  · rcases SameHead.array_shape (same ▸ head) with ⟨element',length',shape⟩
    exact arrayImpossible element' length' shape
  · rcases SameHead.nominal_shape (same ▸ head) with ⟨actual,shape⟩
    exact nominalImpossible id actual shape

/-- The resident's own actual head at a nominal application: the stored value is a
constructor of that data's variant, so its constructor identity is the variant's. -/
theorem Typing.ValueTyped.constructor_head {program : Kernel.Program} {world : World} {value : Value}
    (typed : Typing.ValueTyped program world value) {id : DeclId} {arguments : List Term}
    {data : DataDefinition} {variant : VariantDefinition}
    (found : program.declarations.data id = some data) (single : data.variants = [variant])
    (same : value.type = .nominal id arguments) : value.head = .constructor variant.header.id := by
  cases value with
  | resident owner actual head live fields resources =>
    cases typed with
    | aggregate constructed _ =>
      rcases constructed with ⟨impossible,_,_⟩ | ⟨_,_,_,_,impossible,_⟩ |
        ⟨who,args,data',constructor,substitution,sameNominal,variantShape,headShape,constructed,instantiated,graph⟩
      · exact nomatch (impossible.symm.trans same)
      · exact nomatch (impossible.symm.trans same)
      · have idEq : id = data'.header.id := (Term.nominal.inj (same.symm.trans sameNominal)).1
        have dataEq : data' = data := (Option.some.inj ((idEq ▸ found).symm.trans constructed.1)).symm
        have member : constructor ∈ data.variants := dataEq ▸ constructed.2.1
        rw [single] at member
        have variantEq : constructor = variant := List.mem_singleton.mp member
        change head = .constructor variant.header.id
        rw [headShape,← constructed.2.2,← variantEq]
    | unit => cases same
    | scalar _ => cases same
    | reference _ _ _ _ _ => cases same
    | pointer _ _ => cases same
    | callable _ _ => cases same
    | operation _ => cases same
    | label => cases same
    | continuation form =>
      obtain ⟨_,_,_,_,typeEq⟩ := form
      exact nomatch (typeEq.symm.trans same)
    | available _ _ _ _ _ => cases same
    | bindings _ _ _ _ _ => cases same


theorem DefinitionallyEqual.layout_context {program : Program} {module : ModuleId} {unsafeAllowed : Bool}
    {left right : Term} (equal : DefinitionallyEqual program ⟨[],[],0,module,unsafeAllowed,{}⟩ left right) :
    DefinitionallyEqual program ⟨[],[],0,default,false,{}⟩ left right :=
  (Equal.cut_same_domain (target := ⟨[],[],0,default,false,{}⟩) (.definitional equal) rfl rfl rfl
    (by intro requirement member; cases member)).closed_definitional rfl

theorem Program.data_header {program : Program} {id : DeclId} {data : DataDefinition}
    (found : program.data id = some data) : data.header.id = id := by
  have lookup := Program.data_lookup found
  have matching := List.find?_some lookup
  change (data.header.id.package == id.package && data.header.id.serial == id.serial) = true at matching
  simp only [Bool.and_eq_true,beq_iff_eq] at matching
  cases identity : data.header.id
  cases id
  simp_all

/-- The physical field step at a nominal container, from the container's actual
admitted layout and the resident constructor actually stored there. -/
theorem FieldOffset.nominal_step {program : Kernel.Program} {world : World} {address : Address}
    {module : ModuleId} {unsafeAllowed : Bool} {container selected : Term} {layout : Layout}
    {idU : DeclId} {argumentsU : List Term} {dataU : DataDefinition} {variantU : VariantDefinition}
    {substitutionU : Substitution} {typesU : List Term} {index : Nat} {child : Term}
    {fieldLayouts : List Layout} {offsets : List Nat}
    (_valid : ProgramWellFormed program.declarations) (typed : Typing.WorldTyped program world)
    {value : Value} (stored : world.Stores address value)
    (same : selected = .nominal idU argumentsU) (sameType : value.type = selected)
    (foundU : program.declarations.data idU = some dataU) (notEnumU : dataU.isEnum = false)
    (variantsU : dataU.variants = [variantU]) (instantiatedU : Instantiates dataU.generics argumentsU substitutionU)
    (graphU : ListRel (Substitutes substitutionU) (variantU.fields.map (·.type)) typesU)
    (selectedU : typesU[index]? = some child)
    (equal : Equal program.declarations ⟨[],[],0,module,unsafeAllowed,{}⟩ container (.nominal idU argumentsU))
    (derived : LayoutOf program.declarations ⟨[],[],0,module,unsafeAllowed,{}⟩ container layout)
    (fieldLayoutsRelated : ListRel (LayoutOf program.declarations ⟨[],[],0,module,unsafeAllowed,{}⟩) typesU fieldLayouts)
    (offsetsLength : offsets.length = typesU.length) (offsetEq : layout.offsets = offsets) :
    (∃ offset, FieldOffset program.declarations world address selected index child offset) ∧
      (∃ childLayout, LayoutOf program.declarations ⟨[],[],0,module,unsafeAllowed,{}⟩ child childLayout) := by
  have indexBound : index < typesU.length := (List.getElem?_eq_some_iff.mp selectedU).1
  have offsetsBound : index < offsets.length := by rw [offsetsLength]; exact indexBound
  have layoutAt : layout.offsets[index]? = some offsets[index] := by
    rw [offsetEq]
    exact List.getElem?_eq_getElem offsetsBound
  have nominalLayout : LayoutOf program.declarations ⟨[],[],0,dataU.header.module,false,{}⟩
      (.nominal idU argumentsU) layout := (LayoutOf.alias equal derived).runtime_context
  have headEq : value.head = .constructor variantU.header.id :=
    Typing.ValueTyped.constructor_head (World.stores_typed (Typing.WorldTyped.roots typed) stored)
      foundU variantsU (sameType.trans same)
  have headerEq : dataU.header.id = idU := Program.data_header foundU
  have constructorAt : program.declarations.Constructor variantU.header.id dataU variantU :=
    ⟨by rw [headerEq]; exact foundU, by rw [variantsU]; exact List.mem_cons_self, rfl⟩
  have fieldOffset : FieldOffset program.declarations world address selected index child offsets[index] := by
    rw [same]
    exact .nominal constructorAt headerEq instantiatedU graphU selectedU nominalLayout stored headEq
      (Or.inl ⟨notEnumU,layoutAt⟩)
  have childBound : index < fieldLayouts.length := by rw [← fieldLayoutsRelated.length_eq]; exact indexBound
  have childAt : LayoutOf program.declarations ⟨[],[],0,module,unsafeAllowed,{}⟩ child fieldLayouts[index] :=
    ListRel.at fieldLayoutsRelated selectedU (List.getElem?_eq_getElem childBound)
  exact ⟨⟨offsets[index],fieldOffset⟩,⟨fieldLayouts[index],childAt⟩⟩


namespace Typing

/-- A resident's array type is counted by a constant: actual construction
writes the arity as an integer literal (`Execution.ConstructorHead`), so the
declared length of an occupied array storage is syntactically that literal -
never an unexpanded alias or projection term. This is read from the resident's
own typing, not from the layout derivation, which is exactly why a physically
occupied array needs no canonical-form premise about its declared type. -/
theorem ValueTyped.array_count {program : Kernel.Program} {world : World} {value : Value}
    (typed : Typing.ValueTyped program world value) {element length : Term}
    (shape : value.type = .array element length) :
    ∃ sign width count, length = .constant (.integer sign width count) ∧ 0 ≤ count := by
  cases value with
  | resident owner type head live fields resources =>
    change type = .array element length at shape
    cases typed with
    | unit => cases shape
    | scalar _ => cases shape
    | aggregate constructed _ =>
      rcases constructed with ⟨same,_,_⟩ | ⟨element',sign,width,count,same,_,_,countEq,_⟩ |
        ⟨id,arguments,data,constructor,substitution,same,_,_,_,_⟩
      · exact nomatch (same.symm.trans shape)
      · have lengthEq : length = .constant (.integer sign width count) :=
          (Term.array.inj (same.symm.trans shape)).2.symm
        exact ⟨sign,width,count,lengthEq,by rw [countEq]; exact Int.natCast_nonneg _⟩
      · exact nomatch (same.symm.trans shape)
    | reference _ _ _ _ _ => cases shape
    | pointer _ _ => cases shape
    | callable _ _ => cases shape
    | operation _ => cases shape
    | label => cases shape
    | continuation form => obtain ⟨_,_,_,_,typeEq⟩ := form; exact nomatch (typeEq.symm.trans shape)
    | available _ _ _ _ _ => cases shape
    | bindings _ _ _ _ _ => cases shape

end Typing

/-- Every source field step of an admitted declared storage type at an occupied
address is an actual physical field offset, and the selected child carries its own
admitted layout. The container is the type the addressed resident actually has,
read through the same source equality the caller holds. -/
theorem LayoutOf.field_realization {program : Kernel.Program} {world : World} {address : Address}
    {module : ModuleId} {unsafeAllowed : Bool} {fieldContext : Language.Context}
    (valid : ProgramWellFormed program.declarations) (typed : Typing.WorldTyped program world)
    {value : Value} (stored : world.Stores address value)
    {container : Term} {layout : Layout}
    (derived : LayoutOf program.declarations ⟨[],[],0,module,unsafeAllowed,{}⟩ container layout) :
    ∀ (selected : Term), Equal program.declarations ⟨[],[],0,module,unsafeAllowed,{}⟩ container selected →
      selected.StructuralHead → value.type = selected →
      ∀ (index : Nat) (child : Term),
        Typing.FieldType program.declarations fieldContext selected index child true →
        selected.FrameBound index →
        (∃ offset, FieldOffset program.declarations world address selected index child offset) ∧
          (∃ childLayout, LayoutOf program.declarations ⟨[],[],0,module,unsafeAllowed,{}⟩ child childLayout) := by
  have closed : (⟨[],[],0,module,unsafeAllowed,{}⟩ : Language.Context).assumptions = [] := rfl
  have valueTyped : Typing.ValueTyped program world value :=
    World.stores_typed (Typing.WorldTyped.roots typed) stored
  have kinded : ∀ requirement ∈ (⟨[],[],0,module,unsafeAllowed,{}⟩ : Language.Context).assumptions,
      ConstraintKinded program.declarations ⟨[],[],0,module,unsafeAllowed,{}⟩ requirement := by
    intro requirement member; rw [closed] at member; cases member
  refine LayoutOf.rec
    (motive_1 := fun container layout _ => ∀ (selected : Term),
      Equal program.declarations ⟨[],[],0,module,unsafeAllowed,{}⟩ container selected →
      selected.StructuralHead → value.type = selected →
      ∀ (index : Nat) (child : Term),
        Typing.FieldType program.declarations fieldContext selected index child true →
        selected.FrameBound index →
        (∃ offset, FieldOffset program.declarations world address selected index child offset) ∧
          (∃ childLayout, LayoutOf program.declarations ⟨[],[],0,module,unsafeAllowed,{}⟩ child childLayout))
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ => True)
    (motive_4 := fun _ _ _ => True) (motive_5 := fun _ _ _ => True) (motive_6 := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ 
    derived
  · intro selected equal structural sameType index child physical bound
    have head := ((equal.closed_definitional closed).structural_decomposition valid kinded True.intro structural).1
    exfalso
    exact FieldType.absurd head physical (fun fields h => by cases h) (fun element length h => by cases h)
      (fun i actual h => by cases h)
  · intro scalar validScalar selected equal structural sameType index child physical bound
    have head := ((equal.closed_definitional closed).structural_decomposition valid kinded True.intro structural).1
    exfalso
    exact FieldType.absurd head physical (fun fields h => by cases h) (fun element length h => by cases h)
      (fun i actual h => by cases h)
  · intro mode region referent selected equal structural sameType index child physical bound
    have head := ((equal.closed_definitional closed).structural_decomposition valid kinded True.intro structural).1
    exfalso
    exact FieldType.absurd head physical (fun fields h => by cases h) (fun element length h => by cases h)
      (fun i actual h => by cases h)
  · intro mode referent selected equal structural sameType index child physical bound
    have head := ((equal.closed_definitional closed).structural_decomposition valid kinded True.intro structural).1
    exfalso
    exact FieldType.absurd head physical (fun fields h => by cases h) (fun element length h => by cases h)
      (fun i actual h => by cases h)
  · intro fields layouts ruleLayout related aggregate ih selected equal structural sameType index child physical bound
    have defEq := equal.closed_definitional closed
    obtain ⟨head,children⟩ := defEq.structural_decomposition valid kinded True.intro structural
    rcases physical with ⟨fieldsU,same,selectedAt⟩ | ⟨elementU,lengthU,same,fieldEq⟩ |
      ⟨idU,argumentsU,dataU,variantU,substitutionU,typesU,same,foundU,notEnumU,variantsU,instantiatedU,graphU,selectedU,visibility⟩
    · have children' : ListRel (DefinitionallyEqual program.declarations ⟨[],[],0,module,unsafeAllowed,{}⟩)
          fields fieldsU := by
        cases same
        exact children
      have layoutsDefault : ListRel (LayoutOf program.declarations ⟨[],[],0,default,false,{}⟩) fields layouts :=
        related.imp (fun _ _ located => located.runtime_context)
      have layoutsU : ListRel (LayoutOf program.declarations ⟨[],[],0,default,false,{}⟩) fieldsU layouts :=
        ListRel.layout_convert (children'.imp (fun _ _ equal => equal.layout_context)) layoutsDefault
      have indexBound : index < layouts.length := by
        have bound' : index < fieldsU.length := (List.getElem?_eq_some_iff.mp selectedAt).1
        have first := children'.length_eq
        have second := related.length_eq
        omega
      have offsetsBound : index < ruleLayout.offsets.length := by
        rw [aggregate.offsets_length]; exact indexBound
      have offsetsAt : ruleLayout.offsets[index]? = some ruleLayout.offsets[index] :=
        List.getElem?_eq_getElem offsetsBound
      have fieldOffset : FieldOffset program.declarations world address selected index child
          ruleLayout.offsets[index] := by
        rw [same]
        exact .tuple selectedAt layoutsU aggregate offsetsAt
      have childAt : LayoutOf program.declarations ⟨[],[],0,default,false,{}⟩ child layouts[index] :=
        ListRel.at layoutsU selectedAt (List.getElem?_eq_getElem indexBound)
      exact ⟨⟨ruleLayout.offsets[index],fieldOffset⟩,⟨layouts[index],childAt.runtime_context⟩⟩
    · exfalso
      rcases SameHead.array_shape (same ▸ head) with ⟨a,l,shape⟩
      exact nomatch shape
    · exfalso
      rcases SameHead.nominal_shape (same ▸ head) with ⟨actual,shape⟩
      exact nomatch shape
  · intro declared arguments fields layouts ruleLayout declaredFields related aggregate ih selected equal structural
      sameType index child physical bound
    have head := ((equal.closed_definitional closed).structural_decomposition valid kinded True.intro structural).1
    exfalso
    exact FieldType.absurd head physical (fun fields h => by cases h) (fun element length h => by cases h)
      (fun i actual h => by cases h)
  · intro brand argument answer effects quantity selected equal structural sameType index child physical bound
    have head := ((equal.closed_definitional closed).structural_decomposition valid kinded True.intro structural).1
    exfalso
    exact FieldType.absurd head physical (fun fields h => by cases h) (fun element length h => by cases h)
      (fun i actual h => by cases h)
  · intro brand region result selected equal structural sameType index child physical bound
    have head := ((equal.closed_definitional closed).structural_decomposition valid kinded True.intro structural).1
    exfalso
    exact FieldType.absurd head physical (fun fields h => by cases h) (fun element length h => by cases h)
      (fun i actual h => by cases h)
  · intro brand region residents selected equal structural sameType index child physical bound
    have head := ((equal.closed_definitional closed).structural_decomposition valid kinded True.intro structural).1
    exfalso
    exact FieldType.absurd head physical (fun fields h => by cases h) (fun element length h => by cases h)
      (fun i actual h => by cases h)
  · intro brand region fields layouts ruleLayout related aggregate ih selected equal structural sameType index child
      physical bound
    have head := ((equal.closed_definitional closed).structural_decomposition valid kinded True.intro structural).1
    exfalso
    exact FieldType.absurd head physical (fun fields h => by cases h) (fun element length h => by cases h)
      (fun i actual h => by cases h)
  · intro brand region residents layouts ruleLayout related aggregate ih selected equal structural sameType index child
      physical bound
    have head := ((equal.closed_definitional closed).structural_decomposition valid kinded True.intro structural).1
    exfalso
    exact FieldType.absurd head physical (fun fields h => by cases h) (fun element length h => by cases h)
      (fun i actual h => by cases h)
  · intro element sign width length elementLayout ruleLayout nonnegative range elementDerived arrayDerived ih
    intro selected equal structural sameType index child physical bound
    have defEq := equal.closed_definitional closed
    obtain ⟨head,children⟩ := defEq.structural_decomposition valid kinded True.intro structural
    rcases physical with ⟨fieldsU,same,selectedAt⟩ | ⟨elementU,lengthU,same,fieldEq⟩ |
      ⟨idU,argumentsU,dataU,variantU,substitutionU,typesU,same,foundU,notEnumU,variantsU,instantiatedU,graphU,selectedU,visibility⟩
    · exfalso
      rcases SameHead.tuple_shape (same ▸ head) with ⟨actual,shape⟩
      exact nomatch shape
    · have elementEq : DefinitionallyEqual program.declarations ⟨[],[],0,module,unsafeAllowed,{}⟩ element elementU := by
        have childrenArray : ListRel (DefinitionallyEqual program.declarations ⟨[],[],0,module,unsafeAllowed,{}⟩)
            [element,Term.constant (.integer sign width length)] [elementU,lengthU] := by
          cases same
          exact children
        cases childrenArray with
        | cons elementEq _ => exact elementEq
      obtain ⟨countSign,countWidth,count,lengthEq,countNonneg⟩ :=
        valueTyped.array_count (sameType.trans same)
      have elementLayoutU : LayoutOf program.declarations ⟨[],[],0,module,unsafeAllowed,{}⟩ elementU elementLayout :=
        .alias (.definitional elementEq) elementDerived
      have bound' : index < count.toNat := by
        rw [same,lengthEq] at bound
        exact bound
      refine ⟨⟨index * alignUp elementLayout.size elementLayout.alignment,?_⟩,⟨elementLayout,?_⟩⟩
      · rw [same,lengthEq,fieldEq]
        exact .array countNonneg bound' elementLayoutU.runtime_context
      · rw [fieldEq]
        exact elementLayoutU
    · exfalso
      rcases SameHead.nominal_shape (same ▸ head) with ⟨actual,shape⟩
      exact nomatch shape
  · intro declared data arguments substitution variantTypes variantLayouts ruleLayout found representation instantiated
      relatedVariants relatedLayouts enumOrRecord sizeBound ih
    intro selected equal structural sameType index child physical bound
    have defEq := equal.closed_definitional closed
    obtain ⟨head,children⟩ := defEq.structural_decomposition valid kinded True.intro structural
    rcases physical with ⟨fieldsU,same,selectedAt⟩ | ⟨elementU,lengthU,same,fieldEq⟩ |
      ⟨idU,argumentsU,dataU,variantU,substitutionU,typesU,same,foundU,notEnumU,variantsU,instantiatedU,graphU,selectedU,visibility⟩
    · exfalso
      rcases SameHead.tuple_shape (same ▸ head) with ⟨actual,shape⟩
      exact nomatch shape
    · exfalso
      rcases SameHead.array_shape (same ▸ head) with ⟨a,l,shape⟩
      exact nomatch shape
    · have nominalDerived : LayoutOf program.declarations ⟨[],[],0,module,unsafeAllowed,{}⟩
          (.nominal declared arguments) ruleLayout :=
        .nominal found representation instantiated relatedVariants relatedLayouts enumOrRecord sizeBound
      obtain ⟨fieldLayouts,offsets,fieldLayoutsRelated,offsetsLength,offsetEq,variantFact⟩ :=
        LayoutOf.nominal_realization (tag := 0) valid closed nominalDerived foundU (by rw [variantsU]; rfl)
          instantiatedU graphU (same ▸ equal)
      exact FieldOffset.nominal_step valid typed stored same sameType foundU notEnumU variantsU instantiatedU graphU
        selectedU (same ▸ equal) nominalDerived fieldLayoutsRelated offsetsLength (offsetEq notEnumU)
  · intro declared data arguments substitution variant fields types layouts distinguished represented ruleLayout found
      representation notEnum singleVariant fieldsEq instantiated graph relatedLayouts selected representedCompatible
      zeros ihLayout ihList
    intro queried equal structural sameType index child physical bound
    have defEq := equal.closed_definitional closed
    obtain ⟨head,children⟩ := defEq.structural_decomposition valid kinded True.intro structural
    rcases physical with ⟨fieldsU,same,selectedAt⟩ | ⟨elementU,lengthU,same,fieldEq⟩ |
      ⟨idU,argumentsU,dataU,variantU,substitutionU,typesU,same,foundU,notEnumU,variantsU,instantiatedU,graphU,selectedU,visibility⟩
    · exfalso
      rcases SameHead.tuple_shape (same ▸ head) with ⟨actual,shape⟩
      exact nomatch shape
    · exfalso
      rcases SameHead.array_shape (same ▸ head) with ⟨a,l,shape⟩
      exact nomatch shape
    · have transparentDerived : LayoutOf program.declarations ⟨[],[],0,module,unsafeAllowed,{}⟩
          (.nominal declared arguments) ruleLayout :=
        .transparent found representation notEnum singleVariant fieldsEq instantiated graph relatedLayouts selected
          representedCompatible zeros ihLayout
      obtain ⟨fieldLayouts,offsets,fieldLayoutsRelated,offsetsLength,offsetEq,variantFact⟩ :=
        LayoutOf.nominal_realization (tag := 0) valid closed transparentDerived foundU (by rw [variantsU]; rfl)
          instantiatedU graphU (same ▸ equal)
      exact FieldOffset.nominal_step valid typed stored same sameType foundU notEnumU variantsU instantiatedU graphU
        selectedU (same ▸ equal) transparentDerived fieldLayoutsRelated offsetsLength (offsetEq notEnumU)
  · intro declared data arguments ruleLayout found representation compatible ih
    intro selected equal structural sameType index child physical bound
    have defEq := equal.closed_definitional closed
    obtain ⟨head,children⟩ := defEq.structural_decomposition valid kinded True.intro structural
    rcases physical with ⟨fieldsU,same,selectedAt⟩ | ⟨elementU,lengthU,same,fieldEq⟩ |
      ⟨idU,argumentsU,dataU,variantU,substitutionU,typesU,same,foundU,notEnumU,variantsU,instantiatedU,graphU,selectedU,visibility⟩
    · exfalso
      rcases SameHead.tuple_shape (same ▸ head) with ⟨actual,shape⟩
      exact nomatch shape
    · exfalso
      rcases SameHead.array_shape (same ▸ head) with ⟨a,l,shape⟩
      exact nomatch shape
    · have cDerived : LayoutOf program.declarations ⟨[],[],0,module,unsafeAllowed,{}⟩
          (.nominal declared arguments) ruleLayout :=
        .cRepresentation found representation compatible
      obtain ⟨fieldLayouts,offsets,fieldLayoutsRelated,offsetsLength,offsetEq,variantFact⟩ :=
        LayoutOf.nominal_realization (tag := 0) valid closed cDerived foundU (by rw [variantsU]; rfl)
          instantiatedU graphU (same ▸ equal)
      exact FieldOffset.nominal_step valid typed stored same sameType foundU notEnumU variantsU instantiatedU graphU
        selectedU (same ▸ equal) cDerived fieldLayoutsRelated offsetsLength (offsetEq notEnumU)
  · intro a b ruleLayout previous inner ih selected equal structural sameType index child physical bound
    exact ih selected (previous.trans equal) structural sameType index child physical bound
  · intros; exact True.intro
  · intros; exact True.intro
  · intros; exact True.intro
  · intros; exact True.intro
  · intros; exact True.intro
  · intros; exact True.intro
  · intros; exact True.intro
  · intros; exact True.intro
  · intros; exact True.intro
  · intros; exact True.intro
  · intros; exact True.intro
  · intros; exact True.intro
  · intros; exact True.intro


namespace Typing

/-- Every typed resident's actual type is structurally headed: resident typing
only produces tuple, array, nominal and the fixed-head forms, so no unexpanded
alias, projection or row type is ever a resident's type. -/
theorem ValueTyped.type_structural {program : Kernel.Program} {world : World} {value : Value}
    (typed : Typing.ValueTyped program world value) : value.type.StructuralHead := by
  cases typed with
  | unit => trivial
  | scalar _ => trivial
  | aggregate constructed _ =>
    rcases constructed with ⟨same,_,_⟩ | ⟨_,_,_,_,same,_,_,_,_⟩ | ⟨_,_,_,_,_,same,_,_,_,_⟩ <;> rw [same] <;> trivial
  | reference _ _ _ _ _ => trivial
  | pointer _ _ => trivial
  | callable _ _ => trivial
  | operation _ => trivial
  | label => trivial
  | continuation form => obtain ⟨_,_,_,_,same⟩ := form; rw [same]; trivial
  | available _ _ _ _ _ => trivial
  | bindings _ _ _ _ _ => trivial

/-- The world's realization of declared storage types: every source field step
read at a located declared type has its actual physical field offset. The
container is the type the addressed storage actually has - an occupied address
is read at its resident's own (structurally headed) type, and the source
projection only steps through that same structural head, since a source place
of alias-headed type is first transported to its expansion by `Projections.equal`.
An alias-headed container therefore has no source field step at all, and its
physical children are supplied by the alias rule of `FieldOffset` when a
derivation at it is demanded. `World.representation` derives this product from
the authoritative world typing invariant; actual allocation and preservation
maintain its root layout facts. The resident itself is required because a
nominal offset is read at the stored constructor and an array's declared length
is the resident's own constant count. -/
structure TargetRepresentation (program : Kernel.Program) (world : World)
    (runtime : Execution.Context) : Prop where
  offsets : ∀ (address : Address) (container : Term) (index : Nat) (child : Term) {value : Value},
    AddressType program.declarations world address container →
    world.Stores address value →
    FieldType program.declarations runtime.static container index child true →
    container.FrameBound index →
    ∃ offset, FieldOffset program.declarations world address container index child offset

end Typing

/-- The selected child of an actual physical field offset carries its own
admitted layout, read from the offset's own derivation: the ordered layout row
of an aggregate, the element layout of an array, the substituted field layout of
a nominal container, and the expansion's layout for an alias application. -/
theorem FieldOffset.child_layout {program : Kernel.Program} {world : World} {address : Address}
    {container : Term} {index : Nat} {type : Term} {offset : Nat}
    (valid : ProgramWellFormed program.declarations)
    (field : FieldOffset program.declarations world address container index type offset) :
    ∃ layout, LayoutOf program.declarations ⟨[],[],0,default,false,{}⟩ type layout := by
  refine FieldOffset.rec
    (motive := fun container index type offset _ =>
      ∃ layout, LayoutOf program.declarations ⟨[],[],0,default,false,{}⟩ type layout)
    ?_ ?_ ?_ ?_ ?_ ?_ field
  · intro fields index type layouts layout offset selected related aggregate offsetsAt
    have bound : index < layouts.length := by
      have lengths := related.length_eq
      have indexBound := (List.getElem?_eq_some_iff.mp selected).1
      omega
    exact ⟨layouts[index]'bound, ListRel.at related selected (List.getElem?_eq_getElem bound)⟩
  · intro brand region fields index type layouts layout offset selected related aggregate offsetsAt
    have bound : index < layouts.length := by
      have lengths := related.length_eq
      have indexBound := (List.getElem?_eq_some_iff.mp selected).1
      omega
    exact ⟨layouts[index]'bound, ListRel.at related selected (List.getElem?_eq_getElem bound)⟩
  · intro id arguments fields index type layouts layout offset declared selected related aggregate offsetsAt
    have bound : index < layouts.length := by
      have lengths := related.length_eq
      have indexBound := (List.getElem?_eq_some_iff.mp selected).1
      omega
    exact ⟨layouts[index]'bound, ListRel.at related selected (List.getElem?_eq_getElem bound)⟩
  · intro element sign width count index layout nonneg bound derived
    exact ⟨layout, derived⟩
  · intro id arguments data variant substitution types index type layout offset value constructed headerEq
      instantiated graph selected derived stored head disjunct
    obtain ⟨tag, selectedTag⟩ : ∃ tag, data.variants[tag]? = some variant :=
      List.mem_iff_getElem?.mp constructed.2.1
    have closed : (⟨[],[],0,data.header.module,false,{}⟩ : Language.Context).assumptions = [] := rfl
    obtain ⟨fieldLayouts, offsets, fieldLayoutsRelated, offsetsLength, offsetEq, variantFact⟩ :=
      LayoutOf.nominal_realization (tag := tag) valid closed derived
        (by rw [← headerEq]; exact constructed.1) selectedTag instantiated graph .refl
    have bound : index < fieldLayouts.length := by
      have lengths := fieldLayoutsRelated.length_eq
      have indexBound := (List.getElem?_eq_some_iff.mp selected).1
      omega
    exact ⟨fieldLayouts[index]'bound,
      (ListRel.at fieldLayoutsRelated selected (List.getElem?_eq_getElem bound)).runtime_context⟩
  · intro id declaration arguments substitution expanded index type offset found instantiated graph inner ih
    exact ih

/-- Every located declared storage type carries an admitted layout at the
physical layout context. The root's is the one its own allocation admitted; a
child's is read off the actual physical field offset that put it there. -/
theorem AddressOffset.layoutOf {program : Kernel.Program} {world : World}
    {address : Address} {container : Term} {offset : Nat} {module : ModuleId} {unsafeAllowed : Bool}
    (valid : ProgramWellFormed program.declarations)
    (located : AddressOffset program.declarations world address container offset)
    (typed : Typing.WorldTyped program world) :
    ∃ layout, LayoutOf program.declarations ⟨[],[],0,module,unsafeAllowed,{}⟩ container layout := by
  induction located with
  | root found live => exact ⟨_,(typed.2.2.2.2 _ _ found live).runtime_context⟩
  | child _ field _ => exact (FieldOffset.child_layout valid field).imp (fun _ derived => derived.runtime_context)

/-- World typing produces the target representation outright: the root layout
law and resident typing come from the same invariant. The container layout is
read from its actual address offset, and each physical field offset and child
layout come from the source field step at the resident actually stored there. -/
theorem World.representation {program : Kernel.Program} {world : World} {runtime : Execution.Context}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program world) :
    Typing.TargetRepresentation program world runtime where
  offsets := by
    intro address container index child value located stored fieldType bound
    obtain ⟨offset, atOffset⟩ := located
    obtain ⟨layout, derived⟩ := AddressOffset.layoutOf (module := default) (unsafeAllowed := false) valid atOffset typed
    have valueType : value.type = container :=
      atOffset.stored_type valid inventory (Typing.WorldTyped.roots typed) stored
    have structural : container.StructuralHead :=
      valueType ▸ (World.stores_typed (Typing.WorldTyped.roots typed) stored).type_structural
    exact (LayoutOf.field_realization valid typed stored derived container .refl structural valueType
      index child fieldType bound).1

end Glorious.Language
