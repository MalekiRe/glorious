import GloriousLanguage.BindingPersistence
import GloriousLanguage.DefinitionalSeparation
import GloriousLanguage.Preservation
import GloriousLanguage.ProjectionStorage
import GloriousLanguage.SourceInterpretation
import GloriousLanguage.RealizationLayout

/-! The source place/projection bridge to actual physical storage typing.

A source `PlaceType` derivation projects a local slot's declared type through
the real source projection judgment; the actual runtime resolves the same
projection list from the actual environment. This module derives, for an
arbitrary projection list, the actual declared type at the resolved address and
its `AddressType` derivation, together with the runtime image of the source
result type. The field steps consume the physical field-offset product supplied
by the world interpretation; no requested address type, and no equality between
the source subtype and the runtime type, is assumed. The runtime conversion law
`Typing.SourceConversionClosed` is the single source-equality transport used. -/
namespace Glorious.Language

/-- The runtime closing context carries no assumptions, so every requirement of
its assumption list is discharged by membership alone. -/
theorem Typing.RuntimeContext.assumptionKinded {program : Language.Program} {runtime : Execution.Context} :
    ∀ requirement ∈ runtime.static.assumptions, ConstraintKinded program runtime.static requirement := by
  intro requirement member
  rw [show runtime.static.assumptions = [] from rfl] at member
  cases member

/-- Conversion cannot relate terms of different structural heads. This is the
conversion decomposition at an explicit final clash, not a new evaluator. -/
theorem DefinitionallyEqual.head_clash {program : Language.Program} (valid : ProgramWellFormed program)
    {runtime : Execution.Context} {left right : Term} (equal : DefinitionallyEqual program runtime.static left right)
    (leftStructural : left.StructuralHead) (rightStructural : right.StructuralHead)
    (clash : left.mapChildren (fun _ => .unit) ≠ right.mapChildren (fun _ => .unit)) : False :=
  clash (equal.structural_decomposition valid (Typing.RuntimeContext.assumptionKinded (program := program))
    leftStructural rightStructural).1

/-- Constructor decomposition of a conversion at an explicitly headed term. -/
theorem DefinitionallyEqual.same_head {program : Language.Program} (valid : ProgramWellFormed program)
    {runtime : Execution.Context} {left right : Term}
    (equal : DefinitionallyEqual program runtime.static left right)
    (leftStructural : left.StructuralHead) (rightStructural : right.StructuralHead) :
    SameHead left right ∧ ListRel (DefinitionallyEqual program runtime.static) left.children right.children :=
  equal.structural_decomposition valid (Typing.RuntimeContext.assumptionKinded (program := program))
    leftStructural rightStructural

/-- Inversion of a conversion at a tuple image: the converted term is an
ordered tuple whose children convert to the image's children. -/
theorem DefinitionallyEqual.tuple_shape {program : Language.Program} (valid : ProgramWellFormed program)
    {runtime : Execution.Context} {left : Term} {keys : List Term}
    (equal : DefinitionallyEqual program runtime.static left (.tuple keys)) (structural : left.StructuralHead) :
    ∃ actual, left = .tuple actual ∧
      ListRel (DefinitionallyEqual program runtime.static) actual keys := by
  cases left with
  | tuple actual =>
      exact ⟨actual,rfl,(equal.same_head valid True.intro True.intro).2⟩
  | alias declaration arguments => cases structural
  | projection trait member owners items kind => cases structural
  | row instances tails => cases structural
  | _ =>
      exact False.elim (equal.head_clash valid structural True.intro (by
        simp only [Term.mapChildren]
        intro clash
        cases clash))

/-- Inversion of a conversion at an array image. -/
theorem DefinitionallyEqual.array_shape {program : Language.Program} (valid : ProgramWellFormed program)
    {runtime : Execution.Context} {left : Term} {element length : Term}
    (equal : DefinitionallyEqual program runtime.static left (.array element length))
    (structural : left.StructuralHead) :
    ∃ actualElement actualLength, left = .array actualElement actualLength ∧
      DefinitionallyEqual program runtime.static actualElement element ∧
      DefinitionallyEqual program runtime.static actualLength length := by
  cases left with
  | array actualElement actualLength =>
      obtain ⟨_,children⟩ := equal.same_head valid True.intro True.intro
      cases children with
      | cons elementEq rest =>
        cases rest with
        | cons lengthEq _ => exact ⟨actualElement,actualLength,rfl,elementEq,lengthEq⟩
  | alias declaration arguments => cases structural
  | projection trait member owners items kind => cases structural
  | row instances tails => cases structural
  | _ =>
      exact False.elim (equal.head_clash valid structural True.intro (by
        simp only [Term.mapChildren]
        intro clash
        cases clash))

/-- Inversion of a conversion at a nominal image. -/
theorem DefinitionallyEqual.nominal_shape {program : Language.Program} (valid : ProgramWellFormed program)
    {runtime : Execution.Context} {left : Term} {id : DeclId} {arguments : List Term}
    (equal : DefinitionallyEqual program runtime.static left (.nominal id arguments))
    (structural : left.StructuralHead) :
    ∃ actualArguments, left = .nominal id actualArguments ∧
      ListRel (DefinitionallyEqual program runtime.static) actualArguments arguments := by
  cases left with
  | nominal actualId actualArguments =>
      obtain ⟨same,children⟩ := equal.same_head valid True.intro True.intro
      have identity : actualId = id := (Term.nominal.inj same).1
      subst identity
      exact ⟨actualArguments,rfl,children⟩
  | alias declaration arguments => cases structural
  | projection trait member owners items kind => cases structural
  | row instances tails => cases structural
  | _ =>
      exact False.elim (equal.head_clash valid structural True.intro (by
        simp only [Term.mapChildren]
        intro clash
        cases clash))

/-- Inversion of a conversion at a reference image. -/
theorem DefinitionallyEqual.reference_shape {program : Language.Program} (valid : ProgramWellFormed program)
    {runtime : Execution.Context} {left : Term} {mode : Mutability} {region referent : Term}
    (equal : DefinitionallyEqual program runtime.static left (.reference mode region referent))
    (structural : left.StructuralHead) :
    ∃ actualRegion actualReferent, left = .reference mode actualRegion actualReferent ∧
      DefinitionallyEqual program runtime.static actualRegion region ∧
      DefinitionallyEqual program runtime.static actualReferent referent := by
  cases left with
  | reference actualMode actualRegion actualReferent =>
      obtain ⟨same,children⟩ := equal.same_head valid True.intro True.intro
      cases (Term.reference.inj same).1
      cases children with
      | cons regionEq rest =>
        cases rest with
        | cons referentEq _ => exact ⟨actualRegion,actualReferent,rfl,regionEq,referentEq⟩
  | alias declaration arguments => cases structural
  | projection trait member owners items kind => cases structural
  | row instances tails => cases structural
  | _ =>
      exact False.elim (equal.head_clash valid structural True.intro (by
        simp only [Term.mapChildren]
        intro clash
        cases clash))

/-- An ordered relation selects a related element at any present index. -/
theorem ListRel.at_exists {α β : Type} {relation : α → β → Prop} {left : List α} {right : List β}
    (related : ListRel relation left right) :
    ∀ {index : Nat} {first : β}, right[index]? = some first →
      ∃ second, left[index]? = some second ∧ relation second first := by
  induction related with
  | nil => intro index first found; cases found
  | cons head _ ih =>
    intro index first found
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at found
      exact ⟨_,rfl,found ▸ head⟩
    | succ index =>
      simp only [List.getElem?_cons_succ] at found
      obtain ⟨second,selected,relation⟩ := ih found
      exact ⟨second,by simp only [List.getElem?_cons_succ,selected],relation⟩

/-- Two ordered relations over a common image compose elementwise. -/
theorem ListRel.trim {α β γ : Type} {outer : α → β → Prop} {inner : γ → β → Prop}
    {combine : α → γ → Prop}
    (join : ∀ a c b, outer a b → inner c b → combine a c) :
    ∀ {left : List α} {right : List γ} {middle : List β},
      ListRel outer left middle → ListRel inner right middle → ListRel combine left right := by
  intro left
  induction left with
  | nil =>
    intro right middle related inner
    cases related
    cases inner
    exact .nil
  | cons value values ih =>
    intro right middle first second
    cases first with
    | cons head tail =>
      cases second with
      | cons other rest => exact .cons (join _ _ _ head other) (ih tail rest)

/-- A projection derivation over the empty list converts its endpoints. -/
theorem Typing.Projections.endpoints_convertible {program : Language.Program} {context : Typing.Context}
    {type result : Term} {mutable writable : Bool} {projections : List Kernel.Projection}
    (projected : Typing.Projections program context type mutable projections result writable) :
    Equal program context.static type result ∨ projections ≠ [] := by
  induction projected with
  | nil => exact Or.inl .refl
  | field _ _ => exact Or.inr (by intro same; cases same)
  | index _ _ => exact Or.inr (by intro same; cases same)
  | dereference _ => exact Or.inr (by intro same; cases same)
  | equal equal _ ih => exact ih.elim (fun same => Or.inl (.trans equal same)) Or.inr

/-- The image of a list under a term map, related to the originals. -/
theorem ListRel.term_map_image (scope : ScopeInstantiation) (values : List Term) :
    ListRel (fun image value => image = scope.term value) (values.map scope.term) values := by
  induction values with
  | nil => exact .nil
  | cons value values ih => exact .cons rfl ih

/-- Substituting a common template list through convertible tables keeps the
declared substitution product, with the syntactic image of the new table. -/
theorem ListRel.substitutes_congr {program : Language.Program} (valid : ProgramWellFormed program)
    {context : Language.Context} {left right : Substitution} {templates middle : List Term}
    (related : ListRel (Substitutes left) templates middle)
    (tables : SubstitutionsConvertible program context left right) :
    ListRel (Substitutes right) templates (templates.map (·.substitute right)) := by
  induction related with
  | nil => exact .nil
  | cons head _ ih => exact .cons (head.congr_substitution valid tables.substitution_getD) ih

/-- The source field-type judgment is read at the runtime image of the scope:
the field selected by the physical container's own ordered structure is the
runtime image of the source field, and its declared type is the source field
type read at the runtime arguments. This is the interpreted source assumption
of one field step, proved from the field judgment and the container
conversion rather than assumed. -/
theorem Typing.FieldType.instantiated {program : Language.Program} (valid : ProgramWellFormed program)
    {scope : ScopeInstantiation} {source : Language.Context} {runtime : Execution.Context}
    (moduleEq : runtime.module = source.module)
    {type : Term} {index : Nat} {field : Term}
    (located : Typing.FieldType program source type index field true)
    {container : Term} (structural : container.StructuralHead)
    (agree : DefinitionallyEqual program runtime.static container (scope.term type)) :
    ∃ actualField, Typing.FieldType program runtime.static container index actualField true ∧
      DefinitionallyEqual program runtime.static actualField (scope.term field) := by
  rcases located with ⟨fields, same, selected⟩ | ⟨element, length, same, fieldEq⟩ |
    ⟨id, arguments, data, variant, substitution, types, same, found, notEnum, variants, instantiated,
      substituted, selected, visibility⟩
  · rw [same] at agree
    simp only [ScopeInstantiation.term] at agree
    obtain ⟨actualFields, rfl, children⟩ := agree.tuple_shape valid structural
    have imageAt : (fields.map scope.term)[index]? = some (scope.term field) := by
      simp only [List.getElem?_map,selected,Option.map_some]
    obtain ⟨actualField, selectedAt, relation⟩ := children.at_exists imageAt
    exact ⟨actualField,Or.inl ⟨actualFields,rfl,selectedAt⟩,relation⟩
  · rw [same] at agree
    simp only [ScopeInstantiation.term] at agree
    obtain ⟨actualElement, actualLength, rfl, elementAgrees, _⟩ := agree.array_shape valid structural
    rw [fieldEq]
    exact ⟨actualElement,Or.inr (Or.inl ⟨actualElement,actualLength,rfl,rfl⟩),elementAgrees⟩
  · rw [same] at agree
    simp only [ScopeInstantiation.term] at agree
    obtain ⟨actualArguments, rfl, argumentsRelated⟩ := agree.nominal_shape valid structural
    have flipped : ListRel (fun image actual => DefinitionallyEqual program runtime.static image actual)
        (arguments.map scope.term) actualArguments :=
      argumentsRelated.swap.imp (fun _ _ related => related.symm)
    have images : ListRel (fun argument image => image = scope.term argument)
        arguments (arguments.map scope.term) := (ListRel.term_map_image scope arguments).swap
    have scopedAgrees : ListRel (fun actual argument =>
        DefinitionallyEqual program runtime.static actual (scope.term argument)) actualArguments arguments :=
      ListRel.trim
        (outer := fun (actual : Term) (image : Term) => DefinitionallyEqual program runtime.static actual image)
        (inner := fun (argument : Term) (image : Term) => image = scope.term argument)
        (combine := fun (actual : Term) (argument : Term) =>
          DefinitionallyEqual program runtime.static actual (scope.term argument))
        (join := fun (actual : Term) (argument : Term) (image : Term) related same => same ▸ related)
        argumentsRelated images
    have kinds : ListRel (fun binder term => binder.kind = term.kind) data.generics actualArguments :=
      ListRel.trim
        (outer := fun (binder : Binder) (argument : Term) => binder.kind = argument.kind)
        (inner := fun (actual : Term) (argument : Term) =>
          DefinitionallyEqual program runtime.static actual (scope.term argument))
        (combine := fun (binder : Binder) (actual : Term) => binder.kind = actual.kind)
        (join := fun (binder : Binder) (actual : Term) (argument : Term) binderKind argumentAgrees =>
          binderKind.trans ((argumentAgrees.kind_eq valid).trans
            (ScopeInstantiation.term_kind scope argument)).symm) instantiated.2.1 scopedAgrees
    have actualInstantiated : Instantiates data.generics actualArguments
        ((data.generics.map (·.id)).zip actualArguments) :=
      ⟨instantiated.1,kinds,rfl⟩
    have closedData := valid.scopeClosed (List.mem_of_find?_eq_some (Program.data_lookup found))
    have templateClosed : ∀ term ∈ variant.fields.map (·.type), term.ScopeClosed := by
      intro term member
      obtain ⟨definition, inFields, rfl⟩ := List.mem_map.mp member
      exact closedData definition.type (by
        simp only [Definition.terms,List.mem_append,List.mem_flatMap,List.mem_map]
        exact Or.inl (Or.inl (Or.inl ⟨definition,⟨variant,by rw [variants]; simp,inFields⟩,rfl⟩)))
    have fixed : ∀ term ∈ variant.fields.map (·.type), scope.term term = term :=
      fun term member => ScopeInstantiation.term_fixed scope term (templateClosed term member)
    have images := ScopeInstantiation.substitutes_values scope substituted fixed
    have tables : SubstitutionsConvertible program runtime.static
        (substitution.map (fun entry => (entry.1,scope.term entry.2)))
        ((data.generics.map (·.id)).zip actualArguments) :=
      (instantiated.map_values scope.term
        (fun argument _ => ScopeInstantiation.term_kind scope argument)).related_values flipped
    have converted := images.substitutes_congr valid tables
    have mapped : types = (variant.fields.map (·.type)).map (fun term => term.substitute substitution) :=
      substituted.substitutes_eq_map
    have imageAt : ((variant.fields.map (·.type)).map (fun term => term.substitute substitution))[index]? =
        some field := by
      rw [← mapped]; exact selected
    rw [List.getElem?_map] at imageAt
    obtain ⟨template, atTemplate, substitutedField⟩ := Option.map_eq_some_iff.mp imageAt
    have agree : DefinitionallyEqual program runtime.static
        (template.substitute ((data.generics.map (·.id)).zip actualArguments)) (scope.term field) := by
      refine (Term.substitutions_convert program runtime.static template
        (tables.substitution_getD)).symm.trans ?_
      have valuesEq : scope.term (Term.substitute substitution template) =
          Term.substitute (substitution.map (fun entry => (entry.1,scope.term entry.2))) template := by
        rw [ScopeInstantiation.map_substituted_values scope template substitution
          (ScopeInstantiation.atomsFixed scope template)]
        rw [ScopeInstantiation.term_fixed scope template
          (templateClosed template (List.mem_of_getElem? atTemplate))]
      rw [← valuesEq, ← substitutedField]
      exact DefinitionallyEqual.refl
    refine ⟨template.substitute ((data.generics.map (·.id)).zip actualArguments),
      Or.inr (Or.inr ⟨id,actualArguments,data,variant,(data.generics.map (·.id)).zip actualArguments,
        (variant.fields.map (·.type)).map (fun term => term.substitute ((data.generics.map (·.id)).zip actualArguments)),
        rfl,found,notEnum,variants,actualInstantiated,converted,?_,?_⟩),agree⟩
    · rw [List.getElem?_map,atTemplate]
      rfl
    · intro trivial
      obtain ⟨definition, atField, shown⟩ := visibility trivial
      exact ⟨definition, atField, by
        simpa only [show runtime.static.module = source.module from moduleEq] using shown⟩

/-- A source place's declared storage type as it actually is at the resolved
address: the located declared type and its reading at the runtime image of the
source type. A proposition, so it may be eliminated while proving. -/
def Typing.AddressTyped (program : Kernel.Program) (world : World) (runtime : Execution.Context)
    (address : Address) (type : Term) : Prop :=
  ∃ actual, AddressType program.declarations world address actual ∧
    DefinitionallyEqual program.declarations runtime.static actual (runtime.term type)

/-- An occupied address is read at its resident's own type: the located
declared type and the resident's type are the same term, and resident typing
only produces structurally headed types. This replaces a world-level
"every located type is structural" premise, which an admitted alias-headed
allocation would falsify, by the actual judgement at the point of use. -/
theorem AddressType.structural_of_stored {program : Kernel.Program} {world : World}
    {address : Address} {container : Term}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program world)
    (located : AddressType program.declarations world address container)
    {value : Value} (stored : world.Stores address value) : container.StructuralHead := by
  obtain ⟨offset, atOffset⟩ := located
  have typeEq := atOffset.stored_type valid inventory (Typing.WorldTyped.roots worldTyped) stored
  rw [← typeEq]
  exact (World.stores_typed (Typing.WorldTyped.roots worldTyped) stored).type_structural

/-- A resident's own array frame bound: a source field step only selects a slot
the resident actually has, and a typed array's arity is its declared count. -/
theorem Typing.ValueTyped.frameBound {program : Kernel.Program} {world : World} {value : Value}
    (typed : Typing.ValueTyped program world value) {index : Nat} (bound : index < value.fields.length) :
    value.type.FrameBound index := by
  cases typed with
  | aggregate constructed fields =>
      rcases constructed with ⟨same,_,_⟩ | ⟨element,sign,width,length,same,_,_,arity,_⟩ |
        ⟨_,_,_,_,_,same,_⟩
      · rw [same]
        trivial
      · rw [same]
        show index < length.toNat
        rw [arity, Int.toNat_natCast]
        exact lt_of_lt_of_eq bound fields.length
      · rw [same]
        trivial
  | _ => trivial


/-- The runtime decoding preserves structural heads: it rewrites exactly the
lexical atoms, which are leaves, and is structural on every other constructor.
Hence a declared local type that the source projection judgment sees as an
ordered head is seen as the same head at the runtime image. -/
theorem ScopeInstantiation.term_structural {scope : ScopeInstantiation} {term : Term}
    (structural : term.StructuralHead) : (scope.term term).StructuralHead := by
  cases term <;>
    simp only [ScopeInstantiation.term,Term.StructuralHead] at *
  all_goals try trivial
  case scopedRegion id => cases scope.regions.get id <;> trivial
  case scopedBrand id => cases scope.brands.get id <;> trivial

/-- A resident reference value whose head names the actual reference identity
determines the located type of that loan's referent. -/
theorem Typing.ValueTyped.reference_referent {program : Kernel.Program} {world : World} {value : Value}
    {mode : Mutability} {region referent : Term} {identity : Identity} {loan : Loan}
    (typed : Typing.ValueTyped program world value) (shape : value.type = .reference mode region referent)
    (head : value.head = .reference identity) (found : world.loans.get identity = some loan) :
    AddressType program.declarations world loan.referent referent := by
  cases value with
  | resident owner actual valueHead live fields resources =>
    change actual = .reference mode region referent at shape
    subst shape
    cases typed with
    | @reference owner actualMode actualRegion actualReferent referenceIdentity referenceLoan live
        referenceFound liveEq modeEq regionEq located =>
      have sameIdentity : referenceIdentity = identity := ValueHead.reference.inj head
      have sameLoan : referenceLoan = loan := Option.some.inj (by
        rw [sameIdentity] at referenceFound
        exact referenceFound.symm.trans found)
      exact sameLoan ▸ located
    | aggregate constructed fields =>
      rcases constructed with ⟨same,_⟩ | ⟨_,_,_,_,same,_⟩ | ⟨_,_,_,_,_,same,_⟩ <;> cases same
    | continuation form =>
      obtain ⟨_,_,_,_,impossible⟩ := form
      cases impossible

namespace Typing

/-- Every source projection step lifts to the actual declared storage type at
the resolved address, and the declared type reads as the runtime image of the
source result type. The derivation consumes the actual resolution, the world's
target representation and the runtime closing law; it assumes no address type
at the projected address. -/
theorem ResolvesProjections.addressTyped {program : Kernel.Program} {world : World}
    {source : Typing.Context} {runtime : Execution.Context}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program world)
    (moduleEq : runtime.module = source.static.module)
    (closed : Typing.SourceConversionClosed program.declarations source.static runtime)
    {module : ModuleId} {unsafeAllowed : Bool}
    (realized : World.LayoutRealized program.declarations world module unsafeAllowed)
    {type : Term} {mutable : Bool} {projections : List Kernel.Projection} {result : Term} {writable : Bool}
    (projected : Typing.Projections program.declarations source type mutable projections result writable)
    {base : Address} {authority : Authority} {address : Address} {permission : Authority}
    (baseTyped : Typing.AddressTyped program world runtime base type)
    (resolved : Kernel.ResolvesProjections world runtime.environment base authority projections address permission) :
    Typing.AddressTyped program world runtime address result := by
  have representation : Typing.TargetRepresentation program world runtime :=
    World.representation valid inventory worldTyped realized
  induction projected generalizing base authority address permission with
  | nil => cases resolved with | nil => exact baseTyped
  | @field type mutable index rest field result writable located tail ih =>
    obtain ⟨parentActual, parentLocated, parentAgrees⟩ := baseTyped
    cases resolved with
    | field stored selected inner =>
      have childTyped : Typing.AddressTyped program world runtime (base.child index) field := by
        obtain ⟨actualField, physicalField, agrees⟩ := located.instantiated valid (scope := runtime.instantiation)
          (runtime := runtime) moduleEq
          (AddressType.structural_of_stored valid inventory worldTyped parentLocated stored) parentAgrees
        obtain ⟨offset, fieldOffset⟩ := representation.offsets base parentActual index actualField parentLocated stored
          physicalField (by
            obtain ⟨parentOffset, parentOffsetLocated⟩ := parentLocated
            have typeEq := parentOffsetLocated.stored_type valid inventory (Typing.WorldTyped.roots worldTyped) stored
            rw [← typeEq]
            exact (World.stores_typed (Typing.WorldTyped.roots worldTyped) stored).frameBound
              (List.getElem?_eq_some_iff.mp selected).1)
        obtain ⟨parentOffset, parentOffsetLocated⟩ := parentLocated
        exact ⟨actualField,⟨_,AddressOffset.child parentOffsetLocated fieldOffset⟩,agrees⟩
      exact ih childTyped inner
    | vacantField stored vacant =>
      have childTyped : Typing.AddressTyped program world runtime (base.child index) field := by
        obtain ⟨actualField, physicalField, agrees⟩ := located.instantiated valid (scope := runtime.instantiation)
          (runtime := runtime) moduleEq
          (AddressType.structural_of_stored valid inventory worldTyped parentLocated stored) parentAgrees
        obtain ⟨offset, fieldOffset⟩ := representation.offsets base parentActual index actualField parentLocated stored
          physicalField (by
            obtain ⟨parentOffset, parentOffsetLocated⟩ := parentLocated
            have typeEq := parentOffsetLocated.stored_type valid inventory (Typing.WorldTyped.roots worldTyped) stored
            rw [← typeEq]
            exact (World.stores_typed (Typing.WorldTyped.roots worldTyped) stored).frameBound
              (List.getElem?_eq_some_iff.mp vacant).1)
        obtain ⟨parentOffset, parentOffsetLocated⟩ := parentLocated
        exact ⟨actualField,⟨_,AddressOffset.child parentOffsetLocated fieldOffset⟩,agrees⟩
      have convertible := tail.endpoints_convertible.elim id (fun different => absurd rfl different)
      obtain ⟨actualField, childLocated, childAgrees⟩ := childTyped
      exact ⟨actualField,childLocated,childAgrees.trans (closed field result convertible)⟩
  | @index element length mutable localSlot rest result writable indexed tail ih =>
    obtain ⟨parentActual, parentLocated, parentAgrees⟩ := baseTyped
    simp only [Execution.Context.term,ScopeInstantiation.term] at parentAgrees
    cases resolved with
    | @index headBase headAuthority headLocal headRest headBinding headValue headInteger headResult
        headPermission selected stored valueHead initialized permitted nonnegative inner =>
      cases inner with
      | field storedInArray selectedInArray innerRest =>
        obtain ⟨actualElement, actualLength, shape, elementAgrees, _⟩ :=
          parentAgrees.array_shape valid
            (AddressType.structural_of_stored valid inventory worldTyped parentLocated storedInArray)
        have elementTyped : Typing.AddressTyped program world runtime (base.child headInteger.toNat) element := by
          refine ⟨actualElement,?_,elementAgrees⟩
          obtain ⟨offset, fieldOffset⟩ := representation.offsets base parentActual headInteger.toNat actualElement
            parentLocated storedInArray (Or.inr (Or.inl ⟨actualElement,actualLength,shape,rfl⟩)) (by
              obtain ⟨parentOffset, parentOffsetLocated⟩ := parentLocated
              have typeEq := parentOffsetLocated.stored_type valid inventory
                (Typing.WorldTyped.roots worldTyped) storedInArray
              rw [← typeEq]
              exact (World.stores_typed (Typing.WorldTyped.roots worldTyped) storedInArray).frameBound
                (List.getElem?_eq_some_iff.mp selectedInArray).1)
          obtain ⟨parentOffset, parentOffsetLocated⟩ := parentLocated
          exact ⟨_,AddressOffset.child parentOffsetLocated fieldOffset⟩
        exact ih elementTyped innerRest
      | vacantField storedInArray vacantInArray =>
        obtain ⟨actualElement, actualLength, shape, elementAgrees, _⟩ :=
          parentAgrees.array_shape valid
            (AddressType.structural_of_stored valid inventory worldTyped parentLocated storedInArray)
        have elementTyped : Typing.AddressTyped program world runtime (base.child headInteger.toNat) element := by
          refine ⟨actualElement,?_,elementAgrees⟩
          obtain ⟨offset, fieldOffset⟩ := representation.offsets base parentActual headInteger.toNat actualElement
            parentLocated storedInArray (Or.inr (Or.inl ⟨actualElement,actualLength,shape,rfl⟩)) (by
              obtain ⟨parentOffset, parentOffsetLocated⟩ := parentLocated
              have typeEq := parentOffsetLocated.stored_type valid inventory
                (Typing.WorldTyped.roots worldTyped) storedInArray
              rw [← typeEq]
              exact (World.stores_typed (Typing.WorldTyped.roots worldTyped) storedInArray).frameBound
                (List.getElem?_eq_some_iff.mp vacantInArray).1)
          obtain ⟨parentOffset, parentOffsetLocated⟩ := parentLocated
          exact ⟨_,AddressOffset.child parentOffsetLocated fieldOffset⟩
        have convertible := tail.endpoints_convertible.elim id (fun different => absurd rfl different)
        obtain ⟨actualChild, childLocated, childAgrees⟩ := elementTyped
        exact ⟨actualChild,childLocated,childAgrees.trans (closed element result convertible)⟩
  | @dereference mode region referent mutable rest result writable tail ih =>
    cases resolved with
    | dereference stored valueHead initialized permitted found live referenceView inner =>
      obtain ⟨parentActual, parentLocated, parentAgrees⟩ := baseTyped
      have valueTyped := World.stores_typed (Typing.WorldTyped.roots worldTyped) stored
      obtain ⟨parentOffset, parentOffsetLocated⟩ := parentLocated
      have valueType := parentOffsetLocated.stored_type valid inventory
        (Typing.WorldTyped.roots worldTyped) stored
      simp only [Execution.Context.term,ScopeInstantiation.term] at parentAgrees
      obtain ⟨actualRegion, actualReferent, shape, _, referentAgrees⟩ :=
        parentAgrees.reference_shape valid
          (AddressType.structural_of_stored valid inventory worldTyped ⟨parentOffset,parentOffsetLocated⟩ stored)
      exact ih ⟨actualReferent,
        valueTyped.reference_referent (valueType.trans shape) valueHead found, referentAgrees⟩ inner
  | @equal a b mutable projections result writable same tail ih =>
    obtain ⟨parentActual, parentLocated, parentAgrees⟩ := baseTyped
    exact ih ⟨parentActual,parentLocated,parentAgrees.trans (closed a b same)⟩ resolved


/-- The local storage location of a source place is a typed runtime address. A
resident at the resolved address is present either way: the resolution itself
visits its own base whenever a projection is present, and the empty projection
resolves to the base. -/
theorem ContextBindingsTyped.place_location {program : Kernel.Program} {world : World}
    {source : Typing.Context} {runtime : Execution.Context}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program world)
    (typed : Typing.ContextBindingsTyped program world source runtime)
    {localSlot : Kernel.Local} (member : localSlot ∈ source.locals)
    {binding : Kernel.Binding} (selected : runtime.environment.Selects localSlot.id binding)
    {projections : List Kernel.Projection} {address : Address} {permission : Authority}
    (resolved : Kernel.ResolvesProjections world runtime.environment binding.address binding.authority
      projections address permission)
    {value : Value} (stored : world.Stores address value) :
    Typing.AddressTyped program world runtime binding.address localSlot.type := by
  obtain ⟨actual, found, storage⟩ := typed.selects member
  have same := selected.2.2 actual found.1 found.2.1
  subst actual
  have baseStored : ∃ resident, world.Stores binding.address resident := by
    by_cases empty : projections = []
    · subst empty
      cases resolved
      exact ⟨value,stored⟩
    · exact resolved.nonempty_stored empty
  obtain ⟨resident, residentStored⟩ := baseStored
  obtain ⟨located, _, _⟩ := storage.read valid inventory worldTyped residentStored
  exact ⟨runtime.term localSlot.type, located, DefinitionallyEqual.refl⟩

/-- A resident stored at a located address has the runtime image of the source
type: the located declared type reads as the source type and determines its
resident's type. -/
theorem AddressTyped.resident_type {program : Kernel.Program} {world : World}
    {runtime : Execution.Context} {address : Address} {type : Term}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program world)
    (located : Typing.AddressTyped program world runtime address type)
    {value : Value} (stored : world.Stores address value) :
    DefinitionallyEqual program.declarations runtime.static value.type (runtime.term type) := by
  obtain ⟨actual, physical, agrees⟩ := located
  obtain ⟨offset, atOffset⟩ := physical
  have valueType := atOffset.stored_type valid inventory (Typing.WorldTyped.roots worldTyped) stored
  exact valueType.symm ▸ agrees

/-- The full source place bridge: a source `PlaceType` derivation resolves to an
actual address whose declared storage type is the located reading of the
source place type. Only the entry-established local location, the world target
representation and the runtime closing law are consumed. -/
theorem ContextBindingsTyped.place_addressTyped {program : Kernel.Program} {world : World}
    {source : Typing.Context} {runtime : Execution.Context}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program world)
    (closed : Typing.SourceConversionClosed program.declarations source.static runtime)
    {module : ModuleId} {unsafeAllowed : Bool}
    (realized : World.LayoutRealized program.declarations world module unsafeAllowed)
    (typed : Typing.ContextBindingsTyped program world source runtime)
    {place : Kernel.Place} {type : Term} {writable : Bool}
    (placeTyped : Typing.PlaceType program.declarations source place type writable)
    {address : Address} {authority : Authority}
    (resolved : Kernel.ResolvesPlace world runtime.environment place address authority)
    {value : Value} (stored : world.Stores address value) :
    Typing.AddressTyped program world runtime address type := by
  obtain ⟨localSlot, member, identity, projected⟩ := placeTyped
  cases resolved with
  | @localSlot binding address authority selected projections =>
    have selected' : runtime.environment.Selects localSlot.id binding := by
      rw [identity]
      exact selected
    have located := Typing.ContextBindingsTyped.place_location valid inventory worldTyped typed
      member selected' projections stored
    exact Typing.ResolvesProjections.addressTyped valid inventory worldTyped typed.moduleEq closed
      realized projected located projections

end Typing
end Glorious.Language
