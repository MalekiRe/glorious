import GloriousLanguage.Declarations

/-! Declarative static semantics. Proof search, inference-cell mutation and
normalization algorithms are deliberately not definitions of these relations. -/
namespace Glorious.Language

structure Context where
  binders : List Binder := []
  assumptions : List Constraint := []
  universe : Nat := 0
  module : ModuleId
  unsafe : Bool := false
  deriving Repr, Inhabited

inductive Kinding (program : Program) (context : Context) : Term → Kind → Prop where
  | quantity {quantity} : (∀ upper, quantity.upper = some upper → quantity.lower ≤ upper) →
      Kinding program context (.quantity quantity) .quantity
  | parameter {binder} : binder ∈ context.binders → Kinding program context (.parameter binder.id binder.kind) binder.kind
  | rigid {id kind level} : level ≤ context.universe → Kinding program context (.rigid id kind level) kind
  | variable {id kind level} : level ≤ context.universe → Kinding program context (.variable id kind level) kind
  | unit : Kinding program context .unit .type
  | bottom : Kinding program context .bottom .type
  | scalar {scalar} : scalar.Valid program.input.target → Kinding program context (.scalar scalar) .type
  | tuple {fields} : (∀ field ∈ fields, Kinding program context field .type) → Kinding program context (.tuple fields) .type
  | array {element length} : Kinding program context element .type → Kinding program context length .constant →
      Kinding program context (.array element length) .type
  | reference {mode region referent} : Kinding program context region .region → Kinding program context referent .type →
      Kinding program context (.reference mode region referent) .type
  | rawPointer {mode referent} : Kinding program context referent .type → Kinding program context (.rawPointer mode referent) .type
  | nominal {id data arguments substitution} : program.data id = some data →
      Instantiates data.generics arguments substitution →
      (∀ argument ∈ arguments, Kinding program context argument argument.kind) → Kinding program context (.nominal id arguments) .type
  | alias {id declaration arguments substitution} : program.alias id = some declaration →
      Instantiates declaration.generics arguments substitution →
      (∀ argument ∈ arguments, Kinding program context argument argument.kind) → Kinding program context (.alias id arguments) .type
  | callable {id declaration arguments substitution} : program.function id = some declaration →
      Instantiates declaration.signature.generics arguments substitution →
      (∀ argument ∈ arguments, Kinding program context argument argument.kind) → Kinding program context (.callable id arguments) .type
  | continuation {brand argument answer effects quantity} : Kinding program context brand .brand →
      Kinding program context argument .type → Kinding program context answer .type →
      Kinding program context effects .row → quantity.SurfaceResumption →
      Kinding program context (.continuation brand argument answer effects quantity) .type
  | label {brand region result} : Kinding program context brand .brand → Kinding program context region .region →
      Kinding program context result .type → Kinding program context (.label brand region result) .type
  | environment {brand region} : Kinding program context brand .brand → Kinding program context region .region →
      Kinding program context (.environment brand region) .type
  | available {brand region} : Kinding program context brand .brand → Kinding program context region .region →
      Kinding program context (.available brand region) .type
  | bindings {brand region arguments} : Kinding program context brand .brand → Kinding program context region .region →
      (∀ argument ∈ arguments, Kinding program context argument .type) →
      Kinding program context (.bindings brand region arguments) .type
  | effect {id declaration arguments substitution} : program.effect id = some declaration →
      Instantiates declaration.generics arguments substitution →
      (∀ argument ∈ arguments, Kinding program context argument argument.kind) → Kinding program context (.effect id arguments) .effect
  | row {instances tails} : (∀ instance ∈ instances, Kinding program context instance .effect) →
      (∀ tail ∈ tails, Kinding program context tail .row) → Kinding program context (.row instances tails) .row
  | projection {trait member declaration associated owners items ownerSub itemSub} :
      program.trait trait = some declaration → member ∈ declaration.members →
      program.associated member = some associated → associated.owner = trait →
      Instantiates declaration.generics owners ownerSub → Instantiates associated.generics items itemSub →
      (∀ argument ∈ owners ++ items, Kinding program context argument argument.kind) →
      Kinding program context (.projection trait member owners items associated.kind) associated.kind
  | scalarConstant {value} : value.Valid program.input.target → Kinding program context (.constant value) .constant
  | tupleConstant {fields} : (∀ field ∈ fields, Kinding program context field .constant) →
      Kinding program context (.constantTuple fields) .constant
  | constructorConstant {constructor data variant arguments fields substitution} :
      program.Constructor constructor data variant → Instantiates data.generics arguments substitution →
      fields.length = variant.fields.length → (∀ field ∈ fields, Kinding program context field .constant) →
      Kinding program context (.constantConstructor constructor arguments fields) .constant
  | quantity {principal} : Kinding program context (.principal principal) .quantity
  | static : Kinding program context .staticRegion .region

inductive SubstituteConstraint (substitution : Substitution) : Constraint → Constraint → Prop where
  | equal {a b x y} : Substitutes substitution a x → Substitutes substitution b y →
      SubstituteConstraint substitution (.equal a b) (.equal x y)
  | outlives {a b x y} : Substitutes substitution a x → Substitutes substitution b y →
      SubstituteConstraint substitution (.outlives a b) (.outlives x y)
  | typeOutlives {a b x y} : Substitutes substitution a x → Substitutes substitution b y →
      SubstituteConstraint substitution (.typeOutlives a b) (.typeOutlives x y)
  | rows {a b x y} : Substitutes substitution a x → Substitutes substitution b y →
      SubstituteConstraint substitution (.rowIncludes a b) (.rowIncludes x y)
  | implementation {id before after negative} : ListRel (Substitutes substitution) before after →
      SubstituteConstraint substitution (.implements id before negative) (.implements id after negative)
  | use {before after quantity} : Substitutes substitution before after →
      SubstituteConstraint substitution (.use before quantity) (.use after quantity)
  | callable {r args out effects r' args' out' effects' unsafe} : Substitutes substitution r r' →
      ListRel (Substitutes substitution) args args' → Substitutes substitution out out' →
      Substitutes substitution effects effects' →
      SubstituteConstraint substitution (.callable r args out effects unsafe) (.callable r' args' out' effects' unsafe)
  | runsIn {r access args after r' access' args' after' unsafe} : Substitutes substitution r r' →
      Substitutes substitution access access' → ListRel (Substitutes substitution) args args' →
      Substitutes substitution after after' →
      SubstituteConstraint substitution (.runsIn r access args after unsafe) (.runsIn r' access' args' after' unsafe)
  | quantified {binders before after restricted} :
      restricted = substitution.filter (fun entry => !(binders.any (fun binder => binder.id == entry.1))) →
      ListRel (SubstituteConstraint restricted) before after →
      SubstituteConstraint substitution (.quantified binders before) (.quantified binders after)

/-- A capability equation is local. Recursive nominal derivation is specified
below as its greatest solution, not an acyclic field walk or assumed Copy. -/
inductive CapabilityEquation (program : Program) (assignment : Term → Principal) : Term → Principal → Prop where
  | unit : CapabilityEquation program assignment .unit .duplicable
  | bottom : CapabilityEquation program assignment .bottom .duplicable
  | scalar {type} : CapabilityEquation program assignment (.scalar type) .duplicable
  | raw {mode type} : CapabilityEquation program assignment (.rawPointer mode type) .duplicable
  | shared {region type} : CapabilityEquation program assignment (.reference .shared region type) .duplicable
  | unique {region type} : CapabilityEquation program assignment (.reference .unique region type) .affine
  | label {brand region result} : CapabilityEquation program assignment (.label brand region result) .duplicable
  | tuple {fields} : CapabilityEquation program assignment (.tuple fields) (Principal.fields (fields.map assignment))
  | emptyArray {element sign width} :
      CapabilityEquation program assignment (.array element (.constant (.integer sign width 0))) .duplicable
  | array {element sign width length} : 0 < length →
      CapabilityEquation program assignment (.array element (.constant (.integer sign width length))) (assignment element)
  | alias {id declaration arguments substitution value} : program.alias id = some declaration →
      Instantiates declaration.generics arguments substitution → Substitutes substitution declaration.value value →
      CapabilityEquation program assignment (.alias id arguments) (assignment value)
  | nominal {id data arguments substitution fields marker structural principal} : program.data id = some data →
      Instantiates data.generics arguments substitution →
      ListRel (Substitutes substitution) ((data.variants.flatMap (·.fields)).map (·.type)) fields →
      (data.quantitySource = none ∧ marker = .duplicable ∨
       ∃ source value, data.quantitySource = some source ∧ Substitutes substitution source value ∧
         (value = .principal marker ∨ value.kind = .type ∧ marker = assignment value)) →
      structural = (Principal.fields (fields.map assignment)).meet marker →
      (data.principalRestriction = none ∧ principal = structural ∨
       data.principalRestriction = some principal ∧ principal.Restricts structural) →
      (data.dropHook.isSome = true → principal.MayDiscard) →
      CapabilityEquation program assignment (.nominal id arguments) principal
  | callable {id function arguments substitution captures} : program.function id = some function →
      Instantiates function.signature.generics arguments substitution →
      ListRel (Substitutes substitution) function.captures captures →
      CapabilityEquation program assignment (.callable id arguments) (Principal.fields (captures.map assignment))
  | environment {definition brand region} : Definition.environment definition ∈ program.declarations →
      definition.brand = brand → definition.region = region →
      CapabilityEquation program assignment (.environment brand region) (Principal.fields (definition.residents.map assignment))
  | available {brand region} : CapabilityEquation program assignment (.available brand region)
      (assignment (.environment brand region))
  | bindings {brand region fields} : CapabilityEquation program assignment (.bindings brand region fields)
      (Principal.fields (fields.map assignment))
  | optionalContinuation {brand argument answer effects} :
      CapabilityEquation program assignment (.continuation brand argument answer effects ⟨0,some 1⟩) .affine
  | exactContinuation {brand argument answer effects n} : 0 < n →
      CapabilityEquation program assignment (.continuation brand argument answer effects ⟨n,some n⟩) .exact

def CapabilitySolution (program : Program) (assignment : Term → Principal) : Prop :=
  ∀ context term, Kinding program context term .type → Closed term →
    CapabilityEquation program assignment term (assignment term)

structure CapabilityModel (program : Program) where
  principal : Term → Principal
  equations : CapabilitySolution program principal
  greatest : ∀ other, CapabilitySolution program other → ∀ context term,
    Kinding program context term .type → Closed term → (other term).Restricts (principal term)

def PrincipalOf (program : Program) (type : Term) (principal : Principal) : Prop :=
  ∃ model : CapabilityModel program, model.principal type = principal

mutual
  inductive Equal (program : Program) (context : Context) : Term → Term → Prop where
    | refl {a} : Equal program context a a
    | symm {a b} : Equal program context a b → Equal program context b a
    | trans {a b c} : Equal program context a b → Equal program context b c → Equal program context a c
    | congr {a b} : SameHead a b → ListRel (Equal program context) a.children b.children → Equal program context a b
    | assumed {a b} : Constraint.equal a b ∈ context.assumptions → Equal program context a b
    | alias {id declaration arguments substitution value} : program.alias id = some declaration →
        Instantiates declaration.generics arguments substitution → Substitutes substitution declaration.value value →
        Equal program context (.alias id arguments) value
    | projection {trait member owners items implementation implSub associated body specialized itemSub value} :
        SelectsImpl program context trait owners false implementation implSub →
        program.associated member = some associated → associated.owner = trait →
        (member,body) ∈ implementation.associated → Substitutes implSub body specialized →
        Instantiates associated.generics items itemSub → Substitutes itemSub specialized value →
        Equal program context (.projection trait member owners items associated.kind) value
    | defaultProjection {trait member owners items implementation implSub associated body specialized itemSub value} :
        SelectsImpl program context trait owners false implementation implSub →
        program.associated member = some associated → associated.owner = trait →
        (∀ body, (member,body) ∉ implementation.associated) → associated.defaultValue = some body →
        Substitutes implSub body specialized → Instantiates associated.generics items itemSub →
        Substitutes itemSub specialized value → Equal program context (.projection trait member owners items associated.kind) value
    | rowPermutation {instances tails instances' tails'} : instances.Perm instances' → tails.Perm tails' →
        Equal program context (.row instances tails) (.row instances' tails')
    | rowFlatten {instances tails nested nestedTails} :
        Equal program context (.row instances (.row nested nestedTails :: tails)) (.row (instances ++ nested) (nestedTails ++ tails))
    | rowDuplicate {a b rest tails} : Equal program context a b →
        Equal program context (.row (a :: b :: rest) tails) (.row (a :: rest) tails)
    | tailDuplicate {instances a b tails} : Equal program context a b →
        Equal program context (.row instances (a :: b :: tails)) (.row instances (a :: tails))

  inductive SelectsImpl (program : Program) (context : Context) :
      DeclId → List Term → Bool → ImplDefinition → Substitution → Prop where
    | selected {trait arguments negative implementation substitution head requirements} :
        Definition.implementation implementation ∈ program.declarations → implementation.trait = trait →
        implementation.negative = negative →
        (∃ values, Instantiates implementation.generics values substitution ∧
          ∀ value ∈ values, Kinding program context value value.kind) →
        ListRel (Substitutes substitution) implementation.arguments head →
        ListRel (Equal program context) head arguments →
        ListRel (SubstituteConstraint substitution) implementation.requirements requirements →
        (∀ requirement ∈ requirements, Entails program context requirement) →
        SelectsImpl program context trait arguments negative implementation substitution

  inductive RowMember (program : Program) (context : Context) : Term → Term → Prop where
    | head {effect instances tails instance} : instance ∈ instances → Equal program context effect instance →
        RowMember program context effect (.row instances tails)
    | tail {effect instances tails tail} : tail ∈ tails → RowMember program context effect tail →
        RowMember program context effect (.row instances tails)
    | equal {effect a b} : Equal program context a b → RowMember program context effect a → RowMember program context effect b

  inductive RowSubset (program : Program) (context : Context) : Term → Term → Prop where
    | empty {allowed} : RowSubset program context (.row [] []) allowed
    | assumed {required allowed} : Constraint.rowIncludes allowed required ∈ context.assumptions →
        RowSubset program context required allowed
    | same {a b} : Equal program context a b → RowSubset program context a b
    | trans {a b c} : RowSubset program context a b → RowSubset program context b c → RowSubset program context a c
    | instances {instances tails allowed} : (∀ instance ∈ instances, RowMember program context instance allowed) →
        (∀ tail ∈ tails, RowSubset program context tail allowed) → RowSubset program context (.row instances tails) allowed

  inductive TypeOutlives (program : Program) (context : Context) : Term → Term → Prop where
    | assumed {type region} : Constraint.typeOutlives type region ∈ context.assumptions → TypeOutlives program context type region
    | scalar {type region} : TypeOutlives program context (.scalar type) region
    | unit {region} : TypeOutlives program context .unit region
    | pointer {mode type region} : TypeOutlives program context (.rawPointer mode type) region
    | reference {mode long type short} : RegionIncludes context.assumptions long short →
        TypeOutlives program context (.reference mode long type) short
    | aggregate {type region} :
        (∀ mode lifetime referent, type ≠ .reference mode lifetime referent) →
        (∀ id kind, type ≠ .parameter id kind) →
        (∀ child ∈ type.children, child.kind = .region → RegionIncludes context.assumptions child region) →
        (∀ child ∈ type.children, child.kind = .type → TypeOutlives program context child region) →
        TypeOutlives program context type region
    | equal {a b region} : Equal program context a b → TypeOutlives program context a region → TypeOutlives program context b region

  inductive Entails (program : Program) : Context → Constraint → Prop where
    | checkedCallable {context function relation substitution receiver arguments result effects} :
        program.function function.header.id = some function → relation ∈ function.invocations →
        Substitutes substitution relation.receiver receiver → ListRel (Substitutes substitution) relation.arguments arguments →
        Substitutes substitution relation.result result → Substitutes substitution relation.effects effects →
        Entails program context (.callable receiver arguments result effects relation.unsafe)
    | checkedRunsIn {context function relation substitution receiver access arguments after} :
        program.function function.header.id = some function → relation ∈ function.invocations →
        Substitutes substitution relation.receiver receiver → Substitutes substitution relation.access access →
        ListRel (Substitutes substitution) relation.arguments arguments → Substitutes substitution relation.after after →
        Entails program context (.runsIn receiver access arguments after relation.unsafe)
    | assumed {context constraint} : constraint ∈ context.assumptions → Entails program context constraint
    | equality {context a b} : Equal program context a b → Entails program context (.equal a b)
    | outlives {context a b} : RegionIncludes context.assumptions a b → Entails program context (.outlives a b)
    | typeOutlives {context type region} : TypeOutlives program context type region → Entails program context (.typeOutlives type region)
    | rows {context allowed required} : RowSubset program context required allowed → Entails program context (.rowIncludes allowed required)
    | implementation {context trait arguments negative implementation substitution} :
        SelectsImpl program context trait arguments negative implementation substitution →
        Entails program context (.implements trait arguments negative)
    | use {context type quantity principal} : PrincipalOf program type principal → quantity.Request principal →
        Entails program context (.use type quantity)
    | quantified {context binders requirements} :
        (∀ values substitution, Instantiates binders values substitution →
          (∀ value ∈ values, Kinding program context value value.kind) →
          ∀ requirement ∈ requirements, ∃ instantiated,
            SubstituteConstraint substitution requirement instantiated ∧ Entails program context instantiated) →
        Entails program context (.quantified binders requirements)
end

def ConstraintsHold (program : Program) (context : Context) (substitution : Substitution)
    (requirements : List Constraint) : Prop :=
  ∀ requirement ∈ requirements, ∃ instantiated,
    SubstituteConstraint substitution requirement instantiated ∧ Entails program context instantiated

def DomainValid (program : Program) (context : Context) (term : Term) : Prop :=
  (∀ id arguments data substitution, Occurs (.nominal id arguments) term → program.data id = some data →
    Instantiates data.generics arguments substitution → ConstraintsHold program context substitution data.requirements) ∧
  (∀ id arguments effect substitution, Occurs (.effect id arguments) term → program.effect id = some effect →
    Instantiates effect.generics arguments substitution → ConstraintsHold program context substitution effect.requirements) ∧
  (∀ trait member owners items declaration associated ownerSub itemSub,
    Occurs (.projection trait member owners items associated.kind) term →
    program.trait trait = some declaration → program.associated member = some associated →
    Instantiates declaration.generics owners ownerSub → Instantiates associated.generics items itemSub →
    ConstraintsHold program context ownerSub declaration.requirements ∧
    ConstraintsHold program context (itemSub ++ ownerSub) associated.requirements)

def WellKinded (program : Program) (context : Context) (term : Term) (kind : Kind) : Prop :=
  Kinding program context term kind ∧ DomainValid program context term

inductive ConstantType (program : Program) (context : Context) : Term → Term → Prop where
  | scalar {value} : value.Valid program.input.target → ConstantType program context (.constant value) (.scalar value.type)
  | unit : ConstantType program context (.constantTuple []) .unit
  | tuple {fields types} : ListRel (ConstantType program context) fields types →
      ConstantType program context (.constantTuple fields) (.tuple types)
  | constructor {constructor data variant arguments values substitution types} :
      program.Constructor constructor data variant → Instantiates data.generics arguments substitution →
      ListRel (Substitutes substitution) (variant.fields.map (·.type)) types →
      ListRel (ConstantType program context) values types →
      ConstantType program context (.constantConstructor constructor arguments values) (.nominal data.header.id arguments)
  | equal {value a b} : ConstantType program context value a → Equal program context a b → ConstantType program context value b

inductive Variance where
  | invariant | covariant | contravariant | unused
  deriving DecidableEq, BEq, Repr, Inhabited

def Variance.flip : Variance → Variance
  | .covariant => .contravariant | .contravariant => .covariant | other => other

inductive ParameterPosition (program : Program) (parameter : Identity) : Term → Variance → Prop where
  | parameter {kind} : ParameterPosition program parameter (.parameter parameter kind) .covariant
  | sharedRegion {region type variance} : ParameterPosition program parameter region variance →
      ParameterPosition program parameter (.reference .shared region type) variance
  | sharedType {region type variance} : ParameterPosition program parameter type variance →
      ParameterPosition program parameter (.reference .shared region type) variance
  | uniqueRegion {region type variance} : ParameterPosition program parameter region variance →
      ParameterPosition program parameter (.reference .unique region type) variance
  | uniqueType {region type variance} : ParameterPosition program parameter type variance →
      ParameterPosition program parameter (.reference .unique region type) .invariant
  | brand {type id level} : Occurs (.parameter parameter .brand) type →
      Occurs (.rigid id .brand level) type → ParameterPosition program parameter type .invariant
  | aggregate {type child variance} : child ∈ type.children →
      (∀ mode region referent, type ≠ .reference mode region referent) →
      (∀ trait member owners items kind, type ≠ .projection trait member owners items kind) →
      ParameterPosition program parameter child variance → ParameterPosition program parameter type variance
  | projection {trait member owners items kind argument variance} : argument ∈ owners ++ items →
      ParameterPosition program parameter argument variance →
      ParameterPosition program parameter (.projection trait member owners items kind) .invariant

def NominalVariance (program : Program) (data : DataDefinition) (parameter : Identity) (variance : Variance) : Prop :=
  let fields := (data.variants.flatMap (·.fields)).map (·.type)
  match variance with
  | .unused => ∀ field ∈ fields, ∀ position, ¬ ParameterPosition program parameter field position
  | .covariant => (∀ field ∈ fields, ∀ position, ParameterPosition program parameter field position → position = .covariant) ∧
      ∃ field ∈ fields, ParameterPosition program parameter field .covariant
  | .contravariant => (∀ field ∈ fields, ∀ position, ParameterPosition program parameter field position → position = .contravariant) ∧
      ∃ field ∈ fields, ParameterPosition program parameter field .contravariant
  | .invariant => True

inductive Subtype (program : Program) (context : Context) : Term → Term → Prop where
  | equal {a b} : Equal program context a b → Subtype program context a b
  | bottom {type} : WellKinded program context type .type → Subtype program context .bottom type
  | shared {long short a b} : RegionIncludes context.assumptions long short → Subtype program context a b →
      Subtype program context (.reference .shared long a) (.reference .shared short b)
  | unique {long short a b} : RegionIncludes context.assumptions long short → Equal program context a b →
      Subtype program context (.reference .unique long a) (.reference .unique short b)
  | tuple {a b} : ListRel (Subtype program context) a b → Subtype program context (.tuple a) (.tuple b)
  | array {a b n m} : Subtype program context a b → Equal program context n m →
      Subtype program context (.array a n) (.array b m)
  | nominal {id data a b} : program.data id = some data → a.length = data.generics.length → b.length = a.length →
      (∀ i binder x y, data.generics[i]? = some binder → a[i]? = some x → b[i]? = some y →
        Equal program context x y ∨
        (NominalVariance program data binder.id .covariant ∧ Subtype program context x y) ∨
        (NominalVariance program data binder.id .contravariant ∧ Subtype program context y x) ∨
        NominalVariance program data binder.id .unused) →
      Subtype program context (.nominal id a) (.nominal id b)

inductive LayoutOf (program : Program) (context : Context) : Term → Layout → Prop where
  | unit : LayoutOf program context .unit ⟨0,1,[],0,0,[]⟩
  | scalar {scalar} : scalar.Valid program.input.target →
      LayoutOf program context (.scalar scalar) ⟨scalar.bytes program.input.target,
        program.input.target.scalarAlignment scalar,[],0,0,[]⟩
  | reference {mode region referent} :
      LayoutOf program context (.reference mode region referent)
        ⟨program.input.target.pointerBits / 8,program.input.target.pointerBits / 8,[],0,0,[]⟩
  | pointer {mode referent} : LayoutOf program context (.rawPointer mode referent)
      ⟨program.input.target.pointerBits / 8,program.input.target.pointerBits / 8,[],0,0,[]⟩
  | tuple {fields layouts layout} : ListRel (LayoutOf program context) fields layouts → AggregateLayout layouts layout →
      LayoutOf program context (.tuple fields) layout
  | array {element sign width length elementLayout layout} : 0 ≤ length →
      IntegerRange program.input.target false .pointer length → LayoutOf program context element elementLayout →
      ArrayLayout elementLayout length.toNat layout →
      LayoutOf program context (.array element (.constant (.integer sign width length))) layout
  | nominal {id data arguments substitution variantTypes variantLayouts layout} : program.data id = some data →
      data.representation = .glorious → Instantiates data.generics arguments substitution →
      ListRel (fun variant types => ListRel (Substitutes substitution) (variant.fields.map (·.type)) types)
        data.variants variantTypes →
      ListRel (fun types layout => ∃ fields, ListRel (LayoutOf program context) types fields ∧ AggregateLayout fields layout)
        variantTypes variantLayouts →
      (data.isEnum = true ∧ EnumLayout variantLayouts layout ∨ data.isEnum = false ∧ variantLayouts = [layout]) →
      layout.size ≤ program.input.target.maximumObjectBytes → LayoutOf program context (.nominal id arguments) layout
  | transparent {id data arguments substitution variant fields types layouts distinguished layout} :
      program.data id = some data → data.representation = .transparent → data.isEnum = false → data.variants = [variant] →
      fields = variant.fields → Instantiates data.generics arguments substitution →
      ListRel (Substitutes substitution) (fields.map (·.type)) types → ListRel (LayoutOf program context) types layouts →
      layouts[distinguished]? = some layout →
      (∀ i other, layouts[i]? = some other → i ≠ distinguished → other.size = 0 ∧ other.alignment ≤ layout.alignment) →
      LayoutOf program context (.nominal id arguments) layout
  | alias {a b layout} : Equal program context a b → LayoutOf program context a layout → LayoutOf program context b layout

inductive CCompatible (program : Program) (context : Context) : Term → Layout → Prop where
  | scalar {scalar} : scalar ∈ program.input.target.cCompatibleScalars →
      CCompatible program context (.scalar scalar) ⟨scalar.bytes program.input.target,
        program.input.target.cScalarAlignment scalar,[],0,0,[]⟩
  | pointer {mode referent} : CCompatible program context (.rawPointer mode referent)
      ⟨program.input.target.pointerBits/8,program.input.target.pointerBits/8,[],0,0,[]⟩
  | record {id data arguments substitution variant types layouts layout} : program.data id = some data →
      data.representation = .c → data.isEnum = false → data.variants = [variant] →
      Instantiates data.generics arguments substitution → ListRel (Substitutes substitution) (variant.fields.map (·.type)) types →
      ListRel (CCompatible program context) types layouts → AggregateLayout layouts layout →
      CCompatible program context (.nominal id arguments) layout
  | enumeration {id data arguments sign width} : program.data id = some data →
      data.representation = .integer sign width → data.isEnum = true →
      (∀ variant ∈ data.variants, variant.fields = []) →
      IntegerRange program.input.target sign width (Int.ofNat data.variants.length - 1) →
      CCompatible program context (.nominal id arguments)
        ⟨width.bits program.input.target/8,program.input.target.cScalarAlignment (.integer sign width),[],0,0,[]⟩
  | transparent {type layout} : LayoutOf program context type layout →
      (∃ id data arguments variant substitution types layouts index represented,
        type = .nominal id arguments ∧ program.data id = some data ∧ data.representation = .transparent ∧
        data.variants = [variant] ∧ Instantiates data.generics arguments substitution ∧
        ListRel (Substitutes substitution) (variant.fields.map (·.type)) types ∧
        ListRel (LayoutOf program context) types layouts ∧ types[index]? = some represented ∧
        CCompatible program context represented layout ∧
        ∀ i other, layouts[i]? = some other → i ≠ index → other.size = 0) →
      CCompatible program context type layout
  | alias {a b layout} : Equal program context a b → CCompatible program context a layout → CCompatible program context b layout

def ImplLocal (program : Program) (implementation : ImplDefinition) : Prop :=
  implementation.trait.package = implementation.header.id.package ∨
  ∃ self id arguments normalized,
    implementation.arguments.head? = some self ∧
    Equal program ⟨implementation.generics,implementation.requirements,0,implementation.header.module,false⟩ self normalized ∧
    normalized = .nominal id arguments ∧ id.package = implementation.header.id.package

def Coherent (program : Program) : Prop :=
  ∀ left right, Definition.implementation left ∈ program.declarations →
    Definition.implementation right ∈ program.declarations → left.trait = right.trait →
    (∃ context leftValues rightValues leftSub rightSub leftHead rightHead,
      Instantiates left.generics leftValues leftSub ∧ Instantiates right.generics rightValues rightSub ∧
      ListRel (Substitutes leftSub) left.arguments leftHead ∧ ListRel (Substitutes rightSub) right.arguments rightHead ∧
      (∀ value ∈ leftValues ++ rightValues, WellKinded program context value value.kind) ∧
      ListRel (Equal program context) leftHead rightHead) → left.header.id = right.header.id

def SignatureWellFormed (program : Program) (module : ModuleId) (signature : Signature) : Prop :=
  let context : Context := ⟨signature.generics,signature.constraints,0,module,false⟩
  (signature.generics.map (·.id)).Nodup ∧
  (∀ parameter ∈ signature.parameters, WellKinded program context parameter .type) ∧
  WellKinded program context signature.result .type ∧ WellKinded program context signature.effects .row ∧
  (∀ i binder defaultValue, signature.generics[i]? = some binder → binder.defaultValue = some defaultValue →
    WellKinded program { context with binders := signature.generics.take i } defaultValue binder.kind)

def DeclarationWellFormed (program : Program) : Definition → Prop
  | .data data =>
    let context : Context := ⟨data.generics,data.requirements,0,data.header.module,false⟩
    (data.generics.map (·.id)).Nodup ∧ (data.variants.map (·.header.name)).Nodup ∧
    (data.isEnum = false → data.variants.length = 1) ∧
    (∀ variant ∈ data.variants, (variant.fields.map (·.header.name)).Nodup ∧
      ∀ field ∈ variant.fields, WellKinded program context field.type .type ∧ field.header.module = data.header.module) ∧
    (data.quantitySource.isSome = true → data.invariant.isSome = true) ∧
    (∀ hook, data.dropHook = some hook → ∃ function, program.function hook = some function ∧
      function.signature.effects = .row [] [] ∧ function.signature.result = .unit)
  | .alias alias => WellKinded program ⟨alias.generics,[],0,alias.header.module,false⟩ alias.value .type
  | .function function => SignatureWellFormed program function.header.module function.signature ∧
    function.parameters.length = function.signature.parameters.length ∧ function.parameters.Nodup ∧
    (function.cABI = true → function.signature.generics = [] ∧
      ∀ parameter ∈ function.signature.parameters ++ [function.signature.result],
        ∃ layout, CCompatible program ⟨[],[],0,function.header.module,false⟩ parameter layout) ∧
    (function.origin = .foreign → function.cABI = true) ∧
    (∀ manifest, function.origin = .runtime manifest → manifest = program.input.manifest.identity ∧
      ∃ binding ∈ program.input.manifest.bindings, binding.declaration = function.header.id ∧ binding.signature = function.signature)
  | .trait trait => (trait.generics.map (·.id)).Nodup ∧ trait.members.Nodup ∧
    (trait.relation ≠ .ordinary → ∃ binding ∈ program.input.manifest.bindings, binding.declaration = trait.header.id)
  | .associated associated => ∃ trait, program.trait associated.owner = some trait ∧ associated.header.id ∈ trait.members ∧
    (∀ value, associated.defaultValue = some value →
      WellKinded program ⟨trait.generics ++ associated.generics,trait.requirements ++ associated.requirements,
        0,associated.header.module,false⟩ value associated.kind)
  | .implementation implementation => ImplLocal program implementation ∧
    ∃ trait, program.trait implementation.trait = some trait ∧
      (trait.relation = .ordinary ∨ trait.relation = .use ∨ trait.relation = .drop) ∧
      (trait.unsafe = true → implementation.unsafe = true) ∧
      (implementation.associated.map Prod.fst).Nodup ∧ (implementation.functions.map Prod.fst).Nodup
  | .effect effect => (effect.generics.map (·.id)).Nodup ∧ effect.operations.Nodup ∧
    ∀ operation ∈ effect.operations, ∃ declaration, program.operation operation = some declaration ∧ declaration.family = effect.header.id
  | .operation operation => SignatureWellFormed program operation.header.module operation.signature ∧
    (operation.terminal = true ∧ operation.signature.result = .bottom ∧ operation.quantity = none ∨
     operation.terminal = false ∧ operation.signature.result ≠ .bottom ∧
       ∃ quantity, operation.quantity = some quantity ∧ quantity.SurfaceResumption)
  | .constant constant => ConstantType program ⟨constant.generics,[],0,constant.header.module,false⟩ constant.value constant.type
  | .global global => WellKinded program ⟨[],[],0,global.header.module,false⟩ global.type .type ∧
    PrincipalOf program global.type .duplicable
  | .module _ => True
  | .import _ => True
  | .fixity fixity => fixity.precedence ≤ 255 ∧
    ∃ function, program.function fixity.target = some function ∧ Visible function.header fixity.header.module
  | .environment environment => environment.brand.kind = .brand ∧ environment.region.kind = .region

def ProgramWellFormed (program : Program) : Prop :=
  SourceClosure program ∧ (program.declarations.map (·.header.id)).Nodup ∧
  (∀ left right, program.Header left → program.Header right → left.id = right.id → left = right) ∧
  (∀ left right, program.Header left → program.Header right →
    left.module = right.module → left.namespace = right.namespace → left.name = right.name → left.id = right.id) ∧
  (∀ declaration ∈ program.declarations, DeclarationWellFormed program declaration) ∧ Coherent program

end Glorious.Language
