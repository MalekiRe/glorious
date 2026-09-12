import GloriousLanguage.Declarations
import GloriousLanguage.RowSemantics

/-! Declarative static semantics. Proof search, inference-cell mutation and
normalization algorithms are deliberately not definitions of these relations. -/
namespace Glorious.Language

structure Context where
  binders : List Binder := []
  assumptions : List Constraint := []
  universeLevel : Nat := 0
  module : ModuleId
  unsafeAllowed : Bool := false
  scope : LexicalScope := {}
  deriving Repr, Inhabited

/-- The concrete resident fields of either a source callable or an operation
value. Capability, layout and byte addressing consume this same instance. -/
inductive CallableFields (program : Program) : DeclId → List Term → List Term → Prop where
  | function {id function arguments substitution captures} : program.function id = some function →
      Instantiates function.signature.generics arguments substitution →
      ListRel (Substitutes substitution) function.captures captures → CallableFields program id arguments captures
  | operation {id operation arguments substitution} : program.operation id = some operation →
      Instantiates operation.signature.generics arguments substitution → CallableFields program id arguments []

inductive Kinding (program : Program) (context : Context) : Term → Kind → Prop where
  | quantity {quantity} : (∀ upper, quantity.upper = some upper → quantity.lower ≤ upper) →
      Kinding program context (.quantity quantity) .quantity
  | parameter {binder} : binder ∈ context.binders → Kinding program context (.parameter binder.id binder.kind) binder.kind
  | rigid {id kind level} : level ≤ context.universeLevel → Kinding program context (.rigid id kind level) kind
  | scopedRegion {id} : id ∈ context.scope.regions → Kinding program context (.scopedRegion id) .region
  | scopedBrand {id} : id ∈ context.scope.brands → Kinding program context (.scopedBrand id) .brand
  | runtimeRegion {id} : Kinding program context (.runtimeRegion id) .region
  | runtimeBrand {id} : Kinding program context (.runtimeBrand id) .brand
  | variable {id kind level} : level ≤ context.universeLevel → Kinding program context (.variable id kind level) kind
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
  | environment {brand region residents} : Kinding program context brand .brand → Kinding program context region .region →
      (∀ resident ∈ residents, Kinding program context resident .type) →
      Kinding program context (.environment brand region residents) .type
  | available {brand region residents} : Kinding program context brand .brand → Kinding program context region .region →
      (∀ resident ∈ residents, Kinding program context resident .type) →
      Kinding program context (.available brand region residents) .type
  | bindings {brand region arguments} : Kinding program context brand .brand → Kinding program context region .region →
      (∀ argument ∈ arguments, Kinding program context argument .type) →
      Kinding program context (.bindings brand region arguments) .type
  | effect {id declaration arguments substitution} : program.effect id = some declaration →
      Instantiates declaration.generics arguments substitution →
      (∀ argument ∈ arguments, Kinding program context argument argument.kind) → Kinding program context (.effect id arguments) .effect
  | row {instances tails} : (∀ instanceTerm ∈ instances, Kinding program context instanceTerm .effect) →
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
      (∀ argument ∈ arguments, Kinding program context argument argument.kind) →
      fields.length = variant.fields.length → (∀ field ∈ fields, Kinding program context field .constant) →
      Kinding program context (.constantConstructor constructor arguments fields) .constant
  | principal {principal} : Kinding program context (.principal principal) .quantity
  | static : Kinding program context .staticRegion .region

/-- A capability equation is local. Recursive nominal derivation is specified
below as its greatest solution, not an acyclic field walk or assumed Copy. -/
inductive CapabilityEquation (program : Program) (assignment : Term → Option Principal) : Term → Principal → Prop where
  | unit : CapabilityEquation program assignment .unit .duplicable
  | bottom : CapabilityEquation program assignment .bottom .duplicable
  | scalar {type} : CapabilityEquation program assignment (.scalar type) .duplicable
  | raw {mode type} : CapabilityEquation program assignment (.rawPointer mode type) .duplicable
  | shared {region type} : CapabilityEquation program assignment (.reference .shared region type) .duplicable
  | unique {region type} : CapabilityEquation program assignment (.reference .unique region type) .affine
  | label {brand region result} : CapabilityEquation program assignment (.label brand region result) .duplicable
  | tuple {fields principals} : ListRel (fun field principal => assignment field = some principal) fields principals →
      CapabilityEquation program assignment (.tuple fields) (Principal.fields principals)
  | emptyArray {element sign width} :
      CapabilityEquation program assignment (.array element (.constant (.integer sign width 0))) .duplicable
  | array {element sign width length principal} : 0 < length → assignment element = some principal →
      CapabilityEquation program assignment (.array element (.constant (.integer sign width length))) principal
  | alias {id declaration arguments substitution value principal} : program.alias id = some declaration →
      Instantiates declaration.generics arguments substitution → Substitutes substitution declaration.value value →
      assignment value = some principal → CapabilityEquation program assignment (.alias id arguments) principal
  | nominal {id data arguments substitution fields principals marker structural principal} : program.data id = some data →
      Instantiates data.generics arguments substitution →
      ListRel (Substitutes substitution) ((data.variants.flatMap (·.fields)).map (·.type)) fields →
      ListRel (fun field capability => assignment field = some capability) fields principals →
      (data.quantitySource = none ∧ marker = .duplicable ∨
       ∃ source value, data.quantitySource = some source ∧ Substitutes substitution source value ∧
         (value = .principal marker ∨ value.kind = .type ∧ assignment value = some marker)) →
      structural = (Principal.fields principals).meet marker →
      (data.principalRestriction = none ∧ principal = structural ∨
       data.principalRestriction = some principal ∧ principal.Restricts structural) →
      (data.dropHook.isSome = true → principal.MayDiscard) →
      CapabilityEquation program assignment (.nominal id arguments) principal
  | callable {id arguments captures principals} : CallableFields program id arguments captures →
      ListRel (fun field capability => assignment field = some capability) captures principals →
      CapabilityEquation program assignment (.callable id arguments) (Principal.fields principals)
  | environment {brand region residents principals} :
      ListRel (fun field capability => assignment field = some capability) residents principals →
      CapabilityEquation program assignment (.environment brand region residents) (Principal.fields principals)
  | available {brand region residents principal} : assignment (.environment brand region residents) = some principal →
      CapabilityEquation program assignment (.available brand region residents) principal
  | bindings {brand region fields principals} :
      ListRel (fun field capability => assignment field = some capability) fields principals →
      CapabilityEquation program assignment (.bindings brand region fields) (Principal.fields principals)
  | optionalContinuation {brand argument answer effects} :
      CapabilityEquation program assignment (.continuation brand argument answer effects ⟨0,some 1⟩) .affine
  | exactContinuation {brand argument answer effects n} : 0 < n →
      CapabilityEquation program assignment (.continuation brand argument answer effects ⟨n,some n⟩) .exact

/-- Absence is an explicit unknown, not an unconstrained principal. Every
published answer, including one involving abstract regions or brands, must
satisfy an equation; unsupported types cannot gain permission by omission. -/
def CapabilitySolution (program : Program) (assignment : Term → Option Principal) : Prop :=
  ∀ term principal, assignment term = some principal ↔ CapabilityEquation program assignment term principal

structure CapabilityModel (program : Program) where
  principal : Term → Option Principal
  equations : CapabilitySolution program principal
  greatest : ∀ other, CapabilitySolution program other → ∀ term result,
    other term = some result → ∃ selected, principal term = some selected ∧ result.Restricts selected

def PrincipalOf (program : Program) (type : Term) (principal : Principal) : Prop :=
  ∃ model : CapabilityModel program, model.principal type = some principal

/-- Logical replacement shares the existing predicate template and its two
actual capture-admissible simultaneous substitutions. In particular, quantified
binder identities are masked by `SubstituteConstraint`, while the predicate
constructor, quantities, trait polarity and unsafe annotations remain fixed. -/
inductive ConstraintCongruence (relation : Term → Term → Prop) : Constraint → Constraint → Prop where
  | substitution {template left right leftSub rightSub} :
      (∀ id kind, relation ((leftSub.get id).getD (.parameter id kind))
        ((rightSub.get id).getD (.parameter id kind))) →
      SubstituteConstraint leftSub template left → SubstituteConstraint rightSub template right →
      ConstraintCongruence relation left right

mutual
  inductive Equal (program : Program) (context : Context) : Term → Term → Prop where
    | refl {a} : Equal program context a a
    | symm {a b} : Equal program context a b → Equal program context b a
    | trans {a b c} : Equal program context a b → Equal program context b c → Equal program context a c
    | congr {a b} : SameHead a b → ListRel (Equal program context) a.children b.children → Equal program context a b
    | assumed {a b} : Constraint.equal a b ∈ context.assumptions → Equal program context a b
    | entailed {a b} : Entails program context (.equal a b) → Equal program context a b
    | definitional {a b} : DefinitionallyEqual program context a b → Equal program context a b
    | rowDuplicate {a b rest tails} : Equal program context a b →
        Equal program context (.row (a :: b :: rest) tails) (.row (a :: rest) tails)
    | tailDuplicate {instances a b tails} : Equal program context a b →
        Equal program context (.row instances (a :: b :: tails)) (.row instances (a :: tails))

  inductive SelectsImpl (program : Program) (context : Context) :
      DeclId → List Term → Bool → ImplDefinition → Substitution → Prop where
    | selected {trait arguments negative implementation substitution} :
        Definition.implementation implementation ∈ program.declarations → implementation.trait = trait →
        implementation.negative = negative → MatchesImplHead program context implementation arguments substitution →
        (∀ requirement ∈ implementation.requirements, EntailsSubstitution program context substitution requirement) →
        SelectsImpl program context trait arguments negative implementation substitution

  inductive RowMember (program : Program) (context : Context) : Term → Term → Prop where
    | head {effect instances tails instanceTerm} : instanceTerm ∈ instances → Equal program context effect instanceTerm →
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
    | instances {instances tails allowed} : (∀ instanceTerm ∈ instances, RowMember program context instanceTerm allowed) →
        (∀ tail ∈ tails, RowSubset program context tail allowed) → RowSubset program context (.row instances tails) allowed
    | entailed {required allowed} : Entails program context (.rowIncludes allowed required) →
        RowSubset program context required allowed

  inductive TypeOutlives (program : Program) (context : Context) : Term → Term → Prop where
    | assumed {type region} : Constraint.typeOutlives type region ∈ context.assumptions → TypeOutlives program context type region
    | scalar {type region} : TypeOutlives program context (.scalar type) region
    | unit {region} : TypeOutlives program context .unit region
    | pointer {mode type region} : TypeOutlives program context (.rawPointer mode type) region
    | reference {mode long type short} : Entails program context (.outlives long short) →
        TypeOutlives program context (.reference mode long type) short
    | bottom {region} : TypeOutlives program context .bottom region
    | tuple {fields region} : (∀ field ∈ fields, TypeOutlives program context field region) →
        TypeOutlives program context (.tuple fields) region
    | array {element count region} : TypeOutlives program context element region →
        TypeOutlives program context (.array element count) region
    | nominal {id arguments data substitution fields region} : program.data id = some data →
        Instantiates data.generics arguments substitution →
        ListRel (Substitutes substitution) ((data.variants.flatMap (·.fields)).map (·.type)) fields →
        (∀ field ∈ fields, TypeOutlives program context field region) →
        TypeOutlives program context (.nominal id arguments) region
    | callable {id arguments fields region} : CallableFields program id arguments fields →
        (∀ field ∈ fields, TypeOutlives program context field region) →
        TypeOutlives program context (.callable id arguments) region
    | label {brand long result short} : Entails program context (.outlives long short) →
        TypeOutlives program context (.label brand long result) short
    | environment {brand long residents short} : Entails program context (.outlives long short) →
        (∀ field ∈ residents, TypeOutlives program context field short) →
        TypeOutlives program context (.environment brand long residents) short
    | available {brand long residents short} : TypeOutlives program context (.environment brand long residents) short →
        TypeOutlives program context (.available brand long residents) short
    | bindings {brand long fields short} : Entails program context (.outlives long short) →
        (∀ field ∈ fields, TypeOutlives program context field short) →
        TypeOutlives program context (.bindings brand long fields) short
    | equal {a b region} : Equal program context a b → TypeOutlives program context a region → TypeOutlives program context b region
    | entailed {type region} : Entails program context (.typeOutlives type region) → TypeOutlives program context type region

  inductive Entails (program : Program) (context : Context) : Constraint → Prop where
    | checkedCallable {function relation substitution receiver arguments result effects} :
        program.function function.header.id = some function → relation ∈ function.invocations →
        Substitutes substitution relation.receiver receiver → ListRel (Substitutes substitution) relation.arguments arguments →
        Substitutes substitution relation.result result → Substitutes substitution relation.effects effects →
        Entails program context (.callable receiver arguments result effects relation.unsafeAllowed)
    | checkedRunsIn {function relation substitution receiver access arguments after} :
        program.function function.header.id = some function → relation ∈ function.invocations →
        Substitutes substitution relation.receiver receiver → Substitutes substitution relation.access access →
        ListRel (Substitutes substitution) relation.arguments arguments → Substitutes substitution relation.after after →
        Entails program context (.runsIn receiver access arguments after relation.unsafeAllowed)
    | assumed {constraint} : constraint ∈ context.assumptions → Entails program context constraint
    | congr {before after} : ConstraintCongruence (Equal program context) before after →
        Entails program context before → Entails program context after
    | equality {a b} : Equal program context a b → Entails program context (.equal a b)
    | outlivesRefl {region} : Entails program context (.outlives region region)
    | outlivesStatic {region} : Entails program context (.outlives .staticRegion region)
    | outlivesTrans {a b c} : Entails program context (.outlives a b) → Entails program context (.outlives b c) →
        Entails program context (.outlives a c)
    | typeOutlives {type region} : TypeOutlives program context type region → Entails program context (.typeOutlives type region)
    | rows {allowed required} : RowSubset program context required allowed → Entails program context (.rowIncludes allowed required)
    | implementation {trait arguments negative implementation substitution} :
        SelectsImpl program context trait arguments negative implementation substitution →
        Entails program context (.implements trait arguments negative)
    | use {type quantity principal} : PrincipalOf program type principal → quantity.Request principal →
        Entails program context (.use type quantity)
    | quantified {binders requirements} :
        (∀ values substitution, Instantiates binders values substitution →
          (∀ value ∈ values, Kinding program context value value.kind) →
          ∀ requirement ∈ requirements, EntailsSubstitution program context substitution requirement) →
        Entails program context (.quantified binders requirements)
    | quantifiedInstance {binders requirements values substitution requirement result} :
        Entails program context (.quantified binders requirements) → Instantiates binders values substitution →
        (∀ value ∈ values, Kinding program context value value.kind) → requirement ∈ requirements →
        SubstituteConstraint substitution requirement result → Entails program context result

  inductive EntailsSubstitution (program : Program) (context : Context) : Substitution → Constraint → Prop where
    | instantiated {substitution requirement result} : SubstituteConstraint substitution requirement result →
        Entails program context result → EntailsSubstitution program context substitution requirement

  /-- Positive, demand-driven declaration expansion. Opaque arguments need
  only be kinded; unused alias and GAT arguments are not eagerly normalized.
  One simultaneous substitution preserves the identity of caller parameters. -/
  inductive DefinitionalStep (program : Program) (context : Context) : Term → Term → Prop where
    | alias {id declaration arguments substitution value} :
        program.alias id = some declaration → Instantiates declaration.generics arguments substitution →
        (∀ argument ∈ arguments, Kinding program context argument argument.kind) →
        Substitutes substitution declaration.value value → DefinitionalStep program context (.alias id arguments) value
    | projection {trait member owners items associated ownerSub itemSub implementation implSub body value} :
        ProjectionDomain program context trait member owners items associated ownerSub itemSub →
        SelectsImpl program context trait owners false implementation implSub →
        (member,body) ∈ implementation.associated → Substitutes (implSub ++ itemSub) body value →
        DefinitionalStep program context (.projection trait member owners items associated.kind) value
    | defaultProjection {trait member owners items associated ownerSub itemSub implementation implSub body value} :
        ProjectionDomain program context trait member owners items associated ownerSub itemSub →
        SelectsImpl program context trait owners false implementation implSub →
        (∀ body, (member,body) ∉ implementation.associated) → associated.defaultValue = some body →
        Substitutes (ownerSub ++ itemSub) body value →
        DefinitionalStep program context (.projection trait member owners items associated.kind) value

  /-- Definitional convertibility contains no arbitrary context equality.
  In particular, an opaque projection compares reflexively without an assumed
  absence of reduction or a fabricated normal form. -/
  inductive DefinitionallyEqual (program : Program) (context : Context) : Term → Term → Prop where
    | refl {term} : DefinitionallyEqual program context term term
    | symm {left right} : DefinitionallyEqual program context left right → DefinitionallyEqual program context right left
    | trans {left middle right} : DefinitionallyEqual program context left middle →
        DefinitionallyEqual program context middle right → DefinitionallyEqual program context left right
    | congr {left right} : SameHead left right →
        ListRel (DefinitionallyEqual program context) left.children right.children → DefinitionallyEqual program context left right
    | step {left right} : DefinitionalStep program context left right → DefinitionallyEqual program context left right
    | row {left right} : RowEquivalent left right → DefinitionallyEqual program context left right

  /-- The positive reduction closure is kept distinct from symmetric
  convertibility. Its joinability and confluence are proof obligations, not
  constructor premises or assertions that an eager evaluator terminates. -/
  inductive DefinitionalReduction (program : Program) (context : Context) : Term → Term → Prop where
    | refl {term} : DefinitionalReduction program context term term
    | step {left right} : DefinitionalStep program context left right → DefinitionalReduction program context left right
    | trans {left middle right} : DefinitionalReduction program context left middle →
        DefinitionalReduction program context middle right → DefinitionalReduction program context left right
    | congr {left right} : SameHead left right →
        ListRel (DefinitionalReduction program context) left.children right.children → DefinitionalReduction program context left right
    | row {left right} : RowEquivalent left right → DefinitionalReduction program context left right

  /-- Actual inferred arguments and the single source substitution graph are
  authoritative. Matching compares instantiated heads by positive conversion,
  including opaque and row-equivalent arguments. -/
  inductive MatchesImplHead (program : Program) (context : Context) :
      ImplDefinition → List Term → Substitution → Prop where
    | matched {implementation arguments values substitution specialized} :
        Instantiates implementation.generics values substitution →
        (∀ value ∈ values, Kinding program context value value.kind) →
        ListRel (Substitutes substitution) implementation.arguments specialized →
        ListRel (DefinitionallyEqual program context) specialized arguments →
        MatchesImplHead program context implementation arguments substitution

  /-- Actual lexical trait and GAT domains. Ordered arguments are instantiated
  once against disjoint template binders, without normalizing unused items. -/
  inductive ProjectionDomain (program : Program) (context : Context) :
      DeclId → DeclId → List Term → List Term → AssociatedDefinition → Substitution → Substitution → Prop where
    | valid {trait member owners items declaration associated ownerSub itemSub} :
        program.trait trait = some declaration → member ∈ declaration.members →
        program.associated member = some associated → associated.owner = trait →
        Instantiates declaration.generics owners ownerSub → Instantiates associated.generics items itemSub →
        (∀ argument ∈ owners ++ items, Kinding program context argument argument.kind) →
        (∀ requirement ∈ declaration.requirements, EntailsSubstitution program context ownerSub requirement) →
        (∀ requirement ∈ associated.requirements, EntailsSubstitution program context (ownerSub ++ itemSub) requirement) →
        ProjectionDomain program context trait member owners items associated ownerSub itemSub
end

/-- Joining is positive evidence from the declared reductions. -/
def DefinitionallyJoinable (program : Program) (context : Context) (left right : Term) : Prop :=
  ∃ common, DefinitionalReduction program context left common ∧ DefinitionalReduction program context right common

def SubstitutionsJoinable (program : Program) (context : Context) (left right : Substitution) : Prop :=
  ListRel (fun first second => first.1 = second.1 ∧ DefinitionallyJoinable program context first.2 second.2) left right

/-- This admission check constrains common head solutions and inferred generic
arguments, not the associated-type result whose determinism is proved from it. -/
def HeadSolutionsCoherent (program : Program) (context : Context) : Prop :=
  ∀ left right, Definition.implementation left ∈ program.declarations →
    Definition.implementation right ∈ program.declarations → left.trait = right.trait →
    ∀ arguments leftSub rightSub,
      MatchesImplHead program context left arguments leftSub →
      MatchesImplHead program context right arguments rightSub →
      left.header.id = right.header.id ∧ SubstitutionsJoinable program context leftSub rightSub

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
    ConstraintsHold program context (ownerSub ++ itemSub) associated.requirements)

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

mutual
  inductive Subtype (program : Program) (context : Context) : Term → Term → Prop where
    | equal {a b} : Equal program context a b → Subtype program context a b
    | bottom {type} : WellKinded program context type .type → Subtype program context .bottom type
    | shared {long short a b} : Entails program context (.outlives long short) → Subtype program context a b →
        Subtype program context (.reference .shared long a) (.reference .shared short b)
    | unique {long short a b} : Entails program context (.outlives long short) → Equal program context a b →
        Subtype program context (.reference .unique long a) (.reference .unique short b)
    | tuple {a b} : ListRel (Subtype program context) a b → Subtype program context (.tuple a) (.tuple b)
    | array {a b n m} : Subtype program context a b → Equal program context n m →
        Subtype program context (.array a n) (.array b m)
    | nominal {id data a b} : program.data id = some data → a.length = data.generics.length → b.length = a.length →
        (∀ (i : Nat) (binder : Binder) (x y : Term), data.generics[i]? = some binder → a[i]? = some x → b[i]? = some y →
          VarianceSubtype program context data binder.id x y) →
        Subtype program context (.nominal id a) (.nominal id b)

  inductive VarianceSubtype (program : Program) (context : Context) : DataDefinition → Identity → Term → Term → Prop where
    | equal {data parameter a b} : Equal program context a b → VarianceSubtype program context data parameter a b
    | covariant {data parameter a b} : NominalVariance program data parameter .covariant → Subtype program context a b →
        VarianceSubtype program context data parameter a b
    | contravariant {data parameter a b} : NominalVariance program data parameter .contravariant → Subtype program context b a →
        VarianceSubtype program context data parameter a b
    | unused {data parameter a b} : NominalVariance program data parameter .unused → VarianceSubtype program context data parameter a b
end

mutual
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
    | callable {id arguments fields layouts layout} : CallableFields program id arguments fields →
        ListRel (LayoutOf program context) fields layouts →
        AggregateLayout (program.input.target.codeIdentityLayout :: layouts) layout →
        LayoutOf program context (.callable id arguments) layout
    | continuation {brand argument answer effects quantity} :
        LayoutOf program context (.continuation brand argument answer effects quantity) program.input.target.continuationLayout
    | label {brand region result} : LayoutOf program context (.label brand region result) ⟨0,1,[],0,0,[]⟩
    | available {brand region residents} : LayoutOf program context (.available brand region residents) ⟨0,1,[],0,0,[]⟩
    | bindings {brand region fields layouts layout} : ListRel (LayoutOf program context) fields layouts →
        AggregateLayout layouts layout → LayoutOf program context (.bindings brand region fields) layout
    | environment {brand region residents layouts layout} :
        ListRel (LayoutOf program context) residents layouts → AggregateLayout layouts layout →
        LayoutOf program context (.environment brand region residents) layout
    | array {element sign width length elementLayout layout} : 0 ≤ length →
        IntegerRange program.input.target false .pointer length → LayoutOf program context element elementLayout →
        ArrayLayout elementLayout length.toNat layout →
        LayoutOf program context (.array element (.constant (.integer sign width length))) layout
    | nominal {id data arguments substitution variantTypes variantLayouts layout} : program.data id = some data →
        data.representation = .glorious → Instantiates data.generics arguments substitution →
        ListRel (fun variant types => ListRel (Substitutes substitution) (variant.fields.map (·.type)) types)
          data.variants variantTypes →
        ListRel (FieldsHaveLayout program context) variantTypes variantLayouts →
        (data.isEnum = true ∧ EnumLayout variantLayouts layout ∨ data.isEnum = false ∧ variantLayouts = [layout]) →
        layout.size ≤ program.input.target.maximumObjectBytes → LayoutOf program context (.nominal id arguments) layout
    | transparent {id data arguments substitution variant fields types layouts distinguished represented layout} :
        program.data id = some data → data.representation = .transparent → data.isEnum = false → data.variants = [variant] →
        fields = variant.fields → Instantiates data.generics arguments substitution →
        ListRel (Substitutes substitution) (fields.map (·.type)) types → ListRel (LayoutOf program context) types layouts →
        layouts[distinguished]? = some represented → 0 < represented.size →
        (∀ (i : Nat) (other : Layout), layouts[i]? = some other → i ≠ distinguished → other.size = 0 ∧ other.alignment ≤ represented.alignment) →
        layout = { represented with offsets := List.replicate fields.length 0, tagBytes := 0, payloadOffset := 0, variants := [] } →
        LayoutOf program context (.nominal id arguments) layout
    | cRepresentation {id data arguments layout} : program.data id = some data →
        (data.representation = .c ∨ ∃ sign width, data.representation = .integer sign width) →
        CCompatible program context (.nominal id arguments) layout → LayoutOf program context (.nominal id arguments) layout
    | alias {a b layout} : Equal program context a b → LayoutOf program context a layout → LayoutOf program context b layout

  inductive FieldsHaveLayout (program : Program) (context : Context) : List Term → Layout → Prop where
    | fields {types layouts layout} : ListRel (LayoutOf program context) types layouts → AggregateLayout layouts layout →
        FieldsHaveLayout program context types layout
  inductive CCompatible (program : Program) (context : Context) : Term → Layout → Prop where
    | scalar {scalar} : scalar ∈ program.input.target.cCompatibleScalars →
        program.input.target.scalarAlignment scalar = program.input.target.cScalarAlignment scalar →
        CCompatible program context (.scalar scalar) ⟨scalar.bytes program.input.target,
          program.input.target.cScalarAlignment scalar,[],0,0,[]⟩
    | pointer {mode referent} : CCompatible program context (.rawPointer mode referent)
        ⟨program.input.target.pointerBits/8,program.input.target.pointerBits/8,[],0,0,[]⟩
    | record {id data arguments substitution variant types layouts layout} : program.data id = some data →
        data.representation = .c → data.isEnum = false → data.variants = [variant] →
        Instantiates data.generics arguments substitution → ListRel (Substitutes substitution) (variant.fields.map (·.type)) types →
        ListRel (CCompatible program context) types layouts → CRecordLayout program.input.target layouts layout →
        CCompatible program context (.nominal id arguments) layout
    | enumeration {id data arguments substitution sign width} : program.data id = some data →
        Instantiates data.generics arguments substitution → data.representation = .integer sign width → data.isEnum = true →
        data.variants ≠ [] → Scalar.Valid program.input.target (.integer sign width) →
        (∀ variant ∈ data.variants, variant.fields = []) →
        IntegerRange program.input.target sign width (Int.ofNat data.variants.length - 1) →
        CCompatible program context (.nominal id arguments)
          ⟨width.bits program.input.target/8,program.input.target.cScalarAlignment (.integer sign width),[],
            width.bits program.input.target/8,0,List.replicate data.variants.length []⟩
    | transparent {id data arguments variant substitution types layouts index represented representation layout} :
        LayoutOf program context (.nominal id arguments) layout → program.data id = some data →
        data.representation = .transparent → data.variants = [variant] → Instantiates data.generics arguments substitution →
        ListRel (Substitutes substitution) (variant.fields.map (·.type)) types →
        ListRel (LayoutOf program context) types layouts → types[index]? = some represented →
        CCompatible program context represented representation → 0 < representation.size →
        layout.size = representation.size → layout.alignment = representation.alignment →
        (∀ (i : Nat) (other : Layout), layouts[i]? = some other → i ≠ index → other.size = 0) →
        CCompatible program context (.nominal id arguments) layout
    | alias {a b layout} : Equal program context a b → CCompatible program context a layout → CCompatible program context b layout
end

/-- Logical ownership places are not necessarily machine-addressable.
Labels and open-environment witnesses have no constructor here. -/
inductive Addressable (program : Program) (context : Context) : Term → Prop where
  | unit : Addressable program context .unit
  | scalar {scalar} : Addressable program context (.scalar scalar)
  | tuple {fields} : Addressable program context (.tuple fields)
  | array {element count} : Addressable program context (.array element count)
  | nominal {id arguments} : Addressable program context (.nominal id arguments)
  | reference {mode region type} : Addressable program context (.reference mode region type)
  | pointer {mode type} : Addressable program context (.rawPointer mode type)
  | callable {id arguments} : Addressable program context (.callable id arguments)
  | continuation {brand argument answer effects quantity} :
      Addressable program context (.continuation brand argument answer effects quantity)
  | bindings {brand region fields} : Addressable program context (.bindings brand region fields)
  | equal {a b} : Equal program context a b → Addressable program context a → Addressable program context b

def ImplLocal (program : Program) (implementation : ImplDefinition) : Prop :=
  implementation.trait.package = implementation.header.id.package ∨
  ∃ (self : Term) (id : DeclId) (arguments : List Term) (normalized : Term),
    implementation.arguments.head? = some self ∧
    Equal program ⟨implementation.generics,implementation.requirements,0,implementation.header.module,false,{}⟩ self normalized ∧
    normalized = .nominal id arguments ∧ id.package = implementation.header.id.package

def Coherent (program : Program) : Prop :=
  ∀ context, HeadSolutionsCoherent program context

def SignatureWellFormed (program : Program) (module : ModuleId) (signature : Signature) : Prop :=
  let context : Context := ⟨signature.generics,signature.constraints,0,module,false,{}⟩
  (signature.generics.map (·.id)).Nodup ∧
  (∀ parameter ∈ signature.parameters, WellKinded program context parameter .type) ∧
  WellKinded program context signature.result .type ∧ WellKinded program context signature.effects .row ∧
  (∀ i binder defaultValue, signature.generics[i]? = some binder → binder.defaultValue = some defaultValue →
    WellKinded program { context with binders := signature.generics.take i } defaultValue binder.kind)

/-- Implementation heads and associated overrides are checked at the actual
trait and item domains. Distinct template binder identities permit one
simultaneous substitution; caller arguments are never recursively rewritten
by another template's parameter binding. -/
def ImplementationSignatureWellFormed (program : Program) (implementation : ImplDefinition)
    (trait : TraitDefinition) : Prop :=
  let context : Context := ⟨implementation.generics,implementation.requirements,0,implementation.header.module,false,{}⟩
  (implementation.generics.map (·.id)).Nodup ∧
  ∃ ownerSub, Instantiates trait.generics implementation.arguments ownerSub ∧
    (∀ argument ∈ implementation.arguments, WellKinded program context argument argument.kind) ∧
    ConstraintsHold program context ownerSub trait.requirements ∧
    ∀ member body, (member,body) ∈ implementation.associated →
      ∃ associated requirements, program.associated member = some associated ∧ member ∈ trait.members ∧
        associated.owner = implementation.trait ∧
        ((implementation.generics ++ associated.generics).map (·.id)).Nodup ∧
        ListRel (SubstituteConstraint ownerSub) associated.requirements requirements ∧
        WellKinded program ⟨implementation.generics ++ associated.generics,
          implementation.requirements ++ requirements,0,implementation.header.module,false,{}⟩ body associated.kind

def DeclarationShapeWellFormed (program : Program) : Definition → Prop
  | .data data =>
    let context : Context := ⟨data.generics,data.requirements,0,data.header.module,false,{}⟩
    (data.generics.map (·.id)).Nodup ∧ (data.variants.map (·.header.name)).Nodup ∧
    (data.isEnum = false → data.variants.length = 1) ∧
    (∀ variant ∈ data.variants, (variant.fields.map (·.header.name)).Nodup ∧
      ∀ field ∈ variant.fields, WellKinded program context field.type .type ∧ field.header.module = data.header.module) ∧
    (data.quantitySource.isSome = true → data.invariant.isSome = true) ∧
    (∀ hook, data.dropHook = some hook → ∃ function, program.function hook = some function)
  | .alias alias => (alias.generics.map (·.id)).Nodup ∧
    WellKinded program ⟨alias.generics,[],0,alias.header.module,false,{}⟩ alias.value .type
  | .function function => SignatureWellFormed program function.header.module function.signature ∧
    function.parameters.length = function.signature.parameters.length ∧ function.parameters.Nodup ∧
    (function.cABI = true → function.signature.generics = [] ∧
      (∀ parameter ∈ function.signature.parameters,
        ∃ layout, CCompatible program ⟨[],[],0,function.header.module,false,{}⟩ parameter layout) ∧
      (function.signature.result = .unit ∨ ∃ layout, CCompatible program ⟨[],[],0,function.header.module,false,{}⟩ function.signature.result layout)) ∧
    (function.origin = .foreign → function.cABI = true) ∧
    (∀ manifest, function.origin = .runtime manifest → manifest = program.input.manifest.identity ∧
      ∃ binding ∈ program.input.manifest.bindings, binding.declaration = function.header.id ∧ binding.signature = function.signature)
  | .trait trait => (trait.generics.map (·.id)).Nodup ∧ trait.members.Nodup ∧
    (trait.relation ≠ .ordinary → (trait.header.id,trait.relation) ∈ program.input.manifest.sealedRelations)
  | .associated associated => ∃ trait, program.trait associated.owner = some trait ∧ associated.header.id ∈ trait.members ∧
    ((trait.generics ++ associated.generics).map (·.id)).Nodup ∧
    (∀ value, associated.defaultValue = some value →
      WellKinded program ⟨trait.generics ++ associated.generics,trait.requirements ++ associated.requirements,
        0,associated.header.module,false,{}⟩ value associated.kind)
  | .implementation implementation => ImplLocal program implementation ∧
    ∃ trait, program.trait implementation.trait = some trait ∧
      (trait.relation = .ordinary ∨ trait.relation = .use ∨ trait.relation = .drop) ∧
      (trait.unsafeAllowed = true → implementation.unsafeAllowed = true) ∧
      (implementation.associated.map Prod.fst).Nodup ∧ (implementation.functions.map Prod.fst).Nodup ∧
      ImplementationSignatureWellFormed program implementation trait
  | .effect effect => (effect.generics.map (·.id)).Nodup ∧ effect.operations.Nodup ∧
    ∀ operation ∈ effect.operations, ∃ declaration, program.operation operation = some declaration ∧ declaration.family = effect.header.id
  | .operation operation => SignatureWellFormed program operation.header.module operation.signature ∧
    (operation.terminal = true ∧ operation.signature.result = .bottom ∧ operation.quantity = none ∨
     operation.terminal = false ∧ operation.signature.result ≠ .bottom ∧
       ∃ quantity, operation.quantity = some quantity ∧ quantity.SurfaceResumption)
  | .constant constant => ConstantType program ⟨constant.generics,[],0,constant.header.module,false,{}⟩ constant.value constant.type
  | .global global => WellKinded program ⟨[],[],0,global.header.module,false,{}⟩ global.type .type ∧
    PrincipalOf program global.type .duplicable
  | .module _ => True
  | .import _ => True
  | .fixity fixity => fixity.precedence ≤ 255 ∧
    ∃ function, program.function fixity.target = some function ∧ Visible function.header fixity.header.module

/-- Source templates are checked before runtime instantiation. Runtime atoms
remain well-kinded in execution judgments, but cannot occur literally in the
immutable declarations those judgments instantiate. -/
def DeclarationWellFormed (program : Program) (definition : Definition) : Prop :=
  (definition.Lexical ∧ definition.ScopeClosed) ∧ DeclarationShapeWellFormed program definition

def ProgramWellFormed (program : Program) : Prop :=
  SourceClosure program ∧ (program.declarations.map (·.header.id)).Nodup ∧
  (∀ left right, program.Header left → program.Header right → left.id = right.id → left = right) ∧
  (∀ left right, program.Header left → program.Header right →
    left.module = right.module → left.nameSpace = right.nameSpace → left.name = right.name → left.id = right.id) ∧
  (∀ declaration ∈ program.declarations, DeclarationWellFormed program declaration) ∧ Coherent program

end Glorious.Language
