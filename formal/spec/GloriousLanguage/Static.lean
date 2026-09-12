import GloriousLanguage.Declarations
import GloriousLanguage.RowSemantics
import GloriousLanguage.HeadStructure

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

def ImplDefinition.context (implementation : ImplDefinition) : Context :=
  ⟨implementation.generics,implementation.requirements,0,implementation.header.module,false,{}⟩

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

/-- A capability equation exposes a genuine structural head. Recursive
nominal dependencies use the greatest assignment below; transparent alias and
projection expansion must first finish through the actual finite reduction
judgment and cannot themselves guard a recursive permission claim. -/
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
  /-- Evidence is a lower bound on permissions, not a claim that a requested
  interval identifies the principal class. Recursive structural dependencies
  are coinductive; every logical leaf has a finite derivation in this mutual
  inductive judgment. A projection depending on Use cannot justify that same
  Use through an unsupported logical cycle. -/
  inductive CapabilityEvidence (program : Program) : Context → Term → Principal → Prop where
    | structural {context type principal assignment} : assignment type = some principal →
        (∀ term claimed, assignment term = some claimed → CapabilityUnfolds program context assignment term claimed) →
        CapabilityEvidence program context type principal
    | logical {context type quantity principal} : Entails program context (.use type quantity) →
        quantity.Valid → (∀ permitted, quantity.Request permitted → principal.Restricts permitted) →
        CapabilityEvidence program context type principal
    | equal {context left right principal} : Equal program context left right →
        CapabilityEvidence program context left principal → CapabilityEvidence program context right principal

  /-- One structural layer or one already justified logical leaf. Keeping
  this layer explicit separates the greatest structural recursion from the
  finite logical proof tree; it introduces no second dependency analysis. -/
  inductive CapabilityUnfolds (program : Program) :
      Context → (Term → Option Principal) → Term → Principal → Prop where
    | equation {context assignment type claimed supported} : claimed.Restricts supported →
        CapabilityEquation program assignment type supported → CapabilityUnfolds program context assignment type claimed
    | evidence {context assignment type claimed supported} : claimed.Restricts supported →
        CapabilityEvidence program context type supported → CapabilityUnfolds program context assignment type claimed
    | expansion {context assignment type exposed claimed} :
        DefinitionalStep program context type exposed →
        CapabilityUnfolds program context assignment exposed claimed →
        CapabilityUnfolds program context assignment type claimed

  inductive Equal (program : Program) : Context → Term → Term → Prop where
    | refl {context a} : Equal program context a a
    | symm {context a b} : Equal program context a b → Equal program context b a
    | trans {context a b c} : Equal program context a b → Equal program context b c → Equal program context a c
    | congrChildren {context a b} : SameHead a b →
        (∀ (index : Nat) first second, a.children[index]? = some first → b.children[index]? = some second →
          Equal program context first second) → Equal program context a b
    | assumed {context a b} : Constraint.equal a b ∈ context.assumptions → Equal program context a b
    | entailed {context a b} : Entails program context (.equal a b) → Equal program context a b
    | definitional {context a b} : DefinitionallyEqual program context a b → Equal program context a b
    | rowDuplicate {context a b rest tails} : Equal program context a b →
        Equal program context (.row (a :: b :: rest) tails) (.row (a :: rest) tails)
    | tailDuplicate {context instances a b tails} : Equal program context a b →
        Equal program context (.row instances (a :: b :: tails)) (.row instances (a :: tails))

  inductive SelectsImpl (program : Program) :
      Context → DeclId → List Term → Bool → ImplDefinition → Substitution → Prop where
    | selected {context trait arguments negative implementation substitution} :
        Definition.implementation implementation ∈ program.declarations → implementation.trait = trait →
        implementation.negative = negative → MatchesImplHead program context implementation arguments substitution →
        (∀ requirement ∈ implementation.requirements, EntailsSubstitution program context substitution requirement) →
        SelectsImpl program context trait arguments negative implementation substitution

  inductive RowMember (program : Program) : Context → Term → Term → Prop where
    | head {context effect instances tails instanceTerm} : instanceTerm ∈ instances → Equal program context effect instanceTerm →
        RowMember program context effect (.row instances tails)
    | tail {context effect instances tails tail} : tail ∈ tails → RowMember program context effect tail →
        RowMember program context effect (.row instances tails)
    | equal {context effect a b} : Equal program context a b → RowMember program context effect a → RowMember program context effect b

  inductive RowSubset (program : Program) : Context → Term → Term → Prop where
    | empty {context allowed} : RowSubset program context (.row [] []) allowed
    | assumed {context required allowed} : Constraint.rowIncludes allowed required ∈ context.assumptions →
        RowSubset program context required allowed
    | same {context a b} : Equal program context a b → RowSubset program context a b
    | trans {context a b c} : RowSubset program context a b → RowSubset program context b c → RowSubset program context a c
    | instances {context instances tails allowed} : (∀ instanceTerm ∈ instances, RowMember program context instanceTerm allowed) →
        (∀ tail ∈ tails, RowSubset program context tail allowed) → RowSubset program context (.row instances tails) allowed
    | entailed {context required allowed} : Entails program context (.rowIncludes allowed required) →
        RowSubset program context required allowed

  inductive TypeOutlives (program : Program) : Context → Term → Term → Prop where
    | assumed {context type region} : Constraint.typeOutlives type region ∈ context.assumptions → TypeOutlives program context type region
    | scalar {context type region} : TypeOutlives program context (.scalar type) region
    | unit {context region} : TypeOutlives program context .unit region
    | pointer {context mode type region} : TypeOutlives program context (.rawPointer mode type) region
    | reference {context mode long type short} : Entails program context (.outlives long short) →
        TypeOutlives program context (.reference mode long type) short
    | bottom {context region} : TypeOutlives program context .bottom region
    | tuple {context fields region} : (∀ field ∈ fields, TypeOutlives program context field region) →
        TypeOutlives program context (.tuple fields) region
    | array {context element count region} : TypeOutlives program context element region →
        TypeOutlives program context (.array element count) region
    | nominal {context id arguments data substitution fields region} : program.data id = some data →
        Instantiates data.generics arguments substitution →
        ListRel (Substitutes substitution) ((data.variants.flatMap (·.fields)).map (·.type)) fields →
        (∀ field ∈ fields, TypeOutlives program context field region) →
        TypeOutlives program context (.nominal id arguments) region
    | callable {context id arguments fields region} : CallableFields program id arguments fields →
        (∀ field ∈ fields, TypeOutlives program context field region) →
        TypeOutlives program context (.callable id arguments) region
    | label {context brand long result short} : Entails program context (.outlives long short) →
        TypeOutlives program context (.label brand long result) short
    | environment {context brand long residents short} : Entails program context (.outlives long short) →
        (∀ field ∈ residents, TypeOutlives program context field short) →
        TypeOutlives program context (.environment brand long residents) short
    | available {context brand long residents short} : TypeOutlives program context (.environment brand long residents) short →
        TypeOutlives program context (.available brand long residents) short
    | bindings {context brand long fields short} : Entails program context (.outlives long short) →
        (∀ field ∈ fields, TypeOutlives program context field short) →
        TypeOutlives program context (.bindings brand long fields) short
    | equal {context a b region} : Equal program context a b → TypeOutlives program context a region → TypeOutlives program context b region
    | entailed {context type region} : Entails program context (.typeOutlives type region) → TypeOutlives program context type region

  inductive Entails (program : Program) : Context → Constraint → Prop where
    | checkedCallable {context function relation substitution receiver arguments result effects} :
        program.function function.header.id = some function → relation ∈ function.invocations →
        Substitutes substitution relation.receiver receiver → ListRel (Substitutes substitution) relation.arguments arguments →
        Substitutes substitution relation.result result → Substitutes substitution relation.effects effects →
        Entails program context (.callable receiver arguments result effects relation.unsafeAllowed)
    | checkedRunsIn {context function relation substitution receiver access arguments after} :
        program.function function.header.id = some function → relation ∈ function.invocations →
        Substitutes substitution relation.receiver receiver → Substitutes substitution relation.access access →
        ListRel (Substitutes substitution) relation.arguments arguments → Substitutes substitution relation.after after →
        Entails program context (.runsIn receiver access arguments after relation.unsafeAllowed)
    | assumed {context constraint} : constraint ∈ context.assumptions → Entails program context constraint
    | congrSubstitution {context template before after leftSub rightSub} :
        (∀ id kind, Equal program context ((leftSub.get id).getD (.parameter id kind))
          ((rightSub.get id).getD (.parameter id kind))) →
        SubstituteConstraint leftSub template before → SubstituteConstraint rightSub template after →
        Entails program context before → Entails program context after
    | equality {context a b} : Equal program context a b → Entails program context (.equal a b)
    | outlivesRefl {context region} : Entails program context (.outlives region region)
    | outlivesStatic {context region} : Entails program context (.outlives .staticRegion region)
    | outlivesTrans {context a b c} : Entails program context (.outlives a b) → Entails program context (.outlives b c) →
        Entails program context (.outlives a c)
    | typeOutlives {context type region} : TypeOutlives program context type region → Entails program context (.typeOutlives type region)
    | rows {context allowed required} : RowSubset program context required allowed → Entails program context (.rowIncludes allowed required)
    | implementation {context trait arguments negative implementation substitution} :
        SelectsImpl program context trait arguments negative implementation substitution →
        Entails program context (.implements trait arguments negative)
    | use {context type quantity principal} : CapabilityEvidence program context type principal → quantity.Request principal →
        Entails program context (.use type quantity)
    | quantified {context binders requirements} :
        (∀ values substitution, Instantiates binders values substitution →
          (∀ value ∈ values, Kinding program context value value.kind) →
          ∀ requirement ∈ requirements, EntailsSubstitution program context substitution requirement) →
        Entails program context (.quantified binders requirements)
    | quantifiedInstance {context binders requirements values substitution requirement result} :
        Entails program context (.quantified binders requirements) → Instantiates binders values substitution →
        (∀ value ∈ values, Kinding program context value value.kind) → requirement ∈ requirements →
        SubstituteConstraint substitution requirement result → Entails program context result

  inductive EntailsSubstitution (program : Program) : Context → Substitution → Constraint → Prop where
    | instantiated {context substitution requirement result} : SubstituteConstraint substitution requirement result →
        Entails program context result → EntailsSubstitution program context substitution requirement

  /-- Positive, demand-driven declaration expansion. Opaque arguments need
  only be kinded; unused alias and GAT arguments are not eagerly normalized.
  One simultaneous substitution preserves the identity of caller parameters. -/
  inductive DefinitionalStep (program : Program) : Context → Term → Term → Prop where
    | alias {context id declaration arguments substitution value} :
        program.alias id = some declaration → Instantiates declaration.generics arguments substitution →
        (∀ argument ∈ arguments, Kinding program context argument argument.kind) →
        Substitutes substitution declaration.value value → DefinitionalStep program context (.alias id arguments) value
    | projection {context trait member owners items associated ownerSub itemSub implementation implSub body value} :
        ProjectionDomain program context trait member owners items associated ownerSub itemSub →
        SelectsImpl program context trait owners false implementation implSub →
        (member,body) ∈ implementation.associated → Substitutes (implSub ++ itemSub) body value →
        DefinitionalStep program context (.projection trait member owners items associated.kind) value
    | defaultProjection {context trait member owners items associated ownerSub itemSub implementation implSub body value} :
        ProjectionDomain program context trait member owners items associated ownerSub itemSub →
        SelectsImpl program context trait owners false implementation implSub →
        (∀ body, (member,body) ∉ implementation.associated) → associated.defaultValue = some body →
        Substitutes (ownerSub ++ itemSub) body value →
        DefinitionalStep program context (.projection trait member owners items associated.kind) value

  /-- Definitional convertibility contains no arbitrary context equality.
  In particular, an opaque projection compares reflexively without an assumed
  absence of reduction or a fabricated normal form. -/
  inductive DefinitionallyEqual (program : Program) : Context → Term → Term → Prop where
    | refl {context term} : DefinitionallyEqual program context term term
    | symm {context left right} : DefinitionallyEqual program context left right → DefinitionallyEqual program context right left
    | trans {context left middle right} : DefinitionallyEqual program context left middle →
        DefinitionallyEqual program context middle right → DefinitionallyEqual program context left right
    | congrChildren {context left right} : SameHead left right →
        (∀ (index : Nat) first second, left.children[index]? = some first → right.children[index]? = some second →
          DefinitionallyEqual program context first second) → DefinitionallyEqual program context left right
    | step {context left right} : DefinitionalStep program context left right → DefinitionallyEqual program context left right
    | row {context left right} : RowEquivalent left right → DefinitionallyEqual program context left right

  /-- The positive reduction closure is kept distinct from symmetric
  convertibility. Its joinability and confluence are proof obligations, not
  constructor premises or assertions that an eager evaluator terminates. -/
  inductive DefinitionalReduction (program : Program) : Context → Term → Term → Prop where
    | refl {context term} : DefinitionalReduction program context term term
    | step {context left right} : DefinitionalStep program context left right → DefinitionalReduction program context left right
    | trans {context left middle right} : DefinitionalReduction program context left middle →
        DefinitionalReduction program context middle right → DefinitionalReduction program context left right
    | congrChildren {context left right} : SameHead left right →
        (∀ (index : Nat) first second, left.children[index]? = some first → right.children[index]? = some second →
          DefinitionalReduction program context first second) → DefinitionalReduction program context left right
    | row {context left right} : RowEquivalent left right → DefinitionalReduction program context left right

  /-- Every instantiated generic value has a finite origin in the actual
  query. The final whole-head conversion checks all remaining constraints,
  including repeated occurrences; it cannot create a missing parameter origin. -/
  inductive MatchesImplHead (program : Program) :
      Context → ImplDefinition → List Term → Substitution → Prop where
    | inferred {context implementation arguments values substitution specialized} :
        Instantiates implementation.generics values substitution →
        (∀ value ∈ values, Kinding program context value value.kind) →
        ListRel (Substitutes substitution) implementation.arguments specialized →
        specialized.length = arguments.length →
        (∀ (index : Nat) first second, specialized[index]? = some first → arguments[index]? = some second →
          DefinitionallyEqual program context first second) →
        (∀ (index : Nat) binder value, implementation.generics[index]? = some binder → values[index]? = some value →
          InfersHeadArgument program context implementation arguments binder value) →
        MatchesImplHead program context implementation arguments substitution

  /-- Actual lexical trait and GAT domains. Ordered arguments are instantiated
  once against disjoint template binders, without normalizing unused items. -/
  inductive ProjectionDomain (program : Program) :
      Context → DeclId → DeclId → List Term → List Term → AssociatedDefinition → Substitution → Substitution → Prop where
    | valid {context trait member owners items declaration associated ownerSub itemSub} :
        program.trait trait = some declaration → member ∈ declaration.members →
        program.associated member = some associated → associated.owner = trait →
        Instantiates declaration.generics owners ownerSub → Instantiates associated.generics items itemSub →
        (∀ argument ∈ owners ++ items, Kinding program context argument argument.kind) →
        (∀ requirement ∈ declaration.requirements, EntailsSubstitution program context ownerSub requirement) →
        (∀ requirement ∈ associated.requirements, EntailsSubstitution program context (ownerSub ++ itemSub) requirement) →
        ProjectionDomain program context trait member owners items associated ownerSub itemSub

  /-- Source templates can expose a determining position only by actual
  positive expansion or by an ordered injective constructor. Query conversion
  preserves the language's existing definitional matching, but never changes
  which source parameter is being inferred. Both contexts are real indices. -/
  inductive InfersHeadParameter (program : Program) :
      Context → Context → Binder → Term → Term → Term → Prop where
    | parameter {context sourceContext binder value} : value.kind = binder.kind →
        InfersHeadParameter program sourceContext context binder (.parameter binder.id binder.kind) value value
    | child {context sourceContext binder template query templateChild queryChild value} {index : Nat} :
        template.StructuralHead → SameHead template query →
        template.children[index]? = some templateChild → query.children[index]? = some queryChild →
        InfersHeadParameter program sourceContext context binder templateChild queryChild value →
        InfersHeadParameter program sourceContext context binder template query value
    | sourceReduction {context sourceContext binder template reduced query value} :
        DefinitionalReduction program sourceContext template reduced →
        InfersHeadParameter program sourceContext context binder reduced query value →
        InfersHeadParameter program sourceContext context binder template query value
    | queryConversion {context sourceContext binder template query converted value} :
        DefinitionallyEqual program context query converted →
        InfersHeadParameter program sourceContext context binder template converted value →
        InfersHeadParameter program sourceContext context binder template query value

  /-- One generic argument is inferred at one actual paired head position.
  Keeping this constructor explicit makes the recursive occurrence positive
  without hiding its source context inside an existential encoding. -/
  inductive InfersHeadArgument (program : Program) :
      Context → ImplDefinition → List Term → Binder → Term → Prop where
    | argument {context implementation arguments binder value template query} {index : Nat} :
        implementation.arguments[index]? = some template → arguments[index]? = some query →
        InfersHeadParameter program implementation.context context binder template query value →
        InfersHeadArgument program context implementation arguments binder value
end

/-- These public interfaces consume the same ordered relation as before;
their kernel constructors use its equivalent pointwise presentation. -/
theorem Equal.congr {program : Program} {context : Context} {left right : Term}
    (same : SameHead left right) (children : ListRel (Equal program context) left.children right.children) :
    Equal program context left right := .congrChildren same (fun _ _ _ first second => children.at first second)

theorem DefinitionallyEqual.congr {program : Program} {context : Context} {left right : Term}
    (same : SameHead left right) (children : ListRel (DefinitionallyEqual program context) left.children right.children) :
    DefinitionallyEqual program context left right :=
  .congrChildren same (fun _ _ _ first second => children.at first second)

theorem DefinitionalReduction.congr {program : Program} {context : Context} {left right : Term}
    (same : SameHead left right) (children : ListRel (DefinitionalReduction program context) left.children right.children) :
    DefinitionalReduction program context left right :=
  .congrChildren same (fun _ _ _ first second => children.at first second)

theorem Entails.congr {program : Program} {context : Context} {before after : Constraint}
    (congruent : ConstraintCongruence (Equal program context) before after) (held : Entails program context before) :
    Entails program context after := by
  cases congruent with
  | substitution equal left right => exact .congrSubstitution equal left right held

theorem MatchesImplHead.matched {program : Program} {context : Context} {implementation : ImplDefinition}
    {arguments values specialized : List Term} {substitution : Substitution}
    (instantiated : Instantiates implementation.generics values substitution)
    (kinded : ∀ value ∈ values, Kinding program context value value.kind)
    (substituted : ListRel (Substitutes substitution) implementation.arguments specialized)
    (equal : ListRel (DefinitionallyEqual program context) specialized arguments)
    (inferred : ∀ (index : Nat) binder value, implementation.generics[index]? = some binder → values[index]? = some value →
      InfersHeadArgument program context implementation arguments binder value) :
    MatchesImplHead program context implementation arguments substitution :=
  .inferred instantiated kinded substituted equal.length_eq (fun _ _ _ first second => equal.at first second) inferred

/-- Runtime permissions may use only assumption-free evidence. Different
checking scopes cannot smuggle an open Use/equality assumption into this
context-free judgment. Unsupported types have no fallback certificate. -/
def CapabilitySupport (program : Program) (type : Term) (principal : Principal) : Prop :=
  ∃ context, context.assumptions = [] ∧ CapabilityEvidence program context type principal

/-- A principal is the greatest certified permission class, not an arbitrary
lower bound. The finite class lattice permits construction without assuming
normalization or the structural inversion theorem needed by destruction. -/
def PrincipalOf (program : Program) (type : Term) (principal : Principal) : Prop :=
  CapabilitySupport program type principal ∧
    ∀ other, CapabilitySupport program type other → other.Restricts principal

def CapabilitySolution (program : Program) (assignment : Term → Option Principal) : Prop :=
  ∀ term principal, assignment term = some principal ↔ PrincipalOf program term principal

structure CapabilityModel (program : Program) where
  principal : Term → Option Principal
  equations : CapabilitySolution program principal

/-- Joining is positive evidence from the declared reductions. -/
def DefinitionallyJoinable (program : Program) (context : Context) (left right : Term) : Prop :=
  ∃ common, DefinitionalReduction program context left common ∧ DefinitionalReduction program context right common

def SubstitutionsJoinable (program : Program) (context : Context) (left right : Substitution) : Prop :=
  ListRel (fun first second => first.1 = second.1 ∧ DefinitionallyJoinable program context first.2 second.2) left right

/-- Inferred solutions retain actual binder keys and agree modulo the
language's definitional equality. Positive joining is a separate theorem
obligation and is deliberately not built into declaration admission. -/
def SubstitutionsConvertible (program : Program) (context : Context) (left right : Substitution) : Prop :=
  ListRel (fun first second => first.1 = second.1 ∧ DefinitionallyEqual program context first.2 second.2) left right

/-- Common legal heads must identify one declaration and one inferred solution
modulo definitional equality. Requiring positive joining here would already
assume conversion-to-joinability for arbitrary kinded generic arguments. -/
def HeadSolutionsCoherent (program : Program) (context : Context) : Prop :=
  ∀ left right, Definition.implementation left ∈ program.declarations →
    Definition.implementation right ∈ program.declarations → left.trait = right.trait →
    ∀ arguments leftSub rightSub,
      MatchesImplHead program context left arguments leftSub →
      MatchesImplHead program context right arguments rightSub →
      left.header.id = right.header.id ∧ SubstitutionsConvertible program context leftSub rightSub

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

/-- A quantified declaration owns its parameter identities. Entering its
scope masks same-identity outer entries; freshening therefore need not avoid
unrelated, unused identities from an arbitrary enclosing context. -/
def Context.bindParameters (context : Context) (binders : List Binder) : Context :=
  { context with binders := binders ++ context.binders.filter (fun previous => !(binders.any (fun binder => binder.id == previous.id))) }

/-- A default sees its preceding binder prefix, never itself or a later
binder. The same lexical entry operation is used by source declarations and
quantified predicates, including associated items with outer owner binders. -/
def BinderDefaultsKinded (program : Program) (context : Context) (binders : List Binder) : Prop :=
  ∀ i binder value, binders[i]? = some binder → binder.defaultValue = some value →
    Kinding program (context.bindParameters (binders.take i)) value binder.kind

def BinderDefaultsWellFormed (program : Program) (context : Context) (binders : List Binder) : Prop :=
  BinderDefaultsKinded program context binders ∧
  ∀ i binder value, binders[i]? = some binder → binder.defaultValue = some value →
    DomainValid program (context.bindParameters (binders.take i)) value

/-- Predicate kind admission is distinct from proving the predicate true.
Its term premises use the same source kinding producer as signatures and
implementation heads. Nested quantifiers own their binder scope and check
defaults only in the preceding lexical prefix. -/
inductive ConstraintKinded (program : Program) : Context → Constraint → Prop where
  | equal {context left right kind} : Kinding program context left kind → Kinding program context right kind →
      ConstraintKinded program context (.equal left right)
  | outlives {context long short} : Kinding program context long .region → Kinding program context short .region →
      ConstraintKinded program context (.outlives long short)
  | typeOutlives {context type region} : Kinding program context type .type → Kinding program context region .region →
      ConstraintKinded program context (.typeOutlives type region)
  | rowIncludes {context allowed required} : Kinding program context allowed .row → Kinding program context required .row →
      ConstraintKinded program context (.rowIncludes allowed required)
  | implements {context id trait arguments negative substitution} : program.trait id = some trait →
      Instantiates trait.generics arguments substitution →
      (∀ argument ∈ arguments, Kinding program context argument argument.kind) →
      ConstraintKinded program context (.implements id arguments negative)
  | use {context type quantity} : Kinding program context type .type → quantity.Valid →
      ConstraintKinded program context (.use type quantity)
  | callable {context receiver arguments result effects unsafeAllowed} : Kinding program context receiver .type →
      (∀ argument ∈ arguments, Kinding program context argument .type) → Kinding program context result .type →
      Kinding program context effects .row →
      ConstraintKinded program context (.callable receiver arguments result effects unsafeAllowed)
  | runsIn {context receiver access arguments after unsafeAllowed} : Kinding program context receiver .type →
      Kinding program context access .type → (∀ argument ∈ arguments, Kinding program context argument .type) →
      Kinding program context after .type → ConstraintKinded program context (.runsIn receiver access arguments after unsafeAllowed)
  | quantified {context binders requirements} : (binders.map (·.id)).Nodup →
      BinderDefaultsKinded program context binders →
      (∀ requirement ∈ requirements, ConstraintKinded program (context.bindParameters binders) requirement) →
      ConstraintKinded program context (.quantified binders requirements)

inductive ConstantType (program : Program) (context : Context) : Term → Term → Prop where
  | scalar {value} : value.Valid program.input.target → ConstantType program context (.constant value) (.scalar value.type)
  | unit : ConstantType program context (.constantTuple []) .unit
  | tuple {fields types} : ListRel (ConstantType program context) fields types →
      ConstantType program context (.constantTuple fields) (.tuple types)
  | constructor {constructor data variant arguments values substitution types} :
      program.Constructor constructor data variant → Instantiates data.generics arguments substitution →
      (∀ argument ∈ arguments, Kinding program context argument argument.kind) →
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
    | scalar {scalar} : program.input.target.CScalarMapping scalar →
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
        data.variants ≠ [] → program.input.target.CScalarMapping (.integer sign width) →
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
  BinderDefaultsWellFormed program { context with binders := [] } signature.generics

/-- Implementation heads and associated overrides are checked at the actual
trait and item domains. Distinct template binder identities permit one
simultaneous substitution; caller arguments are never recursively rewritten
by another template's parameter binding. -/
def ImplementationHeadDetermined (program : Program) (implementation : ImplDefinition) : Prop :=
  ∀ binder ∈ implementation.generics,
    InfersHeadArgument program implementation.context implementation implementation.arguments binder
      (.parameter binder.id binder.kind)

def ImplementationSignatureWellFormed (program : Program) (implementation : ImplDefinition)
    (trait : TraitDefinition) : Prop :=
  let context : Context := ⟨implementation.generics,implementation.requirements,0,implementation.header.module,false,{}⟩
  (implementation.generics.map (·.id)).Nodup ∧
  ImplementationHeadDetermined program implementation ∧
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
    (∀ hook, data.dropHook = some hook → ∃ function, program.function hook = some function) ∧
    (∀ source, data.quantitySource = some source → WellKinded program context source source.kind ∧
      (source.kind = .quantity ∨ source.kind = .type)) ∧
    BinderDefaultsWellFormed program { context with binders := [] } data.generics
  | .alias alias => (alias.generics.map (·.id)).Nodup ∧
    WellKinded program ⟨alias.generics,[],0,alias.header.module,false,{}⟩ alias.value .type ∧
    BinderDefaultsWellFormed program ⟨[],[],0,alias.header.module,false,{}⟩ alias.generics
  | .function function => SignatureWellFormed program function.header.module function.signature ∧
    function.parameters.length = function.signature.parameters.length ∧ function.parameters.Nodup ∧
    (function.cABI = true → function.signature.generics = [] ∧
      (∀ parameter ∈ function.signature.parameters,
        ∃ layout, CCompatible program ⟨[],[],0,function.header.module,false,{}⟩ parameter layout) ∧
      (function.signature.result = .unit ∨ ∃ layout, CCompatible program ⟨[],[],0,function.header.module,false,{}⟩ function.signature.result layout)) ∧
    (function.origin = .foreign → function.cABI = true) ∧
    (∀ manifest, function.origin = .runtime manifest → manifest = program.input.manifest.identity ∧
      ∃ binding ∈ program.input.manifest.bindings, binding.declaration = function.header.id ∧ binding.signature = function.signature) ∧
    (∀ capture ∈ function.captures,
      WellKinded program ⟨function.signature.generics,function.signature.constraints,0,function.header.module,false,{}⟩
        capture .type)
  | .trait trait => (trait.generics.map (·.id)).Nodup ∧ trait.members.Nodup ∧
    (trait.relation ≠ .ordinary → (trait.header.id,trait.relation) ∈ program.input.manifest.sealedRelations) ∧
    BinderDefaultsWellFormed program ⟨[],trait.requirements,0,trait.header.module,false,{}⟩ trait.generics
  | .associated associated => ∃ trait, program.trait associated.owner = some trait ∧ associated.header.id ∈ trait.members ∧
    ((trait.generics ++ associated.generics).map (·.id)).Nodup ∧
    (∀ value, associated.defaultValue = some value →
      WellKinded program ⟨trait.generics ++ associated.generics,trait.requirements ++ associated.requirements,
        0,associated.header.module,false,{}⟩ value associated.kind) ∧
    BinderDefaultsWellFormed program ⟨trait.generics,trait.requirements ++ associated.requirements,
      0,associated.header.module,false,{}⟩ associated.generics
  | .implementation implementation => ImplLocal program implementation ∧
    ∃ trait, program.trait implementation.trait = some trait ∧
      (trait.relation = .ordinary ∨ trait.relation = .use ∨ trait.relation = .drop) ∧
      (trait.unsafeAllowed = true → implementation.unsafeAllowed = true) ∧
      (implementation.associated.map Prod.fst).Nodup ∧ (implementation.functions.map Prod.fst).Nodup ∧
      ImplementationSignatureWellFormed program implementation trait ∧
      BinderDefaultsWellFormed program ⟨[],implementation.requirements,0,implementation.header.module,false,{}⟩
        implementation.generics
  | .effect effect => (effect.generics.map (·.id)).Nodup ∧ effect.operations.Nodup ∧
    (∀ operation ∈ effect.operations, ∃ declaration, program.operation operation = some declaration ∧ declaration.family = effect.header.id) ∧
    BinderDefaultsWellFormed program ⟨[],effect.requirements,0,effect.header.module,false,{}⟩ effect.generics
  | .operation operation => SignatureWellFormed program operation.header.module operation.signature ∧
    (operation.terminal = true ∧ operation.signature.result = .bottom ∧ operation.quantity = none ∨
     operation.terminal = false ∧ operation.signature.result ≠ .bottom ∧
       ∃ quantity, operation.quantity = some quantity ∧ quantity.SurfaceResumption)
  | .constant constant => ConstantType program ⟨constant.generics,[],0,constant.header.module,false,{}⟩ constant.value constant.type ∧
    BinderDefaultsWellFormed program ⟨[],[],0,constant.header.module,false,{}⟩ constant.generics
  | .global global => WellKinded program ⟨[],[],0,global.header.module,false,{}⟩ global.type .type ∧
    PrincipalOf program global.type .duplicable
  | .module _ => True
  | .import _ => True
  | .fixity fixity => fixity.precedence ≤ 255 ∧
    ∃ function, program.function fixity.target = some function ∧ Visible function.header fixity.header.module

/-- All published logical predicates are admitted in their actual declaration
scope. Associated predicates include their owning trait's parameters, while
implementation predicates use the implementation's own head parameters.
This checks kinds, not satisfiability or the missing global confluence result. -/
def DeclarationConstraintsKinded (program : Program) : Definition → Prop
  | .data data => ∀ requirement ∈ data.requirements,
      ConstraintKinded program ⟨data.generics,data.requirements,0,data.header.module,false,{}⟩ requirement
  | .function function =>
      let context : Context := ⟨function.signature.generics,function.signature.constraints,0,function.header.module,false,{}⟩
      (∀ requirement ∈ function.signature.constraints, ConstraintKinded program context requirement) ∧
      ∀ relation ∈ function.invocations,
        ConstraintKinded program context (.callable relation.receiver relation.arguments relation.result relation.effects relation.unsafeAllowed) ∧
        ConstraintKinded program context (.runsIn relation.receiver relation.access relation.arguments relation.after relation.unsafeAllowed)
  | .trait trait => ∀ requirement ∈ trait.requirements,
      ConstraintKinded program ⟨trait.generics,trait.requirements,0,trait.header.module,false,{}⟩ requirement
  | .associated associated => ∃ trait, program.trait associated.owner = some trait ∧
      ∀ requirement ∈ associated.requirements,
        ConstraintKinded program ⟨trait.generics ++ associated.generics,trait.requirements ++ associated.requirements,
          0,associated.header.module,false,{}⟩ requirement
  | .implementation implementation => ∀ requirement ∈ implementation.requirements,
      ConstraintKinded program ⟨implementation.generics,implementation.requirements,0,implementation.header.module,false,{}⟩ requirement
  | .effect effect => ∀ requirement ∈ effect.requirements,
      ConstraintKinded program ⟨effect.generics,effect.requirements,0,effect.header.module,false,{}⟩ requirement
  | .operation operation => ∀ requirement ∈ operation.signature.constraints,
      ConstraintKinded program ⟨operation.signature.generics,operation.signature.constraints,0,operation.header.module,false,{}⟩ requirement
  | .alias _ | .constant _ | .global _ | .module _ | .import _ | .fixity _ => True

/-- Source templates are checked before runtime instantiation. Runtime atoms
remain well-kinded in execution judgments, but cannot occur literally in the
immutable declarations those judgments instantiate. -/
def DeclarationWellFormed (program : Program) (definition : Definition) : Prop :=
  (definition.Lexical ∧ definition.ScopeClosed) ∧
    DeclarationShapeWellFormed program definition ∧ DeclarationConstraintsKinded program definition

def ProgramWellFormed (program : Program) : Prop :=
  SourceClosure program ∧ (program.declarations.map (·.header.id)).Nodup ∧
  (∀ left right, program.Header left → program.Header right → left.id = right.id → left = right) ∧
  (∀ left right, program.Header left → program.Header right →
    left.module = right.module → left.nameSpace = right.nameSpace → left.name = right.name → left.id = right.id) ∧
  (∀ declaration ∈ program.declarations, DeclarationWellFormed program declaration) ∧ Coherent program

end Glorious.Language
