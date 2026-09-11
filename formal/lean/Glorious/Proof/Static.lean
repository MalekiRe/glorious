import Glorious.Semantics.Core
import Glorious.Proof.Behavior

/-! Declarative source obligations, independent of the inference and
normalization procedures. These judgments do not have a constructor saying
that a compiler check returned true. Failed proof search grants no rule. -/
namespace Glorious.Semantics.Spec

abbrev Context := List Binder

def Instantiates (binders : List Binder) (arguments : List Term)
    (substitution : List (Id × Term)) : Prop :=
  Glorious.Proof.Forall₂ (fun binder argument => binder.kind = argument.kind) binders arguments ∧
  substitution = (binders.map (·.id)).zip arguments

inductive Kinding (program : Program) (context : Context) : Term → Kind → Prop where
  | parameter {binder} (declared : binder ∈ context) :
      Kinding program context (.param binder.id binder.kind) binder.kind
  | rigid {identity kind level} : Kinding program context (.rigid identity kind level) kind
  | staticRegion : Kinding program context .staticRegion .region
  | unit : Kinding program context .unit .type
  | bottom : Kinding program context .bottom .type
  | scalar {scalar} : Kinding program context (.scalar scalar) .type
  | tuple {fields} (children : ∀ field ∈ fields, Kinding program context field .type) :
      Kinding program context (.tuple fields) .type
  | array {element length} (elementType : Kinding program context element .type)
      (constantLength : Kinding program context length .constant) :
      Kinding program context (.array element length) .type
  | reference {mode region referent} (lifetime : Kinding program context region .region)
      (valueType : Kinding program context referent .type) :
      Kinding program context (.reference mode region referent) .type
  | pointer {mode referent} (valueType : Kinding program context referent .type) :
      Kinding program context (.rawPointer mode referent) .type
  | nominal {declaration arguments substitution}
      (declared : declaration ∈ program.dataTypes)
      (argumentsValid : Instantiates declaration.generics arguments substitution)
      (argumentKinds : ∀ argument ∈ arguments, Kinding program context argument argument.kind) :
      Kinding program context (.nominal declaration.header.id arguments) .type
  | aliasType {declaration arguments substitution}
      (declared : declaration ∈ program.aliases)
      (argumentsValid : Instantiates declaration.generics arguments substitution)
      (argumentKinds : ∀ argument ∈ arguments, Kinding program context argument argument.kind) :
      Kinding program context (.alias declaration.header.id arguments) .type
  | callable {declaration arguments substitution}
      (declared : declaration ∈ program.functions)
      (argumentsValid : Instantiates declaration.signature.generics arguments substitution)
      (argumentKinds : ∀ argument ∈ arguments, Kinding program context argument argument.kind) :
      Kinding program context (.callable declaration.header.id arguments) .type
  | label {brand region result}
      (b : Kinding program context brand .brand) (r : Kinding program context region .region)
      (t : Kinding program context result .type) :
      Kinding program context (.label brand region result) .type
  | environment {brand region}
      (b : Kinding program context brand .brand) (r : Kinding program context region .region) :
      Kinding program context (.environment brand region) .type
  | available {brand region}
      (b : Kinding program context brand .brand) (r : Kinding program context region .region) :
      Kinding program context (.available brand region) .type
  | bindings {brand region arguments}
      (b : Kinding program context brand .brand) (r : Kinding program context region .region)
      (types : ∀ argument ∈ arguments, Kinding program context argument .type) :
      Kinding program context (.bindings brand region arguments) .type
  | continuation {identity argument result effects}
      (a : Kinding program context argument .type) (r : Kinding program context result .type)
      (e : Kinding program context effects .row) :
      Kinding program context (.continuation identity argument result effects) .type
  | effect {declaration arguments substitution}
      (declared : declaration ∈ program.effects)
      (argumentsValid : Instantiates declaration.generics arguments substitution)
      (argumentKinds : ∀ argument ∈ arguments, Kinding program context argument argument.kind) :
      Kinding program context (.effect declaration.header.id arguments) .effect
  | row {instances tails}
      (effects : ∀ effect ∈ instances, Kinding program context effect .effect)
      (rows : ∀ row ∈ tails, Kinding program context row .row) :
      Kinding program context (.row instances tails) .row
  | scalarConstant {value} : Kinding program context (.constant value) .constant
  | tupleConstant {values} (constants : ∀ value ∈ values, Kinding program context value .constant) :
      Kinding program context (.constantTuple values) .constant
  | constructorConstant {declaration arguments values data variant substitution}
      (declared : program.constructor declaration = some (data, variant))
      (argumentsValid : Instantiates data.generics arguments substitution)
      (constants : ∀ value ∈ values, Kinding program context value .constant) :
      Kinding program context (.constantConstructor declaration arguments values) .constant

mutual
  inductive Equal (program : Program) : Term → Term → Prop where
    | refl {term} : Equal program term term
    | symm {a b} : Equal program a b → Equal program b a
    | trans {a b c} : Equal program a b → Equal program b c → Equal program a c
    | congr {a b} (head : SameHead a b)
        (children : Glorious.Proof.Forall₂ (Equal program) a.children b.children) : Equal program a b
    | aliasType {declaration arguments substitution value}
        (declared : declaration ∈ program.aliases)
        (argumentsValid : Instantiates declaration.generics arguments substitution)
        (body : Substitutes substitution declaration.value value) :
        Equal program (.alias declaration.header.id arguments) value
    | associated {implementation member arguments substitution value body}
        (selected : SelectsImpl program implementation.traitDecl arguments implementation substitution)
        (declared : (member, body) ∈ implementation.associated)
        (specialized : Substitutes substitution body value) :
        Equal program (.projection implementation.traitDecl member arguments value.kind) value

  inductive SelectsImpl (program : Program) :
      DeclId → List Term → ImplDecl → List (Id × Term) → Prop where
    | selected {traitId arguments implementation substitution instantiated}
        (declared : implementation ∈ program.implementations)
        (identity : implementation.traitDecl = traitId)
        (positive : implementation.negative = false)
        (head : Glorious.Proof.Forall₂ (Substitutes substitution) implementation.arguments instantiated)
        (matching : Glorious.Proof.Forall₂ (Equal program) instantiated arguments)
        (requirements : ∀ requirement ∈ implementation.requirements,
          Satisfies program substitution requirement) :
        SelectsImpl program traitId arguments implementation substitution

  inductive Satisfies (program : Program) : List (Id × Term) → Constraint → Prop where
    | equality {substitution a b x y} (left : Substitutes substitution a x)
        (right : Substitutes substitution b y) (same : Equal program x y) :
        Satisfies program substitution (.equal a b)
    | implementation {substitution traitId arguments instantiated implementation selected}
        (specialized : Glorious.Proof.Forall₂ (Substitutes substitution) arguments instantiated)
        (proof : SelectsImpl program traitId instantiated implementation selected) :
        Satisfies program substitution (.implements traitId arguments false)
    | negative {substitution traitId arguments instantiated implementation replacement head}
        (specialized : Glorious.Proof.Forall₂ (Substitutes substitution) arguments instantiated)
        (declared : implementation ∈ program.implementations)
        (identity : implementation.traitDecl = traitId)
        (negative : implementation.negative = true)
        (specializedHead : Glorious.Proof.Forall₂ (Substitutes replacement) implementation.arguments head)
        (matching : Glorious.Proof.Forall₂ (Equal program) head instantiated)
        (requirements : ∀ requirement ∈ implementation.requirements,
          Satisfies program replacement requirement) :
        Satisfies program substitution (.implements traitId arguments true)
    | quantified {substitution binders requirements}
        (universal : ∀ arguments extended,
          Instantiates binders arguments extended →
          (∀ argument ∈ arguments, Kinding program [] argument argument.kind) →
          ∀ requirement ∈ requirements, Satisfies program (extended ++ substitution) requirement) :
        Satisfies program substitution (.higherRanked binders requirements)
end

inductive Outlives (assumptions : List (Term × Term)) : Term → Term → Prop where
  | refl {region} : Outlives assumptions region region
  | static {region} : Outlives assumptions .staticRegion region
  | assumed {a b} (declared : (a, b) ∈ assumptions) : Outlives assumptions a b
  | trans {a b c} : Outlives assumptions a b → Outlives assumptions b c → Outlives assumptions a c

inductive RowMember (program : Program) (effect : Term) : Term → Prop where
  | head {instances tails member} (present : member ∈ instances) (same : Equal program effect member) :
      RowMember program effect (.row instances tails)
  | tail {instances tails row} (present : row ∈ tails) (member : RowMember program effect row) :
      RowMember program effect (.row instances tails)
  | equal {a b} (same : Equal program a b) (member : RowMember program effect a) : RowMember program effect b

def RowIncludes (program : Program) (allowed required : Term) : Prop :=
  ∀ effect, RowMember program effect required → RowMember program effect allowed

inductive Subtype (program : Program) (regions : List (Term × Term)) : Term → Term → Prop where
  | equal {a b} (same : Equal program a b) : Subtype program regions a b
  | bottom {type} (kinded : Kinding program [] type .type) : Subtype program regions .bottom type
  | shared {long short a b} (region : Outlives regions long short)
      (referent : Subtype program regions a b) :
      Subtype program regions (.reference .shared long a) (.reference .shared short b)
  | unique {long short type} (region : Outlives regions long short) :
      Subtype program regions (.reference .unique long type) (.reference .unique short type)
  | tuple {a b} (fields : Glorious.Proof.Forall₂ (Subtype program regions) a b) :
      Subtype program regions (.tuple a) (.tuple b)

def ScalarBits (target : Target) : IntWidth → Nat
  | .w8 => 8 | .w16 => 16 | .w32 => 32 | .w64 => 64 | .w128 => 128
  | .pointer => target.pointerBits

def ValidScalar (target : Target) : ScalarValue → Prop
  | .integer signed width value =>
    let bits := ScalarBits target width
    bits > 0 ∧ if signed then -(2 ^ (bits - 1) : Int) ≤ value ∧ value < 2 ^ (bits - 1)
      else 0 ≤ value ∧ value < 2 ^ bits
  | .floating width bits => bits < 2 ^ (if width = .w32 then 32 else 64)
  | .character value => value < 0x110000 ∧ (value < 0xD800 ∨ 0xDFFF < value)

inductive PrincipalOf (program : Program) : Term → Principal → Prop where
  | unit : PrincipalOf program .unit .duplicable
  | scalar {scalar} : PrincipalOf program (.scalar scalar) .duplicable
  | pointer {mode type} : PrincipalOf program (.rawPointer mode type) .duplicable
  | shared {region type} : PrincipalOf program (.reference .shared region type) .duplicable
  | unique {region type} : PrincipalOf program (.reference .unique region type) .affine
  | label {brand region type} : PrincipalOf program (.label brand region type) .duplicable
  | tuple {types principals}
      (fields : Glorious.Proof.Forall₂ (PrincipalOf program) types principals) :
      PrincipalOf program (.tuple types) (Principal.residents principals)
  | emptyArray {element width} :
      PrincipalOf program (.array element (.constant (.integer false width 0))) .duplicable
  | array {element width length principal}
      (positive : 0 < length) (resident : PrincipalOf program element principal) :
      PrincipalOf program (.array element (.constant (.integer false width length))) principal
  | nominal {data arguments substitution types principals structural principal}
      (declared : data ∈ program.dataTypes)
      (instantiated : Instantiates data.generics arguments substitution)
      (fields : Glorious.Proof.Forall₂ (Substitutes substitution)
        (data.variants.flatMap (fun variant => variant.fields.map (·.type))) types)
      (residents : Glorious.Proof.Forall₂ (PrincipalOf program) types principals)
      (meet : structural = Principal.residents principals)
      (restriction : principal.Restricts structural)
      (selected : data.principalRestriction = some principal ∨ (data.principalRestriction = none ∧ principal = structural)) :
      PrincipalOf program (.nominal data.header.id arguments) principal
  | aliasType {a b principal} (same : Equal program a b)
      (available : PrincipalOf program a principal) : PrincipalOf program b principal

def SignatureWellFormed (program : Program) (signature : Signature) : Prop :=
  (∀ type ∈ signature.arguments, Kinding program signature.generics type .type) ∧
  Kinding program signature.generics signature.output .type ∧
  Kinding program signature.generics signature.effects .row ∧
  (signature.generics.map (·.id)).Nodup

def ModuleMaySee (source : ModuleId) (header : DeclHeader) : Prop :=
  source.packageId = header.module.packageId ∧ header.module.path.IsPrefix source.path ∨
  header.visibility = .public ∨
  (header.visibility = .package ∧ source.packageId = header.module.packageId) ∨
  (header.visibility = .parent ∧ source.packageId = header.module.packageId ∧
    header.module.path.dropLast.IsPrefix source.path)

structure ProgramWellFormed (program : Program) : Prop where
  packages : (program.packages.map (·.id)).Nodup
  modules : (program.modules.map (·.identity)).Nodup
  functions : (program.functions.map (·.header.id)).Nodup
  signatures : ∀ function ∈ program.functions, SignatureWellFormed program function.signature
  parameters : ∀ function ∈ program.functions,
    function.parameters.length = function.signature.arguments.length ∧
    (function.parameters.map (·.id)).Nodup
  noBodylessOrdinary : ∀ function ∈ program.functions,
    function.body.isSome = true ∨ function.runtimeBinding.isSome = true ∨ function.traitMember.isSome = true
  imports : ∀ binding ∈ program.imports,
    ∃ function ∈ program.functions, function.runtimeBinding = some binding.identity ∧
      function.signature.arguments = binding.signature.arguments ∧
      function.signature.output = binding.signature.output ∧
      function.signature.effects = binding.signature.effects ∧
      function.signature.abi = binding.signature.abi
  coherent : ∀ traitId arguments a b sa sb,
    SelectsImpl program traitId arguments a sa → SelectsImpl program traitId arguments b sb →
    a.header.id = b.header.id

theorem shared_reference_copyable (program : Program) (region type : Term) :
    PrincipalOf program (.reference .shared region type) .duplicable := .shared

theorem unique_reference_not_unrestricted (principal : Principal)
    (selected : principal = .affine) : ¬ principal.MayCopy := by
  subst principal
  intro h
  have impossible := h 2
  simp [Principal.permits] at impossible

end Glorious.Semantics.Spec
