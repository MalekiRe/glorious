import Grounded.Patterns
import Grounded.Places

/-! Decoded expression, argument and clause checking. This finite-derivation
fragment still checks function bodies at call sites; it is not recursive-language admission. -/
namespace Grounded

/-- This restricts constant syntax, not a second evaluator. Constant dependencies
are checked by the same typing derivation and use the same evaluation relation. -/
inductive Structural : Expr → Prop where
  | unit : Structural .unit
  | integer (type : IntegerType) (magnitude : Nat) : Structural (.integer type magnitude)
  | character (number : Nat) : Structural (.character number)
  | group {body : Expr} (closed : Structural body) : Structural (.group body)
  | tuple {head : Expr} {tail : List Expr} (first : Structural head)
      (rest : ∀ expression ∈ tail, Structural expression) : Structural (.tuple head tail)
  | array {elements : List Expr} (residents : ∀ expression ∈ elements, Structural expression) :
      Structural (.array elements)
  | project {body : Expr} (closed : Structural body) (key : FieldKey) : Structural (.project body key)
  | constant (name : String) : Structural (.constant name)
  | construct {fields : List Expr} (identity : Nat) (tag : Option Nat)
      (residents : ∀ expression ∈ fields, Structural expression) :
      Structural (.construct identity tag fields)

mutual
inductive HasType (program : Program) : Module → List (String × BindingType) → Expr → Ty → Prop where
  | unit {home : Module} {context : List (String × BindingType)} : HasType program home context .unit .unit
  | integer {home : Module} {context : List (String × BindingType)} {type : IntegerType} {magnitude : Nat}
      (fits : type.Contains program.target magnitude) :
      HasType program home context (.integer type magnitude) (.integer type)
  | character {home : Module} {context : List (String × BindingType)} {number : Nat}
      (valid : UnicodeScalar number) :
      HasType program home context (.character number) .character
  | group {home : Module} {context : List (String × BindingType)} {body : Expr} {type : Ty}
      (typed : HasType program home context body type) : HasType program home context (.group body) type
  | read {home : Module} {context : List (String × BindingType)} {place : Place} {type : Ty} {mutable : Bool}
      (selected : PlaceType program home context place type mutable) (copyable : Duplicable program.data type) :
      HasType program home context (.read place) type
  | sequence {home : Module} {context : List (String × BindingType)} {first rest : Expr} {discarded type : Ty}
      (head : HasType program home context first discarded) (drop : Duplicable program.data discarded)
      (tail : HasType program home context rest type) : HasType program home context (.sequence first rest) type
  | bind {home : Module} {context : List (String × BindingType)} {mutable : Bool} {name : String} {annotation : Option TypeExpr} {initial body : Expr}
      {localType type : Ty} (initialized : HasType program home context initial localType)
      (drop : Duplicable program.data localType) (annotated : Annotation program.aliases annotation localType)
      (continued : HasType program home ((name, ⟨localType, mutable⟩) :: context) body type) :
      HasType program home context (.bind mutable name annotation initial body) type
  | tuple {home : Module} {context : List (String × BindingType)} {head : Expr} {tail : List Expr}
      {first : Ty} {rest : List Ty} (headTyped : HasType program home context head first)
      (tailTyped : HasTypes program home context tail rest) :
      HasType program home context (.tuple head tail) (.tuple first rest)
  | project {home : Module} {context : List (String × BindingType)} {body : Expr} {key : FieldKey}
      {parent type : Ty} {index : Nat} (source : HasType program home context body parent)
      (discard : Duplicable program.data parent) (selected : ProjectionType program home parent key index type) :
      HasType program home context (.project body key) type
  | array {home : Module} {context : List (String × BindingType)} {elements : List Expr} {element : Ty} {length : Nat}
      (residents : HasTypes program home context elements (List.replicate length element))
      (elementValid : FiniteLayout program.target program.data element)
      (size : length < 2 ^ program.target.pointerBits) :
      HasType program home context (.array elements) (.array element length)
  | constant {home : Module} {context : List (String × BindingType)} {name : String}
      {declaration : ConstantDecl} {type : Ty} (declared : program.constants name = some declaration)
      (visible : declaration.visibility.Allows declaration.home home)
      (resolved : ResolvesType program.aliases declaration.type type) (structural : Structural declaration.body)
      (initialized : HasType program declaration.home [] declaration.body type) :
      HasType program home context (.constant name) type
  | construct {home : Module} {context : List (String × BindingType)} {identity : Nat} {tag : Option Nat}
      {declaration : DataDecl} {schema : Fields} {fields : List Expr}
      (declared : program.data identity = some declaration)
      (chosen : declaration.constructor tag = some schema)
      (finite : FiniteLayout program.target program.data (.nominal identity))
      (copyable : Duplicable program.data (.nominal identity))
      (visible : declaration.visibility.Allows declaration.home home)
      (access : ∀ field ∈ schema.residents, field.visibility.Allows declaration.home home)
      (residents : HasTypes program home context fields (schema.residents.map Field.type)) :
      HasType program home context (.construct identity tag fields) (.nominal identity)
  | call {home : Module} {context : List (String × BindingType)} {identity : Nat}
      {arguments : List Expr} {declaration : FunctionDecl}
      (declared : program.functions identity = some declaration)
      (visible : declaration.visibility.Allows declaration.home home)
      (distinct : (declaration.parameters.map Prod.fst).Nodup)
      (discard : ∀ parameter ∈ declaration.parameters, Duplicable program.data parameter.2.type)
      (inputs : HasTypes program home context arguments (declaration.parameters.map (fun parameter => parameter.2.type)))
      (body : HasType program declaration.home declaration.parameters declaration.body declaration.result) :
      HasType program home context (.call identity arguments) declaration.result
  | assign {home : Module} {context : List (String × BindingType)} {place : Place}
      {value rest : Expr} {type result : Ty}
      (selected : PlaceType program home context place type true)
      (discard : Duplicable program.data type)
      (resident : HasType program home context value type)
      (continued : HasType program home context rest result) :
      HasType program home context (.assign place value rest) result
  | applyPatterns {home : Module} {context : List (String × BindingType)} {inputs : List Ty}
      {arguments : List Expr} {arms : List (Pattern × Expr)} {result : Ty}
      (argumentsTyped : HasTypes program home context arguments inputs)
      (nonempty : arms ≠ [])
      (covered : Covers program [argumentType inputs] (arms.map (fun arm => [arm.1])))
      (bodies : ArmsType program home context (argumentType inputs) result [] arms) :
      HasType program home context (.applyPatterns inputs arguments arms) result

inductive HasTypes (program : Program) : Module → List (String × BindingType) → List Expr → List Ty → Prop where
  | nil {home : Module} {context : List (String × BindingType)} : HasTypes program home context [] []
  | cons {home : Module} {context : List (String × BindingType)} {head : Expr} {tail : List Expr}
      {first : Ty} {rest : List Ty} (headTyped : HasType program home context head first)
      (tailTyped : HasTypes program home context tail rest) :
      HasTypes program home context (head :: tail) (first :: rest)
inductive ArmsType (program : Program) :
    Module → List (String × BindingType) → Ty → Ty → List Pattern → List (Pattern × Expr) → Prop where
  | empty {home : Module} {context : List (String × BindingType)} {subject result : Ty} {previous : List Pattern} :
      ArmsType program home context subject result previous []
  | clause {home : Module} {context : List (String × BindingType)} {subject result : Ty}
      {previous : List Pattern} {pattern : Pattern} {body : Expr} {rest : List (Pattern × Expr)}
      {bindings : List (String × BindingType)} (patternTyped : PatternType program home pattern subject bindings)
      (distinct : (bindings.map Prod.fst).Nodup) (useful : Useful program subject previous pattern)
      (bodyTyped : HasType program home (bindings ++ context) body result)
      (tailTyped : ArmsType program home context subject result (previous ++ [pattern]) rest) :
      ArmsType program home context subject result previous ((pattern, body) :: rest)
end

/-- Recover the original selected body's admission and actual local realization;
no alternative's runtime bindings or successful body execution is supplied. -/
theorem ArmsType.selected {program : Program} {home : Module} {context : List (String × BindingType)}
    {subject result : Ty} {previous : List Pattern} {arms : List (Pattern × Expr)}
    (checked : ArmsType program home context subject result previous arms)
    {value : Value} (resident : ValueHasType program value subject)
    {bindings : List (String × Value)} {body : Expr}
    (selected : selectArm value arms = some (bindings, body)) :
    ∃ locals, EnvironmentTyped program bindings locals ∧
      (∀ binding ∈ locals, Duplicable program.data binding.2.type) ∧
      HasType program home (locals ++ context) body result := by
  induction arms generalizing previous with
  | nil => simp [selectArm] at selected
  | cons arm arms ih =>
    cases checked with
    | clause patternTyped distinct useful bodyTyped tailTyped =>
      simp only [selectArm] at selected
      split at selected
      next matched found =>
        cases Option.some.inj selected
        exact ⟨_, patternTyped.bindings resident found, patternTyped.disposable, bodyTyped⟩
      next missed => exact ih tailTyped selected


end Grounded
