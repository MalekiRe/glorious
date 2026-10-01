import Grounded.Places
import Grounded.Matching

/-! State-threaded operational rules, independent of expression checking.
Logical lexical storage does not model physical allocation or loans. -/
namespace Grounded

mutual
inductive Evaluates (program : Program) : List (String × Value) → Expr → Value → List (String × Value) → Prop where
  | unit {environment : List (String × Value)} : Evaluates program environment .unit .unit environment
  | integer {environment : List (String × Value)} {type : IntegerType} {magnitude : Nat}
      (fits : type.Contains program.target magnitude) :
      Evaluates program environment (.integer type magnitude) (.integer type magnitude) environment
  | character {environment : List (String × Value)} {number : Nat} (valid : UnicodeScalar number) :
      Evaluates program environment (.character number) (.character number) environment
  | group {environment after : List (String × Value)} {body : Expr} {value : Value}
      (evaluated : Evaluates program environment body value after) :
      Evaluates program environment (.group body) value after
  | read {environment : List (String × Value)} {place : Place} {value : Value}
      (selected : readPlace program place environment = some value) :
      Evaluates program environment (.read place) value environment
  | sequence {environment middle after : List (String × Value)} {first rest : Expr}
      {discarded value : Value} (head : Evaluates program environment first discarded middle)
      (tail : Evaluates program middle rest value after) :
      Evaluates program environment (.sequence first rest) value after
  | bind {environment middle after : List (String × Value)} {mutable : Bool} {name : String}
      {annotation : Option TypeExpr} {initial body : Expr} {resident value : Value}
      (initialized : Evaluates program environment initial resident middle)
      (continued : Evaluates program ((name, resident) :: middle) body value after) :
      Evaluates program environment (.bind mutable name annotation initial body) value (after.drop 1)
  | assign {environment middle updated after : List (String × Value)} {place : Place}
      {expression rest : Expr} {resident value : Value}
      (evaluated : Evaluates program environment expression resident middle)
      (written : writePlace program place resident middle = some updated)
      (continued : Evaluates program updated rest value after) :
      Evaluates program environment (.assign place expression rest) value after
  | tuple {environment middle after : List (String × Value)} {head : Expr} {tail : List Expr}
      {first : Value} {rest : List Value} (headEval : Evaluates program environment head first middle)
      (tailEval : EvaluatesMany program middle tail rest after) :
      Evaluates program environment (.tuple head tail) (.tuple first rest) after
  | project {environment after : List (String × Value)} {body : Expr} {key : FieldKey} {index : Nat}
      {aggregate value : Value}
      (source : Evaluates program environment body aggregate after)
      (selected : aggregate.projectField program key = some (index, value)) :
      Evaluates program environment (.project body key) value after
  | array {environment after : List (String × Value)} {elements : List Expr} {values : List Value}
      (residents : EvaluatesMany program environment elements values after) :
      Evaluates program environment (.array elements) (.array values) after
  | constant {environment : List (String × Value)} {name : String} {declaration : ConstantDecl}
      {value : Value} (declared : program.constants name = some declaration)
      (initialized : Evaluates program [] declaration.body value []) :
      Evaluates program environment (.constant name) value environment
  | construct {environment after : List (String × Value)} {identity : Nat} {tag : Option Nat}
      {fields : List Expr} {values : List Value} (residents : EvaluatesMany program environment fields values after) :
      Evaluates program environment (.construct identity tag fields) (.nominal identity tag values) after
  | call {environment middle localAfter : List (String × Value)} {identity : Nat} {arguments : List Expr}
      {declaration : FunctionDecl} {values : List Value} {value : Value}
      (declared : program.functions identity = some declaration)
      (inputs : EvaluatesMany program environment arguments values middle)
      (body : Evaluates program (List.zip (declaration.parameters.map Prod.fst) values) declaration.body value localAfter) :
      Evaluates program environment (.call identity arguments) value middle
  | applyPatterns {environment middle after : List (String × Value)} {inputs : List Ty} {arguments : List Expr}
      {arms : List (Pattern × Expr)} {values : List Value}
      {bindings : List (String × Value)} {body : Expr} {value : Value}
      (argumentsEval : EvaluatesMany program environment arguments values middle)
      (selected : selectArm (argumentValue values) arms = some (bindings, body))
      (bodyEval : Evaluates program (bindings ++ middle) body value after) :
      Evaluates program environment (.applyPatterns inputs arguments arms) value (after.drop bindings.length)

inductive EvaluatesMany (program : Program) : List (String × Value) → List Expr → List Value → List (String × Value) → Prop where
  | nil {environment : List (String × Value)} : EvaluatesMany program environment [] [] environment
  | cons {environment middle after : List (String × Value)} {head : Expr} {tail : List Expr}
      {first : Value} {rest : List Value} (headEval : Evaluates program environment head first middle)
      (tailEval : EvaluatesMany program middle tail rest after) :
      EvaluatesMany program environment (head :: tail) (first :: rest) after
end

end Grounded
