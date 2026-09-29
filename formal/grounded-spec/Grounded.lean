/-!
Target-indexed expressions, immutable composition, structural and nominal data.
Normative basis: §§2.2–2.3, 3.2–3.4, 4.1–4.4, 5.1, 5.3, 7.2–7.3 and 13.1.
Declarations, field types, identities and lexical names are already decoded.
Constructors consume argument expressions in their recorded order. Literal
magnitudes and Unicode numbers are decoded; source elaboration is not proved.
Only duplicable nominal owners without hooks or indirections are admitted.
Physical representation, exhaustion and nonduplicable ownership remain outside
this logical AST-to-value boundary.
Admission has no execution premise. No prior specification modules are imported.
-/

namespace Grounded

/-- The selected target supplies its positive pointer width (§4.4). Other ABI
properties enter when their semantic consumers are introduced. -/
structure Target where
  pointerBits : Nat
  positive : 0 < pointerBits

inductive Width where
  | w8 | w16 | w32 | w64 | w128
  | pointer

def Width.bits (target : Target) : Width → Nat
  | .w8 => 8
  | .w16 => 16
  | .w32 => 32
  | .w64 => 64
  | .w128 => 128
  | .pointer => target.pointerBits

structure IntegerType where
  signed : Bool
  width : Width

/-- Mathematical scalar range; there is no implicit wrapping of literals. -/
def IntegerType.Contains (target : Target) (type : IntegerType) (value : Int) : Prop :=
  let bound : Int := 2 ^ (type.width.bits target - if type.signed then 1 else 0)
  (if type.signed then -bound else 0) ≤ value ∧ value < bound

def UnicodeScalar (number : Nat) : Prop :=
  number < 0x110000 ∧ (number < 0xd800 ∨ 0xe000 ≤ number)

inductive Ty where
  | unit
  | integer (type : IntegerType)
  | character
  | tuple (head : Ty) (tail : List Ty)
  | array (element : Ty) (length : Nat)
  | nominal (identity : Nat)
/-- Decoded type expressions retain alias references until static resolution. -/
inductive TypeExpr where
  | concrete (type : Ty)
  | alias (name : String)
  | tuple (head : TypeExpr) (tail : List TypeExpr)
  | array (element : TypeExpr) (length : Nat)

abbrev Aliases := String → Option TypeExpr


mutual
/-- Alias expansion is finite and independent of declaration order. No alias
identity survives in the resolved type (§4.3). -/
inductive ResolvesType (aliases : Aliases) : TypeExpr → Ty → Prop where
  | concrete (type : Ty) : ResolvesType aliases (.concrete type) type
  | alias {name : String} {body : TypeExpr} {type : Ty}
      (declared : aliases name = some body) (expanded : ResolvesType aliases body type) :
      ResolvesType aliases (.alias name) type
  | tuple {head : TypeExpr} {tail : List TypeExpr} {first : Ty} {rest : List Ty}
      (firstType : ResolvesType aliases head first) (restTypes : ResolvesTypes aliases tail rest) :
      ResolvesType aliases (.tuple head tail) (.tuple first rest)
  | array {element : TypeExpr} {type : Ty} (length : Nat)
      (resolved : ResolvesType aliases element type) :
      ResolvesType aliases (.array element length) (.array type length)

inductive ResolvesTypes (aliases : Aliases) : List TypeExpr → List Ty → Prop where
  | nil : ResolvesTypes aliases [] []
  | cons {head : TypeExpr} {tail : List TypeExpr} {first : Ty} {rest : List Ty}
      (firstType : ResolvesType aliases head first) (restTypes : ResolvesTypes aliases tail rest) :
      ResolvesTypes aliases (head :: tail) (first :: rest)
end

inductive Annotation (aliases : Aliases) : Option TypeExpr → Ty → Prop where
  | inferred (type : Ty) : Annotation aliases none type
  | explicit {source : TypeExpr} {type : Ty} (resolved : ResolvesType aliases source type) :
      Annotation aliases (some source) type

/-- Resolved module identity, including the package boundary (§2.2). -/
structure Module where
  package : Nat
  path : List Nat

inductive Visibility where
  | «private» | package | parent | «public»

def Visibility.Allows (visibility : Visibility) (owner caller : Module) : Prop :=
  match visibility with
  | .private => caller.package = owner.package ∧ owner.path.IsPrefix caller.path
  | .package => caller.package = owner.package
  | .parent => owner.path ≠ [] ∧ caller.package = owner.package ∧
      owner.path.dropLast.IsPrefix caller.path
  | .public => True

inductive FieldKey where
  | named (name : String)
  | positional (index : Nat)

structure Field where
  type : Ty
  visibility : Visibility := .private

/-- Declaration order is retained even for named fields. -/
inductive Fields where
  | tuple (fields : List Field)
  | record (fields : List (String × Field))

def Fields.residents : Fields → List Field
  | .tuple fields => fields
  | .record fields => fields.map Prod.snd

def Fields.Valid : Fields → Prop
  | .tuple _ => True
  | .record fields => (fields.map Prod.fst).Nodup

def Fields.index : Fields → FieldKey → Option Nat
  | .tuple fields, .positional index => if index < fields.length then some index else none
  | .record fields, .named name => fields.findIdx? (fun field => field.1 == name)
  | _, _ => none

inductive DataShape where
  | «structure» (fields : Fields)
  | enumeration (variants : List Fields)

inductive Principal where
  | duplicable | affine | exact

structure DataDecl where
  home : Module
  visibility : Visibility := .private
  shape : DataShape
  restriction : Option Principal := none

def DataDecl.schemas (declaration : DataDecl) : List Fields :=
  match declaration.shape with
  | .structure fields => [fields]
  | .enumeration variants => variants

/-- No variant tag denotes a struct; an explicit tag denotes an enum variant. -/
def DataDecl.constructor (declaration : DataDecl) (tag : Option Nat) : Option Fields :=
  match declaration.shape, tag with
  | .structure fields, none => some fields
  | .enumeration variants, some index => variants[index]?
  | _, _ => none

abbrev DataDeclarations := Nat → Option DataDecl

/-- Inline type expansion must be finite, including every enum variant. There
are no indirections in this subset; zero array length does not license Self. -/
inductive FiniteLayout (target : Target) (data : DataDeclarations) : Ty → Prop where
  | unit : FiniteLayout target data .unit
  | integer (type : IntegerType) : FiniteLayout target data (.integer type)
  | character : FiniteLayout target data .character
  | tuple {head : Ty} {tail : List Ty} (first : FiniteLayout target data head)
      (rest : ∀ type ∈ tail, FiniteLayout target data type) :
      FiniteLayout target data (.tuple head tail)
  | array {element : Ty} {length : Nat} (resident : FiniteLayout target data element)
      (size : length < 2 ^ target.pointerBits) : FiniteLayout target data (.array element length)
  | nominal {identity : Nat} {declaration : DataDecl}
      (declared : data identity = some declaration)
      (schemas : ∀ schema ∈ declaration.schemas, schema.Valid)
      (fields : ∀ schema ∈ declaration.schemas, ∀ field ∈ schema.residents,
        FiniteLayout target data field.type) : FiniteLayout target data (.nominal identity)

inductive Expr where
  | unit
  | integer (type : IntegerType) (magnitude : Nat)
  | character (number : Nat)
  | group (body : Expr)
  | local (name : String)
  | sequence (first rest : Expr)
  | bind (name : String) (annotation : Option TypeExpr) (initial body : Expr)
  | tuple (head : Expr) (tail : List Expr)
  | project (body : Expr) (index : Nat)
  | array (elements : List Expr)
  | constant (name : String)
  | construct (identity : Nat) (tag : Option Nat) (fields : List Expr)
  | field (body : Expr) (key : FieldKey)
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
  | project {body : Expr} (closed : Structural body) (index : Nat) : Structural (.project body index)
  | constant (name : String) : Structural (.constant name)
  | construct {fields : List Expr} (identity : Nat) (tag : Option Nat)
      (residents : ∀ expression ∈ fields, Structural expression) :
      Structural (.construct identity tag fields)
  | field {body : Expr} (closed : Structural body) (key : FieldKey) : Structural (.field body key)
structure ConstantDecl where
  home : Module
  visibility : Visibility := .private
  type : TypeExpr
  body : Expr

abbrev Constants := String → Option ConstantDecl

/-- One immutable decoded program supplies the facts shared by static and
dynamic semantics. It carries source declarations, never execution guarantees. -/
structure Program where
  target : Target
  aliases : Aliases
  constants : Constants
  data : DataDeclarations
variable {program : Program}
variable {home : Module}
/-- §7.2: scalar owned use may copy; scalar values may also be discarded.
Keep this explicit at consumers rather than making all future types copyable. -/
inductive Duplicable (data : DataDeclarations) : Ty → Prop where
  | unit : Duplicable data .unit
  | integer (type : IntegerType) : Duplicable data (.integer type)
  | character : Duplicable data .character
  | tuple {head : Ty} {tail : List Ty} (first : Duplicable data head)
      (rest : ∀ type ∈ tail, Duplicable data type) : Duplicable data (.tuple head tail)
  | array {element : Ty} (length : Nat) (resident : Duplicable data element) :
      Duplicable data (.array element length)
  | emptyArray (element : Ty) : Duplicable data (.array element 0)
  | nominal {identity : Nat} {declaration : DataDecl}
      (declared : data identity = some declaration)
      (restriction : declaration.restriction = none ∨ declaration.restriction = some .duplicable)
      (fields : ∀ schema ∈ declaration.schemas, ∀ field ∈ schema.residents, Duplicable data field.type) :
      Duplicable data (.nominal identity)
inductive Value where
  | unit
  | integer (type : IntegerType) (number : Int)
  | character (number : Nat)
  | tuple (head : Value) (tail : List Value)
  | array (elements : List Value)
  | nominal (identity : Nat) (tag : Option Nat) (fields : List Value)
/-- Nearest lexical binding wins, including in shadowing initializers. -/
def lookup {α : Type} (name : String) : List (String × α) → Option α
  | [] => none
  | (key, value) :: rest => if name = key then some value else lookup name rest

mutual
inductive HasType (program : Program) : Module → List (String × Ty) → Expr → Ty → Prop where
  | unit {home : Module} {context : List (String × Ty)} : HasType program home context .unit .unit
  | integer {home : Module} {context : List (String × Ty)} {type : IntegerType} {magnitude : Nat}
      (fits : type.Contains program.target magnitude) :
      HasType program home context (.integer type magnitude) (.integer type)
  | character {home : Module} {context : List (String × Ty)} {number : Nat}
      (valid : UnicodeScalar number) :
      HasType program home context (.character number) .character
  | group {home : Module} {context : List (String × Ty)} {body : Expr} {type : Ty}
      (typed : HasType program home context body type) : HasType program home context (.group body) type
  | local {home : Module} {context : List (String × Ty)} {name : String} {type : Ty}
      (selected : lookup name context = some type) (copyable : Duplicable program.data type) :
      HasType program home context (.local name) type
  | sequence {home : Module} {context : List (String × Ty)} {first rest : Expr} {discarded type : Ty}
      (head : HasType program home context first discarded) (drop : Duplicable program.data discarded)
      (tail : HasType program home context rest type) : HasType program home context (.sequence first rest) type
  | bind {home : Module} {context : List (String × Ty)} {name : String} {annotation : Option TypeExpr} {initial body : Expr}
      {localType type : Ty} (initialized : HasType program home context initial localType)
      (drop : Duplicable program.data localType) (annotated : Annotation program.aliases annotation localType)
      (continued : HasType program home ((name, localType) :: context) body type) :
      HasType program home context (.bind name annotation initial body) type
  | tuple {home : Module} {context : List (String × Ty)} {head : Expr} {tail : List Expr}
      {first : Ty} {rest : List Ty} (headTyped : HasType program home context head first)
      (tailTyped : HasTypes program home context tail rest) :
      HasType program home context (.tuple head tail) (.tuple first rest)
  | project {home : Module} {context : List (String × Ty)} {body : Expr} {index : Nat}
      {first type : Ty} {rest : List Ty} (source : HasType program home context body (.tuple first rest))
      (discard : Duplicable program.data (.tuple first rest)) (selected : (first :: rest)[index]? = some type) :
      HasType program home context (.project body index) type
  | array {home : Module} {context : List (String × Ty)} {elements : List Expr} {element : Ty} {length : Nat}
      (residents : HasTypes program home context elements (List.replicate length element))
      (elementValid : FiniteLayout program.target program.data element)
      (size : length < 2 ^ program.target.pointerBits) :
      HasType program home context (.array elements) (.array element length)
  | constant {home : Module} {context : List (String × Ty)} {name : String}
      {declaration : ConstantDecl} {type : Ty} (declared : program.constants name = some declaration)
      (visible : declaration.visibility.Allows declaration.home home)
      (resolved : ResolvesType program.aliases declaration.type type) (structural : Structural declaration.body)
      (initialized : HasType program declaration.home [] declaration.body type) :
      HasType program home context (.constant name) type
  | construct {home : Module} {context : List (String × Ty)} {identity : Nat} {tag : Option Nat}
      {declaration : DataDecl} {schema : Fields} {fields : List Expr}
      (declared : program.data identity = some declaration)
      (chosen : declaration.constructor tag = some schema)
      (finite : FiniteLayout program.target program.data (.nominal identity))
      (copyable : Duplicable program.data (.nominal identity))
      (visible : declaration.visibility.Allows declaration.home home)
      (access : ∀ field ∈ schema.residents, field.visibility.Allows declaration.home home)
      (residents : HasTypes program home context fields (schema.residents.map Field.type)) :
      HasType program home context (.construct identity tag fields) (.nominal identity)
  | field {home : Module} {context : List (String × Ty)} {body : Expr} {key : FieldKey}
      {identity index : Nat} {declaration : DataDecl} {schema : Fields} {field : Field}
      (source : HasType program home context body (.nominal identity))
      (discard : Duplicable program.data (.nominal identity))
      (declared : program.data identity = some declaration)
      (structureOnly : declaration.shape = .structure schema)
      (indexed : schema.index key = some index) (selected : schema.residents[index]? = some field)
      (visible : field.visibility.Allows declaration.home home) :
      HasType program home context (.field body key) field.type

inductive HasTypes (program : Program) : Module → List (String × Ty) → List Expr → List Ty → Prop where
  | nil {home : Module} {context : List (String × Ty)} : HasTypes program home context [] []
  | cons {home : Module} {context : List (String × Ty)} {head : Expr} {tail : List Expr}
      {first : Ty} {rest : List Ty} (headTyped : HasType program home context head first)
      (tailTyped : HasTypes program home context tail rest) :
      HasTypes program home context (head :: tail) (first :: rest)
end

mutual
inductive ValueHasType (program : Program) : Value → Ty → Prop where
  | unit : ValueHasType program .unit .unit
  | integer {type : IntegerType} {number : Int}
      (fits : type.Contains program.target number) :
      ValueHasType program (.integer type number) (.integer type)
  | character {number : Nat} (valid : UnicodeScalar number) :
      ValueHasType program (.character number) .character
  | tuple {head : Value} {tail : List Value} {first : Ty} {rest : List Ty}
      (headTyped : ValueHasType program head first) (tailTyped : ValuesHaveTypes program tail rest) :
      ValueHasType program (.tuple head tail) (.tuple first rest)
  | array {values : List Value} {element : Ty} {length : Nat}
      (residents : ValuesHaveTypes program values (List.replicate length element))
      (elementValid : FiniteLayout program.target program.data element)
      (size : length < 2 ^ program.target.pointerBits) :
      ValueHasType program (.array values) (.array element length)
  | nominal {identity : Nat} {tag : Option Nat} {declaration : DataDecl} {schema : Fields}
      {values : List Value} (declared : program.data identity = some declaration)
      (chosen : declaration.constructor tag = some schema)
      (finite : FiniteLayout program.target program.data (.nominal identity))
      (residents : ValuesHaveTypes program values (schema.residents.map Field.type)) :
      ValueHasType program (.nominal identity tag values) (.nominal identity)
inductive ValuesHaveTypes (program : Program) : List Value → List Ty → Prop where
  | nil : ValuesHaveTypes program [] []
  | cons {head : Value} {tail : List Value} {first : Ty} {rest : List Ty}
      (headTyped : ValueHasType program head first) (tailTyped : ValuesHaveTypes program tail rest) :
      ValuesHaveTypes program (head :: tail) (first :: rest)
end

inductive EnvironmentTyped (program : Program) : List (String × Value) → List (String × Ty) → Prop where
  | nil : EnvironmentTyped program [] []
  | cons {name : String} {value : Value} {type : Ty}
      {environment : List (String × Value)} {context : List (String × Ty)}
      (resident : ValueHasType program value type) (rest : EnvironmentTyped program environment context) :
      EnvironmentTyped program ((name, value) :: environment) ((name, type) :: context)

mutual
inductive Evaluates (program : Program) : List (String × Value) → Expr → Value → Prop where
  | unit {environment : List (String × Value)} : Evaluates program environment .unit .unit
  | integer {environment : List (String × Value)} {type : IntegerType} {magnitude : Nat}
      (fits : type.Contains program.target magnitude) :
      Evaluates program environment (.integer type magnitude) (.integer type magnitude)
  | character {environment : List (String × Value)} {number : Nat}
      (valid : UnicodeScalar number) :
      Evaluates program environment (.character number) (.character number)
  | group {environment : List (String × Value)} {body : Expr} {value : Value}
      (evaluated : Evaluates program environment body value) :
      Evaluates program environment (.group body) value
  | local {environment : List (String × Value)} {name : String} {value : Value}
      (selected : lookup name environment = some value) :
      Evaluates program environment (.local name) value
  | sequence {environment : List (String × Value)} {first rest : Expr}
      {discarded value : Value} (head : Evaluates program environment first discarded)
      (tail : Evaluates program environment rest value) :
      Evaluates program environment (.sequence first rest) value
  | bind {environment : List (String × Value)} {name : String} {annotation : Option TypeExpr} {initial body : Expr}
      {resident value : Value} (initialized : Evaluates program environment initial resident)
      (continued : Evaluates program ((name, resident) :: environment) body value) :
      Evaluates program environment (.bind name annotation initial body) value
  | tuple {environment : List (String × Value)} {head : Expr} {tail : List Expr}
      {first : Value} {rest : List Value} (headEval : Evaluates program environment head first)
      (tailEval : EvaluatesMany program environment tail rest) :
      Evaluates program environment (.tuple head tail) (.tuple first rest)
  | project {environment : List (String × Value)} {body : Expr} {index : Nat}
      {first value : Value} {rest : List Value}
      (source : Evaluates program environment body (.tuple first rest))
      (selected : (first :: rest)[index]? = some value) :
      Evaluates program environment (.project body index) value
  | array {environment : List (String × Value)} {elements : List Expr} {values : List Value}
      (residents : EvaluatesMany program environment elements values) :
      Evaluates program environment (.array elements) (.array values)
  | constant {environment : List (String × Value)} {name : String} {declaration : ConstantDecl}
      {value : Value} (declared : program.constants name = some declaration)
      (initialized : Evaluates program [] declaration.body value) :
      Evaluates program environment (.constant name) value
  | construct {environment : List (String × Value)} {identity : Nat} {tag : Option Nat}
      {fields : List Expr} {values : List Value} (residents : EvaluatesMany program environment fields values) :
      Evaluates program environment (.construct identity tag fields) (.nominal identity tag values)
  | field {environment : List (String × Value)} {body : Expr} {key : FieldKey} {identity index : Nat}
      {declaration : DataDecl} {schema : Fields} {values : List Value} {value : Value}
      (source : Evaluates program environment body (.nominal identity none values))
      (declared : program.data identity = some declaration)
      (structureOnly : declaration.shape = .structure schema)
      (indexed : schema.index key = some index) (selected : values[index]? = some value) :
      Evaluates program environment (.field body key) value

inductive EvaluatesMany (program : Program) : List (String × Value) → List Expr → List Value → Prop where
  | nil {environment : List (String × Value)} : EvaluatesMany program environment [] []
  | cons {environment : List (String × Value)} {head : Expr} {tail : List Expr}
      {first : Value} {rest : List Value} (headEval : Evaluates program environment head first)
      (tailEval : EvaluatesMany program environment tail rest) :
      EvaluatesMany program environment (head :: tail) (first :: rest)
end

/-- Both structural and nominal projections consume the same positional typing fact. -/
theorem ValuesHaveTypes.select {types : List Ty} {values : List Value}
    (typed : ValuesHaveTypes program values types) (index : Nat) (type : Ty)
    (selection : types[index]? = some type) :
    ∃ value, values[index]? = some value ∧ ValueHasType program value type := by
  induction types generalizing values index with
  | nil => cases typed; simp at selection
  | cons head tail ih =>
    cases typed with
    | cons headTyped tailTyped =>
      cases index with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at selection
        subst type
        exact ⟨_, rfl, headTyped⟩
      | succ index => exact ih tailTyped index selection

/-- Every admitted expression in a typed lexical environment terminates with a
correctly typed, unique result. Binding constructs its body's typed environment;
no continuation-readiness or successful-evaluation premise is assumed. -/
theorem correctness {context : List (String × Ty)} {expression : Expr} {type : Ty}
    (admitted : HasType program home context expression type)
    {environment : List (String × Value)} (environmentTyped : EnvironmentTyped program environment context) :
    ∃ value, Evaluates program environment expression value ∧ ValueHasType program value type ∧
      ∀ other, Evaluates program environment expression other → other = value := by
  induction admitted using HasType.rec
    (motive_2 := fun home context expressions types _ =>
      ∀ environment, EnvironmentTyped program environment context →
        ∃ values, EvaluatesMany program environment expressions values ∧ ValuesHaveTypes program values types ∧
          ∀ other, EvaluatesMany program environment expressions other → other = values)
    generalizing environment with
  | unit =>
    refine ⟨.unit, .unit, .unit, ?_⟩
    intro other evaluated
    cases evaluated
    rfl
  | integer fits =>
    refine ⟨_, .integer fits, .integer fits, ?_⟩
    intro other evaluated
    cases evaluated
    rfl
  | character valid =>
    refine ⟨_, .character valid, .character valid, ?_⟩
    intro other evaluated
    cases evaluated
    rfl
  | constant declared visible resolved structural initialized ih =>
    obtain ⟨value, evaluated, typed, unique⟩ := ih EnvironmentTyped.nil
    refine ⟨value, .constant declared evaluated, typed, ?_⟩
    intro other evaluation
    cases evaluation with
    | constant otherDeclared otherEval =>
      have same := Option.some.inj (otherDeclared.symm.trans declared)
      cases same
      exact unique other otherEval
  | group typed ih =>
    obtain ⟨value, evaluated, valueTyped, unique⟩ := ih environmentTyped
    refine ⟨value, .group evaluated, valueTyped, ?_⟩
    intro other evaluation
    cases evaluation with
    | group inner => exact unique other inner
  | @«local» home context name type selected copyable =>
    have resident : ∃ value, lookup name environment = some value ∧ ValueHasType program value type := by
      induction environmentTyped with
      | nil => simp [lookup] at selected
      | @cons name value type environment context valueTyped rest ih =>
        simp only [lookup] at selected ⊢
        split at selected
        · cases selected
          exact ⟨value, by simp_all, valueTyped⟩
        · obtain ⟨found, selection, typed⟩ := ih selected
          exact ⟨found, by simp_all, typed⟩
    obtain ⟨value, selectedValue, valueTyped⟩ := resident
    refine ⟨value, .local selectedValue, valueTyped, ?_⟩
    intro other evaluated
    cases evaluated with
    | «local» found => exact Option.some.inj (found.symm.trans selectedValue)
  | sequence head drop tail headIH tailIH =>
    obtain ⟨discarded, headEval, _, _⟩ := headIH environmentTyped
    obtain ⟨value, tailEval, valueTyped, unique⟩ := tailIH environmentTyped
    refine ⟨value, .sequence headEval tailEval, valueTyped, ?_⟩
    intro other evaluated
    cases evaluated with
    | sequence _ tailEval => exact unique other tailEval
  | bind initialized drop annotated continued initialIH bodyIH =>
    obtain ⟨resident, initialEval, residentTyped, initialUnique⟩ := initialIH environmentTyped
    obtain ⟨value, bodyEval, valueTyped, bodyUnique⟩ :=
      bodyIH (.cons residentTyped environmentTyped)
    refine ⟨value, .bind initialEval bodyEval, valueTyped, ?_⟩
    intro other evaluated
    cases evaluated with
    | bind otherInitial otherBody =>
      have equal := initialUnique _ otherInitial
      subst equal
      exact bodyUnique other otherBody
  | tuple head tail headIH tailIH =>
    obtain ⟨first, headEval, headTyped, headUnique⟩ := headIH environmentTyped
    obtain ⟨rest, tailEval, tailTyped, tailUnique⟩ := tailIH environment environmentTyped
    refine ⟨.tuple first rest, .tuple headEval tailEval, .tuple headTyped tailTyped, ?_⟩
    intro other evaluated
    cases evaluated with
    | tuple otherHead otherTail =>
      have sameHead := headUnique _ otherHead
      have sameTail := tailUnique _ otherTail
      subst sameHead
      subst sameTail
      rfl
  | array residents elementValid size ih =>
    obtain ⟨values, evaluated, typed, unique⟩ := ih environment environmentTyped
    refine ⟨.array values, .array evaluated, .array typed elementValid size, ?_⟩
    intro other evaluation
    cases evaluation with
    | array elements =>
      have same := unique _ elements
      subst same
      rfl
  | @project home context body index first type rest source discard selected sourceIH =>
    obtain ⟨aggregate, sourceEval, aggregateTyped, sourceUnique⟩ := sourceIH environmentTyped
    cases aggregateTyped with
    | tuple headTyped tailTyped =>
      obtain ⟨value, fieldSelected, valueTyped⟩ :=
        ValuesHaveTypes.select (.cons headTyped tailTyped) index type selected
      refine ⟨value, .project sourceEval fieldSelected, valueTyped, ?_⟩
      intro other evaluated
      cases evaluated with
      | project otherSource otherSelected =>
        have same := sourceUnique _ otherSource
        cases same
        exact Option.some.inj (otherSelected.symm.trans fieldSelected)
  | construct declared chosen finite copyable visible access residents ih =>
    obtain ⟨values, evaluated, typed, unique⟩ := ih environment environmentTyped
    refine ⟨_, .construct evaluated, .nominal declared chosen finite typed, ?_⟩
    intro other evaluation
    cases evaluation with
    | construct otherFields =>
      have same := unique _ otherFields
      subst same
      rfl
  | @field home context body key identity index declaration schema field source discard declared structureOnly indexed selected visible ih =>
    obtain ⟨aggregate, evaluated, typed, unique⟩ := ih environmentTyped
    cases typed with
    | @nominal _ tag otherDeclaration otherSchema values otherDeclared chosen finite residents =>
      have sameDeclaration := Option.some.inj (otherDeclared.symm.trans declared)
      subst otherDeclaration
      cases tag with
      | some tag => simp [DataDecl.constructor, structureOnly] at chosen
      | none =>
        have sameSchema : otherSchema = schema := by
          simpa [DataDecl.constructor, structureOnly] using chosen.symm
        subst otherSchema
        have selectedType : (schema.residents.map Field.type)[index]? = some field.type := by
          simp [List.getElem?_map, selected]
        obtain ⟨value, valueSelected, valueTyped⟩ := residents.select index field.type selectedType
        refine ⟨value, .field evaluated declared structureOnly indexed valueSelected, valueTyped, ?_⟩
        intro other evaluation
        cases evaluation with
        | field otherSource otherDeclared otherStructure otherIndex otherSelected =>
          have sameValue := unique _ otherSource
          cases sameValue
          have sameDeclaration := Option.some.inj (otherDeclared.symm.trans declared)
          cases sameDeclaration
          have sameSchema := DataShape.structure.inj (otherStructure.symm.trans structureOnly)
          cases sameSchema
          have sameIndex := Option.some.inj (otherIndex.symm.trans indexed)
          cases sameIndex
          exact Option.some.inj (otherSelected.symm.trans valueSelected)
  | nil =>
    refine ⟨[], .nil, .nil, ?_⟩
    intro other evaluated
    cases evaluated
    rfl
  | cons head tail headIH tailIH =>
    rename_i environment environmentTyped
    obtain ⟨first, headEval, headTyped, headUnique⟩ := headIH environmentTyped
    obtain ⟨rest, tailEval, tailTyped, tailUnique⟩ := tailIH environment environmentTyped
    refine ⟨first :: rest, .cons headEval tailEval, .cons headTyped tailTyped, ?_⟩
    intro other evaluated
    cases evaluated with
    | cons otherHead otherTail =>
      have sameHead := headUnique _ otherHead
      have sameTail := tailUnique _ otherTail
      subst sameHead
      subst sameTail
      rfl

/-- Empty source environments are realized, not assumed. -/
theorem closed_correctness {expression : Expr} {type : Ty}
    (admitted : HasType program home [] expression type) :
    ∃ value, Evaluates program [] expression value ∧ ValueHasType program value type ∧
      ∀ other, Evaluates program [] expression other → other = value :=
  correctness admitted .nil

/-- Exact admission boundary, in every lexical context and at every width. -/
theorem integer_admission (context : List (String × Ty)) (type : IntegerType) (magnitude : Nat) :
    (∃ result, HasType program home context (.integer type magnitude) result) ↔ type.Contains program.target magnitude := by
  constructor
  · rintro ⟨_, admitted⟩
    cases admitted with
    | integer fits => exact fits
  · intro fits
    exact ⟨_, .integer fits⟩

theorem character_admission (context : List (String × Ty)) (number : Nat) :
    (∃ result, HasType program home context (.character number) result) ↔ UnicodeScalar number := by
  constructor
  · rintro ⟨_, admitted⟩
    cases admitted with
    | character valid => exact valid
  · intro valid
    exact ⟨_, .character valid⟩

/-- The original unit subset retains precisely its admission and evaluation meaning. -/
theorem unit_agreement : HasType program home [] .unit .unit ∧
    ∀ value, Evaluates program [] .unit value ↔ value = .unit := by
  obtain ⟨value, evaluated, _, unique⟩ := closed_correctness (program := program) (home := home) HasType.unit
  have same : value = .unit := by cases evaluated; rfl
  refine ⟨.unit, fun other => ⟨?_, ?_⟩⟩
  · intro evaluation
    exact (unique other evaluation).trans same
  · intro equal
    subst other
    exact .unit

end Grounded
