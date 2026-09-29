/-!
Target-indexed expressions, immutable composition, structural and nominal data.
Normative basis: §§2.2–2.3, 3.2–3.4, 4.1–4.4, 5.1–5.3, 6.1–6.3, 7.2–7.3 and 13.1.
Declarations, field types, identities and lexical names are already decoded.
Constructors consume argument expressions in their recorded order. Literal
magnitudes and Unicode numbers are decoded; source elaboration is not proved.
Direct named calls and immediate pattern-callable application share correctness.
Only duplicable nominal owners without hooks or indirections are admitted.
Physical representation, exhaustion and nonduplicable ownership remain outside
this logical AST-to-value boundary.
Admission supplies no successful execution or normalization witness.
Constant-normal-form checks are consumed only after normalization is derived.
No prior specification modules are imported.
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
  deriving DecidableEq

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
  deriving DecidableEq

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

/-- Constructor identity for structural matching; tuples remain distinct from nominal data. -/
inductive Head where
  | unit
  | integer (type : IntegerType) (number : Int)
  | character (number : Nat)
  | tuple | array
  | nominal (identity : Nat) (tag : Option Nat)
  deriving DecidableEq

inductive Value where
  | unit
  | integer (type : IntegerType) (number : Int)
  | character (number : Nat)
  | tuple (head : Value) (tail : List Value)
  | array (elements : List Value)
  | nominal (identity : Nat) (tag : Option Nat) (fields : List Value)

mutual
/-- Total structural equality for constant patterns, without user-defined Eq. -/
def Value.equal (left right : Value) : Bool :=
  match left, right with
  | .unit, .unit => true
  | .integer type number, .integer otherType otherNumber => decide (type = otherType) && decide (number = otherNumber)
  | .character number, .character other => decide (number = other)
  | .tuple head tail, .tuple otherHead otherTail => head.equal otherHead && valuesEqual tail otherTail
  | .array values, .array others => valuesEqual values others
  | .nominal identity tag values, .nominal otherIdentity otherTag others =>
      decide (identity = otherIdentity) && decide (tag = otherTag) && valuesEqual values others
  | _, _ => false
termination_by sizeOf left

def valuesEqual (left right : List Value) : Bool :=
  match left, right with
  | [], [] => true
  | head :: tail, otherHead :: otherTail => head.equal otherHead && valuesEqual tail otherTail
  | _, _ => false
termination_by sizeOf left
end

instance : BEq Value := ⟨Value.equal⟩

instance : LawfulBEq Value := by
  have equal_iff : ∀ (left right : Value), left.equal right = true ↔ left = right := by
    intro left
    induction left using Value.rec
      (motive_2 := fun values => ∀ others, valuesEqual values others = true ↔ values = others) with
    | unit => intro right; cases right <;> simp [Value.equal]
    | integer type number => intro right; cases right <;> simp [Value.equal]
    | character number => intro right; cases right <;> simp [Value.equal]
    | tuple head tail headIH tailIH => intro right; cases right <;> simp [Value.equal, headIH, tailIH]
    | array values ih => intro right; cases right <;> simp [Value.equal, ih]
    | nominal identity tag values ih => intro right; cases right <;> simp [Value.equal, ih, and_assoc]
    | nil => rename_i others; cases others <;> simp [valuesEqual]
    | cons head tail headIH tailIH => rename_i others; cases others <;> simp [valuesEqual, headIH, tailIH]
  exact { rfl := (equal_iff _ _).mpr rfl, eq_of_beq := fun matched => (equal_iff _ _).mp matched }

instance : DecidableEq Value := instDecidableEqOfLawfulBEq


inductive Pattern where
  | wildcard
  | binder (name : String)
  | node (head : Head) (fields : List Pattern)
  /-- Some retains the declared type; None occurs only in coverage specialization. -/
  | literal (type : Option Ty) (value : Value)


inductive PatternSource where
  | wildcard
  | binder (name : String)
  | node (head : Head) (fields : List PatternSource)
  | constant (name : String)

structure BindingType where
  type : Ty
  mutable : Bool := false

structure Place where
  root : String
  fields : List FieldKey := []

inductive Expr where
  | unit
  | integer (type : IntegerType) (magnitude : Nat)
  | character (number : Nat)
  | group (body : Expr)
  | read (place : Place)
  | sequence (first rest : Expr)
  | bind (mutable : Bool) (name : String) (annotation : Option TypeExpr) (initial body : Expr)
  | tuple (head : Expr) (tail : List Expr)
  | array (elements : List Expr)
  | constant (name : String)
  | construct (identity : Nat) (tag : Option Nat) (fields : List Expr)
  | field (body : Expr) (key : FieldKey)
  | call (identity : Nat) (arguments : List Expr)
  | assign (place : Place) (value rest : Expr)
  | applyPatterns (inputs : List Ty) (arguments : List Expr) (arms : List (PatternSource × Expr))
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

/-- Direct, noncapturing, effect-free functions; omitted results denote unit. -/
structure FunctionDecl where
  home : Module
  visibility : Visibility := .private
  parameters : List (String × BindingType)
  result : Ty := .unit
  body : Expr

/-- One immutable decoded program supplies the facts shared by static and
dynamic semantics. It carries source declarations, never execution guarantees. -/
structure Program where
  target : Target
  aliases : Aliases
  constants : Constants
  data : DataDeclarations
  functions : Nat → Option FunctionDecl
variable {program : Program}
variable {home : Module}
/-- One field contract supplies tuple bounds and nominal visibility to reads and writes. -/
inductive ProjectionType (program : Program) (home : Module) : Ty → FieldKey → Ty → Prop where
  | tuple {first type : Ty} {rest : List Ty} {index : Nat}
      (selected : (first :: rest)[index]? = some type) :
      ProjectionType program home (.tuple first rest) (.positional index) type
  | nominal {identity index : Nat} {key : FieldKey} {declaration : DataDecl} {schema : Fields} {field : Field}
      (declared : program.data identity = some declaration)
      (structureOnly : declaration.shape = .structure schema)
      (indexed : schema.index key = some index) (selected : schema.residents[index]? = some field)
      (visible : field.visibility.Allows declaration.home home) :
      ProjectionType program home (.nominal identity) key field.type

inductive PathType (program : Program) (home : Module) : Ty → List FieldKey → Ty → Prop where
  | nil (type : Ty) : PathType program home type [] type
  | cons {source middle target : Ty} {key : FieldKey} {keys : List FieldKey}
      (head : ProjectionType program home source key middle) (tail : PathType program home middle keys target) :
      PathType program home source (key :: keys) target

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

/-- Nearest lexical binding wins, including in shadowing initializers. -/
def lookup {α : Type} (name : String) : List (String × α) → Option α
  | [] => none
  | (key, value) :: rest => if name = key then some value else lookup name rest

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

inductive EnvironmentTyped (program : Program) : List (String × Value) → List (String × BindingType) → Prop where
  | nil : EnvironmentTyped program [] []
  | cons {name : String} {value : Value} {type : BindingType}
      {environment : List (String × Value)} {context : List (String × BindingType)}
      (resident : ValueHasType program value type.type) (rest : EnvironmentTyped program environment context) :
      EnvironmentTyped program ((name, value) :: environment) ((name, type) :: context)


def Value.head : Value → Head
  | .unit => .unit
  | .integer type number => .integer type number
  | .character number => .character number
  | .tuple _ _ => .tuple
  | .array _ => .array
  | .nominal identity tag _ => .nominal identity tag

def Value.children : Value → List Value
  | .tuple head tail => head :: tail
  | .array values | .nominal _ _ values => values
  | _ => []

/-- Resolve one actual tuple/structure field; enum payloads and array indexing are not field projection. -/
def Value.fieldIndex (program : Program) (value : Value) (key : FieldKey) : Option Nat :=
  match value, key with
  | .tuple _ _, .positional index => some index
  | .nominal identity none _, key => do
      let declaration ← program.data identity
      match declaration.shape with
      | .structure schema => schema.index key
      | .enumeration _ => none
  | _, _ => none

def Value.readField (program : Program) (value : Value) (key : FieldKey) : Option Value := do
  let index ← value.fieldIndex program key
  value.children[index]?

def Value.replaceChild (value : Value) (index : Nat) (replacement : Value) : Option Value :=
  match value with
  | .tuple head tail =>
      match index with
      | 0 => some (.tuple replacement tail)
      | index + 1 => (tail[index]?).map fun _ => .tuple head (tail.set index replacement)
  | .nominal identity tag fields => (fields[index]?).map fun _ => .nominal identity tag (fields.set index replacement)
  | _ => none

def Value.readPath (program : Program) (value : Value) (keys : List FieldKey) : Option Value :=
  match keys with
  | [] => some value
  | key :: rest => do
      let child ← value.readField program key
      child.readPath program rest

def Value.writePath (program : Program) (value : Value) (keys : List FieldKey) (replacement : Value) : Option Value :=
  match keys with
  | [] => some replacement
  | key :: rest => do
      let index ← value.fieldIndex program key
      let child ← value.children[index]?
      let updated ← child.writePath program rest replacement
      value.replaceChild index updated

mutual
def Pattern.matchValue (pattern : Pattern) (value : Value) : Option (List (String × Value)) :=
  match pattern with
  | .wildcard => some []
  | .binder name => some [(name, value)]
  | .literal _ expected => if value = expected then some [] else none
  | .node head fields =>
      if head = value.head then matchPatterns fields value.children else none
termination_by sizeOf pattern

def matchPatterns (patterns : List Pattern) (values : List Value) : Option (List (String × Value)) :=
  match patterns, values with
  | [], [] => some []
  | pattern :: patterns, value :: values => do
      let first ← pattern.matchValue value
      let rest ← matchPatterns patterns values
      pure (first ++ rest)
  | _, _ => none
termination_by sizeOf patterns
end

/-- Constructor signatures are shared by pattern typing and coverage specialization. -/
inductive HeadType (program : Program) : Head → Ty → List Ty → Prop where
  | unit : HeadType program .unit .unit []
  | integer {type : IntegerType} {number : Int} (fits : type.Contains program.target number) :
      HeadType program (.integer type number) (.integer type) []
  | character {number : Nat} (valid : UnicodeScalar number) :
      HeadType program (.character number) .character []
  | tuple (first : Ty) (rest : List Ty) : HeadType program .tuple (.tuple first rest) (first :: rest)
  | array (element : Ty) (length : Nat) : HeadType program .array (.array element length) (List.replicate length element)
  | nominal {identity : Nat} {tag : Option Nat} {declaration : DataDecl} {schema : Fields}
      (declared : program.data identity = some declaration)
      (chosen : declaration.constructor tag = some schema) :
      HeadType program (.nominal identity tag) (.nominal identity) (schema.residents.map Field.type)

def Head.Accessible (program : Program) (home : Module) : Head → Prop
  | .nominal identity tag => ∃ declaration schema,
      program.data identity = some declaration ∧ declaration.constructor tag = some schema ∧
      declaration.visibility.Allows declaration.home home ∧
      ∀ field ∈ schema.residents, field.visibility.Allows declaration.home home
  | _ => True

mutual
inductive PatternType (program : Program) (home : Module) : Pattern → Ty → List (String × BindingType) → Prop where
  | wildcard {type : Ty} (discard : Duplicable program.data type) : PatternType program home .wildcard type []
  | binder (name : String) {type : Ty} (discard : Duplicable program.data type) :
      PatternType program home (.binder name) type [(name, ⟨type, false⟩)]
  | literal {type : Ty} {value : Value} (typed : ValueHasType program value type)
      (discard : Duplicable program.data type) : PatternType program home (.literal (some type) value) type []
  | node {head : Head} {patterns : List Pattern} {type : Ty} {fields : List Ty} {bindings : List (String × BindingType)}
      (shape : HeadType program head type fields) (access : head.Accessible program home)
      (fieldsTyped : PatternsType program home patterns fields bindings) :
      PatternType program home (.node head patterns) type bindings
inductive PatternsType (program : Program) (home : Module) : List Pattern → List Ty → List (String × BindingType) → Prop where
  | nil : PatternsType program home [] [] []
  | cons {pattern : Pattern} {patterns : List Pattern} {type : Ty} {types : List Ty}
      {first rest : List (String × BindingType)} (headTyped : PatternType program home pattern type first)
      (tailTyped : PatternsType program home patterns types rest) :
      PatternsType program home (pattern :: patterns) (type :: types) (first ++ rest)
end

/-- Static matrix specialization, not an assumption that an execution will match. -/
def Pattern.specialize (head : Head) (arity : Nat) : Pattern → Option (List Pattern)
  | .wildcard | .binder _ => some (List.replicate arity .wildcard)
  | .node selected fields => if selected = head ∧ fields.length = arity then some fields else none
  | .literal _ value => if value.head = head ∧ value.children.length = arity
      then some (value.children.map (Pattern.literal none)) else none

def specializeRow (head : Head) (arity : Nat) : List Pattern → Option (List Pattern)
  | [] => none
  | pattern :: tail => (pattern.specialize head arity).map (· ++ tail)

inductive Covers (program : Program) : List Ty → List (List Pattern) → Prop where
  | done {rows : List (List Pattern)} (empty : [] ∈ rows) : Covers program [] rows
  | split {type : Ty} {types : List Ty} {rows : List (List Pattern)}
      (branches : ∀ head fields, HeadType program head type fields →
        Covers program (fields ++ types) (rows.filterMap (specializeRow head fields.length))) :
      Covers program (type :: types) rows

/-- The callable's argument list is retained; only pattern interpretation unwraps
one argument. A singleton tuple argument is not two arguments (§6.1). -/
def argumentType : List Ty → Ty
  | [] => .unit
  | [type] => type
  | head :: next :: tail => .tuple head (next :: tail)

def argumentValue : List Value → Value
  | [] => .unit
  | [value] => value
  | head :: next :: tail => .tuple head (next :: tail)

def selectArm (value : Value) : List (Pattern × Expr) → Option (List (String × Value) × Expr)
  | [] => none
  | (pattern, body) :: rest =>
      match pattern.matchValue value with
      | some bindings => some (bindings, body)
      | none => selectArm value rest

/-- A static witness distinguishes each clause from its source-order predecessors.
It is a typed datum, not an assumed result of the subject expression. -/
def Useful (program : Program) (type : Ty) (previous : List Pattern) (pattern : Pattern) : Prop :=
  ∃ value, ValueHasType program value type ∧ pattern.matchValue value ≠ none ∧
    ∀ earlier ∈ previous, earlier.matchValue value = none


/-- Replace the nearest lexical binding; an absent destination is rejected. -/
def replaceBinding {α : Type} (name : String) (value : α) : List (String × α) → Option (List (String × α))
  | [] => none
  | (key, old) :: rest =>
      if key = name then some ((key, value) :: rest)
      else ((key, old) :: ·) <$> replaceBinding name value rest

def readPlace (program : Program) (place : Place) (environment : List (String × Value)) : Option Value := do
  let parent ← lookup place.root environment
  parent.readPath program place.fields

def writePlace (program : Program) (place : Place) (replacement : Value) (environment : List (String × Value)) :
    Option (List (String × Value)) := do
  let parent ← lookup place.root environment
  let updated ← parent.writePath program place.fields replacement
  replaceBinding place.root updated environment

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
  | field {environment after : List (String × Value)} {body : Expr} {key : FieldKey} {parent value : Value}
      (source : Evaluates program environment body parent after)
      (selected : parent.readField program key = some value) :
      Evaluates program environment (.field body key) value after
  | call {environment middle localAfter : List (String × Value)} {identity : Nat} {arguments : List Expr}
      {declaration : FunctionDecl} {values : List Value} {value : Value}
      (declared : program.functions identity = some declaration)
      (inputs : EvaluatesMany program environment arguments values middle)
      (body : Evaluates program (List.zip (declaration.parameters.map Prod.fst) values) declaration.body value localAfter) :
      Evaluates program environment (.call identity arguments) value middle
  | applyPatterns {environment middle after : List (String × Value)} {inputs : List Ty} {arguments : List Expr}
      {arms : List (PatternSource × Expr)} {normalized : List (Pattern × Expr)} {values : List Value}
      {bindings : List (String × Value)} {body : Expr} {value : Value}
      (normalization : NormalizesArms program arms normalized)
      (argumentsEval : EvaluatesMany program environment arguments values middle)
      (selected : selectArm (argumentValue values) normalized = some (bindings, body))
      (bodyEval : Evaluates program (bindings ++ middle) body value after) :
      Evaluates program environment (.applyPatterns inputs arguments arms) value (after.drop bindings.length)

inductive EvaluatesMany (program : Program) : List (String × Value) → List Expr → List Value → List (String × Value) → Prop where
  | nil {environment : List (String × Value)} : EvaluatesMany program environment [] [] environment
  | cons {environment middle after : List (String × Value)} {head : Expr} {tail : List Expr}
      {first : Value} {rest : List Value} (headEval : Evaluates program environment head first middle)
      (tailEval : EvaluatesMany program middle tail rest after) :
      EvaluatesMany program environment (head :: tail) (first :: rest) after
inductive NormalizesPattern (program : Program) : PatternSource → Pattern → Prop where
  | wildcard : NormalizesPattern program .wildcard .wildcard
  | binder (name : String) : NormalizesPattern program (.binder name) (.binder name)
  | node {head : Head} {source : List PatternSource} {result : List Pattern}
      (fields : NormalizesPatterns program source result) :
      NormalizesPattern program (.node head source) (.node head result)
  | constant {name : String} {declaration : ConstantDecl} {type : Ty} {value : Value}
      (declared : program.constants name = some declaration)
      (resolved : ResolvesType program.aliases declaration.type type)
      (evaluated : Evaluates program [] (.constant name) value []) :
      NormalizesPattern program (.constant name) (.literal (some type) value)
inductive NormalizesPatterns (program : Program) : List PatternSource → List Pattern → Prop where
  | nil : NormalizesPatterns program [] []
  | cons {source : PatternSource} {sources : List PatternSource} {result : Pattern} {results : List Pattern}
      (head : NormalizesPattern program source result) (tail : NormalizesPatterns program sources results) :
      NormalizesPatterns program (source :: sources) (result :: results)
inductive NormalizesArms (program : Program) : List (PatternSource × Expr) → List (Pattern × Expr) → Prop where
  | nil : NormalizesArms program [] []
  | cons {source : PatternSource} {pattern : Pattern} {body : Expr}
      {sources : List (PatternSource × Expr)} {results : List (Pattern × Expr)}
      (head : NormalizesPattern program source pattern) (tail : NormalizesArms program sources results) :
      NormalizesArms program ((source, body) :: sources) ((pattern, body) :: results)
end

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
  | read {home : Module} {context : List (String × BindingType)} {place : Place} {slot : BindingType} {type : Ty}
      (selected : lookup place.root context = some slot) (path : PathType program home slot.type place.fields type)
      (copyable : Duplicable program.data type) :
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
  | field {home : Module} {context : List (String × BindingType)} {body : Expr} {key : FieldKey}
      {parentType type : Ty} (source : HasType program home context body parentType)
      (discard : Duplicable program.data parentType) (selected : ProjectionType program home parentType key type) :
      HasType program home context (.field body key) type
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
      {value rest : Expr} {slot : BindingType} {target result : Ty}
      (selected : lookup place.root context = some slot) (writable : slot.mutable = true)
      (path : PathType program home slot.type place.fields target)
      (discard : Duplicable program.data target)
      (resident : HasType program home context value target)
      (continued : HasType program home context rest result) :
      HasType program home context (.assign place value rest) result
  | applyPatterns {home : Module} {context : List (String × BindingType)} {inputs : List Ty}
      {arguments : List Expr} {arms : List (PatternSource × Expr)} {result : Ty}
      (argumentsTyped : HasTypes program home context arguments inputs)
      (nonempty : arms ≠ [])
      (constants : ArmConstantsTyped program home arms)
      (covered : ∀ normalized, NormalizesArms program arms normalized →
        Covers program [argumentType inputs] (normalized.map (fun arm => [arm.1])))
      (bodies : ∀ normalized, NormalizesArms program arms normalized →
        ArmsType program home context (argumentType inputs) result [] normalized) :
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
/-- These source rules check constant initializers before pattern normalization.
No evaluated value or successful-normalization witness is supplied. -/
inductive PatternConstantsTyped (program : Program) : Module → PatternSource → Prop where
  | patternWildcard {home : Module} : PatternConstantsTyped program home .wildcard
  | patternBinder {home : Module} (name : String) : PatternConstantsTyped program home (.binder name)
  | patternNode {home : Module} {head : Head} {fields : List PatternSource}
      (constants : PatternsConstantsTyped program home fields) : PatternConstantsTyped program home (.node head fields)
  | patternConstant {home : Module} {name : String} {type : Ty}
      (typed : HasType program home [] (.constant name) type) : PatternConstantsTyped program home (.constant name)
inductive PatternsConstantsTyped (program : Program) : Module → List PatternSource → Prop where
  | patternsEmpty {home : Module} : PatternsConstantsTyped program home []
  | patternsCons {home : Module} {first : PatternSource} {rest : List PatternSource}
      (head : PatternConstantsTyped program home first) (tail : PatternsConstantsTyped program home rest) :
      PatternsConstantsTyped program home (first :: rest)
inductive ArmConstantsTyped (program : Program) : Module → List (PatternSource × Expr) → Prop where
  | armsEmpty {home : Module} : ArmConstantsTyped program home []
  | armsCons {home : Module} {pattern : PatternSource} {body : Expr} {rest : List (PatternSource × Expr)}
      (head : PatternConstantsTyped program home pattern) (tail : ArmConstantsTyped program home rest) :
      ArmConstantsTyped program home ((pattern, body) :: rest)
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

theorem ValuesHaveTypes.set {types : List Ty} {values : List Value}
    (typed : ValuesHaveTypes program values types) (index : Nat) {type : Ty}
    (selected : types[index]? = some type) {replacement : Value} (resident : ValueHasType program replacement type) :
    ValuesHaveTypes program (values.set index replacement) types := by
  induction types generalizing values index with
  | nil => cases typed; simp at selected
  | cons first rest ih =>
    cases typed with
    | cons head tail =>
      cases index with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
        cases selected
        exact .cons resident tail
      | succ index => exact .cons head (ih tail index selected)

/-- The selected resident and lawful replacement are derived from the same field contract. -/
theorem ProjectionType.access {source target : Ty} {key : FieldKey}
    (projection : ProjectionType program home source key target) {value : Value}
    (typed : ValueHasType program value source) :
    ∃ index resident, value.fieldIndex program key = some index ∧ value.children[index]? = some resident ∧
      ValueHasType program resident target ∧
      ∀ replacement, ValueHasType program replacement target →
        ∃ updated, value.replaceChild index replacement = some updated ∧ ValueHasType program updated source ∧
          updated.fieldIndex program key = some index ∧ updated.children[index]? = some replacement := by
  cases projection with
  | @tuple first type rest index selected =>
    cases typed with
    | @tuple head tail _ _ headTyped tailTyped =>
      obtain ⟨resident, found, residentTyped⟩ := ValuesHaveTypes.select (.cons headTyped tailTyped) index target selected
      refine ⟨index, resident, rfl, found, residentTyped, ?_⟩
      intro replacement replacementTyped
      cases index with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
        cases selected
        exact ⟨_, rfl, .tuple replacementTyped tailTyped, rfl, rfl⟩
      | succ index =>
        change tail[index]? = some resident at found
        obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
        exact ⟨_, by simp [Value.replaceChild, found], .tuple headTyped (tailTyped.set index selected replacementTyped),
          rfl, by simp [Value.children, bound]⟩
  | @nominal identity index key declaration schema field declared structureOnly indexed selected visible =>
    cases typed with
    | @nominal _ tag otherDeclaration otherSchema values otherDeclared chosen finite residents =>
      have sameDeclaration := Option.some.inj (otherDeclared.symm.trans declared)
      subst otherDeclaration
      cases tag with
      | some tag => simp [DataDecl.constructor, structureOnly] at chosen
      | none =>
        have sameSchema : otherSchema = schema := by simpa [DataDecl.constructor, structureOnly] using chosen.symm
        subst otherSchema
        have selectedType : (schema.residents.map Field.type)[index]? = some field.type := by simp [List.getElem?_map, selected]
        obtain ⟨resident, found, residentTyped⟩ := residents.select index field.type selectedType
        refine ⟨index, resident, ?_, found, residentTyped, ?_⟩
        · simp [Value.fieldIndex, declared, structureOnly, indexed]
        · intro replacement replacementTyped
          obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
          refine ⟨_, by simp [Value.replaceChild, found], .nominal declared chosen finite (residents.set index selectedType replacementTyped), ?_, ?_⟩
          · simp [Value.fieldIndex, declared, structureOnly, indexed]
          · simp [Value.children, bound]

theorem PathType.read {source target : Ty} {keys : List FieldKey}
    (path : PathType program home source keys target) {value : Value} (typed : ValueHasType program value source) :
    ∃ resident, value.readPath program keys = some resident ∧ ValueHasType program resident target := by
  induction path generalizing value with
  | nil => exact ⟨value, rfl, typed⟩
  | cons head tail ih =>
    obtain ⟨index, child, indexed, found, childTyped, _⟩ := head.access typed
    obtain ⟨resident, selected, residentTyped⟩ := ih childTyped
    exact ⟨resident, by simp [Value.readPath, Value.readField, indexed, found, selected], residentTyped⟩

theorem PathType.write {source target : Ty} {keys : List FieldKey}
    (path : PathType program home source keys target) {value replacement : Value}
    (typed : ValueHasType program value source) (resident : ValueHasType program replacement target) :
    ∃ updated, value.writePath program keys replacement = some updated ∧ ValueHasType program updated source ∧
      updated.readPath program keys = some replacement := by
  induction path generalizing value with
  | nil => exact ⟨replacement, rfl, resident, rfl⟩
  | cons head tail ih =>
    obtain ⟨index, child, indexed, found, childTyped, replace⟩ := head.access typed
    obtain ⟨updatedChild, childWritten, updatedTyped, childRead⟩ := ih childTyped resident
    obtain ⟨updated, written, resultTyped, newIndex, newChild⟩ := replace updatedChild updatedTyped
    exact ⟨updated, by simp [Value.writePath, indexed, found, childWritten, written], resultTyped,
      by simp [Value.readPath, Value.readField, newIndex, newChild, childRead]⟩

theorem EnvironmentTyped.append {left right : List (String × Value)} {first rest : List (String × BindingType)}
    (front : EnvironmentTyped program left first) (back : EnvironmentTyped program right rest) :
    EnvironmentTyped program (left ++ right) (first ++ rest) := by
  induction front with
  | nil => exact back
  | cons resident tail ih => exact .cons resident ih

theorem EnvironmentTyped.drop {environment : List (String × Value)} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) (count : Nat) :
    EnvironmentTyped program (environment.drop count) (context.drop count) := by
  induction count generalizing environment context with
  | zero => exact typed
  | succ count ih => cases typed with
    | nil => exact .nil
    | cons resident rest => exact ih rest

theorem EnvironmentTyped.length {environment : List (String × Value)} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) : environment.length = context.length := by
  induction typed with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem EnvironmentTyped.replace {environment : List (String × Value)} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) {name : String} {slot : BindingType}
    (selected : lookup name context = some slot) {value : Value} (resident : ValueHasType program value slot.type) :
    ∃ after, replaceBinding name value environment = some after ∧ EnvironmentTyped program after context ∧
      lookup name after = some value := by
  induction typed with
  | nil => simp [lookup] at selected
  | @cons key old type environment context oldTyped rest ih =>
    simp only [lookup] at selected
    split at selected
    next same =>
      cases selected
      exact ⟨_, by simp [replaceBinding, same], .cons resident rest, by simp [lookup, same]⟩
    next different =>
      obtain ⟨after, replaced, afterTyped, found⟩ := ih selected
      exact ⟨_, by simp [replaceBinding, Ne.symm different, replaced], .cons oldTyped afterTyped, by simp [lookup, different, found]⟩

theorem EnvironmentTyped.lookup {environment : List (String × Value)} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) {name : String} {type : BindingType}
    (selected : lookup name context = some type) :
    ∃ value, lookup name environment = some value ∧ ValueHasType program value type.type := by
  induction typed with
  | nil => simp [Grounded.lookup] at selected
  | @cons key value type environment context valueTyped rest ih =>
    simp only [Grounded.lookup] at selected ⊢
    split at selected
    · cases selected
      exact ⟨value, by simp_all, valueTyped⟩
    · obtain ⟨found, selection, typed⟩ := ih selected
      exact ⟨found, by simp_all, typed⟩

theorem EnvironmentTyped.readPlace {environment : List (String × Value)} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) {place : Place} {slot : BindingType} {target : Ty}
    (selected : Grounded.lookup place.root context = some slot) (path : PathType program home slot.type place.fields target) :
    ∃ value, Grounded.readPlace program place environment = some value ∧ ValueHasType program value target := by
  obtain ⟨parent, found, parentTyped⟩ := typed.lookup selected
  obtain ⟨resident, read, residentTyped⟩ := path.read parentTyped
  exact ⟨resident, by simp [Grounded.readPlace, found, read], residentTyped⟩

theorem EnvironmentTyped.writePlace {environment : List (String × Value)} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) {place : Place} {slot : BindingType} {target : Ty}
    (selected : Grounded.lookup place.root context = some slot) (path : PathType program home slot.type place.fields target)
    {replacement : Value} (resident : ValueHasType program replacement target) :
    ∃ after, writePlace program place replacement environment = some after ∧ EnvironmentTyped program after context ∧
      Grounded.readPlace program place after = some replacement := by
  obtain ⟨parent, found, parentTyped⟩ := typed.lookup selected
  obtain ⟨updated, written, updatedTyped, readback⟩ := path.write parentTyped resident
  obtain ⟨after, replaced, afterTyped, lookupAfter⟩ := typed.replace selected updatedTyped
  exact ⟨after, by simp [Grounded.writePlace, found, written, replaced], afterTyped,
    by simp [Grounded.readPlace, lookupAfter, readback]⟩

/-- Runtime typing produces the constructor signature consumed by both pattern
binding and exhaustive dispatch; neither consumer guesses resident types. -/
theorem ValueHasType.decompose {value : Value} {type : Ty} (typed : ValueHasType program value type) :
    ∃ fields, HeadType program value.head type fields ∧ ValuesHaveTypes program value.children fields := by
  cases typed with
  | unit => exact ⟨[], .unit, .nil⟩
  | integer fits => exact ⟨[], .integer fits, .nil⟩
  | character valid => exact ⟨[], .character valid, .nil⟩
  | tuple first rest => exact ⟨_, .tuple _ _, .cons first rest⟩
  | array residents _ _ => exact ⟨_, .array _ _, residents⟩
  | nominal declared chosen _ residents => exact ⟨_, .nominal declared chosen, residents⟩

theorem ValuesHaveTypes.argument {values : List Value} {types : List Ty}
    (typed : ValuesHaveTypes program values types) :
    ValueHasType program (argumentValue values) (argumentType types) := by
  cases typed with
  | nil => exact .unit
  | cons head tail =>
    cases tail with
    | nil => exact head
    | cons next rest => exact .tuple head (.cons next rest)

theorem PatternType.bindings {pattern : Pattern} {type : Ty} {context : List (String × BindingType)}
    (typed : PatternType program home pattern type context) {value : Value}
    (valueTyped : ValueHasType program value type) {bindings : List (String × Value)}
    (matched : pattern.matchValue value = some bindings) : EnvironmentTyped program bindings context := by
  induction typed using PatternType.rec
    (motive_2 := fun patterns types context _ => ∀ values, ValuesHaveTypes program values types →
      ∀ bindings, matchPatterns patterns values = some bindings → EnvironmentTyped program bindings context)
    generalizing value bindings with
  | wildcard discard =>
    simp only [Pattern.matchValue, Option.some.injEq] at matched
    subst bindings
    exact .nil
  | binder name discard =>
    simp only [Pattern.matchValue, Option.some.injEq] at matched
    subst bindings
    exact .cons valueTyped .nil
  | literal typed discard =>
    simp only [Pattern.matchValue] at matched
    split at matched
    next equal =>
      have empty := Option.some.inj matched
      subst bindings
      exact .nil
    next different => contradiction
  | @node head patterns type fields context shape access fieldsTyped fieldsIH =>
    simp only [Pattern.matchValue] at matched
    split at matched
    next same =>
      obtain ⟨types, actual, children⟩ := valueTyped.decompose
      rw [← same] at actual
      have aligned : fields = types := by
        cases shape <;> cases actual <;> simp_all
      subst types
      exact fieldsIH _ children bindings matched
    next different => contradiction
  | nil =>
    rename_i values valuesTyped bindings matched
    cases valuesTyped
    simp only [matchPatterns, Option.some.injEq] at matched
    subst bindings
    exact .nil
  | @cons pattern patterns type types frontContext backContext head tail headIH tailIH =>
    rename_i values valuesTyped bindings matched
    cases valuesTyped with
    | @cons value values type types first rest =>
      simp only [matchPatterns] at matched
      cases headMatch : pattern.matchValue value with
      | none => simp [headMatch] at matched
      | some front =>
        cases tailMatch : matchPatterns patterns values with
        | none => simp [headMatch, tailMatch] at matched
        | some back =>
          simp [headMatch, tailMatch] at matched
          subst bindings
          exact EnvironmentTyped.append (headIH first headMatch) (tailIH _ rest _ tailMatch)

/-- Constructor-space coverage constructs an actual first matching clause. No
post-evaluation match result occurs among the admission premises. -/
theorem Covers.selectArm {type : Ty} {arms : List (Pattern × Expr)} {value : Value}
    (covered : Covers program [type] (arms.map (fun arm => [arm.1])))
    (typed : ValueHasType program value type) :
    ∃ bindings body, selectArm value arms = some (bindings, body) := by
  have lengths : ∀ {values : List Value} {types : List Ty},
      ValuesHaveTypes program values types → values.length = types.length := by
    intro values
    induction values with
    | nil => intro types typed; cases typed; rfl
    | cons value values ih =>
      intro types typed
      cases typed with
      | cons first rest => exact congrArg Nat.succ (ih rest)
  have appendTyped : ∀ {first second : List Value} {front back : List Ty},
      ValuesHaveTypes program first front → ValuesHaveTypes program second back →
      ValuesHaveTypes program (first ++ second) (front ++ back) := by
    intro first
    induction first with
    | nil => intro second front back typed rest; cases typed; exact rest
    | cons value values ih =>
      intro second front back typed rest
      cases typed with
      | cons head tail => exact .cons head (ih tail rest)
  have appendMatching : ∀ (patterns : List Pattern) (values : List Value),
      patterns.length = values.length → ∀ tail rest,
      matchPatterns (patterns ++ tail) (values ++ rest) =
        ((matchPatterns patterns values).bind fun first =>
          (matchPatterns tail rest).bind fun second => some (first ++ second)) := by
    intro patterns
    induction patterns with
    | nil =>
      intro values equal tail rest
      have empty : values = [] := by simpa using equal.symm
      subst values
      simp [matchPatterns]
    | cons pattern patterns ih =>
      intro values equal tail rest
      cases values with
      | nil => simp at equal
      | cons value values =>
        have lengths : patterns.length = values.length := by simpa using equal
        simp only [List.cons_append, matchPatterns]
        rw [ih values lengths]
        cases head : pattern.matchValue value <;>
          cases front : matchPatterns patterns values <;>
          cases back : matchPatterns tail rest <;>
          simp [List.append_assoc]
  have literalFields : ∀ (expected actual : List Value) (bindings : List (String × Value)),
      matchPatterns (expected.map (Pattern.literal none)) actual = some bindings → expected = actual := by
    intro expected
    induction expected with
    | nil =>
      intro actual bindings matched
      cases actual with
      | nil => rfl
      | cons head tail => simp [matchPatterns] at matched
    | cons expected rest ih =>
      intro actual bindings matched
      cases actual with
      | nil => simp [matchPatterns] at matched
      | cons value values =>
        simp only [List.map_cons, matchPatterns, Pattern.matchValue] at matched
        split at matched
        next same =>
          subst value
          have tailMatch : matchPatterns (rest.map (Pattern.literal none)) values = some bindings := by
            simpa using matched
          have sameTail := ih values bindings tailMatch
          subst values
          rfl
        next different => simp at matched
  have valueExt : ∀ (left right : Value), left.head = right.head → left.children = right.children → left = right := by
    intro left right heads children
    cases left <;> cases right <;> simp_all [Value.head, Value.children]
  have matrixSound : ∀ {types : List Ty} {rows : List (List Pattern)}, Covers program types rows →
      ∀ values, ValuesHaveTypes program values types →
      ∃ row ∈ rows, ∃ bindings, matchPatterns row values = some bindings := by
    intro types rows coverage
    induction coverage with
    | done contained =>
      intro values typed
      cases typed
      exact ⟨[], contained, [], by simp [matchPatterns]⟩
    | @split type types rows branches ih =>
      intro values typed
      cases typed with
      | @cons value values _ _ first rest =>
        obtain ⟨fields, headTyped, childrenTyped⟩ := first.decompose
        obtain ⟨row, included, bindings, matched⟩ :=
          ih _ fields headTyped _ (appendTyped childrenTyped rest)
        obtain ⟨original, originalIncluded, specialized⟩ := List.mem_filterMap.mp included
        cases original with
        | nil => simp [specializeRow] at specialized
        | cons pattern patterns =>
          simp only [specializeRow, Option.map_eq_some_iff] at specialized
          obtain ⟨front, frontSelected, sameRow⟩ := specialized
          subst row
          have frontLength : front.length = value.children.length := by
            have normalized : front.length = fields.length := by
              cases pattern with
              | wildcard => simp [Pattern.specialize] at frontSelected; subst front; simp
              | binder name => simp [Pattern.specialize] at frontSelected; subst front; simp
              | node head children =>
                simp only [Pattern.specialize] at frontSelected
                split at frontSelected <;> simp_all
              | literal type expected =>
                simp only [Pattern.specialize] at frontSelected
                split at frontSelected
                next selected =>
                  have same := Option.some.inj frontSelected
                  subst front
                  simpa using selected.2
                next impossible => contradiction
            exact normalized.trans (lengths childrenTyped).symm
          rw [appendMatching front value.children frontLength] at matched
          simp only [Option.bind_eq_some_iff] at matched
          obtain ⟨firstBindings, firstMatched, restBindings, restMatched, _⟩ := matched
          have originalMatches : ∃ result, pattern.matchValue value = some result := by
            cases pattern with
            | wildcard => exact ⟨[], by simp [Pattern.matchValue]⟩
            | binder name => exact ⟨[(name, value)], by simp [Pattern.matchValue]⟩
            | node head children =>
              simp only [Pattern.specialize] at frontSelected
              split at frontSelected
              next selected =>
                have sameChildren := Option.some.inj frontSelected
                subst front
                exact ⟨firstBindings, by simpa [Pattern.matchValue, selected.1] using firstMatched⟩
              next impossible => contradiction
            | literal type expected =>
              simp only [Pattern.specialize] at frontSelected
              split at frontSelected
              next selected =>
                have sameFront := Option.some.inj frontSelected
                subst front
                have childrenEqual := literalFields expected.children value.children firstBindings firstMatched
                have equal := valueExt expected value selected.1 childrenEqual
                exact ⟨[], by simp [Pattern.matchValue, equal]⟩
              next impossible => contradiction
          obtain ⟨headBindings, headMatched⟩ := originalMatches
          exact ⟨pattern :: patterns, originalIncluded, headBindings ++ restBindings,
            by simp [matchPatterns, headMatched, restMatched]⟩
  obtain ⟨row, included, bindings, matched⟩ := matrixSound covered [value] (.cons typed .nil)
  obtain ⟨arm, armIncluded, sameRow⟩ := List.mem_map.mp included
  subst row
  have armMatches : arm.1.matchValue value ≠ none := by
    intro missing
    simp [matchPatterns, missing] at matched
  have noneMeansMissing : ∀ (arms : List (Pattern × Expr)), Grounded.selectArm value arms = none →
      ∀ arm ∈ arms, arm.1.matchValue value = none := by
    intro arms
    induction arms with
    | nil => simp
    | cons first rest ih =>
      intro missing arm included
      simp only [Grounded.selectArm] at missing
      cases selected : first.1.matchValue value with
      | some found => simp [selected] at missing
      | none =>
        simp only [selected] at missing
        rcases List.mem_cons.mp included with same | later
        · subst arm; exact selected
        · exact ih missing arm later
  cases selected : Grounded.selectArm value arms with
  | none => exact False.elim (armMatches (noneMeansMissing arms selected arm armIncluded))
  | some result => exact ⟨result.1, result.2, rfl⟩


/-- Every admitted expression produces a uniquely determined, correctly typed
result and updated lexical environment. Later expressions consume that actual
post-state; scopes remove only their own bindings. -/
theorem correctness {context : List (String × BindingType)} {expression : Expr} {type : Ty}
    (admitted : HasType program home context expression type)
    {environment : List (String × Value)} (environmentTyped : EnvironmentTyped program environment context) :
    ∃ value after, Evaluates program environment expression value after ∧ ValueHasType program value type ∧
      EnvironmentTyped program after context ∧
      ∀ other otherAfter, Evaluates program environment expression other otherAfter → other = value ∧ otherAfter = after := by
  induction admitted using HasType.rec
    (motive_2 := fun home context expressions types _ =>
      ∀ environment, EnvironmentTyped program environment context →
        ∃ values after, EvaluatesMany program environment expressions values after ∧ ValuesHaveTypes program values types ∧
          EnvironmentTyped program after context ∧
          ∀ other otherAfter, EvaluatesMany program environment expressions other otherAfter → other = values ∧ otherAfter = after)
    (motive_3 := fun home context subject result previous arms _ =>
      ∀ environment, EnvironmentTyped program environment context →
      ∀ value, ValueHasType program value subject → ∀ bindings body,
        selectArm value arms = some (bindings, body) →
        ∃ resultValue after, Evaluates program (bindings ++ environment) body resultValue after ∧
          ValueHasType program resultValue result ∧ EnvironmentTyped program (after.drop bindings.length) context ∧
          ∀ other otherAfter, Evaluates program (bindings ++ environment) body other otherAfter → other = resultValue ∧ otherAfter = after)
    (motive_4 := fun home source _ => ∃ normalized, NormalizesPattern program source normalized ∧
      ∀ other, NormalizesPattern program source other → other = normalized)
    (motive_5 := fun home sources _ => ∃ normalized, NormalizesPatterns program sources normalized ∧
      ∀ other, NormalizesPatterns program sources other → other = normalized)
    (motive_6 := fun home sources _ => ∃ normalized, NormalizesArms program sources normalized ∧
      ∀ other, NormalizesArms program sources other → other = normalized)
    generalizing environment with
  | unit =>
    refine ⟨.unit, environment, .unit, .unit, environmentTyped, ?_⟩
    intro other otherAfter evaluated
    cases evaluated
    exact ⟨rfl, rfl⟩
  | integer fits =>
    refine ⟨_, environment, .integer fits, .integer fits, environmentTyped, ?_⟩
    intro other otherAfter evaluated
    cases evaluated
    exact ⟨rfl, rfl⟩
  | character valid =>
    refine ⟨_, environment, .character valid, .character valid, environmentTyped, ?_⟩
    intro other otherAfter evaluated
    cases evaluated
    exact ⟨rfl, rfl⟩
  | constant declared visible resolved structural initialized ih =>
    obtain ⟨value, after, evaluated, typed, afterTyped, unique⟩ := ih EnvironmentTyped.nil
    cases afterTyped
    refine ⟨value, environment, .constant declared evaluated, typed, environmentTyped, ?_⟩
    intro other otherAfter evaluation
    cases evaluation with
    | constant otherDeclared otherEval =>
      have same := Option.some.inj (otherDeclared.symm.trans declared)
      cases same
      exact ⟨(unique other [] otherEval).1, rfl⟩
  | @call home context identity arguments declaration declared visible distinct discard inputs body inputsIH bodyIH =>
    obtain ⟨values, middle, inputsEval, inputsTyped, middleTyped, inputsUnique⟩ := inputsIH environment environmentTyped
    have bindParameters : ∀ (parameters : List (String × BindingType)) (values : List Value),
        ValuesHaveTypes program values (parameters.map (fun parameter => parameter.2.type)) →
        EnvironmentTyped program (List.zip (parameters.map Prod.fst) values) parameters := by
      intro parameters
      induction parameters with
      | nil => intro values typed; cases typed; exact .nil
      | cons parameter parameters ih =>
        intro values typed
        cases typed with
        | cons headTyped tailTyped => exact .cons headTyped (ih _ tailTyped)
    obtain ⟨value, localAfter, bodyEval, valueTyped, _, bodyUnique⟩ :=
      bodyIH (bindParameters declaration.parameters values inputsTyped)
    refine ⟨value, middle, .call declared inputsEval bodyEval, valueTyped, middleTyped, ?_⟩
    intro other otherAfter evaluation
    cases evaluation with
    | call otherDeclared otherInputs otherBody =>
      have sameDeclaration := Option.some.inj (otherDeclared.symm.trans declared)
      cases sameDeclaration
      obtain ⟨rfl, rfl⟩ := inputsUnique _ _ otherInputs
      exact ⟨(bodyUnique _ _ otherBody).1, rfl⟩
  | applyPatterns argumentsTyped nonempty constants covered bodies argumentsIH constantsIH bodiesIH =>
    obtain ⟨normalized, normalization, normalizationUnique⟩ := constantsIH
    have coverage := covered normalized normalization
    obtain ⟨values, middle, argumentsEval, valuesTyped, middleTyped, argumentsUnique⟩ := argumentsIH environment environmentTyped
    have subjectTyped := valuesTyped.argument
    obtain ⟨bindings, body, selected⟩ := coverage.selectArm subjectTyped
    obtain ⟨value, after, bodyEval, valueTyped, afterTyped, unique⟩ :=
      bodiesIH normalized normalization middle middleTyped _ subjectTyped bindings body selected
    refine ⟨value, after.drop bindings.length, .applyPatterns normalization argumentsEval selected bodyEval, valueTyped, afterTyped, ?_⟩
    intro other otherAfter evaluation
    cases evaluation with
    | applyPatterns otherNormalization otherArguments otherSelected otherBody =>
      have sameNormalization := normalizationUnique _ otherNormalization
      subst sameNormalization
      obtain ⟨rfl, rfl⟩ := argumentsUnique _ _ otherArguments
      have sameSelection := Option.some.inj (otherSelected.symm.trans selected)
      cases sameSelection
      obtain ⟨rfl, rfl⟩ := unique _ _ otherBody
      exact ⟨rfl, rfl⟩
  | group typed ih =>
    obtain ⟨value, after, evaluated, valueTyped, afterTyped, unique⟩ := ih environmentTyped
    refine ⟨value, after, .group evaluated, valueTyped, afterTyped, ?_⟩
    intro other otherAfter evaluation
    cases evaluation with
    | group inner => exact unique _ _ inner
  | read selected path copyable =>
    obtain ⟨value, selectedValue, valueTyped⟩ := environmentTyped.readPlace selected path
    refine ⟨value, environment, .read selectedValue, valueTyped, environmentTyped, ?_⟩
    intro other otherAfter evaluated
    cases evaluated with
    | read found => exact ⟨Option.some.inj (found.symm.trans selectedValue), rfl⟩
  | sequence head drop tail headIH tailIH =>
    obtain ⟨discarded, middle, headEval, _, middleTyped, headUnique⟩ := headIH environmentTyped
    obtain ⟨value, after, tailEval, valueTyped, afterTyped, unique⟩ := tailIH middleTyped
    refine ⟨value, after, .sequence headEval tailEval, valueTyped, afterTyped, ?_⟩
    intro other otherAfter evaluated
    cases evaluated with
    | sequence otherHead otherTail =>
      obtain ⟨rfl, rfl⟩ := headUnique _ _ otherHead
      exact unique _ _ otherTail
  | bind initialized drop annotated continued initialIH bodyIH =>
    obtain ⟨resident, middle, initialEval, residentTyped, middleTyped, initialUnique⟩ := initialIH environmentTyped
    obtain ⟨value, after, bodyEval, valueTyped, afterTyped, bodyUnique⟩ := bodyIH (.cons residentTyped middleTyped)
    refine ⟨value, after.drop 1, .bind initialEval bodyEval, valueTyped, afterTyped.drop 1, ?_⟩
    intro other otherAfter evaluated
    cases evaluated with
    | bind otherInitial otherBody =>
      obtain ⟨rfl, rfl⟩ := initialUnique _ _ otherInitial
      obtain ⟨rfl, rfl⟩ := bodyUnique _ _ otherBody
      exact ⟨rfl, rfl⟩
  | assign selected writable path discard resident continued residentIH bodyIH =>
    obtain ⟨replacement, middle, evaluated, residentTyped, middleTyped, residentUnique⟩ := residentIH environmentTyped
    obtain ⟨updated, written, updatedTyped, _⟩ := middleTyped.writePlace selected path residentTyped
    obtain ⟨value, after, bodyEval, valueTyped, afterTyped, bodyUnique⟩ := bodyIH updatedTyped
    refine ⟨value, after, .assign evaluated written bodyEval, valueTyped, afterTyped, ?_⟩
    intro other otherAfter evaluation
    cases evaluation with
    | assign otherEval otherWritten otherBody =>
      obtain ⟨rfl, rfl⟩ := residentUnique _ _ otherEval
      have same := Option.some.inj (otherWritten.symm.trans written)
      cases same
      exact bodyUnique _ _ otherBody
  | tuple head tail headIH tailIH =>
    obtain ⟨first, middle, headEval, headTyped, middleTyped, headUnique⟩ := headIH environmentTyped
    obtain ⟨rest, after, tailEval, tailTyped, afterTyped, tailUnique⟩ := tailIH middle middleTyped
    refine ⟨.tuple first rest, after, .tuple headEval tailEval, .tuple headTyped tailTyped, afterTyped, ?_⟩
    intro other otherAfter evaluated
    cases evaluated with
    | tuple otherHead otherTail =>
      obtain ⟨rfl, rfl⟩ := headUnique _ _ otherHead
      obtain ⟨rfl, rfl⟩ := tailUnique _ _ otherTail
      exact ⟨rfl, rfl⟩
  | array residents elementValid size ih =>
    obtain ⟨values, after, evaluated, typed, afterTyped, unique⟩ := ih environment environmentTyped
    refine ⟨.array values, after, .array evaluated, .array typed elementValid size, afterTyped, ?_⟩
    intro other otherAfter evaluation
    cases evaluation with
    | array elements =>
      obtain ⟨rfl, rfl⟩ := unique _ _ elements
      exact ⟨rfl, rfl⟩
  | construct declared chosen finite copyable visible access residents ih =>
    obtain ⟨values, after, evaluated, typed, afterTyped, unique⟩ := ih environment environmentTyped
    refine ⟨_, after, .construct evaluated, .nominal declared chosen finite typed, afterTyped, ?_⟩
    intro other otherAfter evaluation
    cases evaluation with
    | construct otherFields =>
      obtain ⟨rfl, rfl⟩ := unique _ _ otherFields
      exact ⟨rfl, rfl⟩
  | @field home context body key parentType type source discard selected ih =>
    obtain ⟨parent, after, evaluated, parentTyped, afterTyped, unique⟩ := ih environmentTyped
    obtain ⟨index, value, indexed, found, valueTyped, _⟩ := selected.access parentTyped
    have selectedValue : parent.readField program key = some value := by simp [Value.readField, indexed, found]
    refine ⟨value, after, .field evaluated selectedValue, valueTyped, afterTyped, ?_⟩
    intro other otherAfter evaluation
    cases evaluation with
    | field otherSource otherSelected =>
      obtain ⟨rfl, rfl⟩ := unique _ _ otherSource
      exact ⟨Option.some.inj (otherSelected.symm.trans selectedValue), rfl⟩
  | nil =>
    rename_i environment environmentTyped
    refine ⟨[], environment, .nil, .nil, environmentTyped, ?_⟩
    intro other otherAfter evaluated
    cases evaluated
    exact ⟨rfl, rfl⟩
  | cons head tail headIH tailIH =>
    rename_i environment environmentTyped
    obtain ⟨first, middle, headEval, headTyped, middleTyped, headUnique⟩ := headIH environmentTyped
    obtain ⟨rest, after, tailEval, tailTyped, afterTyped, tailUnique⟩ := tailIH middle middleTyped
    refine ⟨first :: rest, after, .cons headEval tailEval, .cons headTyped tailTyped, afterTyped, ?_⟩
    intro other otherAfter evaluated
    cases evaluated with
    | cons otherHead otherTail =>
      obtain ⟨rfl, rfl⟩ := headUnique _ _ otherHead
      obtain ⟨rfl, rfl⟩ := tailUnique _ _ otherTail
      exact ⟨rfl, rfl⟩
  | empty =>
    rename_i environment environmentTyped value valueTyped bindings body selected
    simp [selectArm] at selected
  | clause patternTyped distinct useful bodyTyped tailTyped bodyIH tailIH =>
    rename_i environment environmentTyped value valueTyped bindings body selected
    simp only [selectArm] at selected
    split at selected
    next matched found =>
      have same := Option.some.inj selected
      cases same
      have bindingsTyped := patternTyped.bindings valueTyped found
      obtain ⟨result, after, evaluated, resultTyped, afterTyped, unique⟩ :=
        bodyIH (EnvironmentTyped.append bindingsTyped environmentTyped)
      refine ⟨result, after, evaluated, resultTyped, ?_, unique⟩
      simpa [bindingsTyped.length] using afterTyped.drop bindings.length
    next missed => exact tailIH environment environmentTyped value valueTyped bindings body selected

  | patternWildcard =>
    refine ⟨.wildcard, .wildcard, ?_⟩
    intro other normalized
    cases normalized
    rfl
  | patternBinder name =>
    refine ⟨.binder name, .binder name, ?_⟩
    intro other normalized
    cases normalized
    rfl
  | patternNode constants ih =>
    obtain ⟨fields, normalized, unique⟩ := ih
    refine ⟨.node _ fields, .node normalized, ?_⟩
    intro other alternative
    cases alternative with
    | node otherFields =>
      have same := unique _ otherFields
      subst same
      rfl
  | @patternConstant home name type typed ih =>
    have resolvesUnique : ∀ {source : TypeExpr} {first : Ty}, ResolvesType program.aliases source first →
        ∀ {second : Ty}, ResolvesType program.aliases source second → second = first := by
      intro source first resolved second alternative
      induction resolved using ResolvesType.rec
        (motive_2 := fun sources types _ => ∀ others, ResolvesTypes program.aliases sources others → others = types)
        generalizing second with
      | concrete type => cases alternative; rfl
      | alias declared expanded ih =>
        cases alternative with
        | alias otherDeclared otherExpanded =>
          have same := Option.some.inj (otherDeclared.symm.trans declared)
          cases same
          exact ih otherExpanded
      | tuple first rest firstIH restIH =>
        cases alternative with
        | tuple otherFirst otherRest =>
          have sameFirst := firstIH otherFirst
          have sameRest := restIH _ otherRest
          subst sameFirst
          subst sameRest
          rfl
      | array length resolved ih =>
        cases alternative with
        | array otherLength otherResolved =>
          have same := ih otherResolved
          subst same
          rfl
      | nil =>
        rename_i others alternative
        cases alternative
        rfl
      | cons first rest firstIH restIH =>
        rename_i others alternative
        cases alternative with
        | cons otherFirst otherRest =>
          have sameFirst := firstIH otherFirst
          have sameRest := restIH _ otherRest
          subst sameFirst
          subst sameRest
          rfl
    obtain ⟨value, after, evaluated, valueTyped, afterTyped, unique⟩ := ih EnvironmentTyped.nil
    cases afterTyped
    cases typed with
    | constant declared visible resolved structural initialized =>
      refine ⟨.literal (some type) value, .constant declared resolved evaluated, ?_⟩
      intro other normalized
      cases normalized with
      | constant otherDeclared otherResolved otherEvaluated =>
        have sameDeclaration := Option.some.inj (otherDeclared.symm.trans declared)
        cases sameDeclaration
        have sameType := resolvesUnique resolved otherResolved
        have sameValue := (unique _ _ otherEvaluated).1
        subst sameType
        subst sameValue
        rfl
  | patternsEmpty =>
    refine ⟨[], .nil, ?_⟩
    intro other normalized
    cases normalized
    rfl
  | patternsCons head tail headIH tailIH =>
    obtain ⟨first, firstNormalized, firstUnique⟩ := headIH
    obtain ⟨rest, restNormalized, restUnique⟩ := tailIH
    refine ⟨first :: rest, .cons firstNormalized restNormalized, ?_⟩
    intro other normalized
    cases normalized with
    | cons otherHead otherTail =>
      have sameHead := firstUnique _ otherHead
      have sameTail := restUnique _ otherTail
      subst sameHead
      subst sameTail
      rfl
  | armsEmpty =>
    refine ⟨[], .nil, ?_⟩
    intro other normalized
    cases normalized
    rfl
  | armsCons head tail headIH tailIH =>
    obtain ⟨first, firstNormalized, firstUnique⟩ := headIH
    obtain ⟨rest, restNormalized, restUnique⟩ := tailIH
    refine ⟨(_, _) :: rest, .cons firstNormalized restNormalized, ?_⟩
    intro other normalized
    cases normalized with
    | cons otherHead otherTail =>
      have sameHead := firstUnique _ otherHead
      have sameTail := restUnique _ otherTail
      subst sameHead
      subst sameTail
      rfl

/-- Empty source environments are realized, not assumed. -/
theorem closed_correctness {expression : Expr} {type : Ty}
    (admitted : HasType program home [] expression type) :
    ∃ value, Evaluates program [] expression value [] ∧ ValueHasType program value type ∧
      ∀ other after, Evaluates program [] expression other after → other = value ∧ after = [] := by
  obtain ⟨value, after, evaluated, typed, afterTyped, unique⟩ := correctness admitted .nil
  cases afterTyped
  exact ⟨value, evaluated, typed, unique⟩

/-- Exact admission boundary, in every lexical context and at every width. -/
theorem integer_admission (context : List (String × BindingType)) (type : IntegerType) (magnitude : Nat) :
    (∃ result, HasType program home context (.integer type magnitude) result) ↔ type.Contains program.target magnitude := by
  constructor
  · rintro ⟨_, admitted⟩
    cases admitted with
    | integer fits => exact fits
  · intro fits
    exact ⟨_, .integer fits⟩

theorem character_admission (context : List (String × BindingType)) (number : Nat) :
    (∃ result, HasType program home context (.character number) result) ↔ UnicodeScalar number := by
  constructor
  · rintro ⟨_, admitted⟩
    cases admitted with
    | character valid => exact valid
  · intro valid
    exact ⟨_, .character valid⟩

/-- The original unit subset retains precisely its admission and evaluation meaning. -/
theorem unit_agreement : HasType program home [] .unit .unit ∧
    ∀ value, Evaluates program [] .unit value [] ↔ value = .unit := by
  obtain ⟨value, evaluated, _, unique⟩ := closed_correctness (program := program) (home := home) HasType.unit
  have same : value = .unit := by cases evaluated; rfl
  refine ⟨.unit, fun other => ⟨?_, ?_⟩⟩
  · intro evaluation
    exact (unique other [] evaluation).1.trans same
  · intro equal
    subst other
    exact .unit

end Grounded
