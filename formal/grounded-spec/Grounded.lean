/-!
Target-indexed expressions, immutable composition, structural and nominal data.
Normative basis: §§2.2–2.3, 3.2–3.4, 4.1–4.4, 5.1–5.3, 6.1–6.3, 7.2–7.7 and 13.1.
Declarations, field types, identities and lexical names are already decoded.
Constructors consume argument expressions in their recorded order. Literal
magnitudes and Unicode numbers are decoded; source elaboration is not proved.
Direct named calls and immediate pattern-callable application share correctness.
Finite-inline nominal owners have checked structural use bounds and manual
restrictions. Actual zero-use boundaries construct ordered logical destruction.
Affine arm joins retain branch residents under conservative initialization.
Custom hooks, physical storage release, representation and exhaustion remain open.
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
  | vacant
  | unit
  | integer (type : IntegerType) (number : Int)
  | character (number : Nat)
  | tuple | array
  | nominal (identity : Nat) (tag : Option Nat)
  deriving DecidableEq

inductive Value where
  | vacant
  | unit
  | integer (type : IntegerType) (number : Int)
  | character (number : Nat)
  | tuple (head : Value) (tail : List Value)
  | array (elements : List Value)
  | nominal (identity : Nat) (tag : Option Nat) (fields : List Value)

mutual
/-- A whole owned result contains no vacancy at any depth. -/
def Value.initialized : Value → Bool
  | .vacant => false
  | .tuple head tail => head.initialized && valuesInitialized tail
  | .array values | .nominal _ _ values => valuesInitialized values
  | _ => true
termination_by value => sizeOf value

def valuesInitialized : List Value → Bool
  | [] => true
  | value :: values => value.initialized && valuesInitialized values
termination_by values => sizeOf values
end

mutual
/-- Total structural equality for constant patterns, without user-defined Eq. -/
def Value.equal (left right : Value) : Bool :=
  match left, right with
  | .vacant, .vacant => true
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
    | vacant => intro right; cases right <;> simp [Value.equal]
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

inductive Initialization where
  | full
  | vacant
  /-- A correlation-losing affine join retains the actual resident or vacancy. -/
  | maybe
  | fields (entries : List (Nat × Initialization))

/-- Field access requires a definitely present ancestor, not a complete one. -/
@[simp] def Initialization.Present : Initialization → Prop
  | .full | .fields _ => True
  | .vacant | .maybe => False

def Initialization.child (state : Initialization) (index : Nat) : Initialization :=
  match state with
  | .full => .full
  | .vacant => .vacant
  | .maybe => .maybe
  | .fields entries => match entries.find? (fun entry => entry.1 == index) with
    | some entry => entry.2
    | none => .full

inductive Initialization.Complete : Initialization → Prop where
  | full : Complete .full
  | fields {entries : List (Nat × Initialization)}
      (complete : ∀ index, ((Initialization.fields entries).child index).Complete) : Complete (.fields entries)

theorem Initialization.Complete.child {state : Initialization} (complete : state.Complete) (index : Nat) :
    (state.child index).Complete := by
  cases complete with
  | full => exact .full
  | fields complete => exact complete index

def Initialization.setChild (state : Initialization) (index : Nat) (replacement : Initialization) : Initialization :=
  let entries := match state with | .fields entries => entries | _ => []
  .fields ((index, replacement) :: entries.filter (fun entry => entry.1 != index))

theorem Initialization.child_setChild {state : Initialization} (present : state.Present)
    (index : Nat) (replacement : Initialization) (other : Nat) :
    (state.setChild index replacement).child other = if other = index then replacement else state.child other := by
  cases state with
  | vacant | maybe => exact False.elim present
  | full =>
    by_cases same : other = index
    · subst other; simp only [setChild, child, List.find?_cons, show (index == index) = true from decide_eq_true rfl, ↓reduceIte]
    · simp only [setChild, child, List.filter_nil, List.find?_cons, show (index == other) = false from beq_eq_false_iff_ne.mpr (Ne.symm same), List.find?_nil, if_neg same]
  | fields entries =>
    by_cases same : other = index
    · subst other; simp only [setChild, child, List.find?_cons, show (index == index) = true from decide_eq_true rfl, ↓reduceIte]
    · simp only [setChild, child, List.find?_cons]
      simp only [show (index == other) = false from beq_eq_false_iff_ne.mpr (Ne.symm same)]
      rw [List.find?_filter]
      have predicates : (fun entry : Nat × Initialization => decide ((entry.1 != index) = true ∧ (entry.1 == other) = true)) = (fun entry => entry.1 == other) := by
        funext entry
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, bne_iff_ne, beq_iff_eq]
        exact ⟨And.right, fun equal => ⟨fun h => same (equal.symm.trans h), equal⟩⟩
      rw [predicates]
      simp only [if_neg same]

inductive Initialization.Access : Initialization → List Nat → Initialization → Prop where
  | here (state : Initialization) : Access state [] state
  | child {state selected : Initialization} {index : Nat} {indices : List Nat}
      (present : state.Present) (access : Access (state.child index) indices selected) : Access state (index :: indices) selected

/-- Unknown presence permits replacing the whole root, never descending into it. -/
theorem Initialization.Access.maybe_iff {indices : List Nat} {selected : Initialization} :
    Access .maybe indices selected ↔ indices = [] ∧ selected = .maybe := by
  constructor
  · intro access
    cases access with
    | here => exact ⟨rfl, rfl⟩
    | child present access => exact False.elim present
  · rintro ⟨rfl, rfl⟩
    exact .here .maybe

def Initialization.write (state : Initialization) (indices : List Nat) (replacement : Initialization) : Initialization :=
  match indices with
  | [] => replacement
  | index :: rest => state.setChild index ((state.child index).write rest replacement)

theorem Initialization.setChild_complete_iff {state next : Initialization} (present : state.Present) (index : Nat) :
    (state.setChild index next).Complete ↔ next.Complete ∧ ∀ other, other ≠ index → (state.child other).Complete := by
  constructor
  · intro complete
    exact ⟨by simpa only [child_setChild present, ↓reduceIte] using complete.child index,
      fun other different => by simpa only [child_setChild present, if_neg different] using complete.child other⟩
  · rintro ⟨nextComplete, remaining⟩
    apply Complete.fields
    intro other
    change ((state.setChild index next).child other).Complete
    rw [child_setChild present]
    split
    next => exact nextComplete
    next different => exact remaining other different

theorem Initialization.Complete.access {state selected : Initialization} {indices : List Nat}
    (complete : state.Complete) (access : state.Access indices selected) : selected.Complete := by
  induction access with
  | here => exact complete
  | child present access ih => exact ih (complete.child _)

theorem Initialization.Access.write {state selected : Initialization} {indices : List Nat}
    (access : state.Access indices selected) (next : Initialization) : (state.write indices next).Access indices next := by
  induction access with
  | here => exact .here next
  | child present access ih =>
    apply Access.child (by simp [Initialization.write, setChild])
    simpa only [Initialization.write, child_setChild present, ↓reduceIte] using ih

theorem Initialization.Access.clear_incomplete {state selected : Initialization} {indices : List Nat}
    (access : state.Access indices selected) : ¬ (state.write indices .vacant).Complete := by
  intro complete
  have impossible := complete.access (access.write .vacant)
  cases impossible

inductive CoordinatesApart : List Nat → List Nat → Prop where
  | siblings {left right : Nat} {xs ys : List Nat} (different : left ≠ right) : CoordinatesApart (left :: xs) (right :: ys)
  | descend {index : Nat} {xs ys : List Nat} (apart : CoordinatesApart xs ys) : CoordinatesApart (index :: xs) (index :: ys)

theorem Initialization.Access.write_frame {state selected retained : Initialization} {indices observed : List Nat}
    (access : state.Access indices selected) (kept : state.Access observed retained) (apart : CoordinatesApart indices observed)
    (next : Initialization) : (state.write indices next).Access observed retained := by
  induction apart generalizing state selected retained with
  | siblings different =>
    cases access with
    | child present access =>
      cases kept with
      | child keptPresent kept =>
        apply Access.child (by simp [Initialization.write, setChild])
        simpa only [Initialization.write, child_setChild present, if_neg (Ne.symm different)] using kept
  | descend apart ih =>
    cases access with
    | child present access =>
      cases kept with
      | child keptPresent kept =>
        apply Access.child (by simp [Initialization.write, setChild])
        simpa only [Initialization.write, child_setChild present, ↓reduceIte] using ih access kept

theorem Initialization.Access.restore_complete {state selected next : Initialization} {indices : List Nat}
    (access : state.Access indices selected) (first : Initialization) (restored : next.Complete) :
    state.Complete → ((state.write indices first).write indices next).Complete := by
  induction access with
  | here => intro _; exact restored
  | @child state selected index indices present access ih =>
    intro complete
    have outerPresent : (state.write (index :: indices) first).Present := by simp [Initialization.write, setChild]
    apply (setChild_complete_iff outerPresent index).mpr
    constructor
    · simpa only [Initialization.write, child_setChild present, ↓reduceIte] using ih (complete.child index)
    · intro other different
      simpa only [Initialization.write, child_setChild present, if_neg different] using complete.child other

structure BindingType where
  type : Ty
  mutable : Bool := false
  initialization : Initialization := .full

structure Place where
  root : String
  fields : List FieldKey := []

inductive Expr where
  | unit
  | integer (type : IntegerType) (magnitude : Nat)
  | character (number : Nat)
  | group (body : Expr)
  | read (place : Place)
  | move (place : Place)
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
inductive ProjectionType (program : Program) (home : Module) : Ty → FieldKey → Nat → Ty → Prop where
  | tuple {first type : Ty} {rest : List Ty} {index : Nat}
      (selected : (first :: rest)[index]? = some type) :
      ProjectionType program home (.tuple first rest) (.positional index) index type
  | nominal {identity index : Nat} {key : FieldKey} {declaration : DataDecl} {schema : Fields} {field : Field}
      (declared : program.data identity = some declaration)
      (structureOnly : declaration.shape = .structure schema)
      (indexed : schema.index key = some index) (selected : schema.residents[index]? = some field)
      (visible : field.visibility.Allows declaration.home home) :
      ProjectionType program home (.nominal identity) key index field.type

inductive PathType (program : Program) (home : Module) : Ty → List FieldKey → List Nat → Ty → Prop where
  | nil (type : Ty) : PathType program home type [] [] type
  | cons {source middle target : Ty} {key : FieldKey} {keys : List FieldKey} {index : Nat} {indices : List Nat}
      (head : ProjectionType program home source key index middle) (tail : PathType program home middle keys indices target) :
      PathType program home source (key :: keys) (index :: indices) target

/-- A requested interval must be contained in the owner's principal interval. -/
def Principal.Accepts : Principal → Principal → Prop
  | .duplicable, _ => True
  | .affine, .duplicable => False
  | .affine, _ => True
  | .exact, .exact => True
  | .exact, _ => False

/-- One producer checks structural capability and coherent manual restrictions.
The index is a requested bound, not an assertion of the principal class. -/
inductive UsePermission (data : DataDeclarations) : Ty → Principal → Prop where
  | unit {bound : Principal} : UsePermission data .unit bound
  | integer (type : IntegerType) {bound : Principal} : UsePermission data (.integer type) bound
  | character {bound : Principal} : UsePermission data .character bound
  | tuple {head : Ty} {tail : List Ty} {bound : Principal} (first : UsePermission data head bound)
      (rest : ∀ type ∈ tail, UsePermission data type bound) : UsePermission data (.tuple head tail) bound
  | array {element : Ty} {bound : Principal} (length : Nat) (resident : UsePermission data element bound) :
      UsePermission data (.array element length) bound
  | emptyArray (element : Ty) {bound : Principal} : UsePermission data (.array element 0) bound
  | inferred {identity : Nat} {declaration : DataDecl} {bound : Principal}
      (declared : data identity = some declaration) (unrestricted : declaration.restriction = none)
      (fields : ∀ schema ∈ declaration.schemas, ∀ field ∈ schema.residents, UsePermission data field.type bound) :
      UsePermission data (.nominal identity) bound
  | restricted {identity : Nat} {declaration : DataDecl} {principal bound : Principal}
      (declared : data identity = some declaration) (restriction : declaration.restriction = some principal)
      (fields : ∀ schema ∈ declaration.schemas, ∀ field ∈ schema.residents, UsePermission data field.type principal)
      (permitted : principal.Accepts bound) : UsePermission data (.nominal identity) bound

abbrev Duplicable (data : DataDeclarations) (type : Ty) := UsePermission data type .duplicable
abbrev MayDiscard (data : DataDeclarations) (type : Ty) := UsePermission data type .affine

/-- A branch may preserve its exact mask, or forget an affine slot's state.
No resident is destroyed and no runtime choice is supplied by this rule. -/
inductive Initialization.Joins (data : DataDeclarations) (type : Ty) : Initialization → Initialization → Prop where
  | same (state : Initialization) : Joins data type state state
  | affine {state : Initialization} (permission : MayDiscard data type) : Joins data type state .maybe

/-- Correlation-losing joins preserve lexical identity, type and mutability.
Positive-lower slots must retain their entire initialization mask. -/
inductive ContextJoins (program : Program) : List (String × BindingType) → List (String × BindingType) → Prop where
  | nil : ContextJoins program [] []
  | cons {name : String} {type : Ty} {mutable : Bool} {before after : Initialization}
      {context joined : List (String × BindingType)}
      (head : Initialization.Joins program.data type before after) (tail : ContextJoins program context joined) :
      ContextJoins program ((name, ⟨type, mutable, before⟩) :: context) ((name, ⟨type, mutable, after⟩) :: joined)

theorem Initialization.Joins.positive_lower {data : DataDeclarations} {type : Ty} {before after : Initialization}
    (joined : Joins data type before after) (positive : ¬ MayDiscard data type) : before = after := by
  cases joined with
  | same => rfl
  | affine permission => exact False.elim (positive permission)

def Initialization.Hole (program : Program) (state : Initialization) (type : Ty) : Prop :=
  ∃ home keys indices target, PathType program home type keys indices target ∧ state.Access indices .vacant

mutual
inductive StorageDisposition (program : Program) : Initialization → Ty → Prop where
  | vacant {type : Ty} : StorageDisposition program .vacant type
  | whole {state : Initialization} {type : Ty} (permission : MayDiscard program.data type) : StorageDisposition program state type
  | tuple {state : Initialization} {first : Ty} {rest : List Ty}
      (hole : state.Hole program (.tuple first rest)) (fields : StorageDispositions program state.child (first :: rest)) :
      StorageDisposition program state (.tuple first rest)
  | nominal {state : Initialization} {identity : Nat} {declaration : DataDecl} {schema : Fields}
      (declared : program.data identity = some declaration) (structureOnly : declaration.shape = .structure schema)
      (hole : state.Hole program (.nominal identity))
      (fields : StorageDispositions program state.child (schema.residents.map Field.type)) :
      StorageDisposition program state (.nominal identity)
inductive StorageDispositions (program : Program) : (Nat → Initialization) → List Ty → Prop where
  | nil {states : Nat → Initialization} : StorageDispositions program states []
  | cons {states : Nat → Initialization} {first : Ty} {rest : List Ty}
      (head : StorageDisposition program (states 0) first)
      (tail : StorageDispositions program (fun index => states (index + 1)) rest) : StorageDispositions program states (first :: rest)
end

def BindingType.Disposable (program : Program) (slot : BindingType) : Prop :=
  StorageDisposition program slot.initialization slot.type

/-- Nearest lexical binding wins, including in shadowing initializers. -/
def lookup {α : Type} (name : String) : List (String × α) → Option α
  | [] => none
  | (key, value) :: rest => if name = key then some value else lookup name rest

mutual
inductive ResidentTyped (program : Program) : Initialization → Value → Ty → Prop where
  | vacant {type : Ty} : ResidentTyped program .vacant .vacant type
  /-- Static uncertainty never replaces, drops or fabricates a branch resident. -/
  | uncertain {state : Initialization} {value : Value} {type : Ty}
      (actual : ResidentTyped program state value type) (permission : MayDiscard program.data type) :
      ResidentTyped program .maybe value type
  | unit : ResidentTyped program .full .unit .unit
  | integer {type : IntegerType} {number : Int} (fits : type.Contains program.target number) :
      ResidentTyped program .full (.integer type number) (.integer type)
  | character {number : Nat} (valid : UnicodeScalar number) : ResidentTyped program .full (.character number) .character
  | tuple {state : Initialization} {head : Value} {tail : List Value} {first : Ty} {rest : List Ty}
      (headTyped : ResidentTyped program (state.child 0) head first)
      (tailTyped : ResidentsTyped program (fun index => state.child (index + 1)) tail rest)
      (present : state.Present := by trivial) :
      ResidentTyped program state (.tuple head tail) (.tuple first rest)
  | array {state : Initialization} {values : List Value} {element : Ty} {length : Nat}
      (residents : ResidentsTyped program state.child values (List.replicate length element))
      (elementValid : FiniteLayout program.target program.data element)
      (size : length < 2 ^ program.target.pointerBits)
      (present : state.Present := by trivial) :
      ResidentTyped program state (.array values) (.array element length)
  | nominal {state : Initialization} {identity : Nat} {tag : Option Nat} {declaration : DataDecl} {schema : Fields}
      {values : List Value} (declared : program.data identity = some declaration)
      (chosen : declaration.constructor tag = some schema)
      (finite : FiniteLayout program.target program.data (.nominal identity))
      (residents : ResidentsTyped program state.child values (schema.residents.map Field.type))
      (present : state.Present := by trivial) :
      ResidentTyped program state (.nominal identity tag values) (.nominal identity)
inductive ResidentsTyped (program : Program) : (Nat → Initialization) → List Value → List Ty → Prop where
  | nil {states : Nat → Initialization} : ResidentsTyped program states [] []
  | cons {states : Nat → Initialization} {head : Value} {tail : List Value} {first : Ty} {rest : List Ty}
      (headTyped : ResidentTyped program (states 0) head first)
      (tailTyped : ResidentsTyped program (fun index => states (index + 1)) tail rest) :
      ResidentsTyped program states (head :: tail) (first :: rest)
end

abbrev ValueHasType (program : Program) (value : Value) (type : Ty) := ResidentTyped program .full value type
abbrev ValuesHaveTypes (program : Program) (values : List Value) (types : List Ty) :=
  ResidentsTyped program (fun _ => .full) values types

theorem ResidentTyped.complete {program : Program} {state : Initialization} {value : Value} {type : Ty}
    (typed : ResidentTyped program state value type) (complete : state.Complete) :
    ValueHasType program value type ∧ value.initialized = true := by
  induction typed using ResidentTyped.rec
    (motive_2 := fun states values types _ => (∀ index, (states index).Complete) →
      ValuesHaveTypes program values types ∧ valuesInitialized values = true) with
  | vacant => cases complete
  | uncertain actual permission ih => cases complete
  | unit => exact ⟨.unit, by simp [Value.initialized]⟩
  | integer fits => exact ⟨.integer fits, by simp [Value.initialized]⟩
  | character valid => exact ⟨.character valid, by simp [Value.initialized]⟩
  | tuple head tail present headIH tailIH =>
    obtain ⟨headTyped, headLive⟩ := headIH (complete.child 0)
    obtain ⟨tailTyped, tailLive⟩ := tailIH (fun index => complete.child (index + 1))
    exact ⟨.tuple headTyped tailTyped, by simp [Value.initialized, headLive, tailLive]⟩
  | array residents elementValid size present ih =>
    obtain ⟨typed, live⟩ := ih complete.child
    exact ⟨.array typed elementValid size, by simpa [Value.initialized] using live⟩
  | nominal declared chosen finite residents present ih =>
    obtain ⟨typed, live⟩ := ih complete.child
    exact ⟨.nominal declared chosen finite typed, by simpa [Value.initialized] using live⟩
  | nil => exact ⟨.nil, by simp [valuesInitialized]⟩
  | cons head tail headIH tailIH =>
    rename_i complete
    obtain ⟨headTyped, headLive⟩ := headIH (complete 0)
    obtain ⟨tailTyped, tailLive⟩ := tailIH (fun index => complete (index + 1))
    exact ⟨.cons headTyped tailTyped, by simp [valuesInitialized, headLive, tailLive]⟩

abbrev Environment := List (String × Value)

/-- Vacancies are storage, never well-typed owned results. -/
abbrev SlotTyped (program : Program) (resident : Value) (slot : BindingType) :=
  ResidentTyped program slot.initialization resident slot.type

inductive EnvironmentTyped (program : Program) : Environment → List (String × BindingType) → Prop where
  | nil : EnvironmentTyped program [] []
  | cons {name : String} {value : Value} {type : BindingType}
      {environment : Environment} {context : List (String × BindingType)}
      (resident : SlotTyped program value type) (rest : EnvironmentTyped program environment context) :
      EnvironmentTyped program ((name, value) :: environment) ((name, type) :: context)

/-- Join soundness keeps the actual branch resident unchanged. -/
theorem ResidentTyped.join {state joined : Initialization} {value : Value} {type : Ty}
    (typed : ResidentTyped program state value type) (join : Initialization.Joins program.data type state joined) :
    ResidentTyped program joined value type := by
  cases join with
  | same => exact typed
  | affine permission => exact .uncertain typed permission

/-- A common static post-context accepts each actual branch environment verbatim. -/
theorem EnvironmentTyped.join {environment : Environment} {context joined : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) (join : ContextJoins program context joined) :
    EnvironmentTyped program environment joined := by
  induction join generalizing environment with
  | nil => cases typed; exact .nil
  | cons head tail ih =>
    cases typed with
    | cons resident rest => exact .cons (ResidentTyped.join resident head) (ih rest)

theorem Principal.Accepts.trans {first middle last : Principal} (front : first.Accepts middle) (back : middle.Accepts last) : first.Accepts last := by
  cases first <;> cases middle <;> cases last <;> simp_all [Principal.Accepts]

theorem UsePermission.weaken {data : DataDeclarations} {type : Ty} {bound requested : Principal}
    (permission : UsePermission data type bound) (accepted : bound.Accepts requested) : UsePermission data type requested := by
  induction permission with
  | unit => exact .unit
  | integer type => exact .integer type
  | character => exact .character
  | tuple first rest firstIH restIH => exact .tuple (firstIH accepted) (fun type included => restIH type included accepted)
  | array length resident ih => exact .array length (ih accepted)
  | emptyArray element => exact .emptyArray element
  | inferred declared unrestricted fields ih => exact .inferred declared unrestricted (fun schema included field member => ih schema included field member accepted)
  | restricted declared restriction fields permitted ih => exact .restricted declared restriction fields (permitted.trans accepted)

theorem UsePermission.nominal_restriction {data : DataDeclarations} {identity : Nat} {declaration : DataDecl} {principal bound : Principal}
    (permission : UsePermission data (.nominal identity) bound) (declared : data identity = some declaration)
    (restriction : declaration.restriction = some principal) : principal.Accepts bound := by
  cases permission with
  | inferred found unrestricted fields =>
    have same := Option.some.inj (found.symm.trans declared)
    cases same
    simp [restriction] at unrestricted
  | restricted found chosen fields permitted =>
    have same := Option.some.inj (found.symm.trans declared)
    cases same
    have samePrincipal := Option.some.inj (chosen.symm.trans restriction)
    cases samePrincipal
    exact permitted

theorem ResidentTyped.vacant_value {program : Program} {value : Value} {type : Ty}
    (typed : ResidentTyped program .vacant value type) : value = .vacant := by
  cases typed <;> simp_all

inductive Value.Disposable (program : Program) : Value → Prop where
  | vacant : Value.Disposable program .vacant
  | owned {state : Initialization} {value : Value} {type : Ty}
      (typed : ResidentTyped program state value type) (permission : MayDiscard program.data type) : Value.Disposable program value
  | tuple {head : Value} {tail : List Value} (incomplete : (Value.tuple head tail).initialized = false)
      (first : Value.Disposable program head) (rest : ∀ value ∈ tail, Value.Disposable program value) :
      Value.Disposable program (.tuple head tail)
  | nominal {identity : Nat} {declaration : DataDecl} {schema : Fields} {values : List Value}
      (declared : program.data identity = some declaration) (structureOnly : declaration.shape = .structure schema)
      (incomplete : (Value.nominal identity none values).initialized = false)
      (fields : ∀ value ∈ values, Value.Disposable program value) : Value.Disposable program (.nominal identity none values)

theorem ResidentTyped.disposable {state : Initialization} {value : Value} {type : Ty}
    (typed : ResidentTyped program state value type) (allowed : MayDiscard program.data type) : value.Disposable program :=
  .owned typed allowed

theorem EnvironmentTyped.take {environment : Environment} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) (count : Nat) :
    EnvironmentTyped program (environment.take count) (context.take count) := by
  induction count generalizing environment context with
  | zero => exact .nil
  | succ count ih =>
    cases typed with
    | nil => exact .nil
    | cons head tail => exact .cons head (ih tail)



def Value.head : Value → Head
  | .vacant => .vacant
  | .unit => .unit
  | .integer type number => .integer type number
  | .character number => .character number
  | .tuple _ _ => .tuple
  | .array _ => .array
  | .nominal identity tag _ => .nominal identity tag

/-- Children remain in declaration order. -/
def Value.children : Value → List Value
  | .tuple head tail => head :: tail
  | .array values | .nominal _ _ values => values
  | _ => []

mutual
/-- Logical finish events use relative field paths, never physical addresses. -/
def Value.destructionTrace : Value → List (List Nat)
  | .vacant => []
  | .unit | .integer _ _ | .character _ => [[]]
  | .tuple head tail => destructionFields 0 (head :: tail) ++ [[]]
  | .array values | .nominal _ _ values => destructionFields 0 values ++ [[]]
def destructionFields (index : Nat) : List Value → List (List Nat)
  | [] => []
  | value :: values => destructionFields (index + 1) values ++ value.destructionTrace.map (index :: ·)
end

mutual
/-- Finite no-hook logical destruction: vacant slots are skipped, children
execute right to left, and only then does the enclosing resident finish. -/
inductive Value.Destroys (program : Program) : Value → List (List Nat) → Value → Prop where
  | vacant : Value.Destroys program .vacant [] .vacant
  | resident {value : Value} {trace : List (List Nat)}
      (present : value ≠ .vacant) (allowed : value.Disposable program)
      (children : DestroysFields program 0 value.children trace) :
      Value.Destroys program value (trace ++ [[]]) .vacant
inductive DestroysFields (program : Program) : Nat → List Value → List (List Nat) → Prop where
  | nil (index : Nat) : DestroysFields program index [] []
  | cons {index : Nat} {value : Value} {values : List Value} {first rest : List (List Nat)}
      (tail : DestroysFields program (index + 1) values rest)
      (head : value.Destroys program first .vacant) :
      DestroysFields program index (value :: values) (rest ++ first.map (index :: ·))
end

theorem Value.Destroys.result_order {value after : Value} {trace : List (List Nat)}
    (executed : value.Destroys program trace after) :
    after = .vacant ∧ trace = value.destructionTrace := by
  induction executed using Value.Destroys.rec
    (motive_2 := fun index values trace _ => trace = destructionFields index values) with
  | vacant => simp [Value.destructionTrace]
  | @resident value trace present allowed children ih =>
    refine ⟨rfl, ?_⟩
    rw [ih]
    cases value <;> simp_all [destructionTrace, Value.children, destructionFields]
  | nil => simp [destructionFields]
  | cons tail head tailIH headIH => simp [destructionFields, tailIH, headIH.2]

theorem ResidentTyped.children_disposable {state : Initialization} {value : Value} {type : Ty}
    (typed : ResidentTyped program state value type) (allowed : MayDiscard program.data type) :
    ∀ child ∈ value.children, child.Disposable program := by
  have residents : ∀ {states : Nat → Initialization} {values : List Value} {types : List Ty},
      ResidentsTyped program states values types → (∀ type ∈ types, MayDiscard program.data type) →
      ∀ value ∈ values, value.Disposable program := by
    intro states values
    induction values generalizing states with
    | nil => intro types typed permissions value member; cases member
    | cons head tail ih =>
      intro types typed permissions value member
      cases typed with
      | cons first rest =>
        rcases List.mem_cons.mp member with rfl | member
        · exact .owned first (permissions _ (by simp))
        · exact ih rest (fun type member => permissions type (List.mem_cons_of_mem _ member)) value member
  induction typed using ResidentTyped.rec (motive_2 := fun _ _ _ _ => True) with
  | uncertain actual permission ih => exact ih allowed
  | vacant | unit | integer | character => simp [Value.children]
  | tuple head tail present headIH tailIH =>
    cases allowed with
    | tuple first rest => exact residents (.cons head tail) (by simpa using And.intro first rest)
  | array typed finite size present ih =>
    cases allowed with
    | array length resident => exact residents typed (by intro type member; have same := List.eq_of_mem_replicate member; subst type; exact resident)
    | emptyArray element => cases typed; simp [Value.children]
  | @nominal state identity tag declaration schema values declared chosen finite typed present ih =>
    have member : schema ∈ declaration.schemas := by
      cases declaration with
      | mk home visibility shape restriction =>
        cases shape <;> cases tag <;> simp_all [DataDecl.constructor, DataDecl.schemas]
        exact List.mem_of_getElem? chosen
    have fields : ∀ field ∈ schema.residents, MayDiscard program.data field.type := by
      cases allowed with
      | inferred found unrestricted fields =>
        cases Option.some.inj (found.symm.trans declared)
        exact fields schema member
      | restricted found restriction fields permitted =>
        cases Option.some.inj (found.symm.trans declared)
        exact fun field included => (fields schema member field included).weaken permitted
    exact residents typed (by simpa using fields)
  | nil => trivial
  | cons head tail headIH tailIH => trivial

theorem Value.Disposable.children {value : Value} (allowed : value.Disposable program) :
    ∀ child ∈ value.children, child.Disposable program := by
  cases allowed with
  | vacant => simp [Value.children]
  | owned typed permission => exact typed.children_disposable permission
  | tuple incomplete first rest => simpa [Value.children] using And.intro first rest
  | nominal declared structureOnly incomplete fields => exact fields

/-- Runtime permission constructs execution rather than assuming its success. -/
theorem Value.Disposable.destroys {value : Value} (allowed : value.Disposable program) :
    value.Destroys program value.destructionTrace .vacant := by
  induction value using Value.rec
    (motive_2 := fun values => (∀ child ∈ values, child.Disposable program) →
      ∀ index, DestroysFields program index values (destructionFields index values)) with
  | vacant => simpa only [Value.destructionTrace] using (Value.Destroys.vacant (program := program))
  | unit => simpa only [Value.destructionTrace, List.nil_append] using (Value.Destroys.resident (by simp) allowed (.nil 0))
  | integer type number => simpa only [Value.destructionTrace, List.nil_append] using (Value.Destroys.resident (by simp) allowed (.nil 0))
  | character number => simpa only [Value.destructionTrace, List.nil_append] using (Value.Destroys.resident (by simp) allowed (.nil 0))
  | tuple head tail headIH tailIH =>
    have permitted := allowed.children
    simp only [Value.children, List.mem_cons, forall_eq_or_imp] at permitted
    simpa only [Value.destructionTrace, destructionFields] using
      Value.Destroys.resident (by simp) allowed (.cons (tailIH permitted.2 1) (headIH permitted.1))
  | array values ih =>
    simpa only [Value.destructionTrace] using Value.Destroys.resident (by simp) allowed (ih allowed.children 0)
  | nominal identity tag values ih =>
    simpa only [Value.destructionTrace] using Value.Destroys.resident (by simp) allowed (ih allowed.children 0)
  | nil => rename_i permitted index; simpa only [destructionFields] using DestroysFields.nil (program := program) index
  | cons head tail headIH tailIH =>
    rename_i permitted index
    simpa only [destructionFields] using DestroysFields.cons
      (tailIH (fun v m => permitted v (List.mem_cons_of_mem _ m)) (index + 1))
      (headIH (permitted head (List.mem_cons_self ..)))

theorem destructionFields.lower_bound {index : Nat} {values : List Value} {path : List Nat}
    (member : path ∈ destructionFields index values) :
    ∃ field suffix, path = field :: suffix ∧ index ≤ field := by
  induction values generalizing index with
  | nil => simp [destructionFields] at member
  | cons value values ih =>
    simp only [destructionFields, List.mem_append] at member
    rcases member with tail | head
    · obtain ⟨field, suffix, rfl, bound⟩ := ih tail
      exact ⟨field, suffix, rfl, by omega⟩
    · obtain ⟨suffix, _, rfl⟩ := List.mem_map.mp head
      exact ⟨index, suffix, rfl, Nat.le_refl _⟩

/-- Relative field coordinates identify each active resident exactly once. -/
theorem Value.destructionTrace_nodup (value : Value) : value.destructionTrace.Nodup := by
  have finish : ∀ values, (destructionFields 0 values).Nodup → (destructionFields 0 values ++ [[]]).Nodup := by
    intro values unique
    refine List.nodup_append.mpr ⟨unique, by simp, ?_⟩
    intro path member other singleton same
    have empty : other = [] := by simpa using singleton
    obtain ⟨field, suffix, shape, _⟩ := destructionFields.lower_bound member
    simp [empty, same] at shape
  have prefixUnique : ∀ (index : Nat) (trace : List (List Nat)), trace.Nodup → (trace.map (index :: ·)).Nodup := by
    intro index trace unique
    simpa only [List.Nodup, List.pairwise_map, ne_eq, List.cons.injEq, true_and] using unique
  induction value using Value.rec
    (motive_2 := fun values => ∀ index, (destructionFields index values).Nodup) with
  | vacant | unit | integer | character => simp [Value.destructionTrace]
  | tuple head tail headIH tailIH =>
    simp only [Value.destructionTrace]
    apply finish
    simp only [destructionFields]
    refine List.nodup_append.mpr ⟨tailIH 1, prefixUnique 0 _ headIH, ?_⟩
    intro path member other mapped same
    obtain ⟨field, suffix, shape, bound⟩ := destructionFields.lower_bound member
    obtain ⟨rest, _, rfl⟩ := List.mem_map.mp mapped
    have equal := List.cons.inj (shape.symm.trans same)
    omega
  | array values ih => simpa only [Value.destructionTrace] using finish values (ih 0)
  | nominal identity tag values ih => simpa only [Value.destructionTrace] using finish values (ih 0)
  | nil => rename_i index; simp [destructionFields]
  | cons head tail headIH tailIH =>
    rename_i index
    simp only [destructionFields]
    refine List.nodup_append.mpr ⟨tailIH (index + 1), prefixUnique index _ headIH, ?_⟩
    intro path member other mapped same
    obtain ⟨field, suffix, shape, bound⟩ := destructionFields.lower_bound member
    obtain ⟨rest, _, rfl⟩ := List.mem_map.mp mapped
    have equal := List.cons.inj (shape.symm.trans same)
    omega

theorem destructionFields.vacant_slot {values : List Value} {slot : Nat}
    (vacant : values[slot]? = some .vacant) (index : Nat) (suffix : List Nat) :
    (index + slot) :: suffix ∉ destructionFields index values := by
  induction values generalizing slot index with
  | nil => simp at vacant
  | cons value values ih =>
    cases slot with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at vacant
      subst value
      simp only [destructionFields, Value.destructionTrace, List.map_nil, List.append_nil, Nat.add_zero]
      intro member
      obtain ⟨field, rest, shape, bound⟩ := destructionFields.lower_bound member
      have same := (List.cons.inj shape).1
      omega
    | succ slot =>
      simp only [List.getElem?_cons_succ] at vacant
      simp only [destructionFields, List.mem_append, not_or]
      constructor
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih vacant (index + 1)
      · intro member
        obtain ⟨rest, _, equal⟩ := List.mem_map.mp member
        have same := (List.cons.inj equal).1
        omega

theorem Value.Destroys.exactly_once {value after : Value} {trace : List (List Nat)}
    (executed : value.Destroys program trace after) : trace.Nodup := by
  rw [executed.result_order.2]
  exact value.destructionTrace_nodup

theorem Value.Destroys.vacant_trace {trace : List (List Nat)} {after : Value}
    (executed : Value.Destroys program .vacant trace after) : trace = [] ∧ after = .vacant := by
  have result := executed.result_order
  simpa only [Value.destructionTrace] using And.intro result.2 result.1

theorem Value.Destroys.skips_vacant_field {value after : Value} {trace : List (List Nat)}
    (executed : value.Destroys program trace after) {index : Nat}
    (vacant : value.children[index]? = some .vacant) (suffix : List Nat) :
    index :: suffix ∉ trace := by
  rw [executed.result_order.2]
  have absent := destructionFields.vacant_slot vacant 0 suffix
  cases value <;> simp_all [Value.children, Value.destructionTrace]

def cleanupTrace : Nat → Environment → List (List Nat)
  | 0, _ | _, [] => []
  | count + 1, (_, value) :: rest =>
      value.destructionTrace.map (0 :: ·) ++
        (cleanupTrace count rest).map (fun path => match path with | [] => [] | i :: p => (i + 1) :: p)

/-- Scope owners are newest first; the suffix is never traversed. -/
inductive Cleans (program : Program) : Nat → Environment → List (List Nat) → Environment → Prop where
  | zero (environment : Environment) : Cleans program 0 environment [] environment
  | nil (count : Nat) : Cleans program count [] [] []
  | cons {count : Nat} {name : String} {value : Value} {before after : Environment}
      {first rest : List (List Nat)} (head : value.Destroys program first .vacant)
      (tail : Cleans program count before rest after) :
      Cleans program (count + 1) ((name, value) :: before)
        (first.map (0 :: ·) ++ rest.map (fun path => match path with | [] => [] | i :: p => (i + 1) :: p)) after

theorem Cleans.suffix {count : Nat} {before after : Environment} {trace : List (List Nat)}
    (executed : Cleans program count before trace after) : after = before.drop count := by
  induction executed with
  | zero => rfl
  | nil => simp
  | cons head tail ih => simpa using ih

/-- Every scope trace follows newest-owner order, independently of names or
shadowing; child traces still obey reverse field order. -/
theorem Cleans.order {count : Nat} {before after : Environment} {trace : List (List Nat)}
    (executed : Cleans program count before trace after) : trace = cleanupTrace count before := by
  induction executed with
  | zero => rfl
  | nil count => cases count <;> rfl
  | cons head tail ih => simp only [cleanupTrace, head.result_order.2, ih]

theorem Cleans.trace_scoped {count : Nat} {before after : Environment} {trace : List (List Nat)}
    (executed : Cleans program count before trace after) :
    ∀ path ∈ trace, ∃ index suffix, path = index :: suffix ∧ index < count ∧ index < before.length := by
  induction executed with
  | zero | nil => intro path member; cases member
  | @cons count name value before after first rest head tail ih =>
    intro path member
    simp only [List.mem_append, List.mem_map] at member
    rcases member with ⟨suffix, _, rfl⟩ | ⟨path, included, rfl⟩
    · exact ⟨0, suffix, rfl, Nat.zero_lt_succ _, by simp⟩
    · obtain ⟨index, suffix, rfl, within, bound⟩ := ih path included
      exact ⟨index + 1, suffix, rfl, Nat.succ_lt_succ within, by simpa using Nat.succ_lt_succ bound⟩

theorem Cleans.exactly_once {count : Nat} {before after : Environment} {trace : List (List Nat)}
    (executed : Cleans program count before trace after) : trace.Nodup := by
  induction executed with
  | zero | nil => exact List.Pairwise.nil
  | @cons count name value before after first rest head tail ih =>
    let shift : List Nat → List Nat := fun path => match path with | [] => [] | i :: p => (i + 1) :: p
    have injective : ∀ a b, shift a = shift b → a = b := by
      intro a b same
      cases a with
      | nil => cases b with
        | nil => rfl
        | cons b bs => cases same
      | cons a leftTail => cases b with
        | nil => cases same
        | cons b rightTail =>
          have parts := List.cons.inj same
          have equal := Nat.add_right_cancel parts.1
          cases equal
          cases parts.2
          rfl
    refine List.nodup_append.mpr ⟨?_, ?_, ?_⟩
    · simpa only [List.Nodup, List.pairwise_map, ne_eq, List.cons.injEq, true_and] using head.exactly_once
    · change (rest.map shift).Nodup
      simp only [List.Nodup, List.pairwise_map]
      exact ih.imp (fun {a b} different same => different (injective a b same))
    · intro a firstMember b restMember same
      obtain ⟨left, _, rfl⟩ := List.mem_map.mp firstMember
      obtain ⟨right, _, rfl⟩ := List.mem_map.mp restMember
      cases right with
      | nil => cases same
      | cons index suffix => exact Nat.noConfusion (List.cons.inj same).1


theorem Cleans.exists {environment : Environment} (count : Nat)
    (allowed : ∀ entry ∈ environment.take count, entry.2.Disposable program) :
    ∃ trace, Cleans program count environment trace (environment.drop count) := by
  induction count generalizing environment with
  | zero => exact ⟨[], .zero _⟩
  | succ count ih =>
    cases environment with
    | nil => exact ⟨[], .nil _⟩
    | cons entry rest =>
      obtain ⟨trace, tail⟩ := ih (environment := rest) (fun e member => allowed e (by simp [member]))
      exact ⟨_, .cons (allowed entry (by simp)).destroys tail⟩

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
  | wildcard {type : Ty} (discard : MayDiscard program.data type) : PatternType program home .wildcard type []
  | binder (name : String) {type : Ty} :
      PatternType program home (.binder name) type [(name, ⟨type, false, .full⟩)]
  | literal {type : Ty} {value : Value} (typed : ValueHasType program value type)
      (discard : MayDiscard program.data type) : PatternType program home (.literal (some type) value) type []
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

mutual
/-- Matching remains nondestructive. Only the selected pattern consumes its
subject: binders transfer their complete payload, wildcard/literal leaves run
ordered destruction, and deconstruction consumes its shell without copying. -/
inductive Pattern.Consumes (program : Program) : Pattern → Value → Environment → List (List Nat) → Prop where
  | wildcard {value : Value} {trace : List (List Nat)} (destroyed : value.Destroys program trace .vacant) :
      Pattern.Consumes program .wildcard value [] trace
  | binder (name : String) (value : Value) : Pattern.Consumes program (.binder name) value [(name, value)] []
  | literal {type : Option Ty} {value : Value} {trace : List (List Nat)} (destroyed : value.Destroys program trace .vacant) :
      Pattern.Consumes program (.literal type value) value [] trace
  | node {head : Head} {patterns : List Pattern} {value : Value} {bindings : Environment} {trace : List (List Nat)}
      (same : head = value.head) (fields : ConsumesPatterns program 0 patterns value.children bindings trace) :
      Pattern.Consumes program (.node head patterns) value bindings trace
inductive ConsumesPatterns (program : Program) : Nat → List Pattern → List Value → Environment → List (List Nat) → Prop where
  | nil (index : Nat) : ConsumesPatterns program index [] [] [] []
  | cons {index : Nat} {pattern : Pattern} {patterns : List Pattern} {value : Value} {values : List Value}
      {front back : Environment} {first rest : List (List Nat)}
      (tail : ConsumesPatterns program (index + 1) patterns values back rest)
      (head : Pattern.Consumes program pattern value front first) :
      ConsumesPatterns program index (pattern :: patterns) (value :: values) (front ++ back)
        (rest ++ first.map (index :: ·))
end

/-- A failed candidate performs no consumption; successful selection consumes
exactly the same first-match subject selected by the authoritative matcher. -/
inductive ConsumesArm (program : Program) (value : Value) : List (Pattern × Expr) → Environment → Expr → Prop where
  | hit {pattern : Pattern} {body : Expr} {rest : List (Pattern × Expr)} {bindings : Environment} {trace : List (List Nat)}
      (matched : pattern.matchValue value = some bindings) (consumed : Pattern.Consumes program pattern value bindings trace) :
      ConsumesArm program value ((pattern, body) :: rest) bindings body
  | miss {pattern : Pattern} {body result : Expr} {rest : List (Pattern × Expr)} {bindings : Environment}
      (missed : pattern.matchValue value = none) (selected : ConsumesArm program value rest bindings result) :
      ConsumesArm program value ((pattern, body) :: rest) bindings result

theorem Pattern.Consumes.binder_result {name : String} {value : Value} {bindings : Environment} {trace : List (List Nat)}
    (consumed : Pattern.Consumes program (.binder name) value bindings trace) :
    bindings = [(name, value)] ∧ trace = [] := by cases consumed; exact ⟨rfl, rfl⟩

theorem ConsumesArm.matches {value : Value} {arms : List (Pattern × Expr)} {bindings : Environment} {body : Expr}
    (consumed : ConsumesArm program value arms bindings body) : selectArm value arms = some (bindings, body) := by
  induction consumed with
  | hit matched consumed => simp [selectArm, matched]
  | miss missed selected ih => simp [selectArm, missed, ih]

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

def readPlace (program : Program) (place : Place) (environment : Environment) : Option Value := do
  let stored ← lookup place.root environment
  let value ← stored.readPath program place.fields
  if value.initialized then some value else none

def writePlace (program : Program) (place : Place) (replacement : Value) (environment : Environment) : Option Environment := do
  let stored ← lookup place.root environment
  let updated ← stored.writePath program place.fields replacement
  replaceBinding place.root updated environment

def takePlace (program : Program) (place : Place) (environment : Environment) : Option (Value × Environment) := do
  let value ← readPlace program place environment
  let after ← writePlace program place .vacant environment
  some (value, after)

mutual
inductive Evaluates (program : Program) : Environment → Expr → Value → Environment → Prop where
  | unit {environment : Environment} : Evaluates program environment .unit .unit environment
  | integer {environment : Environment} {type : IntegerType} {magnitude : Nat}
      (fits : type.Contains program.target magnitude) :
      Evaluates program environment (.integer type magnitude) (.integer type magnitude) environment
  | character {environment : Environment} {number : Nat} (valid : UnicodeScalar number) :
      Evaluates program environment (.character number) (.character number) environment
  | group {environment after : Environment} {body : Expr} {value : Value}
      (evaluated : Evaluates program environment body value after) :
      Evaluates program environment (.group body) value after
  | read {environment : Environment} {place : Place} {value : Value}
      (selected : readPlace program place environment = some value) :
      Evaluates program environment (.read place) value environment
  | move {environment after : Environment} {place : Place} {value : Value}
      (taken : takePlace program place environment = some (value, after)) :
      Evaluates program environment (.move place) value after
  | sequence {environment middle after : Environment} {first rest : Expr}
      {discarded value : Value} (head : Evaluates program environment first discarded middle)
      (dispose : ∃ trace, discarded.Destroys program trace .vacant)
      (tail : Evaluates program middle rest value after) :
      Evaluates program environment (.sequence first rest) value after
  | bind {environment middle after : Environment} {mutable : Bool} {name : String}
      {annotation : Option TypeExpr} {initial body : Expr} {resident value : Value}
      (initialized : Evaluates program environment initial resident middle)
      (continued : Evaluates program ((name, resident) :: middle) body value after)
      (cleanup : ∃ trace, Cleans program 1 after trace (after.drop 1)) :
      Evaluates program environment (.bind mutable name annotation initial body) value (after.drop 1)
  | assign {environment middle updated after : Environment} {place : Place}
      {expression rest : Expr} {resident value : Value}
      (evaluated : Evaluates program environment expression resident middle)
      (dispose : ∃ parent old, lookup place.root middle = some parent ∧ parent.readPath program place.fields = some old ∧ ∃ trace, old.Destroys program trace .vacant)
      (written : writePlace program place resident middle = some updated)
      (continued : Evaluates program updated rest value after) :
      Evaluates program environment (.assign place expression rest) value after
  | tuple {environment middle after : Environment} {head : Expr} {tail : List Expr}
      {first : Value} {rest : List Value} (headEval : Evaluates program environment head first middle)
      (tailEval : EvaluatesMany program middle tail rest after) :
      Evaluates program environment (.tuple head tail) (.tuple first rest) after
  | array {environment after : Environment} {elements : List Expr} {values : List Value}
      (residents : EvaluatesMany program environment elements values after) :
      Evaluates program environment (.array elements) (.array values) after
  | constant {environment : Environment} {name : String} {declaration : ConstantDecl}
      {value : Value} (declared : program.constants name = some declaration)
      (initialized : Evaluates program [] declaration.body value []) :
      Evaluates program environment (.constant name) value environment
  | construct {environment after : Environment} {identity : Nat} {tag : Option Nat}
      {fields : List Expr} {values : List Value} (residents : EvaluatesMany program environment fields values after) :
      Evaluates program environment (.construct identity tag fields) (.nominal identity tag values) after
  | field {environment after : Environment} {body : Expr} {key : FieldKey} {parent value residual : Value}
      (source : Evaluates program environment body parent after)
      (selected : parent.readField program key = some value)
      (extracted : parent.writePath program [key] .vacant = some residual)
      (dispose : ∃ trace, residual.Destroys program trace .vacant) :
      Evaluates program environment (.field body key) value after
  | call {environment middle localAfter : Environment} {identity : Nat} {arguments : List Expr}
      {declaration : FunctionDecl} {values : List Value} {value : Value}
      (declared : program.functions identity = some declaration)
      (inputs : EvaluatesMany program environment arguments values middle)
      (body : Evaluates program (List.zip (declaration.parameters.map Prod.fst) values).reverse declaration.body value localAfter)
      (cleanup : ∃ trace, Cleans program localAfter.length localAfter trace []) :
      Evaluates program environment (.call identity arguments) value middle
  | applyPatterns {environment middle after : Environment} {inputs : List Ty} {arguments : List Expr}
      {arms : List (PatternSource × Expr)} {normalized : List (Pattern × Expr)} {values : List Value}
      {bindings : List (String × Value)} {body : Expr} {value : Value}
      (normalization : NormalizesArms program arms normalized)
      (argumentsEval : EvaluatesMany program environment arguments values middle)
      (selected : ConsumesArm program (argumentValue values) normalized bindings body)
      (bodyEval : Evaluates program (bindings.reverse ++ middle) body value after)
      (cleanup : ∃ trace, Cleans program bindings.length after trace (after.drop bindings.length)) :
      Evaluates program environment (.applyPatterns inputs arguments arms) value (after.drop bindings.length)

inductive EvaluatesMany (program : Program) : Environment → List Expr → List Value → Environment → Prop where
  | nil {environment : Environment} : EvaluatesMany program environment [] [] environment
  | cons {environment middle after : Environment} {head : Expr} {tail : List Expr}
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
inductive HasType (program : Program) : Module → List (String × BindingType) → Expr → Ty → List (String × BindingType) → Prop where
  | unit {home : Module} {context : List (String × BindingType)} : HasType program home context .unit .unit context
  | integer {home : Module} {context : List (String × BindingType)} {type : IntegerType} {magnitude : Nat}
      (fits : type.Contains program.target magnitude) :
      HasType program home context (.integer type magnitude) (.integer type) context
  | character {home : Module} {context : List (String × BindingType)} {number : Nat} (valid : UnicodeScalar number) :
      HasType program home context (.character number) .character context
  | group {home : Module} {context after : List (String × BindingType)} {body : Expr} {type : Ty}
      (typed : HasType program home context body type after) : HasType program home context (.group body) type after
  | read {home : Module} {context : List (String × BindingType)} {place : Place} {slot : BindingType} {type : Ty} {indices : List Nat} {state : Initialization}
      (selected : lookup place.root context = some slot) (access : slot.initialization.Access indices state) (initialized : state.Complete)
      (path : PathType program home slot.type place.fields indices type) (copyable : Duplicable program.data type) :
      HasType program home context (.read place) type context
  | move {home : Module} {context after : List (String × BindingType)} {place : Place} {slot : BindingType}
      {type : Ty} {indices : List Nat} {state : Initialization}
      (selected : lookup place.root context = some slot) (access : slot.initialization.Access indices state) (initialized : state.Complete)
      (path : PathType program home slot.type place.fields indices type)
      (cleared : replaceBinding place.root { slot with initialization := slot.initialization.write indices .vacant } context = some after) :
      HasType program home context (.move place) type after
  | sequence {home : Module} {context middle after : List (String × BindingType)} {first rest : Expr} {discarded type : Ty}
      (head : HasType program home context first discarded middle) (drop : MayDiscard program.data discarded)
      (tail : HasType program home middle rest type after) : HasType program home context (.sequence first rest) type after
  | bind {home : Module} {context middle after : List (String × BindingType)} {mutable : Bool} {remaining : Initialization}
      {name : String} {annotation : Option TypeExpr} {initial body : Expr} {localType type : Ty}
      (initialized : HasType program home context initial localType middle)
      (drop : BindingType.Disposable program ⟨localType, mutable, remaining⟩) (annotated : Annotation program.aliases annotation localType)
      (continued : HasType program home ((name, ⟨localType, mutable, .full⟩) :: middle) body type
        ((name, ⟨localType, mutable, remaining⟩) :: after)) :
      HasType program home context (.bind mutable name annotation initial body) type after
  | tuple {home : Module} {context middle after : List (String × BindingType)} {head : Expr} {tail : List Expr}
      {first : Ty} {rest : List Ty} (headTyped : HasType program home context head first middle)
      (tailTyped : HasTypes program home middle tail rest after) :
      HasType program home context (.tuple head tail) (.tuple first rest) after
  | array {home : Module} {context after : List (String × BindingType)} {elements : List Expr} {element : Ty} {length : Nat}
      (residents : HasTypes program home context elements (List.replicate length element) after)
      (elementValid : FiniteLayout program.target program.data element) (size : length < 2 ^ program.target.pointerBits) :
      HasType program home context (.array elements) (.array element length) after
  | constant {home : Module} {context : List (String × BindingType)} {name : String}
      {declaration : ConstantDecl} {type : Ty} (declared : program.constants name = some declaration)
      (visible : declaration.visibility.Allows declaration.home home)
      (resolved : ResolvesType program.aliases declaration.type type) (structural : Structural declaration.body)
      (initialized : HasType program declaration.home [] declaration.body type []) :
      HasType program home context (.constant name) type context
  | construct {home : Module} {context after : List (String × BindingType)} {identity : Nat} {tag : Option Nat}
      {declaration : DataDecl} {schema : Fields} {fields : List Expr}
      (declared : program.data identity = some declaration) (chosen : declaration.constructor tag = some schema)
      (finite : FiniteLayout program.target program.data (.nominal identity))
      (capability : UsePermission program.data (.nominal identity) .exact) (visible : declaration.visibility.Allows declaration.home home)
      (access : ∀ field ∈ schema.residents, field.visibility.Allows declaration.home home)
      (residents : HasTypes program home context fields (schema.residents.map Field.type) after) :
      HasType program home context (.construct identity tag fields) (.nominal identity) after
  | field {home : Module} {context after : List (String × BindingType)} {body : Expr} {key : FieldKey}
      {parentType type : Ty} {index : Nat} (source : HasType program home context body parentType after)
      (discard : MayDiscard program.data parentType) (selected : ProjectionType program home parentType key index type) :
      HasType program home context (.field body key) type after
  | call {home : Module} {context after bodyAfter : List (String × BindingType)} {identity : Nat}
      {arguments : List Expr} {declaration : FunctionDecl} (declared : program.functions identity = some declaration)
      (visible : declaration.visibility.Allows declaration.home home) (distinct : (declaration.parameters.map Prod.fst).Nodup)
      (initialized : ∀ parameter ∈ declaration.parameters, parameter.2.initialization = .full)
      (discard : ∀ binding ∈ bodyAfter, binding.2.Disposable program)
      (inputs : HasTypes program home context arguments (declaration.parameters.map (fun parameter => parameter.2.type)) after)
      (body : HasType program declaration.home declaration.parameters.reverse declaration.body declaration.result bodyAfter) :
      HasType program home context (.call identity arguments) declaration.result after
  | assign {home : Module} {context middle updated after : List (String × BindingType)} {place : Place}
      {value rest : Expr} {slot : BindingType} {target result : Ty} {indices : List Nat} {state : Initialization}
      (resident : HasType program home context value target middle)
      (selected : lookup place.root middle = some slot) (writable : slot.mutable = true)
      (available : slot.initialization.Access indices state) (path : PathType program home slot.type place.fields indices target)
      (discard : StorageDisposition program state target)
      (written : replaceBinding place.root { slot with initialization := slot.initialization.write indices .full } middle = some updated)
      (continued : HasType program home updated rest result after) :
      HasType program home context (.assign place value rest) result after
  | applyPatterns {home : Module} {context middle after : List (String × BindingType)} {inputs : List Ty}
      {arguments : List Expr} {arms : List (PatternSource × Expr)} {result : Ty}
      (argumentsTyped : HasTypes program home context arguments inputs middle) (nonempty : arms ≠ [])
      (constants : ArmConstantsTyped program home arms)
      (covered : ∀ normalized, NormalizesArms program arms normalized →
        Covers program [argumentType inputs] (normalized.map (fun arm => [arm.1])))
      (bodies : ∀ normalized, NormalizesArms program arms normalized →
        ArmsType program home middle (argumentType inputs) result [] normalized after) :
      HasType program home context (.applyPatterns inputs arguments arms) result after

inductive HasTypes (program : Program) : Module → List (String × BindingType) → List Expr → List Ty → List (String × BindingType) → Prop where
  | nil {home : Module} {context : List (String × BindingType)} : HasTypes program home context [] [] context
  | cons {home : Module} {context middle after : List (String × BindingType)} {head : Expr} {tail : List Expr}
      {first : Ty} {rest : List Ty} (headTyped : HasType program home context head first middle)
      (tailTyped : HasTypes program home middle tail rest after) :
      HasTypes program home context (head :: tail) (first :: rest) after
inductive ArmsType (program : Program) :
    Module → List (String × BindingType) → Ty → Ty → List Pattern → List (Pattern × Expr) → List (String × BindingType) → Prop where
  | empty {home : Module} {context after : List (String × BindingType)} {subject result : Ty} {previous : List Pattern} :
      ArmsType program home context subject result previous [] after
  | clause {home : Module} {context branchAfter after : List (String × BindingType)} {subject result : Ty}
      {previous : List Pattern} {pattern : Pattern} {body : Expr} {rest : List (Pattern × Expr)}
      {bindings afterBindings : List (String × BindingType)} (patternTyped : PatternType program home pattern subject bindings)
      (distinct : (bindings.map Prod.fst).Nodup) (useful : Useful program subject previous pattern)
      (bodyTyped : HasType program home (bindings.reverse ++ context) body result (afterBindings ++ branchAfter))
      (joined : ContextJoins program branchAfter after)
      (lengths : afterBindings.length = bindings.length)
      (discard : ∀ binding ∈ afterBindings, binding.2.Disposable program)
      (tailTyped : ArmsType program home context subject result (previous ++ [pattern]) rest after) :
      ArmsType program home context subject result previous ((pattern, body) :: rest) after
/-- These source rules check constant initializers before pattern normalization.
No evaluated value or successful-normalization witness is supplied. -/
inductive PatternConstantsTyped (program : Program) : Module → PatternSource → Prop where
  | patternWildcard {home : Module} : PatternConstantsTyped program home .wildcard
  | patternBinder {home : Module} (name : String) : PatternConstantsTyped program home (.binder name)
  | patternNode {home : Module} {head : Head} {fields : List PatternSource}
      (constants : PatternsConstantsTyped program home fields) : PatternConstantsTyped program home (.node head fields)
  | patternConstant {home : Module} {name : String} {type : Ty}
      (typed : HasType program home [] (.constant name) type []) : PatternConstantsTyped program home (.constant name)
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



theorem Value.replaceChild_readback {value replacement updated : Value} {index : Nat}
    (written : value.replaceChild index replacement = some updated) :
    (∀ key, updated.fieldIndex program key = value.fieldIndex program key) ∧
      updated.children[index]? = some replacement := by
  cases value with
  | vacant | unit | integer | character | array => simp [Value.replaceChild] at written
  | tuple head tail =>
    cases index with
    | zero =>
      cases Option.some.inj written
      exact ⟨fun key => by cases key <;> rfl, rfl⟩
    | succ index =>
      obtain ⟨old, found, same⟩ := Option.map_eq_some_iff.mp written
      cases same
      obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
      exact ⟨fun key => by cases key <;> rfl, by simp [Value.children, bound]⟩
  | nominal identity tag fields =>
    obtain ⟨old, found, same⟩ := Option.map_eq_some_iff.mp written
    cases same
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
    exact ⟨fun key => by cases tag <;> cases key <;> rfl, by simp [Value.children, bound]⟩

theorem Value.writePath_readback {value replacement updated : Value} {keys : List FieldKey}
    (written : value.writePath program keys replacement = some updated) :
    updated.readPath program keys = some replacement := by
  induction keys generalizing value updated with
  | nil =>
    cases Option.some.inj written
    rfl
  | cons key keys ih =>
    simp only [Value.writePath, bind, Option.bind_eq_some_iff] at written
    obtain ⟨index, indexed, child, found, next, changed, replaced⟩ := written
    obtain ⟨indexSame, readback⟩ := Value.replaceChild_readback (program := program) replaced
    simp [Value.readPath, Value.readField, indexSame, indexed, readback, ih changed]

theorem replaceBinding_lookup {α : Type} {name : String} {value : α} {before after : List (String × α)}
    (replaced : replaceBinding name value before = some after) : lookup name after = some value := by
  induction before generalizing after with
  | nil => simp [replaceBinding] at replaced
  | cons entry rest ih =>
    obtain ⟨key, old⟩ := entry
    simp only [replaceBinding] at replaced
    split at replaced
    next same =>
      cases Option.some.inj replaced
      simp [lookup, same]
    next different =>
      obtain ⟨next, changed, same⟩ := Option.map_eq_some_iff.mp replaced
      cases same
      simp [lookup, Ne.symm different, ih changed]

theorem writePlace_readback {place : Place} {replacement : Value} {before after : Environment}
    (written : writePlace program place replacement before = some after) :
    ∃ parent, lookup place.root after = some parent ∧ parent.readPath program place.fields = some replacement := by
  simp only [writePlace, bind, Option.bind_eq_some_iff] at written
  obtain ⟨stored, found, updated, changed, replaced⟩ := written
  exact ⟨updated, replaceBinding_lookup replaced, Value.writePath_readback changed⟩

theorem takePlace_eq_some {place : Place} {before after : Environment} {value : Value} :
    takePlace program place before = some (value, after) ↔
      readPlace program place before = some value ∧ writePlace program place .vacant before = some after := by
  simp [takePlace, bind, Option.bind_eq_some_iff]

theorem takePlace_invalidates {place : Place} {before after : Environment} {value : Value}
    (taken : takePlace program place before = some (value, after)) :
    readPlace program place after = none := by
  obtain ⟨_, written⟩ := takePlace_eq_some.mp taken
  obtain ⟨parent, found, readback⟩ := writePlace_readback written
  simp [readPlace, found, readback, Value.initialized]

/-- Invalidation holds for the actual operation, including nested paths and
already partial surrounding aggregates, without a supplied post-state invariant. -/
theorem Evaluates.move_invalidates {place : Place} {before after : Environment} {value : Value}
    (evaluated : Evaluates program before (.move place) value after) :
    readPlace program place after = none := by
  cases evaluated with
  | move taken => exact takePlace_invalidates taken

/-- Owned projection transfers its child before cleanup. No event can target
that child's former slot or descendants, even when its type is not Copy. -/
theorem Evaluates.field_protects_result {before after : Environment} {body : Expr} {key : FieldKey} {value : Value}
    (evaluated : Evaluates program before (.field body key) value after) :
    ∃ (parent residual : Value) (index : Nat) (trace : List (List Nat)), Evaluates program before body parent after ∧
      parent.readField program key = some value ∧ parent.fieldIndex program key = some index ∧
      residual.children[index]? = some .vacant ∧ residual.Destroys program trace .vacant ∧
      ∀ suffix, index :: suffix ∉ trace := by
  cases evaluated with
  | @field _ _ _ _ parent _ residual source selected extracted dispose =>
    obtain ⟨trace, destroyed⟩ := dispose
    change (parent.fieldIndex program key).bind (fun index =>
      (parent.children[index]?).bind (fun _ => parent.replaceChild index .vacant)) = some residual at extracted
    simp only [Option.bind_eq_some_iff] at extracted
    obtain ⟨index, indexed, child, found, written⟩ := extracted
    have vacant := (Value.replaceChild_readback (program := program) written).2
    exact ⟨_, _, index, trace, source, selected, indexed, vacant, destroyed,
      fun suffix => destroyed.skips_vacant_field vacant suffix⟩

theorem Value.replaceChild_inverse {value resident replacement updated : Value} {index : Nat}
    (found : value.children[index]? = some resident)
    (written : value.replaceChild index replacement = some updated) :
    updated.replaceChild index resident = some value := by
  cases value with
  | vacant | unit | integer | character | array => simp [Value.replaceChild] at written
  | tuple head tail =>
    cases index with
    | zero =>
      simp only [Value.children, List.getElem?_cons_zero, Option.some.injEq] at found
      cases found
      cases Option.some.inj written
      rfl
    | succ index =>
      change tail[index]? = some resident at found
      have same : .tuple head (tail.set index replacement) = updated := by
        simpa [Value.replaceChild, found] using written
      cases same
      obtain ⟨bound, selected⟩ := List.getElem?_eq_some_iff.mp found
      rw [← selected]
      simp [Value.replaceChild, bound, List.set_set, List.set_getElem_self]
  | nominal identity tag fields =>
    change fields[index]? = some resident at found
    have same : .nominal identity tag (fields.set index replacement) = updated := by
      simpa [Value.replaceChild, found] using written
    cases same
    obtain ⟨bound, selected⟩ := List.getElem?_eq_some_iff.mp found
    rw [← selected]
    simp [Value.replaceChild, bound, List.set_set, List.set_getElem_self]

theorem Value.writePath_inverse {value resident replacement updated : Value} {keys : List FieldKey}
    (read : value.readPath program keys = some resident)
    (written : value.writePath program keys replacement = some updated) :
    updated.writePath program keys resident = some value := by
  induction keys generalizing value updated with
  | nil =>
    cases Option.some.inj read
    cases Option.some.inj written
    rfl
  | cons key keys ih =>
    simp only [Value.writePath, bind, Option.bind_eq_some_iff] at written
    obtain ⟨index, indexed, child, found, next, changed, replaced⟩ := written
    have childRead : child.readPath program keys = some resident := by
      simpa [Value.readPath, Value.readField, indexed, found] using read
    obtain ⟨indexSame, childAfter⟩ := Value.replaceChild_readback (program := program) replaced
    have parentRestored := Value.replaceChild_inverse found replaced
    simp [Value.writePath, indexSame, indexed, childAfter, ih childRead changed, parentRestored]

theorem replaceBinding_inverse {α : Type} {name : String} {resident replacement : α}
    {before after : List (String × α)} (found : lookup name before = some resident)
    (written : replaceBinding name replacement before = some after) :
    replaceBinding name resident after = some before := by
  induction before generalizing after with
  | nil => simp [lookup] at found
  | cons entry rest ih =>
    obtain ⟨key, old⟩ := entry
    simp only [replaceBinding] at written
    split at written
    next same =>
      subst key
      simp [lookup] at found
      cases found
      cases Option.some.inj written
      simp [replaceBinding]
    next different =>
      have foundRest : lookup name rest = some resident := by
        simpa [lookup, Ne.symm different] using found
      obtain ⟨next, changed, same⟩ := Option.map_eq_some_iff.mp written
      cases same
      simp [replaceBinding, different, ih foundRest changed]

theorem writePlace_inverse {place : Place} {resident replacement : Value} {before after : Environment}
    (read : readPlace program place before = some resident)
    (written : writePlace program place replacement before = some after) :
    writePlace program place resident after = some before := by
  simp only [writePlace, bind, Option.bind_eq_some_iff] at written
  obtain ⟨stored, found, updated, changed, replaced⟩ := written
  have rawRead : stored.readPath program place.fields = some resident := by
    cases selected : stored.readPath program place.fields with
    | none => simp [readPlace, found, selected] at read
    | some value =>
      cases live : value.initialized <;> simp [readPlace, found, selected, live] at read
      cases read
      rfl
  have restored := Value.writePath_inverse rawRead changed
  have foundAfter := replaceBinding_lookup replaced
  have bindingRestored := replaceBinding_inverse found replaced
  simp [writePlace, foundAfter, restored, bindingRestored]

/-- Restoring the extracted value recovers the entire prior environment,
including siblings, existing holes, and shadowed bindings. -/
theorem Evaluates.move_restore {place : Place} {before after : Environment} {value : Value}
    (evaluated : Evaluates program before (.move place) value after) :
    writePlace program place value after = some before := by
  cases evaluated with
  | move taken =>
    obtain ⟨read, written⟩ := takePlace_eq_some.mp taken
    exact writePlace_inverse read written

theorem ValueHasType.initialized {value : Value} {type : Ty}
    (typed : ValueHasType program value type) : value.initialized = true := by
  exact (typed.complete .full).2

/-- Both structural and nominal projections consume the same positional typing fact. -/
theorem ResidentsTyped.select {types : List Ty} {values : List Value} {states : Nat → Initialization}
    (typed : ResidentsTyped program states values types) (index : Nat) (type : Ty)
    (selection : types[index]? = some type) :
    ∃ value, values[index]? = some value ∧ ResidentTyped program (states index) value type := by
  induction types generalizing values index states with
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

theorem ResidentsTyped.set {program : Program} {types : List Ty} {values : List Value} {states : Nat → Initialization}
    (typed : ResidentsTyped program states values types) (index : Nat) {type : Ty}
    (selected : types[index]? = some type) {replacement : Value} {next : Initialization}
    (resident : ResidentTyped program next replacement type) :
    ResidentsTyped program (fun other => if other = index then next else states other) (values.set index replacement) types := by
  induction types generalizing values index states with
  | nil => cases typed; simp at selected
  | cons first rest ih =>
    cases typed with
    | cons head tail =>
      cases index with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
        cases selected
        exact .cons (by simpa only [↓reduceIte] using resident) (by simpa only [Nat.add_one_ne_zero, ↓reduceIte] using tail)
      | succ index =>
        exact .cons (by simpa only [Nat.zero_ne_add_one, ↓reduceIte] using head) (by simpa only [Nat.add_right_cancel_iff] using ih tail index selected)

/-- The selected resident and lawful replacement are derived from the same field contract. -/
theorem ProjectionType.access {source target : Ty} {key : FieldKey} {index : Nat} {state : Initialization}
    (projection : ProjectionType program home source key index target) {value : Value}
    (typed : ResidentTyped program state value source) (present : state.Present := by trivial) :
    ∃ resident, value.fieldIndex program key = some index ∧ value.children[index]? = some resident ∧
      ResidentTyped program (state.child index) resident target ∧
      ∀ replacement next, ResidentTyped program next replacement target →
        ∃ updated, value.replaceChild index replacement = some updated ∧
          ResidentTyped program (state.setChild index next) updated source := by
  cases projection with
  | @tuple first type rest index selected =>
    cases typed with
    | vacant => exact False.elim present
    | uncertain typed permission => exact False.elim present
    | @tuple state head tail _ _ headTyped tailTyped _ =>
      obtain ⟨resident, found, residentTyped⟩ := ResidentsTyped.select (states := state.child) (.cons headTyped tailTyped) index target selected
      refine ⟨resident, rfl, found, residentTyped, ?_⟩
      intro replacement next replacementTyped
      have changed : ResidentsTyped program (state.setChild index next).child ((head :: tail).set index replacement) (first :: rest) := by
        rw [show (state.setChild index next).child = (fun other => if other = index then next else state.child other) from funext (state.child_setChild present index next)]
        exact ResidentsTyped.set (.cons headTyped tailTyped) index selected replacementTyped
      cases index with
      | zero =>
        cases changed with
        | cons firstChanged restChanged => exact ⟨_, rfl, .tuple firstChanged restChanged (by simp [Initialization.setChild])⟩
      | succ index =>
        change tail[index]? = some resident at found
        cases changed with
        | cons firstChanged restChanged =>
          exact ⟨_, by simp [Value.replaceChild, found], .tuple firstChanged restChanged (by simp [Initialization.setChild])⟩
  | @nominal identity index key declaration schema field declared structureOnly indexed selected visible =>
    cases typed with
    | vacant => exact False.elim present
    | uncertain typed permission => exact False.elim present
    | @nominal state _ tag otherDeclaration otherSchema values otherDeclared chosen finite residents _ =>
      have sameDeclaration := Option.some.inj (otherDeclared.symm.trans declared)
      subst otherDeclaration
      cases tag with
      | some tag => simp [DataDecl.constructor, structureOnly] at chosen
      | none =>
        have sameSchema : otherSchema = schema := by simpa [DataDecl.constructor, structureOnly] using chosen.symm
        subst otherSchema
        have selectedType : (schema.residents.map Field.type)[index]? = some field.type := by simp [List.getElem?_map, selected]
        obtain ⟨resident, found, residentTyped⟩ := ResidentsTyped.select residents index field.type selectedType
        refine ⟨resident, ?_, found, residentTyped, ?_⟩
        · simp [Value.fieldIndex, declared, structureOnly, indexed]
        · intro replacement next replacementTyped
          have changed : ResidentsTyped program (state.setChild index next).child (values.set index replacement) (schema.residents.map Field.type) := by
            rw [show (state.setChild index next).child = (fun other => if other = index then next else state.child other) from funext (state.child_setChild present index next)]
            exact residents.set index selectedType replacementTyped
          exact ⟨_, by simp [Value.replaceChild, found], .nominal declared chosen finite changed (by simp [Initialization.setChild])⟩

theorem PathType.resident {source target : Ty} {keys : List FieldKey} {indices : List Nat} {state selected : Initialization}
    (path : PathType program home source keys indices target) {value : Value}
    (typed : ResidentTyped program state value source) (access : state.Access indices selected) :
    ∃ resident, value.readPath program keys = some resident ∧ ResidentTyped program selected resident target := by
  induction path generalizing value state selected with
  | nil => cases access; exact ⟨value, rfl, typed⟩
  | @cons source middle target key keys index indices head tail ih =>
    cases access with
    | child present childAccess =>
      obtain ⟨child, indexed, found, childTyped, _⟩ := head.access typed present
      obtain ⟨resident, selected, residentTyped⟩ := ih childTyped childAccess
      exact ⟨resident, by simp [Value.readPath, Value.readField, indexed, found, selected], residentTyped⟩

theorem PathType.read {source target : Ty} {keys : List FieldKey} {indices : List Nat} {state selected : Initialization}
    (path : PathType program home source keys indices target) {value : Value}
    (typed : ResidentTyped program state value source) (access : state.Access indices selected) (initialized : selected.Complete) :
    ∃ resident, value.readPath program keys = some resident ∧ ValueHasType program resident target := by
  obtain ⟨resident, found, residentTyped⟩ := path.resident typed access
  exact ⟨resident, found, (residentTyped.complete initialized).1⟩

theorem ResidentTyped.fully_initialized {state : Initialization} {value : Value} {type : Ty}
    (typed : ResidentTyped program state value type) (live : value.initialized = true) : ValueHasType program value type := by
  induction typed using ResidentTyped.rec
    (motive_2 := fun states values types _ => valuesInitialized values = true → ValuesHaveTypes program values types) with
  | vacant => simp [Value.initialized] at live
  | uncertain actual permission ih => exact ih live
  | unit => exact .unit
  | integer fits => exact .integer fits
  | character valid => exact .character valid
  | tuple head tail present headIH tailIH =>
    simp only [Value.initialized, Bool.and_eq_true] at live
    exact .tuple (headIH live.1) (tailIH live.2)
  | array residents finite size present ih => exact .array (ih (by simpa [Value.initialized] using live)) finite size
  | nominal declared chosen finite residents present ih => exact .nominal declared chosen finite (ih (by simpa [Value.initialized] using live))
  | nil => exact .nil
  | cons head tail headIH tailIH =>
    rename_i live
    simp only [valuesInitialized, Bool.and_eq_true] at live
    exact .cons (headIH live.1) (tailIH live.2)

theorem Value.Disposable.not_live_exact_nominal {identity : Nat} {tag : Option Nat} {fields : List Value} {declaration : DataDecl}
    (declared : program.data identity = some declaration) (restriction : declaration.restriction = some .exact)
    (live : (Value.nominal identity tag fields).initialized = true) :
    ¬ Value.Disposable program (.nominal identity tag fields) := by
  intro disposable
  cases disposable with
  | owned typed permitted =>
    cases typed.fully_initialized live with
    | nominal found chosen finite residents present => exact permitted.nominal_restriction declared restriction
  | nominal found structureOnly incomplete fields => simp [live] at incomplete

theorem Initialization.Access.full (indices : List Nat) : Initialization.Access .full indices .full := by
  induction indices with
  | nil => exact .here .full
  | cons index indices ih => exact .child (by trivial) ih

theorem ResidentTyped.hole_uninitialized {state : Initialization} {value : Value} {type : Ty}
    (typed : ResidentTyped program state value type) (hole : state.Hole program type) : value.initialized = false := by
  obtain ⟨home, keys, indices, target, path, access⟩ := hole
  obtain ⟨vacancy, selected, vacantTyped⟩ := path.resident typed access
  have absent := ResidentTyped.vacant_value vacantTyped
  subst vacancy
  cases live : value.initialized with
  | false => rfl
  | true =>
    obtain ⟨resident, found, residentTyped⟩ := path.read (typed.fully_initialized live) (Initialization.Access.full indices) .full
    have same := Option.some.inj (selected.symm.trans found)
    subst resident
    have impossible := residentTyped.initialized
    simp [Value.initialized] at impossible
theorem StorageDisposition.realized {state : Initialization} {type : Ty} {value : Value}
    (disposition : StorageDisposition program state type) (typed : ResidentTyped program state value type) : Value.Disposable program value := by
  induction disposition using StorageDisposition.rec
    (motive_2 := fun states types _ => ∀ values, ResidentsTyped program states values types → ∀ value ∈ values, Value.Disposable program value)
    generalizing value with
  | vacant => have same := ResidentTyped.vacant_value typed; subst value; exact .vacant
  | whole permission => exact .owned typed permission
  | tuple hole fields ih =>
    have incomplete := typed.hole_uninitialized hole
    cases typed with
    | vacant => exact .vacant
    | uncertain actual permission => exact .owned actual permission
    | tuple head tail present =>
      have children := ih _ (.cons head tail)
      exact .tuple incomplete (children _ (List.mem_cons_self ..)) (fun value member => children value (List.mem_cons_of_mem _ member))
  | @nominal state identity declaration schema declared structureOnly hole fields ih =>
    have incomplete := typed.hole_uninitialized hole
    cases typed with
    | vacant => exact .vacant
    | uncertain actual permission => exact .owned actual permission
    | @nominal _ _ tag otherDeclaration otherSchema values found chosen finite residents present =>
      have same := Option.some.inj (found.symm.trans declared)
      subst otherDeclaration
      cases tag with
      | some tag => simp [DataDecl.constructor, structureOnly] at chosen
      | none =>
        have sameSchema : otherSchema = schema := by simpa [DataDecl.constructor, structureOnly] using chosen.symm
        subst otherSchema
        exact .nominal declared structureOnly incomplete (ih _ residents)
  | nil =>
    rename_i values typed value included
    cases typed
    cases included
  | cons head tail headIH tailIH =>
    rename_i values typed value included
    cases typed with
    | cons first rest =>
      rcases List.mem_cons.mp included with rfl | member
      · exact headIH first
      · exact tailIH _ rest value member
theorem StorageDisposition.live_requires_discard {state : Initialization} {type : Ty} {value : Value}
    (disposition : StorageDisposition program state type) (typed : ResidentTyped program state value type)
    (live : value.initialized = true) : MayDiscard program.data type := by
  cases disposition with
  | vacant => have same := ResidentTyped.vacant_value typed; subst value; simp [Value.initialized] at live
  | whole permission => exact permission
  | tuple hole fields => have absent := typed.hole_uninitialized hole; simp [live] at absent
  | nominal declared structureOnly hole fields => have absent := typed.hole_uninitialized hole; simp [live] at absent

theorem SlotTyped.disposable {value : Value} {slot : BindingType}
    (typed : SlotTyped program value slot) (allowed : slot.Disposable program) : value.Disposable program :=
  StorageDisposition.realized allowed typed

theorem EnvironmentTyped.disposable {environment : Environment} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) :
    (∀ entry ∈ context, entry.2.Disposable program) → ∀ entry ∈ environment, entry.2.Disposable program := by
  induction typed with
  | nil => intro _ entry included; cases included
  | cons head tail ih =>
    intro allowed entry included
    rcases List.mem_cons.mp included with rfl | member
    · exact SlotTyped.disposable head (allowed _ (List.mem_cons_self ..))
    · exact ih (fun binding member => allowed binding (List.mem_cons_of_mem _ member)) entry member

theorem PathType.write {source target : Ty} {keys : List FieldKey} {indices : List Nat} {state selected next : Initialization}
    (path : PathType program home source keys indices target) {value replacement : Value}
    (typed : ResidentTyped program state value source) (access : state.Access indices selected)
    (resident : ResidentTyped program next replacement target) :
    ∃ updated, value.writePath program keys replacement = some updated ∧
      ResidentTyped program (state.write indices next) updated source ∧ updated.readPath program keys = some replacement := by
  induction path generalizing value state selected with
  | nil => exact ⟨replacement, rfl, resident, rfl⟩
  | @cons source middle target key keys index indices head tail ih =>
    cases access with
    | child present childAccess =>
      obtain ⟨child, index, found, childTyped, replace⟩ := head.access typed present
      obtain ⟨updatedChild, written, updatedChildTyped, _⟩ := ih childTyped childAccess resident
      obtain ⟨updated, replaced, updatedTyped⟩ := replace updatedChild _ updatedChildTyped
      have pathWritten : value.writePath program (key :: keys) replacement = some updated := by
        simp [Value.writePath, index, found, written, replaced]
      exact ⟨updated, pathWritten, updatedTyped, Value.writePath_readback pathWritten⟩

theorem EnvironmentTyped.append {left right : Environment} {first rest : List (String × BindingType)}
    (front : EnvironmentTyped program left first) (back : EnvironmentTyped program right rest) :
    EnvironmentTyped program (left ++ right) (first ++ rest) := by
  induction front with
  | nil => exact back
  | cons resident tail ih => exact .cons resident ih

/-- Runtime and static scope introduction use the same newest-first order. -/
theorem EnvironmentTyped.reverse {environment : Environment} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) :
    EnvironmentTyped program environment.reverse context.reverse := by
  induction typed with
  | nil => exact .nil
  | cons resident tail ih => simpa using ih.append (.cons resident .nil)

theorem EnvironmentTyped.drop {environment : Environment} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) (count : Nat) :
    EnvironmentTyped program (environment.drop count) (context.drop count) := by
  induction count generalizing environment context with
  | zero => exact typed
  | succ count ih => cases typed with
    | nil => exact .nil
    | cons resident rest => exact ih rest

theorem EnvironmentTyped.length {environment : Environment} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) : environment.length = context.length := by
  induction typed with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem EnvironmentTyped.replace {environment : Environment} {context afterContext : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) {name : String} {slot : BindingType}
    (changed : replaceBinding name slot context = some afterContext) {replacement : Value}
    (resident : SlotTyped program replacement slot) :
    ∃ after, replaceBinding name replacement environment = some after ∧ EnvironmentTyped program after afterContext ∧
      lookup name after = some replacement := by
  suffices built : ∃ after, replaceBinding name replacement environment = some after ∧ EnvironmentTyped program after afterContext by
    obtain ⟨after, replaced, afterTyped⟩ := built
    exact ⟨after, replaced, afterTyped, replaceBinding_lookup replaced⟩
  induction typed generalizing afterContext with
  | nil => simp [replaceBinding] at changed
  | @cons key old type environment context oldTyped rest ih =>
    simp only [replaceBinding] at changed
    split at changed
    next same =>
      cases changed
      exact ⟨_, by simp [replaceBinding, same], .cons resident rest⟩
    next different =>
      obtain ⟨next, tailChanged, same⟩ := Option.map_eq_some_iff.mp changed
      cases same
      obtain ⟨after, replaced, afterTyped⟩ := ih tailChanged
      exact ⟨_, by simp [replaceBinding, different, replaced], .cons oldTyped afterTyped⟩

theorem EnvironmentTyped.lookup {environment : Environment} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) {name : String} {type : BindingType}
    (selected : lookup name context = some type) :
    ∃ value, lookup name environment = some value ∧ SlotTyped program value type := by
  induction typed with
  | nil => simp [Grounded.lookup] at selected
  | @cons key value type environment context valueTyped rest ih =>
    simp only [Grounded.lookup] at selected ⊢
    split at selected
    · cases selected
      exact ⟨value, by simp_all, valueTyped⟩
    · obtain ⟨found, selection, typed⟩ := ih selected
      exact ⟨found, by simp_all, typed⟩

theorem EnvironmentTyped.readPlace {environment : Environment} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) {place : Place} {slot : BindingType} {target : Ty} {indices : List Nat} {state : Initialization}
    (selected : Grounded.lookup place.root context = some slot) (access : slot.initialization.Access indices state) (initialized : state.Complete)
    (path : PathType program home slot.type place.fields indices target) :
    ∃ value, Grounded.readPlace program place environment = some value ∧ ValueHasType program value target := by
  obtain ⟨parent, found, parentTyped⟩ := typed.lookup selected
  obtain ⟨resident, read, residentTyped⟩ := path.read parentTyped access initialized
  exact ⟨resident, by simp [Grounded.readPlace, found, read, residentTyped.initialized], residentTyped⟩

theorem EnvironmentTyped.place_disposable {environment : Environment} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) {place : Place} {slot : BindingType} {target : Ty} {indices : List Nat} {state : Initialization}
    (selected : Grounded.lookup place.root context = some slot) (access : slot.initialization.Access indices state)
    (path : PathType program home slot.type place.fields indices target) (allowed : StorageDisposition program state target) :
    ∃ parent resident, Grounded.lookup place.root environment = some parent ∧ parent.readPath program place.fields = some resident ∧ resident.Disposable program := by
  obtain ⟨parent, found, parentTyped⟩ := typed.lookup selected
  obtain ⟨resident, read, residentTyped⟩ := path.resident parentTyped access
  exact ⟨parent, resident, found, read, StorageDisposition.realized allowed residentTyped⟩

theorem EnvironmentTyped.writePlace {environment : Environment} {context afterContext : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) {place : Place} {slot : BindingType} {target : Ty} {indices : List Nat} {state next : Initialization}
    (selected : Grounded.lookup place.root context = some slot)
    (access : slot.initialization.Access indices state) (path : PathType program home slot.type place.fields indices target)
    (changed : replaceBinding place.root { slot with initialization := slot.initialization.write indices next } context = some afterContext)
    {replacement : Value} (resident : ResidentTyped program next replacement target) :
    ∃ after, writePlace program place replacement environment = some after ∧ EnvironmentTyped program after afterContext ∧
      Grounded.readPlace program place after = (if replacement.initialized then some replacement else none) := by
  obtain ⟨parent, found, parentTyped⟩ := typed.lookup selected
  obtain ⟨updated, written, updatedTyped, readback⟩ := path.write parentTyped access resident
  obtain ⟨after, replaced, afterTyped, lookupAfter⟩ := typed.replace changed (replacement := updated) updatedTyped
  refine ⟨after, ?_, afterTyped, by simp [Grounded.readPlace, lookupAfter, readback]⟩
  simp [Grounded.writePlace, found, written, replaced]

theorem EnvironmentTyped.takePlace {environment : Environment} {context afterContext : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) {place : Place} {slot : BindingType} {target : Ty} {indices : List Nat} {state : Initialization}
    (selected : Grounded.lookup place.root context = some slot) (access : slot.initialization.Access indices state) (initialized : state.Complete)
    (path : PathType program home slot.type place.fields indices target)
    (changed : replaceBinding place.root { slot with initialization := slot.initialization.write indices .vacant } context = some afterContext) :
    ∃ value after, Grounded.takePlace program place environment = some (value, after) ∧ ValueHasType program value target ∧
      EnvironmentTyped program after afterContext ∧ Grounded.readPlace program place after = none := by
  obtain ⟨value, read, valueTyped⟩ := typed.readPlace selected access initialized path
  obtain ⟨after, written, afterTyped, readback⟩ := typed.writePlace selected access path changed (replacement := .vacant) .vacant
  exact ⟨value, after, takePlace_eq_some.mpr ⟨read, written⟩, valueTyped, afterTyped, by simpa [Value.initialized] using readback⟩

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

theorem PatternType.consume {pattern : Pattern} {type : Ty} {context : List (String × BindingType)}
    (typed : PatternType program home pattern type context) {value : Value}
    (valueTyped : ValueHasType program value type) {bindings : List (String × Value)}
    (matched : pattern.matchValue value = some bindings) :
    EnvironmentTyped program bindings context ∧ ∃ trace, Pattern.Consumes program pattern value bindings trace := by
  induction typed using PatternType.rec
    (motive_2 := fun patterns types context _ => ∀ values, ValuesHaveTypes program values types →
      ∀ bindings, matchPatterns patterns values = some bindings →
        EnvironmentTyped program bindings context ∧ ∀ index, ∃ trace, ConsumesPatterns program index patterns values bindings trace)
    generalizing value bindings with
  | wildcard discard =>
    simp only [Pattern.matchValue, Option.some.injEq] at matched
    subst bindings
    exact ⟨.nil, _, .wildcard (valueTyped.disposable discard).destroys⟩
  | binder name =>
    simp only [Pattern.matchValue, Option.some.injEq] at matched
    subst bindings
    exact ⟨.cons valueTyped .nil, [], .binder name value⟩
  | literal typed discard =>
    simp only [Pattern.matchValue] at matched
    split at matched
    next equal =>
      have empty := Option.some.inj matched
      subst bindings
      subst value
      exact ⟨.nil, _, .literal (typed.disposable discard).destroys⟩
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
      obtain ⟨bindingsTyped, fields⟩ := fieldsIH _ children bindings matched
      obtain ⟨trace, consumed⟩ := fields 0
      exact ⟨bindingsTyped, trace, .node same consumed⟩
    next different => contradiction
  | nil =>
    rename_i values valuesTyped bindings matched
    cases valuesTyped
    simp only [matchPatterns, Option.some.injEq] at matched
    subst bindings
    exact ⟨.nil, fun index => ⟨[], .nil index⟩⟩
  | @cons pattern patterns type types frontContext backContext head tail headIH tailIH =>
    rename_i values valuesTyped bindings matched
    cases valuesTyped with
    | @cons _ value values type types first rest =>
      simp only [matchPatterns] at matched
      cases headMatch : pattern.matchValue value with
      | none => simp [headMatch] at matched
      | some front =>
        cases tailMatch : matchPatterns patterns values with
        | none => simp [headMatch, tailMatch] at matched
        | some back =>
          simp [headMatch, tailMatch] at matched
          subst bindings
          obtain ⟨frontTyped, firstTrace, firstConsumed⟩ := headIH first headMatch
          obtain ⟨backTyped, restConsumed⟩ := tailIH _ rest _ tailMatch
          refine ⟨EnvironmentTyped.append frontTyped backTyped, ?_⟩
          intro index
          obtain ⟨restTrace, consumed⟩ := restConsumed (index + 1)
          exact ⟨_, .cons consumed firstConsumed⟩

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
      | @cons _ value values _ _ first rest =>
        obtain ⟨fields, headTyped, childrenTyped⟩ := ValueHasType.decompose first
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
theorem correctness {context afterContext : List (String × BindingType)} {expression : Expr} {type : Ty}
    (admitted : HasType program home context expression type afterContext)
    {environment : Environment} (environmentTyped : EnvironmentTyped program environment context) :
    ∃ value after, Evaluates program environment expression value after ∧ ValueHasType program value type ∧
      EnvironmentTyped program after afterContext ∧
      ∀ other otherAfter, Evaluates program environment expression other otherAfter → other = value ∧ otherAfter = after := by
  induction admitted using HasType.rec
    (motive_2 := fun home context expressions types afterContext _ =>
      ∀ environment, EnvironmentTyped program environment context →
        ∃ values after, EvaluatesMany program environment expressions values after ∧ ValuesHaveTypes program values types ∧
          EnvironmentTyped program after afterContext ∧
          ∀ other otherAfter, EvaluatesMany program environment expressions other otherAfter → other = values ∧ otherAfter = after)
    (motive_3 := fun home context subject result previous arms afterContext _ =>
      ∀ environment, EnvironmentTyped program environment context →
      ∀ value, ValueHasType program value subject → ∀ bindings body,
        selectArm value arms = some (bindings, body) →
        ∃ resultValue after, Evaluates program (bindings.reverse ++ environment) body resultValue after ∧
          ValueHasType program resultValue result ∧ EnvironmentTyped program (after.drop bindings.length) afterContext ∧
          (∃ trace, Cleans program bindings.length after trace (after.drop bindings.length)) ∧
          ConsumesArm program value arms bindings body ∧
          ∀ other otherAfter, Evaluates program (bindings.reverse ++ environment) body other otherAfter → other = resultValue ∧ otherAfter = after)
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
  | @call home context afterContext bodyAfter identity arguments declaration declared visible distinct initialized discard inputs body inputsIH bodyIH =>
    obtain ⟨values, middle, inputsEval, inputsTyped, middleTyped, inputsUnique⟩ := inputsIH environment environmentTyped
    have bindParameters : ∀ (parameters : List (String × BindingType)) (values : List Value),
        ValuesHaveTypes program values (parameters.map (fun parameter => parameter.2.type)) →
        (∀ parameter ∈ parameters, parameter.2.initialization = .full) →
        EnvironmentTyped program (List.zip (parameters.map Prod.fst) values) parameters := by
      intro parameters
      induction parameters with
      | nil => intro values typed initialized; cases typed; exact .nil
      | cons parameter parameters ih =>
        intro values typed initialized
        cases typed with
        | cons headTyped tailTyped =>
          exact .cons (by simpa [SlotTyped, initialized parameter (by simp)] using headTyped)
            (ih _ tailTyped (fun p included => initialized p (List.mem_cons_of_mem _ included)))
    obtain ⟨value, localAfter, bodyEval, valueTyped, localTyped, bodyUnique⟩ :=
      bodyIH (bindParameters declaration.parameters values inputsTyped initialized).reverse
    refine ⟨value, middle, .call declared inputsEval bodyEval (by simpa using Cleans.exists (environment := localAfter) localAfter.length (by simpa using localTyped.disposable discard)), valueTyped, middleTyped, ?_⟩
    intro other otherAfter evaluation
    cases evaluation with
    | call otherDeclared otherInputs otherBody otherCleanup =>
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
    obtain ⟨value, after, bodyEval, valueTyped, afterTyped, cleanup, consumed, unique⟩ :=
      bodiesIH normalized normalization middle middleTyped _ subjectTyped bindings body selected
    refine ⟨value, after.drop bindings.length, .applyPatterns normalization argumentsEval consumed bodyEval cleanup, valueTyped, afterTyped, ?_⟩
    intro other otherAfter evaluation
    cases evaluation with
    | applyPatterns otherNormalization otherArguments otherSelected otherBody otherCleanup =>
      have sameNormalization := normalizationUnique _ otherNormalization
      subst sameNormalization
      obtain ⟨rfl, rfl⟩ := argumentsUnique _ _ otherArguments
      have sameSelection := Option.some.inj (otherSelected.matches.symm.trans selected)
      cases sameSelection
      obtain ⟨rfl, rfl⟩ := unique _ _ otherBody
      exact ⟨rfl, rfl⟩
  | group typed ih =>
    obtain ⟨value, after, evaluated, valueTyped, afterTyped, unique⟩ := ih environmentTyped
    refine ⟨value, after, .group evaluated, valueTyped, afterTyped, ?_⟩
    intro other otherAfter evaluation
    cases evaluation with
    | group inner => exact unique _ _ inner
  | read selected access initialized path copyable =>
    obtain ⟨value, selectedValue, valueTyped⟩ := environmentTyped.readPlace selected access initialized path
    refine ⟨value, environment, .read selectedValue, valueTyped, environmentTyped, ?_⟩
    intro other otherAfter evaluated
    cases evaluated with
    | read found => exact ⟨Option.some.inj (found.symm.trans selectedValue), rfl⟩
  | move selected access initialized path cleared =>
    obtain ⟨value, after, taken, valueTyped, afterTyped, _⟩ := environmentTyped.takePlace selected access initialized path cleared
    refine ⟨value, after, .move taken, valueTyped, afterTyped, ?_⟩
    intro other otherAfter evaluated
    cases evaluated with
    | move otherTaken => exact Prod.mk.inj (Option.some.inj (otherTaken.symm.trans taken))
  | sequence head drop tail headIH tailIH =>
    obtain ⟨discarded, middle, headEval, discardedTyped, middleTyped, headUnique⟩ := headIH environmentTyped
    obtain ⟨value, after, tailEval, valueTyped, afterTyped, unique⟩ := tailIH middleTyped
    refine ⟨value, after, .sequence headEval ⟨_, (ResidentTyped.disposable discardedTyped drop).destroys⟩ tailEval, valueTyped, afterTyped, ?_⟩
    intro other otherAfter evaluated
    cases evaluated with
    | sequence otherHead otherDispose otherTail =>
      obtain ⟨rfl, rfl⟩ := headUnique _ _ otherHead
      exact unique _ _ otherTail
  | bind initialized drop annotated continued initialIH bodyIH =>
    obtain ⟨resident, middle, initialEval, residentTyped, middleTyped, initialUnique⟩ := initialIH environmentTyped
    obtain ⟨value, after, bodyEval, valueTyped, afterTyped, bodyUnique⟩ := bodyIH (.cons (value := resident) residentTyped middleTyped)
    have cleanup : ∀ entry ∈ after.take 1, entry.2.Disposable program := by
      apply (afterTyped.take 1).disposable
      intro entry included
      simp at included
      subst entry
      exact drop
    refine ⟨value, after.drop 1, .bind initialEval bodyEval (Cleans.exists 1 cleanup), valueTyped, afterTyped.drop 1, ?_⟩
    intro other otherAfter evaluated
    cases evaluated with
    | bind otherInitial otherBody otherCleanup =>
      obtain ⟨rfl, rfl⟩ := initialUnique _ _ otherInitial
      obtain ⟨rfl, rfl⟩ := bodyUnique _ _ otherBody
      exact ⟨rfl, rfl⟩
  | assign resident selected writable available path discard written continued residentIH bodyIH =>
    obtain ⟨replacement, middle, evaluated, residentTyped, middleTyped, residentUnique⟩ := residentIH environmentTyped
    obtain ⟨parent, old, found, read, allowed⟩ := middleTyped.place_disposable selected available path discard
    obtain ⟨updated, written, updatedTyped, _⟩ := middleTyped.writePlace selected available path written residentTyped
    obtain ⟨value, after, bodyEval, valueTyped, afterTyped, bodyUnique⟩ := bodyIH updatedTyped
    refine ⟨value, after, .assign evaluated ⟨parent, old, found, read, old.destructionTrace, allowed.destroys⟩ written bodyEval, valueTyped, afterTyped, ?_⟩
    intro other otherAfter evaluation
    cases evaluation with
    | assign otherEval otherDisposal otherWritten otherBody =>
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
  | @field home context afterContext body key parentType type index source discard selected ih =>
    obtain ⟨parent, after, evaluated, parentTyped, afterTyped, unique⟩ := ih environmentTyped
    obtain ⟨value, indexed, found, valueTyped, replace⟩ := selected.access parentTyped
    have selectedValue : parent.readField program key = some value := by simp [Value.readField, indexed, found]
    obtain ⟨residual, cleared, residualTyped⟩ := replace .vacant .vacant .vacant
    have extracted : parent.writePath program [key] .vacant = some residual := by
      simp [Value.writePath, indexed, found, cleared]
    refine ⟨value, after, .field evaluated selectedValue extracted ⟨_, (residualTyped.disposable discard).destroys⟩, valueTyped, afterTyped, ?_⟩
    intro other otherAfter evaluation
    cases evaluation with
    | field otherSource otherSelected otherExtracted otherDispose =>
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
  | @clause home context branchAfter afterContext subject result previous pattern bodyExpression rest bindingTypes afterBindings patternTyped distinct useful bodyTyped joined lengths discard tailTyped bodyIH tailIH =>
    rename_i environment environmentTyped value valueTyped bindings body selected
    simp only [selectArm] at selected
    split at selected
    next matched found =>
      have same := Option.some.inj selected
      cases same
      obtain ⟨bindingsTyped, trace, consumed⟩ := patternTyped.consume valueTyped found
      obtain ⟨result, after, evaluated, resultTyped, afterTyped, unique⟩ :=
        bodyIH (EnvironmentTyped.append bindingsTyped.reverse environmentTyped)
      refine ⟨result, after, evaluated, resultTyped, ?_, ?_, .hit found consumed, unique⟩
      · rw [bindingsTyped.length, ← lengths]
        exact (by simpa using afterTyped.drop afterBindings.length : EnvironmentTyped program (after.drop afterBindings.length) branchAfter).join joined
      · rw [bindingsTyped.length, ← lengths]
        apply Cleans.exists
        apply (afterTyped.take afterBindings.length).disposable
        simpa using discard
    next missed found =>
      obtain ⟨result, after, evaluated, resultTyped, afterTyped, cleanup, consumed, unique⟩ :=
        tailIH environment environmentTyped value valueTyped bindings body selected
      exact ⟨result, after, evaluated, resultTyped, afterTyped, cleanup, .miss found consumed, unique⟩

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

/-- Neither whole nor nested source use can recover lost initialization certainty. -/
theorem HasType.no_use_maybe {context after : List (String × BindingType)} {place : Place} {slot : BindingType} {type : Ty}
    (found : lookup place.root context = some slot) (unknown : slot.initialization = .maybe) :
    (¬ HasType program home context (.read place) type after) ∧
      (¬ HasType program home context (.move place) type after) := by
  constructor
  · intro admitted
    cases admitted with
    | read selected access initialized path copyable =>
      have same := Option.some.inj (selected.symm.trans found)
      cases same
      rw [unknown] at access
      have selectedMaybe := (Initialization.Access.maybe_iff.mp access).2
      cases selectedMaybe
      cases initialized
  · intro admitted
    cases admitted with
    | move selected access initialized path cleared =>
      have same := Option.some.inj (selected.symm.trans found)
      cases same
      rw [unknown] at access
      have selectedMaybe := (Initialization.Access.maybe_iff.mp access).2
      cases selectedMaybe
      cases initialized

theorem HasType.read_root_complete {context after : List (String × BindingType)} {root : String} {slot : BindingType} {type : Ty}
    (admitted : HasType program home context (.read ⟨root, []⟩) type after)
    (found : lookup root context = some slot) : slot.initialization.Complete := by
  cases admitted with
  | read selected access initialized path copyable =>
    have same := Option.some.inj (selected.symm.trans found)
    cases same
    cases path
    cases access
    exact initialized

theorem HasType.no_whole_read_after_clear {context cleared after : List (String × BindingType)} {root : String}
    {slot : BindingType} {indices : List Nat} {selected : Initialization} {type : Ty}
    (access : slot.initialization.Access indices selected)
    (changed : replaceBinding root { slot with initialization := slot.initialization.write indices .vacant } context = some cleared) :
    ¬ HasType program home cleared (.read ⟨root, []⟩) type after := by
  intro admitted
  exact access.clear_incomplete (admitted.read_root_complete (replaceBinding_lookup changed))

/-- Empty source environments are realized, not assumed. -/
theorem closed_correctness {expression : Expr} {type : Ty}
    (admitted : HasType program home [] expression type []) :
    ∃ value, Evaluates program [] expression value [] ∧ ValueHasType program value type ∧
      ∀ other after, Evaluates program [] expression other after → other = value ∧ after = [] := by
  obtain ⟨value, after, evaluated, typed, afterTyped, unique⟩ := correctness admitted .nil
  cases afterTyped
  exact ⟨value, evaluated, typed, unique⟩

/-- Exact admission boundary, in every lexical context and at every width. -/
theorem integer_admission (context : List (String × BindingType)) (type : IntegerType) (magnitude : Nat) :
    (∃ result after, HasType program home context (.integer type magnitude) result after) ↔ type.Contains program.target magnitude := by
  constructor
  · rintro ⟨_, _, admitted⟩
    cases admitted with
    | integer fits => exact fits
  · intro fits
    exact ⟨_, _, .integer fits⟩

theorem character_admission (context : List (String × BindingType)) (number : Nat) :
    (∃ result after, HasType program home context (.character number) result after) ↔ UnicodeScalar number := by
  constructor
  · rintro ⟨_, _, admitted⟩
    cases admitted with
    | character valid => exact valid
  · intro valid
    exact ⟨_, _, .character valid⟩

/-- The original unit subset retains precisely its admission and evaluation meaning. -/
theorem unit_agreement : HasType program home [] .unit .unit [] ∧
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
