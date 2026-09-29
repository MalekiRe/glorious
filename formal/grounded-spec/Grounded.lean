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
Lexical names select non-reused logical roots in one authoritative optional-resident
store. Calls retain caller cells; scope cleanup retires only its own roots.
These identities are not physical addresses or successful allocation requests.
Custom hooks, references, physical release, representation and exhaustion remain open.
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

/-- Transferred inputs, not resident storage. Introduction allocates logical roots. -/
abbrev BindingValues := List (String × Value)

/-- Unbounded logical identities, not physical addresses or allocation requests. -/
abbrev Root := Nat
abbrev Store := Root → Option Value

structure Environment where
  bindings : List (String × Root)
  store : Store
  nextRoot : Root

namespace Environment

def empty : Environment := ⟨[], fun _ => none, 0⟩
def roots (environment : Environment) := environment.bindings.map Prod.snd

/-- Hidden cells, as well as visible roots, precede the never-rewound supply.
Distinct lexical roots prevent two owned bindings from aliasing one resident. -/
structure Valid (environment : Environment) : Prop where
  bounded : ∀ root value, environment.store root = some value → root < environment.nextRoot
  named : ∀ root ∈ environment.roots, root < environment.nextRoot
  distinct : environment.roots.Nodup

def get (name : String) (environment : Environment) : Option Value := do
  let root ← lookup name environment.bindings
  environment.store root

def put (root : Root) (resident : Value) (environment : Environment) : Environment :=
  { environment with store := fun other => if other = root then some resident else environment.store other }

def replace (name : String) (resident : Value) (environment : Environment) : Option Environment := do
  let root ← lookup name environment.bindings
  let _ ← environment.store root
  some (environment.put root resident)

def bind (name : String) (resident : Value) (environment : Environment) : Environment :=
  { bindings := (name, environment.nextRoot) :: environment.bindings
    store := fun root => if root = environment.nextRoot then some resident else environment.store root
    nextRoot := environment.nextRoot + 1 }

/-- Source-order introduction produces a reversed, newest-first lexical prefix. -/
def prepare : BindingValues → Environment → Environment
  | [], environment => environment
  | (name, value) :: rest, environment => prepare rest (environment.bind name value)

def hide (environment : Environment) : Environment := { environment with bindings := [] }

/-- Retirement removes cells; a move instead leaves a live vacant cell. -/
def retire (count : Nat) (environment : Environment) : Environment :=
  { environment with
    bindings := environment.bindings.drop count
    store := fun root => if root ∈ (environment.bindings.take count).map Prod.snd then none else environment.store root }

/-- Restore visibility only, retaining the actual callee post-store and supply. -/
def resume (caller after : Environment) : Environment := { after with bindings := caller.bindings }

end Environment

namespace Environment

theorem Valid.empty : empty.Valid := by
  refine ⟨?_, ?_, by simp [roots, Environment.empty]⟩
  · intro root value found; cases found
  · simp [roots, Environment.empty]

/-- Freshness is derived from the store invariant, never assumed as a certificate. -/
theorem Valid.fresh {environment : Environment} (valid : environment.Valid) :
    environment.store environment.nextRoot = none := by
  cases found : environment.store environment.nextRoot with
  | none => rfl
  | some value => exact False.elim (Nat.lt_irrefl _ (valid.bounded _ _ found))

theorem lookup_mem {bindings : List (String × Root)} {name : String} {root : Root}
    (found : lookup name bindings = some root) : root ∈ bindings.map Prod.snd := by
  induction bindings with
  | nil => simp [lookup] at found
  | cons entry rest ih =>
    simp only [lookup] at found
    split at found
    · cases found; simp
    · exact List.mem_cons_of_mem _ (ih found)

theorem Valid.put {environment : Environment} (valid : environment.Valid)
    {root : Root} (bound : root < environment.nextRoot) (value : Value) :
    (environment.put root value).Valid := by
  refine ⟨?_, valid.named, valid.distinct⟩
  intro other resident found
  simp only [Environment.put] at found ⊢
  split at found
  · subst other; exact bound
  · exact valid.bounded _ _ found

theorem Valid.bind {environment : Environment} (valid : environment.Valid) (name : String) (value : Value) :
    (environment.bind name value).Valid := by
  refine ⟨?_, ?_, ?_⟩
  · intro root resident found
    simp only [Environment.bind] at found ⊢
    split at found
    · subst root; exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (valid.bounded _ _ found)
  · intro root included
    simp only [roots, Environment.bind, List.map_cons, List.mem_cons] at included
    rcases included with rfl | included
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (valid.named root included)
  · simp only [roots, Environment.bind, List.map_cons, List.nodup_cons]
    exact ⟨fun included => Nat.lt_irrefl _ (valid.named _ included), valid.distinct⟩

theorem Valid.hide {environment : Environment} (valid : environment.Valid) : environment.hide.Valid :=
  ⟨valid.bounded, by simp [roots, Environment.hide], by simp [roots, Environment.hide]⟩

theorem Valid.prepare {environment : Environment} (valid : environment.Valid) (values : BindingValues) :
    (environment.prepare values).Valid := by
  induction values generalizing environment with
  | nil => exact valid
  | cons entry rest ih => exact ih (valid.bind entry.1 entry.2)

theorem Valid.retire {environment : Environment} (valid : environment.Valid) (count : Nat) :
    (environment.retire count).Valid := by
  refine ⟨?_, ?_, ?_⟩
  · intro root value found
    simp only [Environment.retire] at found ⊢
    split at found
    · cases found
    · exact valid.bounded _ _ found
  · intro root included
    apply valid.named root
    simpa only [roots, Environment.retire, List.map_drop] using (List.mem_of_mem_drop (by simpa [roots, Environment.retire, List.map_drop] using included) : root ∈ environment.roots)
  · simpa only [roots, Environment.retire, List.map_drop, List.Nodup] using (valid.distinct.drop (i := count))

theorem retire_absent (environment : Environment) (count : Nat) {root : Root}
    (retired : root ∈ (environment.bindings.take count).map Prod.snd) :
    (environment.retire count).store root = none := by simp only [Environment.retire, if_pos retired]

theorem retire_frame (environment : Environment) (count : Nat) {root : Root}
    (retained : root ∉ (environment.bindings.take count).map Prod.snd) :
    (environment.retire count).store root = environment.store root := by simp only [Environment.retire, if_neg retained]

theorem retire_retained {environment : Environment} (valid : environment.Valid) (count : Nat) {root : Root}
    (retained : root ∈ (environment.bindings.drop count).map Prod.snd) :
    (environment.retire count).store root = environment.store root := by
  apply retire_frame
  have distinct : ((environment.roots.take count) ++ environment.roots.drop count).Nodup := by
    simpa using valid.distinct
  have disjoint := (List.nodup_append.mp distinct).2.2
  intro included
  exact disjoint _ (by simpa [roots, List.map_take] using included) _
    (by simpa [roots, List.map_drop] using retained) rfl

end Environment

/-- Stable lexical identities, non-reused supply, and exact framing of every
cell outside the incoming lexical owners (including hidden callers). This frame
characterizes the owned-value subset; future indirect reference writes must
account for their referents rather than inherit this lexical-only footprint. -/
structure Environment.Evolution (before after : Environment) : Prop where
  bindings : after.bindings = before.bindings
  supply : before.nextRoot ≤ after.nextRoot
  frame : ∀ root, root ∉ before.roots → after.store root = before.store root

namespace Environment.Evolution

theorem refl (environment : Environment) : Evolution environment environment :=
  ⟨rfl, Nat.le_refl _, fun _ _ => rfl⟩

theorem trans {before middle after : Environment} (first : Evolution before middle)
    (rest : Evolution middle after) : Evolution before after := by
  refine ⟨rest.bindings.trans first.bindings, Nat.le_trans first.supply rest.supply, ?_⟩
  intro root outside
  exact (rest.frame root (by simpa only [Environment.roots, first.bindings] using outside)).trans (first.frame root outside)

theorem put {environment : Environment} {root : Root} (member : root ∈ environment.roots) (value : Value) :
    Evolution environment (environment.put root value) := by
  refine ⟨rfl, Nat.le_refl _, ?_⟩
  intro other outside
  have different : other ≠ root := fun same => outside (same ▸ member)
  simp only [Environment.put, if_neg different]

end Environment.Evolution

namespace Environment

theorem retire_add (environment : Environment) (first rest : Nat) :
    (environment.retire first).retire rest = environment.retire (first + rest) := by
  cases environment with
  | mk bindings store nextRoot =>
    simp only [retire, List.drop_drop]
    congr 1
    funext root
    have takeAdd : ∀ (bindings : List (String × Root)) (first rest : Nat),
        bindings.take (first + rest) = bindings.take first ++ (bindings.drop first).take rest := by
      intro bindings first
      induction first generalizing bindings with
      | zero => intro rest; simp only [Nat.zero_add, List.take_zero, List.drop_zero, List.nil_append]
      | succ first ih =>
        intro rest
        cases bindings with
        | nil => simp
        | cons entry bindings => simpa only [Nat.succ_add, List.take_succ_cons, List.drop_succ_cons, List.cons_append] using congrArg (entry :: ·) (ih bindings rest)
    have union : root ∈ (bindings.take (first + rest)).map Prod.snd ↔
        root ∈ (bindings.take first).map Prod.snd ∨ root ∈ ((bindings.drop first).take rest).map Prod.snd := by
      rw [takeAdd, List.map_append, List.mem_append]
    by_cases tail : root ∈ ((bindings.drop first).take rest).map Prod.snd
    · simp only [if_pos tail, if_pos (union.mpr (Or.inr tail))]
    · by_cases head : root ∈ (bindings.take first).map Prod.snd
      · simp only [if_neg tail, if_pos head, if_pos (union.mpr (Or.inl head))]
      · have absent : root ∉ (bindings.take (first + rest)).map Prod.snd :=
          fun member => (union.mp member).elim head tail
        simp only [if_neg tail, if_neg head, if_neg absent]

theorem Evolution.unbind {before after : Environment} (valid : before.Valid) {name : String} {value : Value}
    (evolved : Evolution (before.bind name value) after) : Evolution before (after.retire 1) := by
  refine ⟨by simp [retire, evolved.bindings, bind], Nat.le_trans (Nat.le_succ _) evolved.supply, ?_⟩
  intro root outside
  by_cases same : root = before.nextRoot
  · subst root
    rw [show (after.retire 1).store before.nextRoot = none by simp [retire, evolved.bindings, bind]]
    exact valid.fresh.symm
  · have hidden : root ∉ (before.bind name value).roots := by simpa [roots, bind, same] using outside
    have framed := evolved.frame root hidden
    simpa [retire, evolved.bindings, bind, same] using framed

theorem Evolution.scope {before after : Environment} (valid : before.Valid) (values : BindingValues)
    (evolved : Evolution (before.prepare values) after) : Evolution before (after.retire values.length) := by
  induction values generalizing before with
  | nil => simpa [prepare, retire] using evolved
  | cons entry rest ih =>
    have inner := ih (valid.bind entry.1 entry.2) evolved
    have outer := inner.unbind valid
    simpa [retire_add, Nat.add_comm] using outer

theorem Evolution.resume {caller after : Environment} (evolved : Evolution caller.hide after) :
    Evolution caller (caller.resume after) := by
  exact ⟨rfl, evolved.supply, fun root _ => evolved.frame root (by simp [roots, hide])⟩

theorem Valid.resume {caller after : Environment} (valid : caller.Valid) (afterValid : after.Valid)
    (supply : caller.nextRoot ≤ after.nextRoot) : (caller.resume after).Valid :=
  ⟨afterValid.bounded, fun root member => Nat.lt_of_lt_of_le (valid.named root member) supply, valid.distinct⟩

end Environment

/-- Read-only logical-value projection. A missing cell has no constructor;
there is no default value and no independent copy of runtime residents. -/
inductive StoredBindings (store : Store) : List (String × Root) → BindingValues → Prop where
  | nil : StoredBindings store [] []
  | cons {name : String} {root : Root} {value : Value} {bindings : List (String × Root)} {values : BindingValues}
      (found : store root = some value) (rest : StoredBindings store bindings values) :
      StoredBindings store ((name, root) :: bindings) ((name, value) :: values)

namespace StoredBindings



theorem frame {before after : Store} {bindings : List (String × Root)} {values : BindingValues}
    (stored : StoredBindings before bindings values)
    (same : ∀ root ∈ bindings.map Prod.snd, after root = before root) : StoredBindings after bindings values := by
  induction stored with
  | nil => exact .nil
  | cons found rest ih =>
    exact .cons ((same _ (by simp)).trans found) (ih (fun root member => same root (List.mem_cons_of_mem _ member)))

theorem take {store : Store} {bindings : List (String × Root)} {values : BindingValues}
    (stored : StoredBindings store bindings values) (count : Nat) :
    StoredBindings store (bindings.take count) (values.take count) := by
  induction count generalizing bindings values with
  | zero => exact .nil
  | succ count ih => cases stored with
    | nil => exact .nil
    | cons found rest => exact .cons found (ih rest)

theorem drop {store : Store} {bindings : List (String × Root)} {values : BindingValues}
    (stored : StoredBindings store bindings values) (count : Nat) :
    StoredBindings store (bindings.drop count) (values.drop count) := by
  induction count generalizing bindings values with
  | zero => exact stored
  | succ count ih => cases stored with
    | nil => exact .nil
    | cons found rest => exact ih rest

theorem lookup {store : Store} {bindings : List (String × Root)} {values : BindingValues}
    (stored : StoredBindings store bindings values) (name : String) :
    (Grounded.lookup name bindings >>= store) = Grounded.lookup name values := by
  induction stored with
  | nil => rfl
  | cons found rest ih => simp only [Grounded.lookup]; split <;> simp_all

end StoredBindings

/-- Vacancies are storage, never well-typed owned results. -/
abbrev SlotTyped (program : Program) (resident : Value) (slot : BindingType) :=
  ResidentTyped program slot.initialization resident slot.type

inductive ValuesBindingsTyped (program : Program) : BindingValues → List (String × BindingType) → Prop where
  | nil : ValuesBindingsTyped program [] []
  | cons {name : String} {value : Value} {type : BindingType}
      {environment : BindingValues} {context : List (String × BindingType)}
      (resident : SlotTyped program value type) (rest : ValuesBindingsTyped program environment context) :
      ValuesBindingsTyped program ((name, value) :: environment) ((name, type) :: context)

/-- Resident typing consumes the authoritative root lookup relation. -/
structure EnvironmentTyped (program : Program) (environment : Environment) (context : List (String × BindingType)) : Prop where
  valid : environment.Valid
  residents : ∃ values, StoredBindings environment.store environment.bindings values ∧ ValuesBindingsTyped program values context

/-- Join soundness keeps the actual branch resident unchanged. -/
theorem ResidentTyped.join {state joined : Initialization} {value : Value} {type : Ty}
    (typed : ResidentTyped program state value type) (join : Initialization.Joins program.data type state joined) :
    ResidentTyped program joined value type := by
  cases join with
  | same => exact typed
  | affine permission => exact .uncertain typed permission

/-- A common static post-context accepts each actual branch environment verbatim. -/
theorem ValuesBindingsTyped.join {environment : BindingValues} {context joined : List (String × BindingType)}
    (typed : ValuesBindingsTyped program environment context) (join : ContextJoins program context joined) :
    ValuesBindingsTyped program environment joined := by
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

theorem ValuesBindingsTyped.take {environment : BindingValues} {context : List (String × BindingType)}
    (typed : ValuesBindingsTyped program environment context) (count : Nat) :
    ValuesBindingsTyped program (environment.take count) (context.take count) := by
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

/-- Ordered cleanup reads each resident through its stable root. Child paths
remain relative; root identities do not shift when a preceding owner retires. -/
inductive DestroysRoots (program : Program) (store : Store) : List Root → List (Root × List Nat) → Prop where
  | nil : DestroysRoots program store [] []
  | cons {root : Root} {roots : List Root} {value : Value} {first : List (List Nat)} {rest : List (Root × List Nat)}
      (found : store root = some value) (head : value.Destroys program first .vacant)
      (tail : DestroysRoots program store roots rest) :
      DestroysRoots program store (root :: roots) (first.map (root, ·) ++ rest)

def cleanupTrace (store : Store) : List Root → Option (List (Root × List Nat))
  | [] => some []
  | root :: roots => do
    let value ← store root
    let rest ← cleanupTrace store roots
    some (value.destructionTrace.map (root, ·) ++ rest)

inductive Cleans (program : Program) (count : Nat) (before : Environment) : List (Root × List Nat) → Environment → Prop where
  | retire {trace : List (Root × List Nat)}
      (destroyed : DestroysRoots program before.store ((before.bindings.take count).map Prod.snd) trace) :
      Cleans program count before trace (before.retire count)

theorem DestroysRoots.order {store : Store} {roots : List Root} {trace : List (Root × List Nat)}
    (executed : DestroysRoots program store roots trace) : cleanupTrace store roots = some trace := by
  induction executed with
  | nil => rfl
  | cons found head tail ih => simp [cleanupTrace, found, ih, head.result_order.2]

theorem DestroysRoots.scoped {store : Store} {roots : List Root} {trace : List (Root × List Nat)}
    (executed : DestroysRoots program store roots trace) : ∀ event ∈ trace, event.1 ∈ roots := by
  induction executed with
  | nil => simp
  | cons found head tail ih =>
    intro event included
    rcases List.mem_append.mp included with first | rest
    · obtain ⟨path, _, rfl⟩ := List.mem_map.mp first
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih event rest)

theorem DestroysRoots.exactly_once {store : Store} {roots : List Root} {trace : List (Root × List Nat)}
    (executed : DestroysRoots program store roots trace) (distinct : roots.Nodup) : trace.Nodup := by
  induction executed with
  | nil => exact List.Pairwise.nil
  | cons found head tail ih =>
    obtain ⟨outside, distinct⟩ := List.nodup_cons.mp distinct
    refine List.nodup_append.mpr ⟨?_, ih distinct, ?_⟩
    · simpa only [List.Nodup, List.pairwise_map, ne_eq, Prod.mk.injEq, true_and] using head.exactly_once
    · intro first included last member equal
      obtain ⟨path, _, rfl⟩ := List.mem_map.mp included
      cases equal
      exact outside (tail.scoped _ member)

theorem Cleans.suffix {count : Nat} {before after : Environment} {trace : List (Root × List Nat)}
    (executed : Cleans program count before trace after) : after = before.retire count := by cases executed; rfl

theorem Cleans.order {count : Nat} {before after : Environment} {trace : List (Root × List Nat)}
    (executed : Cleans program count before trace after) :
    cleanupTrace before.store ((before.bindings.take count).map Prod.snd) = some trace := by
  cases executed with | retire destroyed => exact destroyed.order

theorem Cleans.trace_scoped {count : Nat} {before after : Environment} {trace : List (Root × List Nat)}
    (executed : Cleans program count before trace after) :
    ∀ event ∈ trace, event.1 ∈ (before.bindings.take count).map Prod.snd := by
  cases executed with | retire destroyed => exact destroyed.scoped

theorem Cleans.exactly_once {count : Nat} {before after : Environment} {trace : List (Root × List Nat)}
    (executed : Cleans program count before trace after) (valid : before.Valid) : trace.Nodup := by
  cases executed with
  | retire destroyed =>
    apply destroyed.exactly_once
    simpa only [Environment.roots, List.map_take, List.Nodup] using (valid.distinct.take (i := count))

/-- Retirement, not just name removal, invalidates every cleaned identity. -/
theorem Cleans.retired {count : Nat} {before after : Environment} {trace : List (Root × List Nat)}
    (executed : Cleans program count before trace after) :
    ∀ root ∈ (before.bindings.take count).map Prod.snd, after.store root = none := by
  rw [executed.suffix]
  exact fun _ member => before.retire_absent count member

/-- Cells outside the cleanup prefix are exactly preserved, including hidden callers. -/
theorem Cleans.frame {count : Nat} {before after : Environment} {trace : List (Root × List Nat)}
    (executed : Cleans program count before trace after) :
    ∀ root, root ∉ (before.bindings.take count).map Prod.snd → after.store root = before.store root := by
  rw [executed.suffix]
  exact fun _ outside => before.retire_frame count outside

theorem DestroysRoots.exists {store : Store} {bindings : List (String × Root)} {values : BindingValues}
    (stored : StoredBindings store bindings values) (allowed : ∀ entry ∈ values, entry.2.Disposable program) :
    ∃ trace, DestroysRoots program store (bindings.map Prod.snd) trace := by
  induction stored with
  | nil => exact ⟨[], .nil⟩
  | cons found rest ih =>
    obtain ⟨trace, tail⟩ := ih (fun entry member => allowed entry (List.mem_cons_of_mem _ member))
    exact ⟨_, .cons found (allowed _ (List.mem_cons_self ..)).destroys tail⟩

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
inductive Pattern.Consumes (program : Program) : Pattern → Value → BindingValues → List (List Nat) → Prop where
  | wildcard {value : Value} {trace : List (List Nat)} (destroyed : value.Destroys program trace .vacant) :
      Pattern.Consumes program .wildcard value [] trace
  | binder (name : String) (value : Value) : Pattern.Consumes program (.binder name) value [(name, value)] []
  | literal {type : Option Ty} {value : Value} {trace : List (List Nat)} (destroyed : value.Destroys program trace .vacant) :
      Pattern.Consumes program (.literal type value) value [] trace
  | node {head : Head} {patterns : List Pattern} {value : Value} {bindings : BindingValues} {trace : List (List Nat)}
      (same : head = value.head) (fields : ConsumesPatterns program 0 patterns value.children bindings trace) :
      Pattern.Consumes program (.node head patterns) value bindings trace
inductive ConsumesPatterns (program : Program) : Nat → List Pattern → List Value → BindingValues → List (List Nat) → Prop where
  | nil (index : Nat) : ConsumesPatterns program index [] [] [] []
  | cons {index : Nat} {pattern : Pattern} {patterns : List Pattern} {value : Value} {values : List Value}
      {front back : BindingValues} {first rest : List (List Nat)}
      (tail : ConsumesPatterns program (index + 1) patterns values back rest)
      (head : Pattern.Consumes program pattern value front first) :
      ConsumesPatterns program index (pattern :: patterns) (value :: values) (front ++ back)
        (rest ++ first.map (index :: ·))
end

/-- A failed candidate performs no consumption; successful selection consumes
exactly the same first-match subject selected by the authoritative matcher. -/
inductive ConsumesArm (program : Program) (value : Value) : List (Pattern × Expr) → BindingValues → Expr → Prop where
  | hit {pattern : Pattern} {body : Expr} {rest : List (Pattern × Expr)} {bindings : BindingValues} {trace : List (List Nat)}
      (matched : pattern.matchValue value = some bindings) (consumed : Pattern.Consumes program pattern value bindings trace) :
      ConsumesArm program value ((pattern, body) :: rest) bindings body
  | miss {pattern : Pattern} {body result : Expr} {rest : List (Pattern × Expr)} {bindings : BindingValues}
      (missed : pattern.matchValue value = none) (selected : ConsumesArm program value rest bindings result) :
      ConsumesArm program value ((pattern, body) :: rest) bindings result

theorem Pattern.Consumes.binder_result {name : String} {value : Value} {bindings : BindingValues} {trace : List (List Nat)}
    (consumed : Pattern.Consumes program (.binder name) value bindings trace) :
    bindings = [(name, value)] ∧ trace = [] := by cases consumed; exact ⟨rfl, rfl⟩

theorem ConsumesArm.matches {value : Value} {arms : List (Pattern × Expr)} {bindings : BindingValues} {body : Expr}
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
  let stored ← environment.get place.root
  let value ← stored.readPath program place.fields
  if value.initialized then some value else none

def writePlace (program : Program) (place : Place) (replacement : Value) (environment : Environment) : Option Environment := do
  let stored ← environment.get place.root
  let updated ← stored.writePath program place.fields replacement
  environment.replace place.root updated

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
      (continued : Evaluates program (middle.bind name resident) body value after)
      (cleanup : ∃ trace, Cleans program 1 after trace (after.retire 1)) :
      Evaluates program environment (.bind mutable name annotation initial body) value (after.retire 1)
  | assign {environment middle updated after : Environment} {place : Place}
      {expression rest : Expr} {resident value : Value}
      (evaluated : Evaluates program environment expression resident middle)
      (dispose : ∃ parent old, middle.get place.root = some parent ∧ parent.readPath program place.fields = some old ∧ ∃ trace, old.Destroys program trace .vacant)
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
      {constantAfter : Environment} (initialized : Evaluates program environment.hide declaration.body value constantAfter) :
      Evaluates program environment (.constant name) value (environment.resume constantAfter)
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
      (body : Evaluates program (middle.hide.prepare (List.zip (declaration.parameters.map Prod.fst) values)) declaration.body value localAfter)
      (cleanup : ∃ trace, Cleans program (List.zip (declaration.parameters.map Prod.fst) values).length localAfter trace
        (localAfter.retire (List.zip (declaration.parameters.map Prod.fst) values).length)) :
      Evaluates program environment (.call identity arguments) value
        (middle.resume (localAfter.retire (List.zip (declaration.parameters.map Prod.fst) values).length))
  | applyPatterns {environment middle after : Environment} {inputs : List Ty} {arguments : List Expr}
      {arms : List (PatternSource × Expr)} {normalized : List (Pattern × Expr)} {values : List Value}
      {bindings : List (String × Value)} {body : Expr} {value : Value}
      (normalization : NormalizesArms program arms normalized)
      (argumentsEval : EvaluatesMany program environment arguments values middle)
      (selected : ConsumesArm program (argumentValue values) normalized bindings body)
      (bodyEval : Evaluates program (middle.prepare bindings) body value after)
      (cleanup : ∃ trace, Cleans program bindings.length after trace (after.retire bindings.length)) :
      Evaluates program environment (.applyPatterns inputs arguments arms) value (after.retire bindings.length)

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
  | constantValue {name : String} {declaration : ConstantDecl} {type : Ty} {value : Value}
      (declared : program.constants name = some declaration)
      (resolved : ResolvesType program.aliases declaration.type type)
      {constantAfter : Environment} (evaluated : Evaluates program .empty (.constant name) value constantAfter) :
      NormalizesPattern program (.constant name) (.literal (some type) value)
inductive NormalizesPatterns (program : Program) : List PatternSource → List Pattern → Prop where
  | patternsNil : NormalizesPatterns program [] []
  | patternsCons {source : PatternSource} {sources : List PatternSource} {result : Pattern} {results : List Pattern}
      (head : NormalizesPattern program source result) (tail : NormalizesPatterns program sources results) :
      NormalizesPatterns program (source :: sources) (result :: results)
inductive NormalizesArms (program : Program) : List (PatternSource × Expr) → List (Pattern × Expr) → Prop where
  | armsNil : NormalizesArms program [] []
  | armsCons {source : PatternSource} {pattern : Pattern} {body : Expr}
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
      (discard : StorageDisposition program (Initialization.full.setChild index .vacant) parentType) (selected : ProjectionType program home parentType key index type) :
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

theorem Environment.replace_readback {name : String} {value : Value} {before after : Environment}
    (replaced : before.replace name value = some after) : after.get name = some value := by
  simp only [Environment.replace, Bind.bind, Option.bind_eq_some_iff] at replaced
  obtain ⟨root, found, old, resident, same⟩ := replaced
  cases same
  simp [Environment.get, Environment.put, found]

theorem Environment.replace_valid {name : String} {value : Value} {before after : Environment}
    (valid : before.Valid) (replaced : before.replace name value = some after) : after.Valid := by
  simp only [Environment.replace, Bind.bind, Option.bind_eq_some_iff] at replaced
  obtain ⟨root, found, old, resident, same⟩ := replaced
  cases same
  exact valid.put (valid.bounded _ _ resident) value

theorem Environment.replace_evolution {name : String} {value : Value} {before after : Environment}
    (replaced : before.replace name value = some after) : before.Evolution after := by
  simp only [Environment.replace, Bind.bind, Option.bind_eq_some_iff] at replaced
  obtain ⟨root, found, old, resident, same⟩ := replaced
  cases same
  exact Environment.Evolution.put (Environment.lookup_mem found) value

theorem Environment.replace_inverse {name : String} {value old : Value} {before after : Environment}
    (read : before.get name = some old) (replaced : before.replace name value = some after) :
    after.replace name old = some before := by
  simp only [Environment.replace, Bind.bind, Option.bind_eq_some_iff] at replaced
  obtain ⟨root, found, resident, present, same⟩ := replaced
  cases same
  have oldSame : resident = old := by simpa [Environment.get, found, present] using read
  subst resident
  have restore : (before.put root value).put root old = before := by
    cases before with
    | mk bindings store nextRoot =>
      simp only [Environment.put]
      congr 1
      funext other
      by_cases same : other = root
      · subst other; simpa only [↓reduceIte] using present.symm
      · simp [same]
  simpa [Environment.replace, Environment.put, found] using congrArg some restore

theorem writePlace_readback {place : Place} {replacement : Value} {before after : Environment}
    (written : writePlace program place replacement before = some after) :
    ∃ parent, after.get place.root = some parent ∧ parent.readPath program place.fields = some replacement := by
  simp only [writePlace, bind, Option.bind_eq_some_iff] at written
  obtain ⟨stored, found, updated, changed, replaced⟩ := written
  exact ⟨updated, Environment.replace_readback replaced, Value.writePath_readback changed⟩

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
  have foundAfter := Environment.replace_readback replaced
  have bindingRestored := Environment.replace_inverse found replaced
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

theorem ValuesBindingsTyped.disposable {environment : BindingValues} {context : List (String × BindingType)}
    (typed : ValuesBindingsTyped program environment context) :
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

theorem ValuesBindingsTyped.append {left right : BindingValues} {first rest : List (String × BindingType)}
    (front : ValuesBindingsTyped program left first) (back : ValuesBindingsTyped program right rest) :
    ValuesBindingsTyped program (left ++ right) (first ++ rest) := by
  induction front with
  | nil => exact back
  | cons resident tail ih => exact .cons resident ih

/-- Runtime and static scope introduction use the same newest-first order. -/
theorem ValuesBindingsTyped.reverse {environment : BindingValues} {context : List (String × BindingType)}
    (typed : ValuesBindingsTyped program environment context) :
    ValuesBindingsTyped program environment.reverse context.reverse := by
  induction typed with
  | nil => exact .nil
  | cons resident tail ih => simpa using ih.append (.cons resident .nil)

theorem ValuesBindingsTyped.drop {environment : BindingValues} {context : List (String × BindingType)}
    (typed : ValuesBindingsTyped program environment context) (count : Nat) :
    ValuesBindingsTyped program (environment.drop count) (context.drop count) := by
  induction count generalizing environment context with
  | zero => exact typed
  | succ count ih => cases typed with
    | nil => exact .nil
    | cons resident rest => exact ih rest

theorem ValuesBindingsTyped.length {environment : BindingValues} {context : List (String × BindingType)}
    (typed : ValuesBindingsTyped program environment context) : environment.length = context.length := by
  induction typed with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem ValuesBindingsTyped.replace {environment : BindingValues} {context afterContext : List (String × BindingType)}
    (typed : ValuesBindingsTyped program environment context) {name : String} {slot : BindingType}
    (changed : replaceBinding name slot context = some afterContext) {replacement : Value}
    (resident : SlotTyped program replacement slot) :
    ∃ after, replaceBinding name replacement environment = some after ∧ ValuesBindingsTyped program after afterContext ∧
      lookup name after = some replacement := by
  suffices built : ∃ after, replaceBinding name replacement environment = some after ∧ ValuesBindingsTyped program after afterContext by
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

theorem ValuesBindingsTyped.lookup {environment : BindingValues} {context : List (String × BindingType)}
    (typed : ValuesBindingsTyped program environment context) {name : String} {type : BindingType}
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

theorem StoredBindings.unique {store : Store} {bindings : List (String × Root)} {first second : BindingValues}
    (left : StoredBindings store bindings first) (right : StoredBindings store bindings second) : first = second := by
  induction left generalizing second with
  | nil => cases right; rfl
  | cons found rest ih =>
    cases right with
    | cons otherFound otherRest =>
      cases Option.some.inj (found.symm.trans otherFound)
      cases ih otherRest
      rfl

theorem StoredBindings.bind {environment : Environment} {values : BindingValues}
    (stored : StoredBindings environment.store environment.bindings values) (valid : environment.Valid)
    (name : String) (value : Value) :
    StoredBindings (environment.bind name value).store (environment.bind name value).bindings ((name, value) :: values) := by
  refine .cons (by simp [Environment.bind]) ?_
  apply stored.frame
  intro root member
  have different : root ≠ environment.nextRoot := Nat.ne_of_lt (valid.named root member)
  simp only [Environment.bind, if_neg different]

/-- Preparation agrees with the previous logical binding order without rebuilding
storage from that observation: source inputs are installed once, left to right. -/
theorem StoredBindings.prepare {environment : Environment} {values : BindingValues}
    (stored : StoredBindings environment.store environment.bindings values) (valid : environment.Valid)
    (inputs : BindingValues) :
    StoredBindings (environment.prepare inputs).store (environment.prepare inputs).bindings (inputs.reverse ++ values) := by
  induction inputs generalizing environment values with
  | nil => exact stored
  | cons entry rest ih =>
    simpa [Environment.prepare, List.reverse_cons, List.append_assoc] using
      ih (stored.bind valid entry.1 entry.2) (valid.bind entry.1 entry.2)

theorem StoredBindings.retire {environment : Environment} {values : BindingValues}
    (stored : StoredBindings environment.store environment.bindings values) (valid : environment.Valid) (count : Nat) :
    StoredBindings (environment.retire count).store (environment.retire count).bindings (values.drop count) :=
  (stored.drop count).frame (fun _ member => Environment.retire_retained valid count member)

theorem StoredBindings.replace {store : Store} {bindings : List (String × Root)} {values after : BindingValues}
    (stored : StoredBindings store bindings values) (distinct : (bindings.map Prod.snd).Nodup)
    {name : String} {value : Value} (changed : replaceBinding name value values = some after) :
    ∃ root old, Grounded.lookup name bindings = some root ∧ store root = some old ∧
      StoredBindings (fun other => if other = root then some value else store other) bindings after := by
  induction stored generalizing after with
  | nil => simp [replaceBinding] at changed
  | @cons key root resident bindings values found rest ih =>
    obtain ⟨outside, distinct⟩ := List.nodup_cons.mp distinct
    simp only [replaceBinding] at changed
    split at changed
    next same =>
      cases changed
      refine ⟨root, resident, by simp [Grounded.lookup, same], found, .cons (by simp) ?_⟩
      apply rest.frame
      intro other member
      have different : other ≠ root := fun equal => outside (equal ▸ member)
      simp [different]
    next different =>
      obtain ⟨tailAfter, tailChanged, same⟩ := Option.map_eq_some_iff.mp changed
      cases same
      obtain ⟨selected, old, selectedRoot, selectedValue, tailStored⟩ := ih distinct tailChanged
      have unequal : root ≠ selected := fun equal => outside (equal ▸ Environment.lookup_mem selectedRoot)
      exact ⟨selected, old, by simp [Grounded.lookup, Ne.symm different, selectedRoot], selectedValue,
        .cons (by simp [unequal, found]) tailStored⟩

namespace EnvironmentTyped

theorem empty : EnvironmentTyped program .empty [] := ⟨Environment.Valid.empty, [], .nil, .nil⟩



theorem bind {environment : Environment} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) {name : String} {value : Value} {slot : BindingType}
    (resident : SlotTyped program value slot) :
    EnvironmentTyped program (environment.bind name value) ((name, slot) :: context) := by
  obtain ⟨values, stored, residents⟩ := typed.residents
  exact ⟨typed.valid.bind name value, (name, value) :: values, stored.bind typed.valid name value, .cons resident residents⟩

theorem hide {environment : Environment} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) : EnvironmentTyped program environment.hide [] :=
  ⟨typed.valid.hide, [], .nil, .nil⟩

theorem prepare {environment : Environment} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) {values : BindingValues} {types : List (String × BindingType)}
    (inputs : ValuesBindingsTyped program values types) :
    EnvironmentTyped program (environment.prepare values) (types.reverse ++ context) := by
  obtain ⟨residents, stored, residentTypes⟩ := typed.residents
  exact ⟨typed.valid.prepare values, values.reverse ++ residents, stored.prepare typed.valid values,
    inputs.reverse.append residentTypes⟩

theorem retire {environment : Environment} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) (count : Nat) :
    EnvironmentTyped program (environment.retire count) (context.drop count) := by
  obtain ⟨values, stored, residents⟩ := typed.residents
  refine ⟨typed.valid.retire count, values.drop count, ?_, residents.drop count⟩
  exact stored.retire typed.valid count

theorem join {environment : Environment} {context joined : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) (join : ContextJoins program context joined) :
    EnvironmentTyped program environment joined := by
  obtain ⟨values, stored, residents⟩ := typed.residents
  exact ⟨typed.valid, values, stored, residents.join join⟩

theorem resume {caller after : Environment} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program caller context) (valid : after.Valid)
    (evolved : Environment.Evolution caller.hide after) :
    EnvironmentTyped program (caller.resume after) context := by
  obtain ⟨values, stored, residents⟩ := typed.residents
  refine ⟨typed.valid.resume valid evolved.supply, values, ?_, residents⟩
  exact stored.frame (fun root _ => evolved.frame root (by simp [Environment.roots, Environment.hide]))

theorem cleanup {environment : Environment} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) (count : Nat)
    (allowed : ∀ entry ∈ context.take count, entry.2.Disposable program) :
    ∃ trace, Cleans program count environment trace (environment.retire count) := by
  obtain ⟨values, stored, residents⟩ := typed.residents
  obtain ⟨trace, destroyed⟩ := DestroysRoots.exists (stored.take count) ((residents.take count).disposable allowed)
  exact ⟨trace, .retire destroyed⟩

theorem replace {environment : Environment} {context afterContext : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) {name : String} {slot : BindingType}
    (changed : replaceBinding name slot context = some afterContext) {replacement : Value}
    (resident : SlotTyped program replacement slot) :
    ∃ after, environment.replace name replacement = some after ∧ EnvironmentTyped program after afterContext ∧
      after.get name = some replacement := by
  obtain ⟨values, stored, residents⟩ := typed.residents
  obtain ⟨next, changedValues, nextTyped, _⟩ := residents.replace changed resident
  obtain ⟨root, old, found, present, nextStored⟩ := stored.replace typed.valid.distinct changedValues
  have replaced : environment.replace name replacement = some (environment.put root replacement) := by
    simp [Environment.replace, found, present]
  exact ⟨_, replaced, ⟨Environment.replace_valid typed.valid replaced, next, nextStored, nextTyped⟩,
    Environment.replace_readback replaced⟩

theorem lookup {environment : Environment} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) {name : String} {type : BindingType}
    (selected : Grounded.lookup name context = some type) :
    ∃ value, environment.get name = some value ∧ SlotTyped program value type := by
  obtain ⟨values, stored, residents⟩ := typed.residents
  obtain ⟨value, found, valueTyped⟩ := residents.lookup selected
  exact ⟨value, (stored.lookup name).trans found, valueTyped⟩

end EnvironmentTyped

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
    ∃ parent resident, environment.get place.root = some parent ∧ parent.readPath program place.fields = some resident ∧ resident.Disposable program := by
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
    ValuesBindingsTyped program bindings context ∧ ∃ trace, Pattern.Consumes program pattern value bindings trace := by
  induction typed using PatternType.rec
    (motive_2 := fun patterns types context _ => ∀ values, ValuesHaveTypes program values types →
      ∀ bindings, matchPatterns patterns values = some bindings →
        ValuesBindingsTyped program bindings context ∧ ∀ index, ∃ trace, ConsumesPatterns program index patterns values bindings trace)
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
          refine ⟨ValuesBindingsTyped.append frontTyped backTyped, ?_⟩
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


/-- Agreement observes only lexical logical values. Root names, hidden caller
cells and the supply may differ; neither observation is an executable store. -/
structure Environment.Agrees (left right : Environment) : Prop where
  leftValid : left.Valid
  rightValid : right.Valid
  values : ∃ values, StoredBindings left.store left.bindings values ∧ StoredBindings right.store right.bindings values

namespace Environment.Agrees

theorem get {left right : Environment} (same : left.Agrees right) (name : String) : left.get name = right.get name := by
  obtain ⟨values, first, second⟩ := same.values
  exact (first.lookup name).trans (second.lookup name).symm

theorem bind {left right : Environment} (same : left.Agrees right) (name : String) (value : Value) :
    (left.bind name value).Agrees (right.bind name value) := by
  obtain ⟨values, first, second⟩ := same.values
  exact ⟨same.leftValid.bind name value, same.rightValid.bind name value, (name, value) :: values,
    first.bind same.leftValid name value, second.bind same.rightValid name value⟩

theorem prepare {left right : Environment} (same : left.Agrees right) (inputs : BindingValues) :
    (left.prepare inputs).Agrees (right.prepare inputs) := by
  obtain ⟨values, first, second⟩ := same.values
  exact ⟨same.leftValid.prepare inputs, same.rightValid.prepare inputs, inputs.reverse ++ values,
    first.prepare same.leftValid inputs, second.prepare same.rightValid inputs⟩

theorem hide {left right : Environment} (same : left.Agrees right) : left.hide.Agrees right.hide :=
  ⟨same.leftValid.hide, same.rightValid.hide, [], .nil, .nil⟩

theorem retire {left right : Environment} (same : left.Agrees right) (count : Nat) :
    (left.retire count).Agrees (right.retire count) := by
  obtain ⟨values, first, second⟩ := same.values
  exact ⟨same.leftValid.retire count, same.rightValid.retire count, values.drop count,
    first.retire same.leftValid count, second.retire same.rightValid count⟩

theorem resume {left right first last : Environment} (same : left.Agrees right)
    (firstValid : first.Valid) (lastValid : last.Valid)
    (leftFrame : left.hide.Evolution first) (rightFrame : right.hide.Evolution last) :
    (left.resume first).Agrees (right.resume last) := by
  obtain ⟨values, leftStored, rightStored⟩ := same.values
  exact ⟨same.leftValid.resume firstValid leftFrame.supply, same.rightValid.resume lastValid rightFrame.supply, values,
    leftStored.frame (fun root _ => leftFrame.frame root (by simp [Environment.roots, Environment.hide])),
    rightStored.frame (fun root _ => rightFrame.frame root (by simp [Environment.roots, Environment.hide]))⟩

theorem replace {left right after : Environment} (same : left.Agrees right) {name : String} {value : Value}
    (written : left.replace name value = some after) :
    ∃ other, right.replace name value = some other ∧ after.Agrees other := by
  obtain ⟨values, leftStored, rightStored⟩ := same.values
  have read : ∃ old, left.get name = some old := by
    simp only [Environment.replace, Bind.bind, Option.bind_eq_some_iff] at written
    obtain ⟨root, found, old, present, _⟩ := written
    exact ⟨old, by simp [Environment.get, found, present]⟩
  obtain ⟨old, found⟩ := read
  have available : Grounded.lookup name values = some old := (leftStored.lookup name).symm.trans found
  have replacements : ∀ {values : BindingValues}, Grounded.lookup name values = some old →
      ∃ next, replaceBinding name value values = some next := by
    intro values found
    induction values with
    | nil => simp [Grounded.lookup] at found
    | cons entry rest ih =>
      simp only [Grounded.lookup] at found
      split at found
      next equal => exact ⟨(entry.1, value) :: rest, by simp [replaceBinding, equal]⟩
      next different =>
        obtain ⟨next, changed⟩ := ih found
        exact ⟨entry :: next, by simp [replaceBinding, Ne.symm different, changed]⟩
  obtain ⟨next, changed⟩ := replacements available
  have produce : ∀ environment : Environment, environment.Valid →
      StoredBindings environment.store environment.bindings values →
      ∃ after, environment.replace name value = some after ∧ after.Valid ∧ StoredBindings after.store after.bindings next := by
    intro environment valid stored
    obtain ⟨root, resident, found, present, updated⟩ := stored.replace valid.distinct changed
    have replaced : environment.replace name value = some (environment.put root value) := by
      simp [Environment.replace, found, present]
    exact ⟨_, replaced, Environment.replace_valid valid replaced, updated⟩
  obtain ⟨actual, replaced, afterValid, afterStored⟩ := produce left same.leftValid leftStored
  have equal := Option.some.inj (replaced.symm.trans written)
  subst actual
  obtain ⟨other, otherWritten, otherValid, otherStored⟩ := produce right same.rightValid rightStored
  exact ⟨other, otherWritten, afterValid, otherValid, next, afterStored, otherStored⟩

end Environment.Agrees

/-- Admission/observation transports resident types, never fabricates a cell. -/
theorem EnvironmentTyped.agrees {left right : Environment} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program left context) (same : left.Agrees right) : EnvironmentTyped program right context := by
  obtain ⟨values, stored, residents⟩ := typed.residents
  obtain ⟨observed, first, second⟩ := same.values
  cases stored.unique first
  exact ⟨same.rightValid, values, second, residents⟩

theorem readPlace_agrees {left right : Environment} (same : left.Agrees right) (place : Place) :
    readPlace program place left = readPlace program place right := by simp only [readPlace, same.get]

theorem writePlace_agrees {left right after : Environment} (same : left.Agrees right) {place : Place} {value : Value}
    (written : writePlace program place value left = some after) :
    ∃ other, writePlace program place value right = some other ∧ after.Agrees other := by
  simp only [writePlace, bind, Option.bind_eq_some_iff] at written
  obtain ⟨parent, found, updated, changed, replaced⟩ := written
  obtain ⟨other, written, agreed⟩ := same.replace replaced
  exact ⟨other, by simp [writePlace, ← same.get place.root, found, changed, written], agreed⟩

theorem DestroysRoots.allowed {store : Store} {bindings : List (String × Root)} {values : BindingValues}
    (stored : StoredBindings store bindings values) {trace : List (Root × List Nat)}
    (destroyed : DestroysRoots program store (bindings.map Prod.snd) trace) :
    ∀ entry ∈ values, entry.2.Disposable program := by
  induction stored generalizing trace with
  | nil => simp
  | cons found rest ih =>
    cases destroyed with
    | cons otherFound head tail =>
      cases Option.some.inj (found.symm.trans otherFound)
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · cases head with
        | vacant => exact .vacant
        | resident _ permission _ => exact permission
      · exact ih tail entry member

theorem Cleans.agrees {left right after : Environment} {count : Nat} {trace : List (Root × List Nat)}
    (cleaned : Cleans program count left trace after) (same : left.Agrees right) :
    ∃ otherTrace, Cleans program count right otherTrace (right.retire count) := by
  obtain ⟨values, first, second⟩ := same.values
  cases cleaned with
  | retire destroyed =>
    obtain ⟨otherTrace, otherDestroyed⟩ := DestroysRoots.exists (second.take count) (destroyed.allowed (first.take count))
    exact ⟨otherTrace, .retire otherDestroyed⟩

theorem writePlace_storage {place : Place} {value : Value} {before after : Environment}
    (written : writePlace program place value before = some after) (valid : before.Valid) :
    after.Valid ∧ before.Evolution after := by
  simp only [writePlace, bind, Option.bind_eq_some_iff] at written
  obtain ⟨parent, found, updated, changed, replaced⟩ := written
  exact ⟨Environment.replace_valid valid replaced, Environment.replace_evolution replaced⟩

/-- Every real operation preserves stable lexical roots, the monotone supply,
and all storage outside its incoming owners. Fresh-root availability is derived
inside the bind/parameter preparation steps from Valid, not admission. -/
theorem Evaluates.storage {before after : Environment} {expression : Expr} {value : Value}
    (evaluated : Evaluates program before expression value after) :
    before.Valid → after.Valid ∧ before.Evolution after := by
  induction evaluated using Evaluates.rec
    (motive_2 := fun before _ _ after _ => before.Valid → after.Valid ∧ before.Evolution after)
    (motive_3 := fun _ _ _ => True)
    (motive_4 := fun _ _ _ => True)
    (motive_5 := fun _ _ _ => True) with
  | unit | integer | character | read => exact fun valid => ⟨valid, .refl _⟩
  | group _ ih => exact ih
  | move taken =>
    intro valid
    exact writePlace_storage (takePlace_eq_some.mp taken).2 valid
  | sequence _ _ _ headIH tailIH =>
    intro valid
    obtain ⟨middleValid, first⟩ := headIH valid
    obtain ⟨afterValid, rest⟩ := tailIH middleValid
    exact ⟨afterValid, first.trans rest⟩
  | bind _ _ _ initialIH bodyIH =>
    intro valid
    obtain ⟨middleValid, initial⟩ := initialIH valid
    obtain ⟨afterValid, body⟩ := bodyIH (middleValid.bind _ _)
    exact ⟨afterValid.retire 1, initial.trans (body.unbind middleValid)⟩
  | assign _ _ written _ initialIH bodyIH =>
    intro valid
    obtain ⟨middleValid, initial⟩ := initialIH valid
    obtain ⟨updatedValid, update⟩ := writePlace_storage written middleValid
    obtain ⟨afterValid, body⟩ := bodyIH updatedValid
    exact ⟨afterValid, initial.trans (update.trans body)⟩
  | tuple _ _ headIH tailIH =>
    intro valid
    obtain ⟨middleValid, first⟩ := headIH valid
    obtain ⟨afterValid, rest⟩ := tailIH middleValid
    exact ⟨afterValid, first.trans rest⟩
  | array _ ih | construct _ ih => exact ih
  | constant =>
    first | trivial |
      rename_i ih
      intro valid
      obtain ⟨afterValid, body⟩ := ih valid.hide
      exact ⟨valid.resume afterValid body.supply, body.resume⟩
  | field _ _ _ _ ih => exact ih
  | call _ _ _ _ inputsIH bodyIH =>
    intro valid
    obtain ⟨middleValid, inputs⟩ := inputsIH valid
    obtain ⟨afterValid, body⟩ := bodyIH (middleValid.hide.prepare _)
    have returned := body.scope middleValid.hide _
    exact ⟨middleValid.resume (afterValid.retire _) returned.supply, inputs.trans returned.resume⟩
  | applyPatterns _ _ _ _ _ _ argumentsIH bodyIH =>
    intro valid
    obtain ⟨middleValid, arguments⟩ := argumentsIH valid
    obtain ⟨afterValid, body⟩ := bodyIH (middleValid.prepare _)
    exact ⟨afterValid.retire _, arguments.trans (body.scope middleValid _)⟩
  | nil =>
    first | trivial |
      rename_i valid
      exact ⟨valid, .refl _⟩
  | cons =>
    first | trivial |
      rename_i headIH tailIH valid
      obtain ⟨middleValid, first⟩ := headIH valid
      obtain ⟨afterValid, rest⟩ := tailIH middleValid
      exact ⟨afterValid, first.trans rest⟩
  | wildcard | binder | node | constantValue | patternsNil | patternsCons | armsNil | armsCons => trivial


/-- Once an actual scope cleanup retires a root, no subsequent owned execution
can make that identity resolve again. The proof uses its real continuation and
monotone supply, not an allocation-success or future-state certificate. -/
theorem Cleans.retired_stays_absent {before after final : Environment} {count : Nat}
    {trace : List (Root × List Nat)} {expression : Expr} {value : Value}
    (cleaned : Cleans program count before trace after) (valid : before.Valid)
    (continued : Evaluates program after expression value final) :
    ∀ root ∈ (before.bindings.take count).map Prod.snd, final.store root = none ∧ root < final.nextRoot := by
  have returned := cleaned.suffix
  subst after
  have evolved := (continued.storage (valid.retire count)).2
  intro root retired
  have inPrefix : root ∈ before.roots.take count := by simpa [Environment.roots, List.map_take] using retired
  have bound := valid.named root (List.mem_of_mem_take inPrefix)
  have distinct : (before.roots.take count ++ before.roots.drop count).Nodup := by simpa using valid.distinct
  have outside : root ∉ (before.retire count).roots := by
    intro retained
    exact (List.nodup_append.mp distinct).2.2 root (by simpa [Environment.roots, List.map_take] using retired)
      root (by simpa [Environment.roots, Environment.retire, List.map_drop] using retained) rfl
  exact ⟨(evolved.frame root outside).trans (before.retire_absent count retired), Nat.lt_of_lt_of_le bound evolved.supply⟩

theorem Environment.prepare_old (environment : Environment) (inputs : BindingValues) {root : Root}
    (older : root < environment.nextRoot) :
    (environment.prepare inputs).store root = environment.store root ∧
      (root ∈ (environment.prepare inputs).roots ↔ root ∈ environment.roots) := by
  induction inputs generalizing environment with
  | nil => exact ⟨rfl, Iff.rfl⟩
  | cons entry rest ih =>
    have tail := ih (environment.bind entry.1 entry.2) (Nat.lt_succ_of_lt older)
    have different := Nat.ne_of_lt older
    simpa [Environment.prepare, Environment.bind, Environment.roots, different] using tail

theorem EvaluatesMany.storage {before after : Environment} {expressions : List Expr} {values : List Value}
    (evaluated : EvaluatesMany program before expressions values after) (valid : before.Valid) :
    after.Valid ∧ before.Evolution after := (Evaluates.array evaluated).storage valid

/-- A call preserves the caller's entire post-argument store, not merely names.
Caller roots remain in that same authoritative store while callee names are
isolated, and the returned state keeps the advanced callee supply. -/
theorem Evaluates.call_frame {before after : Environment} {identity : Nat} {arguments : List Expr} {value : Value}
    (evaluated : Evaluates program before (.call identity arguments) value after) (valid : before.Valid) :
    ∃ middle values declaration localAfter,
      program.functions identity = some declaration ∧ EvaluatesMany program before arguments values middle ∧
      Evaluates program (middle.hide.prepare (List.zip (declaration.parameters.map Prod.fst) values)) declaration.body value localAfter ∧
      (∀ root, root < middle.nextRoot →
        (middle.hide.prepare (List.zip (declaration.parameters.map Prod.fst) values)).store root = middle.store root ∧
        root ∉ (middle.hide.prepare (List.zip (declaration.parameters.map Prod.fst) values)).roots) ∧
      after.bindings = middle.bindings ∧ after.store = middle.store ∧ middle.nextRoot ≤ after.nextRoot := by
  cases evaluated with
  | @call environment middle localAfter identity arguments declaration values value declared inputs body cleanup =>
    have middleValid := (inputs.storage valid).1
    have returned := (body.storage (middleValid.hide.prepare _)).2.scope middleValid.hide _
    refine ⟨_, _, _, _, declared, inputs, body, ?_, rfl, ?_, returned.supply⟩
    · intro root older
      obtain ⟨stored, visible⟩ := Environment.prepare_old middle.hide (List.zip (declaration.parameters.map Prod.fst) values) older
      exact ⟨stored, by simpa [Environment.roots, Environment.hide] using visible⟩
    · funext root
      exact returned.frame root (by simp [Environment.roots, Environment.hide])

/-- Root identities and hidden caller cells cannot change owned logical results.
This transports the one evaluator across checked observations; it does not retain
or reconstruct the former name/value evaluator. The final observations agree too. -/
theorem Evaluates.agrees {left after : Environment} {expression : Expr} {value : Value}
    (evaluated : Evaluates program left expression value after) :
    ∀ right, left.Agrees right → ∃ other, Evaluates program right expression value other ∧ after.Agrees other := by
  induction evaluated using Evaluates.rec
    (motive_2 := fun left expressions values after _ =>
      ∀ right, left.Agrees right → ∃ other, EvaluatesMany program right expressions values other ∧ after.Agrees other)
    (motive_3 := fun _ _ _ => True)
    (motive_4 := fun _ _ _ => True)
    (motive_5 := fun _ _ _ => True) with
  | unit => intro right same; exact ⟨right, .unit, same⟩
  | integer fits => intro right same; exact ⟨right, .integer fits, same⟩
  | character valid => intro right same; exact ⟨right, .character valid, same⟩
  | group _ ih =>
    intro right same
    obtain ⟨other, body, agreed⟩ := ih right same
    exact ⟨other, .group body, agreed⟩
  | read selected =>
    intro right same
    exact ⟨right, .read ((readPlace_agrees same _).symm.trans selected), same⟩
  | move taken =>
    intro right same
    obtain ⟨read, written⟩ := takePlace_eq_some.mp taken
    obtain ⟨other, written, agreed⟩ := writePlace_agrees same written
    exact ⟨other, .move (takePlace_eq_some.mpr ⟨(readPlace_agrees same _).symm.trans read, written⟩), agreed⟩
  | sequence _ dispose _ headIH tailIH =>
    intro right same
    obtain ⟨middle, first, middleSame⟩ := headIH right same
    obtain ⟨other, rest, afterSame⟩ := tailIH middle middleSame
    exact ⟨other, .sequence first dispose rest, afterSame⟩
  | bind _ _ cleanup initialIH bodyIH =>
    intro right same
    obtain ⟨middle, initial, middleSame⟩ := initialIH right same
    obtain ⟨other, body, afterSame⟩ := bodyIH _ (middleSame.bind _ _)
    obtain ⟨trace, cleaned⟩ := cleanup
    exact ⟨other.retire 1, .bind initial body (cleaned.agrees afterSame), afterSame.retire 1⟩
  | assign _ disposal written _ initialIH bodyIH =>
    intro right same
    obtain ⟨middle, initial, middleSame⟩ := initialIH right same
    obtain ⟨updated, written, updatedSame⟩ := writePlace_agrees middleSame written
    obtain ⟨other, body, afterSame⟩ := bodyIH updated updatedSame
    obtain ⟨parent, old, found, read, destroyed⟩ := disposal
    exact ⟨other, .assign initial ⟨parent, old, (middleSame.get _).symm.trans found, read, destroyed⟩ written body, afterSame⟩
  | tuple _ _ headIH tailIH =>
    intro right same
    obtain ⟨middle, first, middleSame⟩ := headIH right same
    obtain ⟨other, rest, afterSame⟩ := tailIH middle middleSame
    exact ⟨other, .tuple first rest, afterSame⟩
  | array _ ih =>
    intro right same
    obtain ⟨other, elements, afterSame⟩ := ih right same
    exact ⟨other, .array elements, afterSame⟩
  | constant declared initialized ih =>
    intro right same
    obtain ⟨other, body, afterSame⟩ := ih right.hide same.hide
    exact ⟨right.resume other, .constant declared body, same.resume afterSame.leftValid afterSame.rightValid
      (initialized.storage same.leftValid.hide).2 (body.storage same.rightValid.hide).2⟩
  | construct _ ih =>
    intro right same
    obtain ⟨other, elements, afterSame⟩ := ih right same
    exact ⟨other, .construct elements, afterSame⟩
  | field _ selected extracted dispose ih =>
    intro right same
    obtain ⟨other, body, afterSame⟩ := ih right same
    exact ⟨other, .field body selected extracted dispose, afterSame⟩
  | call declared _ body cleanup inputsIH bodyIH =>
    intro right same
    obtain ⟨middle, inputs, middleSame⟩ := inputsIH right same
    obtain ⟨other, otherBody, afterSame⟩ := bodyIH _ (middleSame.hide.prepare _)
    obtain ⟨trace, cleaned⟩ := cleanup
    have leftFrame := (body.storage (middleSame.leftValid.hide.prepare _)).2.scope middleSame.leftValid.hide _
    have rightFrame := (otherBody.storage (middleSame.rightValid.hide.prepare _)).2.scope middleSame.rightValid.hide _
    exact ⟨_, .call declared inputs otherBody (cleaned.agrees afterSame),
      middleSame.resume (afterSame.leftValid.retire _) (afterSame.rightValid.retire _) leftFrame rightFrame⟩
  | applyPatterns normalization _ selected _ cleanup _ argumentsIH bodyIH =>
    intro right same
    obtain ⟨middle, arguments, middleSame⟩ := argumentsIH right same
    obtain ⟨other, body, afterSame⟩ := bodyIH _ (middleSame.prepare _)
    obtain ⟨trace, cleaned⟩ := cleanup
    exact ⟨_, .applyPatterns normalization arguments selected body (cleaned.agrees afterSame), afterSame.retire _⟩
  | nil => rename_i right same; exact ⟨right, .nil, same⟩
  | cons _ _ headIH tailIH =>
    rename_i right same
    obtain ⟨middle, first, middleSame⟩ := headIH right same
    obtain ⟨other, rest, afterSame⟩ := tailIH middle middleSame
    exact ⟨other, .cons first rest, afterSame⟩
  | wildcard | binder | node | constantValue | patternsNil | patternsCons | armsNil | armsCons => trivial

/-- Every admitted expression produces a uniquely determined, correctly typed
result and updated lexical environment. Later expressions consume that actual
post-state; scopes remove only their own bindings. -/
private theorem execution_correctness {context afterContext : List (String × BindingType)} {expression : Expr} {type : Ty}
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
        ∃ resultValue after, Evaluates program (environment.prepare bindings) body resultValue after ∧
          ValueHasType program resultValue result ∧ EnvironmentTyped program (after.retire bindings.length) afterContext ∧
          (∃ trace, Cleans program bindings.length after trace (after.retire bindings.length)) ∧
          ConsumesArm program value arms bindings body ∧
          ∀ other otherAfter, Evaluates program (environment.prepare bindings) body other otherAfter → other = resultValue ∧ otherAfter = after)
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
    obtain ⟨value, after, evaluated, typed, afterTyped, unique⟩ := ih environmentTyped.hide
    have evolved := (evaluated.storage environmentTyped.valid.hide).2
    refine ⟨value, environment.resume after, .constant declared evaluated, typed,
      environmentTyped.resume afterTyped.valid evolved, ?_⟩
    intro other otherAfter evaluation
    cases evaluation with
    | constant otherDeclared otherEval =>
      have same := Option.some.inj (otherDeclared.symm.trans declared)
      cases same
      obtain ⟨rfl, rfl⟩ := unique _ _ otherEval
      exact ⟨rfl, rfl⟩
  | @call home context afterContext bodyAfter identity arguments declaration declared visible distinct initialized discard inputs body inputsIH bodyIH =>
    obtain ⟨values, middle, inputsEval, inputsTyped, middleTyped, inputsUnique⟩ := inputsIH environment environmentTyped
    have bindParameters : ∀ (parameters : List (String × BindingType)) (values : List Value),
        ValuesHaveTypes program values (parameters.map (fun parameter => parameter.2.type)) →
        (∀ parameter ∈ parameters, parameter.2.initialization = .full) →
        ValuesBindingsTyped program (List.zip (parameters.map Prod.fst) values) parameters := by
      intro parameters
      induction parameters with
      | nil => intro values typed initialized; cases typed; exact .nil
      | cons parameter parameters ih =>
        intro values typed initialized
        cases typed with
        | cons headTyped tailTyped =>
          exact .cons (by simpa [SlotTyped, initialized parameter (by simp)] using headTyped)
            (ih _ tailTyped (fun p included => initialized p (List.mem_cons_of_mem _ included)))
    have parametersTyped := bindParameters declaration.parameters values inputsTyped initialized
    obtain ⟨value, localAfter, bodyEval, valueTyped, localTyped, bodyUnique⟩ :=
      bodyIH (by simpa using middleTyped.hide.prepare parametersTyped)
    have evolved := (bodyEval.storage (middleTyped.valid.hide.prepare _)).2.scope middleTyped.valid.hide _
    have cleanup := localTyped.cleanup (List.zip (declaration.parameters.map Prod.fst) values).length
      (fun entry included => discard entry (List.mem_of_mem_take included))
    refine ⟨value, _, .call declared inputsEval bodyEval cleanup, valueTyped,
      middleTyped.resume (localTyped.valid.retire _) evolved, ?_⟩
    intro other otherAfter evaluation
    cases evaluation with
    | call otherDeclared otherInputs otherBody otherCleanup =>
      have sameDeclaration := Option.some.inj (otherDeclared.symm.trans declared)
      cases sameDeclaration
      obtain ⟨rfl, rfl⟩ := inputsUnique _ _ otherInputs
      obtain ⟨rfl, rfl⟩ := bodyUnique _ _ otherBody
      exact ⟨rfl, rfl⟩
  | applyPatterns argumentsTyped nonempty constants covered bodies argumentsIH constantsIH bodiesIH =>
    obtain ⟨normalized, normalization, normalizationUnique⟩ := constantsIH
    have coverage := covered normalized normalization
    obtain ⟨values, middle, argumentsEval, valuesTyped, middleTyped, argumentsUnique⟩ := argumentsIH environment environmentTyped
    have subjectTyped := valuesTyped.argument
    obtain ⟨bindings, body, selected⟩ := coverage.selectArm subjectTyped
    obtain ⟨value, after, bodyEval, valueTyped, afterTyped, cleanup, consumed, unique⟩ :=
      bodiesIH normalized normalization middle middleTyped _ subjectTyped bindings body selected
    refine ⟨value, after.retire bindings.length, .applyPatterns normalization argumentsEval consumed bodyEval cleanup, valueTyped, afterTyped, ?_⟩
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
    obtain ⟨value, after, bodyEval, valueTyped, afterTyped, bodyUnique⟩ := bodyIH (middleTyped.bind (value := resident) residentTyped)
    have cleanup := afterTyped.cleanup 1 (by
      intro entry included
      simp at included
      subst entry
      exact drop)
    refine ⟨value, after.retire 1, .bind initialEval bodyEval cleanup, valueTyped, afterTyped.retire 1, ?_⟩
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
    refine ⟨value, after, .field evaluated selectedValue extracted ⟨_, (StorageDisposition.realized discard residualTyped).destroys⟩, valueTyped, afterTyped, ?_⟩
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
        bodyIH (environmentTyped.prepare bindingsTyped)
      refine ⟨result, after, evaluated, resultTyped, ?_, ?_, .hit found consumed, unique⟩
      · rw [bindingsTyped.length, ← lengths]
        exact (by simpa using afterTyped.retire afterBindings.length : EnvironmentTyped program (after.retire afterBindings.length) branchAfter).join joined
      · rw [bindingsTyped.length, ← lengths]
        apply afterTyped.cleanup
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
    obtain ⟨value, after, evaluated, valueTyped, afterTyped, unique⟩ := ih EnvironmentTyped.empty
    cases typed with
    | constant declared visible resolved structural initialized =>
      refine ⟨.literal (some type) value, .constantValue declared resolved evaluated, ?_⟩
      intro other normalized
      cases normalized with
      | constantValue otherDeclared otherResolved otherEvaluated =>
        have sameDeclaration := Option.some.inj (otherDeclared.symm.trans declared)
        cases sameDeclaration
        have sameType := resolvesUnique resolved otherResolved
        have sameValue := (unique _ _ otherEvaluated).1
        subst sameType
        subst sameValue
        rfl
  | patternsEmpty =>
    refine ⟨[], .patternsNil, ?_⟩
    intro other normalized
    cases normalized
    rfl
  | patternsCons head tail headIH tailIH =>
    obtain ⟨first, firstNormalized, firstUnique⟩ := headIH
    obtain ⟨rest, restNormalized, restUnique⟩ := tailIH
    refine ⟨first :: rest, .patternsCons firstNormalized restNormalized, ?_⟩
    intro other normalized
    cases normalized with
    | patternsCons otherHead otherTail =>
      have sameHead := firstUnique _ otherHead
      have sameTail := restUnique _ otherTail
      subst sameHead
      subst sameTail
      rfl
  | armsEmpty =>
    refine ⟨[], .armsNil, ?_⟩
    intro other normalized
    cases normalized
    rfl
  | armsCons head tail headIH tailIH =>
    obtain ⟨first, firstNormalized, firstUnique⟩ := headIH
    obtain ⟨rest, restNormalized, restUnique⟩ := tailIH
    refine ⟨(_, _) :: rest, .armsCons firstNormalized restNormalized, ?_⟩
    intro other normalized
    cases normalized with
    | armsCons otherHead otherTail =>
      have sameHead := firstUnique _ otherHead
      have sameTail := restUnique _ otherTail
      subst sameHead
      subst sameTail
      rfl

/-- Connected correctness includes actual root storage and retirement effects,
not merely agreement of lexical values. Every old root outside the expression's
lexical owners is framed exactly, and no operation decreases the fresh supply. -/
theorem correctness {context afterContext : List (String × BindingType)} {expression : Expr} {type : Ty}
    (admitted : HasType program home context expression type afterContext)
    {environment : Environment} (environmentTyped : EnvironmentTyped program environment context) :
    ∃ value after, Evaluates program environment expression value after ∧ ValueHasType program value type ∧
      EnvironmentTyped program after afterContext ∧ environment.Evolution after ∧
      (∀ otherEnvironment, environment.Agrees otherEnvironment →
        ∃ otherAfter, Evaluates program otherEnvironment expression value otherAfter ∧
          EnvironmentTyped program otherAfter afterContext ∧ after.Agrees otherAfter) ∧
      ∀ other otherAfter, Evaluates program environment expression other otherAfter → other = value ∧ otherAfter = after := by
  obtain ⟨value, after, evaluated, typed, afterTyped, unique⟩ := execution_correctness admitted environmentTyped
  refine ⟨value, after, evaluated, typed, afterTyped, (evaluated.storage environmentTyped.valid).2, ?_, unique⟩
  intro otherEnvironment same
  obtain ⟨otherAfter, otherEvaluation, afterSame⟩ := evaluated.agrees otherEnvironment same
  exact ⟨otherAfter, otherEvaluation, afterTyped.agrees afterSame, afterSame⟩

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

/-- Closed executions retire every temporary cell while preserving the advanced
identity supply. Empty storage does not reset identities or mean physical release. -/
theorem closed_correctness {expression : Expr} {type : Ty}
    (admitted : HasType program home [] expression type []) :
    ∃ value after, Evaluates program .empty expression value after ∧ ValueHasType program value type ∧
      EnvironmentTyped program after [] ∧ after.bindings = [] ∧ (∀ root, after.store root = none) ∧
      ∀ other otherAfter, Evaluates program .empty expression other otherAfter → other = value ∧ otherAfter = after := by
  obtain ⟨value, after, evaluated, typed, afterTyped, storage, _, unique⟩ := correctness admitted EnvironmentTyped.empty
  exact ⟨value, after, evaluated, typed, afterTyped, storage.bindings,
    fun root => storage.frame root (by simp [Environment.roots, Environment.empty]), unique⟩

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

/-- The original unit subset retains precisely its admission and logical result. -/
theorem unit_agreement : HasType program home [] .unit .unit [] ∧
    ∀ value, Evaluates program .empty .unit value .empty ↔ value = .unit := by
  obtain ⟨value, after, evaluated, _, _, _, _, unique⟩ :=
    closed_correctness (program := program) (home := home) HasType.unit
  have same : value = .unit := by cases evaluated; rfl
  refine ⟨.unit, fun other => ⟨?_, ?_⟩⟩
  · intro evaluation
    exact (unique other .empty evaluation).1.trans same
  · intro equal
    subst other
    exact .unit

end Grounded
