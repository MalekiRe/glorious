/-!
Target-indexed expressions, structural/nominal data, and first-class shared/unique references.
Normative basis: §§2.2–2.3, 3.2–3.4, 4.1–4.4, 5.1–5.3, 6.1–6.3, 7.2–7.7, 9.1–9.2 and 13.1.
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
Mode-sensitive loans, canonical borrowed subaddresses and checked own-ending
metadata are connected to the same source producer and correctness theorem.
Explicit unique/shared borrowing and reborrowing preserve immutable modes;
canonical referent mutation and restoration consume the same storage invariants.
Default owned reads copy Duplicable data/handles or transfer from positive static
noncopy evidence; reference expectations compel fresh reborrowing instead.
Custom hooks, physical realization and exhaustion remain open.
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

inductive BorrowMode where
  | shared | unique
  deriving DecidableEq

inductive Ty where
  | unit
  | integer (type : IntegerType)
  | character
  | tuple (head : Ty) (tail : List Ty)
  | array (element : Ty) (length : Nat)
  | nominal (identity : Nat)
  | reference (referent : Ty) (mode : BorrowMode := .shared)

mutual
/-- Syntactic supported-data shape, not a claim about unknown nominal layouts.
A non-vacant nominal resident separately supplies its checked FiniteLayout. -/
def Ty.DataShape : Ty → Prop
  | .reference _ _ => False
  | .tuple head tail => head.DataShape ∧ typesDataShape tail
  | .array element _ => element.DataShape
  | _ => True

def typesDataShape : List Ty → Prop
  | [] => True
  | type :: types => type.DataShape ∧ typesDataShape types
end

theorem typesDataShape_iff (types : List Ty) : typesDataShape types ↔ ∀ type ∈ types, type.DataShape := by
  induction types with
  | nil => simp [typesDataShape]
  | cons first rest ih => simp [typesDataShape, ih]

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

theorem FiniteLayout.dataShape {target : Target} {data : DataDeclarations} {type : Ty}
    (finite : FiniteLayout target data type) : type.DataShape := by
  induction finite with
  | unit | integer | character | nominal => trivial
  | tuple first rest firstIH restIH => exact ⟨firstIH, (typesDataShape_iff _).mpr restIH⟩
  | array resident size ih => exact ih

/-- Unknown nominal identities remain admissible in vacant old slots. Direct
reference handles require a finite referent; reference aggregates are outside this slice. -/
inductive StorageType (target : Target) (data : DataDeclarations) : Ty → Prop where
  | data {type : Ty} (shape : type.DataShape) : StorageType target data type
  | reference {referent : Ty} {mode : BorrowMode} (finite : FiniteLayout target data referent) : StorageType target data (.reference referent mode)


/-- Constructor identity for structural matching; tuples remain distinct from nominal data. -/
inductive Head where
  | vacant
  | reference (node : Nat)
  | unit
  | integer (type : IntegerType) (number : Int)
  | character (number : Nat)
  | tuple | array
  | nominal (identity : Nat) (tag : Option Nat)
  deriving DecidableEq

/-- Runtime reference observations are not source constructor patterns. -/
def Head.Source : Head → Prop
  | .reference _ => False
  | _ => True

inductive Value where
  | vacant
  | reference (node : Nat)
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
  | .reference node, .reference other => decide (node = other)
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
    | reference node => intro right; cases right <;> simp [Value.equal]
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

theorem Initialization.Access.append {state middle selected : Initialization} {first second : List Nat}
    (front : state.Access first middle) (back : middle.Access second selected) :
    state.Access (first ++ second) selected := by
  induction front with
  | here => exact back
  | child present _ ih => exact .child present (ih back)

theorem Initialization.Access.deterministic {state first second : Initialization} {indices : List Nat}
    (left : state.Access indices first) (right : state.Access indices second) : first = second := by
  induction left with
  | here => cases right; rfl
  | child _ _ ih => cases right with | child _ rest => exact ih rest

theorem Initialization.Access.split {state selected : Initialization} {first second : List Nat}
    (access : state.Access (first ++ second) selected) :
    ∃ middle, state.Access first middle ∧ middle.Access second selected := by
  induction first generalizing state with
  | nil => exact ⟨state, .here _, access⟩
  | cons index indices ih =>
    cases access with
    | child present rest =>
      obtain ⟨middle, front, back⟩ := ih rest
      exact ⟨middle, .child present front, back⟩

theorem Initialization.Complete.access_all {state : Initialization} (complete : state.Complete)
    (indices : List Nat) : ∃ selected, state.Access indices selected ∧ selected.Complete := by
  induction indices generalizing state with
  | nil => exact ⟨state, .here _, complete⟩
  | cons index indices ih =>
    obtain ⟨selected, access, ready⟩ := ih (complete.child index)
    exact ⟨selected, .child (by cases complete <;> trivial) access, ready⟩


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

/-- Source identities name binders, never allocated runtime roots. -/
inductive OriginBase where
  | binder (identity : Nat)
  | input (identity : Nat)
  deriving DecidableEq

structure Origin where
  base : OriginBase
  fields : List Nat := []

/-- Only shared reference handles are nodes. An ended record remains in history. -/
structure SourceLoan where
  target : Origin
  referent : Ty
  parent : Option Nat
  own : Bool
  mode : BorrowMode := .shared

/-- Declaration metadata is separate from the identities produced at introduction. -/
structure Slot extends BindingType where
  binder : Nat
  reference : Option Nat

def Slot.metadata (slot : Slot) : Ty × Bool × Nat × Option Nat :=
  (slot.type, slot.mutable, slot.binder, slot.reference)

structure Context where
  names : List (String × Nat)
  storage : OriginBase → Option Slot
  loans : List SourceLoan
  nextBinder : Nat
  inputCount : Nat

/-- Lexical lookup is a view of authoritative source storage. Hiding names does
not hide, duplicate, or roll back the initialization of the named storage. -/
def Context.bindings (context : Context) : List (String × Slot) :=
  context.names.filterMap fun entry =>
    (context.storage (.binder entry.2)).map fun slot => (entry.1, slot)

structure ResultType where
  type : Ty
  reference : Option Nat

/-- This is source-level explicit dereference, not an owned temporary projection. -/
inductive AccessPlace where
  | owner (place : Place)
  | dereference (reference : Place) (fields : List FieldKey)


inductive Expr where
  | unit
  | integer (type : IntegerType) (magnitude : Nat)
  | character (number : Nat)
  | group (body : Expr)
  | read (place : Place)
  | move (place : Place)
  | borrow (mode : BorrowMode) (place : AccessPlace)
  | dereference (reference : Place) (fields : List FieldKey)
  | moveIndirect (reference : Place) (fields : List FieldKey)
  | assignIndirect (reference : Place) (fields : List FieldKey) (value rest : Expr)
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

mutual
/-- The sole admission derivation produces this execution metadata. Ending names
an exact lexical slot, not a source node interpreted as a runtime allocation ID. -/
inductive CorePlan where
  | leaf
  | implicitMove
  | reborrow (mode : BorrowMode)
  | unary (body : CorePlan)
  | binary (first rest : CorePlan)
  | batch (elements : List CorePlan)
  | call (arguments : List CorePlan) (body : CorePlan)
  | patterns (arguments : List CorePlan) (arms : List (PatternPlan × CorePlan))
  | endOwn (slot : Nat) (continuation : CorePlan)
  | endAfter (slot : Nat) (body : CorePlan)

inductive PatternPlan where
  | leaf
  | node (fields : List PatternPlan)
  | constant (initializer : CorePlan)
end

structure Core where
  source : Expr
  plan : CorePlan

def Core.erase (core : Core) : Expr := core.source

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

/-- Canonical paths retain checked projection facts, including the module which
 authorized each step. Reborrowing can cross module boundaries. -/
inductive CanonicalPath (program : Program) : Ty → List Nat → Ty → Prop where
  | nil (type : Ty) : CanonicalPath program type [] type
  | cons {source middle target : Ty} {index : Nat} {indices : List Nat}
      {home : Module} {key : FieldKey}
      (head : ProjectionType program home source key index middle)
      (tail : CanonicalPath program middle indices target) :
      CanonicalPath program source (index :: indices) target

theorem PathType.canonical {source target : Ty} {keys : List FieldKey} {indices : List Nat}
    (path : PathType program home source keys indices target) : CanonicalPath program source indices target := by
  induction path with
  | nil => exact .nil _
  | cons head _ ih => exact .cons head ih

theorem CanonicalPath.append {source middle target : Ty} {first second : List Nat}
    (front : CanonicalPath program source first middle) (back : CanonicalPath program middle second target) :
    CanonicalPath program source (first ++ second) target := by
  induction front with
  | nil => exact back
  | cons head _ ih => exact .cons head (ih back)

theorem CanonicalPath.dataShape {source target : Ty} {indices : List Nat}
    (path : CanonicalPath program source indices target)
    (supported : StorageType program.target program.data source) (shape : target.DataShape) : source.DataShape := by
  cases supported with
  | data data => exact data
  | reference finite =>
    cases path with
    | nil => exact False.elim shape
    | cons head tail => cases head



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
  | reference (referent : Ty) {bound : Principal} : UsePermission data (.reference referent) bound
  | unique (referent : Ty) {bound : Principal} (allowed : Principal.affine.Accepts bound) :
      UsePermission data (.reference referent .unique) bound
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

/-- Positive structural/declaration evidence, never failure to find Copy.
An empty concrete array has no resident witness and remains duplicable. -/
inductive Nonduplicable (data : DataDeclarations) : Ty → Prop where
  | unique (referent : Ty) : Nonduplicable data (.reference referent .unique)
  | tupleHead {head : Ty} {tail : List Ty} (resident : Nonduplicable data head) :
      Nonduplicable data (.tuple head tail)
  | tupleTail {head type : Ty} {tail : List Ty} (member : type ∈ tail)
      (resident : Nonduplicable data type) : Nonduplicable data (.tuple head tail)
  | array {element : Ty} {length : Nat} (positive : 0 < length)
      (resident : Nonduplicable data element) : Nonduplicable data (.array element length)
  | restricted {identity : Nat} {declaration : DataDecl} {principal : Principal}
      (declared : data identity = some declaration) (restriction : declaration.restriction = some principal)
      (noncopy : principal = .affine ∨ principal = .exact) : Nonduplicable data (.nominal identity)
  | field {identity : Nat} {declaration : DataDecl} {schema : Fields} {field : Field}
      (declared : data identity = some declaration) (schemaMember : schema ∈ declaration.schemas)
      (fieldMember : field ∈ schema.residents) (resident : Nonduplicable data field.type) :
      Nonduplicable data (.nominal identity)

theorem Nonduplicable.not_duplicable {data : DataDeclarations} {type : Ty}
    (noncopy : Nonduplicable data type) : ¬ Duplicable data type := by
  induction noncopy with
  | unique => intro copy; cases copy with | unique _ allowed => exact allowed
  | tupleHead resident ih => intro copy; cases copy with | tuple first rest => exact ih first
  | tupleTail member resident ih => intro copy; cases copy with | tuple first rest => exact ih (rest _ member)
  | array positive resident ih =>
    intro copy
    cases copy with
    | array _ resident => exact ih resident
    | emptyArray => exact Nat.not_lt_zero _ positive
  | restricted declared restriction noncopy =>
    intro copy
    cases copy with
    | inferred other unrestricted fields =>
      cases Option.some.inj (declared.symm.trans other)
      simp_all
    | restricted other restricted fields permitted =>
      cases Option.some.inj (declared.symm.trans other)
      cases Option.some.inj (restriction.symm.trans restricted)
      rcases noncopy with same | same <;> cases same <;> exact permitted
  | field declared schemaMember fieldMember resident ih =>
    intro copy
    cases copy with
    | inferred other unrestricted fields =>
      cases Option.some.inj (declared.symm.trans other)
      exact ih (fields _ schemaMember _ fieldMember)
    | restricted other restricted fields permitted =>
      cases Option.some.inj (declared.symm.trans other)
      have accepts : ∀ p : Principal, p.Accepts .duplicable → p = .duplicable := by
        intro p; cases p <;> simp [Principal.Accepts]
      cases accepts _ permitted
      exact ih (fields _ schemaMember _ fieldMember)

/-- Shared-handle copying uses the same capability evidence as owned data. -/
theorem UsePermission.duplicable_reference_shared {data : DataDeclarations} {referent : Ty} {mode : BorrowMode}
    (copy : Duplicable data (.reference referent mode)) : mode = .shared := by
  cases mode with
  | shared => rfl
  | unique => exact False.elim ((Nonduplicable.unique referent).not_duplicable copy)

private theorem ownedChoice_list {α : Type} {copy noncopy : α → Prop} {values : List α}
    (choices : ∀ value ∈ values, copy value ∨ noncopy value) :
    (∀ value ∈ values, copy value) ∨ ∃ value ∈ values, noncopy value := by
  induction values with
  | nil => exact .inl (by simp)
  | cons head tail ih =>
    rcases choices head (by simp) with first | first
    · rcases ih (fun value member => choices value (by simp [member])) with rest | rest
      · exact .inl (by intro value member; rcases List.mem_cons.mp member with rfl | member; exact first; exact rest _ member)
      · obtain ⟨value, member, witness⟩ := rest
        exact .inr ⟨value, by simp [member], witness⟩
    · exact .inr ⟨head, by simp, first⟩

/-- Every finite data layout has an evidence-backed owned-use choice. Restriction
checks and resident witnesses, not proof-search failure, select transfer. -/
theorem FiniteLayout.owned_choice {target : Target} {data : DataDeclarations} {type : Ty}
    (finite : FiniteLayout target data type) : Duplicable data type ∨ Nonduplicable data type := by
  induction finite with
  | unit => exact .inl .unit
  | integer type => exact .inl (.integer type)
  | character => exact .inl .character
  | tuple first rest firstIH restIH =>
    rcases firstIH with copy | noncopy
    · rcases ownedChoice_list restIH with copies | witness
      · exact .inl (.tuple copy copies)
      · obtain ⟨type, member, noncopy⟩ := witness
        exact .inr (.tupleTail member noncopy)
    · exact .inr (.tupleHead noncopy)
  | @array element length resident size ih =>
    cases length with
    | zero => exact .inl (.emptyArray element)
    | succ length =>
      rcases ih with copy | noncopy
      · exact .inl (.array _ copy)
      · exact .inr (.array (Nat.zero_lt_succ _) noncopy)
  | @nominal identity declaration declared schemas fields ih =>
    have classified := ownedChoice_list (fun schema member => ownedChoice_list (ih schema member))
    rcases classified with copies | witness
    · cases restriction : declaration.restriction with
      | none => exact .inl (.inferred declared restriction copies)
      | some principal =>
        cases principal with
        | duplicable => exact .inl (.restricted declared restriction copies trivial)
        | affine => exact .inr (.restricted declared restriction (.inl rfl))
        | exact => exact .inr (.restricted declared restriction (.inr rfl))
    · obtain ⟨schema, schemaMember, field, fieldMember, noncopy⟩ := witness
      exact .inr (.field declared schemaMember fieldMember noncopy)

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
  /-- This is inert handle shape, not usable reference validity. -/
  | reference {referent : Ty} {mode : BorrowMode} (node : Nat) (finite : FiniteLayout program.target program.data referent) :
      ResidentTyped program .full (.reference node) (.reference referent mode)
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
  | reference node finite => exact ⟨.reference node finite, by simp [Value.initialized]⟩
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
/-- A logical resident coordinate, never a physical byte address. -/
structure Address where
  root : Root
  fields : List Nat
  deriving DecidableEq

/-- Different roots, or divergent fields below one root, cannot alias. -/
def Address.Apart (left right : Address) : Prop :=
  left.root ≠ right.root ∨ CoordinatesApart left.fields right.fields

/-- A runtime node retains its canonical target and immutable ancestry. Own
availability is independent of carrier location; ending changes only own. -/
structure Loan where
  target : Address
  parent : Option Nat
  own : Bool
  mode : BorrowMode := .shared


structure Environment where
  bindings : List (String × Root)
  store : Store
  nextRoot : Root
  loans : List Loan := []

namespace Environment

def empty : Environment := ⟨[], fun _ => none, 0, []⟩
def roots (environment : Environment) := environment.bindings.map Prod.snd

/-- Coarse mutation framing is not access authorization. Own permission and
mode select live unique targets; inactive history may name retired cells. -/
def UniqueRoot (environment : Environment) (root : Root) : Prop :=
  ∃ (node : Nat) (loan : Loan), environment.loans[node]? = some loan ∧ loan.own = true ∧
    loan.mode = .unique ∧ loan.target.root = root

def MutationRoot (environment : Environment) (root : Root) : Prop :=
  root ∈ environment.roots ∨ environment.UniqueRoot root

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

def bind (name : String) (resident : Value) (environment : Environment) : Environment :=
  { environment with
    bindings := (name, environment.nextRoot) :: environment.bindings
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

/-- Actual execution preserves names and frames cells outside incoming owners
and unique targets. Newly introduced authority originates in that footprint or
the fresh supply. Scoped fresh cells are retired; old vacancies never resurrect. -/
structure Environment.Evolution (before after : Environment) : Prop where
  bindings : after.bindings = before.bindings
  supply : before.nextRoot ≤ after.nextRoot
  frame : ∀ root, ¬ before.MutationRoot root → after.store root = before.store root
  authority : ∀ root, after.UniqueRoot root → before.MutationRoot root ∨ before.nextRoot ≤ root
  vacancies : ∀ root, root < before.nextRoot → before.store root = none → after.store root = none
  fresh : ∀ root, before.nextRoot ≤ root → after.store root = none

namespace Environment.Evolution

theorem absent {before after : Environment} (evolved : Evolution before after)
    (root : Root) (missing : before.store root = none) : after.store root = none := by
  by_cases old : root < before.nextRoot
  · exact evolved.vacancies root old missing
  · exact evolved.fresh root (Nat.le_of_not_gt old)

theorem refl (environment : Environment) (valid : environment.Valid) : Evolution environment environment := by
  refine ⟨rfl, Nat.le_refl _, fun _ _ => rfl, fun _ live => .inl (.inr live), fun _ _ missing => missing, ?_⟩
  intro root fresh
  cases found : environment.store root with
  | none => rfl
  | some value => exact False.elim (Nat.not_lt_of_ge fresh (valid.bounded root value found))

theorem trans {before middle after : Environment} (first : Evolution before middle)
    (rest : Evolution middle after) : Evolution before after := by
  refine ⟨rest.bindings.trans first.bindings, Nat.le_trans first.supply rest.supply, ?_, ?_, ?_, ?_⟩
  · intro root outside
    by_cases old : root < before.nextRoot
    · have hidden : ¬ middle.MutationRoot root := by
        intro member
        rcases member with named | live
        · exact outside (.inl (by simpa only [Environment.roots, first.bindings] using named))
        · rcases first.authority root live with member | fresh
          · exact outside member
          · exact Nat.not_lt_of_ge fresh old
      exact (rest.frame root hidden).trans (first.frame root outside)
    · have missing := first.fresh root (Nat.le_of_not_gt old)
      exact (rest.absent root missing).trans (missing.symm.trans (first.frame root outside))
  · intro root live
    rcases rest.authority root live with member | fresh
    · rcases member with named | live
      · exact .inl (.inl (by simpa only [Environment.roots, first.bindings] using named))
      · exact first.authority root live
    · exact .inr (Nat.le_trans first.supply fresh)
  · intro root old missing
    exact rest.absent root (first.vacancies root old missing)
  · intro root fresh
    exact rest.absent root (first.fresh root fresh)
end Environment.Evolution

namespace Environment

theorem retire_add (environment : Environment) (first rest : Nat) :
    (environment.retire first).retire rest = environment.retire (first + rest) := by
  cases environment with
  | mk bindings store nextRoot loans =>
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
  refine ⟨by simp [retire, evolved.bindings, bind], Nat.le_trans (Nat.le_succ _) evolved.supply, ?_, ?_, ?_, ?_⟩
  · intro root outside
    by_cases same : root = before.nextRoot
    · subst root
      rw [show (after.retire 1).store before.nextRoot = none by simp [retire, evolved.bindings, bind]]
      exact valid.fresh.symm
    · have hidden : ¬ (before.bind name value).MutationRoot root := by
        simpa [MutationRoot, UniqueRoot, roots, bind, same] using outside
      have framed := evolved.frame root hidden
      simpa [retire, evolved.bindings, bind, same] using framed
  · intro root live
    rcases evolved.authority root live with member | fresh
    · rcases member with named | live
      · have included : root = before.nextRoot ∨ root ∈ before.roots := by simpa [roots, bind] using named
        rcases included with same | named
        · exact .inr (Nat.le_of_eq same.symm)
        · exact .inl (.inl named)
      · exact .inl (.inr live)
    · exact .inr (Nat.le_trans (Nat.le_succ _) fresh)
  · intro root old missing
    have different := Nat.ne_of_lt old
    have still := evolved.vacancies root (Nat.lt_succ_of_lt old) (by simpa [bind, different] using missing)
    simpa [retire, evolved.bindings, bind, different] using still
  · intro root fresh
    by_cases same : root = before.nextRoot
    · subst root; simp [retire, evolved.bindings, bind]
    · have later : before.nextRoot + 1 ≤ root := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne fresh (Ne.symm same))
      have missing := evolved.fresh root later
      simpa [retire, evolved.bindings, bind, same] using missing

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
  refine ⟨rfl, evolved.supply, ?_, ?_, evolved.vacancies, evolved.fresh⟩
  · intro root outside
    exact evolved.frame root (by simpa [MutationRoot, UniqueRoot, roots, hide] using (fun live => outside (.inr live)))
  · intro root live
    rcases evolved.authority root live with member | fresh
    · rcases member with named | live
      · simp [roots, hide] at named
      · exact .inl (.inr live)
    · exact .inr fresh

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
  | reference referent => exact .reference referent
  | unique referent allowed => exact .unique referent (allowed.trans accepted)
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
  | .reference node => .reference node
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
  | .unit | .integer _ _ | .character _ | .reference _ => [[]]
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
  | vacant | unit | integer | character | reference => simp [Value.children]
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
  | reference node => simpa only [Value.destructionTrace, List.nil_append] using (Value.Destroys.resident (by simp) allowed (.nil 0))
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
  | vacant | unit | integer | character | reference => simp [Value.destructionTrace]
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

/-- Resolve source keys once, checking every actual child slot. A selected
vacancy is allowed; no projection can descend through it. -/
def Value.resolvePath (program : Program) (value : Value) : List FieldKey → Option (List Nat)
  | [] => some []
  | key :: rest => do
      let index ← value.fieldIndex program key
      let child ← value.children[index]?
      let indices ← child.resolvePath program rest
      some (index :: indices)

def Value.readIndices (value : Value) : List Nat → Option Value
  | [] => some value
  | index :: rest => do
      let child ← value.children[index]?
      child.readIndices rest

def Value.writeIndices (value : Value) (indices : List Nat) (replacement : Value) : Option Value :=
  match indices with
  | [] => some replacement
  | index :: rest => do
      let child ← value.children[index]?
      let updated ← child.writeIndices rest replacement
      value.replaceChild index updated

/-- Owned temporary projection has no stored root to resolve. -/
def Value.takeField (program : Program) (value : Value) (key : FieldKey) : Option Value := do
  let index ← value.fieldIndex program key
  let _ ← value.children[index]?
  value.replaceChild index .vacant

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
  | reference (node : Nat) (referent : Ty) {mode : BorrowMode} : HeadType program (.reference node) (.reference referent mode) []
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

def selectArm {α : Type} (value : Value) : List (Pattern × α) → Option (List (String × Value) × α)
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
inductive ConsumesArm (program : Program) (value : Value) {α : Type} : List (Pattern × α) → BindingValues → α → Prop where
  | hit {pattern : Pattern} {body : α} {rest : List (Pattern × α)} {bindings : BindingValues} {trace : List (List Nat)}
      (matched : pattern.matchValue value = some bindings) (consumed : Pattern.Consumes program pattern value bindings trace) :
      ConsumesArm program value ((pattern, body) :: rest) bindings body
  | miss {pattern : Pattern} {body result : α} {rest : List (Pattern × α)} {bindings : BindingValues}
      (missed : pattern.matchValue value = none) (selected : ConsumesArm program value rest bindings result) :
      ConsumesArm program value ((pattern, body) :: rest) bindings result

theorem Pattern.Consumes.binder_result {name : String} {value : Value} {bindings : BindingValues} {trace : List (List Nat)}
    (consumed : Pattern.Consumes program (.binder name) value bindings trace) :
    bindings = [(name, value)] ∧ trace = [] := by cases consumed; exact ⟨rfl, rfl⟩

theorem ConsumesArm.matches {α : Type} {value : Value} {arms : List (Pattern × α)} {bindings : BindingValues} {body : α}
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

namespace Environment

/-- Lexical selection and canonical field resolution happen once in this store. -/
def resolvePlace (program : Program) (place : Place) (environment : Environment) : Option Address := do
  let root ← lookup place.root environment.bindings
  let parent ← environment.store root
  let indices ← parent.resolvePath program place.fields
  some ⟨root, indices⟩

/-- Raw selected storage, including vacancy, for replacement disposal. -/
def «at» (address : Address) (environment : Environment) : Option Value := do
  let parent ← environment.store address.root
  parent.readIndices address.fields

/-- Owned access additionally requires the entire selected subtree initialized. -/
def readAddress (address : Address) (environment : Environment) : Option Value := do
  let resident ← environment.at address
  if resident.initialized then some resident else none

/-- Even whole-root restoration requires an allocated cell, never a missing root. -/
def writeAddress (address : Address) (replacement : Value) (environment : Environment) : Option Environment := do
  let parent ← environment.store address.root
  let updated ← parent.writeIndices address.fields replacement
  some (environment.put address.root updated)

def takeAddress (address : Address) (environment : Environment) : Option (Value × Environment) := do
  let value ← environment.readAddress address
  let after ← environment.writeAddress address .vacant
  some (value, after)

end Environment

mutual
/-- No reference bits at any aggregate depth. -/
def Value.ReferenceFree : Value → Prop
  | .reference _ => False
  | .tuple head tail => head.ReferenceFree ∧ valuesReferenceFree tail
  | .array values | .nominal _ _ values => valuesReferenceFree values
  | _ => True

def valuesReferenceFree : List Value → Prop
  | [] => True
  | value :: values => value.ReferenceFree ∧ valuesReferenceFree values
end

/-- Supported data shape plus actual resident typing rules out every reference
bit. Unknown nominal names alone do not supply this conclusion. -/
theorem ResidentTyped.referenceFree {state : Initialization} {value : Value} {type : Ty}
    (typed : ResidentTyped program state value type) (shape : type.DataShape) : value.ReferenceFree := by
  induction typed using ResidentTyped.rec
    (motive_2 := fun states values types _ => typesDataShape types → valuesReferenceFree values) with
  | vacant | unit | integer | character => trivial
  | uncertain actual permission ih => exact ih shape
  | reference node finite => exact False.elim shape
  | tuple head tail present headIH tailIH => exact ⟨headIH shape.1, tailIH shape.2⟩
  | @array state values element length residents elementValid size present ih =>
    apply ih
    apply (typesDataShape_iff _).mpr
    intro type included
    cases List.eq_of_mem_replicate included
    exact shape
  | @nominal state identity tag declaration schema values declared chosen finite residents present ih =>
    apply ih
    apply (typesDataShape_iff _).mpr
    intro type included
    obtain ⟨field, member, equal⟩ := List.mem_map.mp included
    cases equal
    have schemaMember : schema ∈ declaration.schemas := by
      cases declaration with
      | mk home visibility shape restriction =>
        cases shape <;> cases tag <;> simp_all [DataDecl.constructor, DataDecl.schemas]
        exact List.mem_of_getElem? chosen
    cases finite with
    | nominal found schemas fields =>
      cases Option.some.inj (found.symm.trans declared)
      exact (fields schema schemaMember field member).dataShape
  | nil => trivial
  | cons head tail headIH tailIH =>
    rename_i shape
    exact ⟨headIH shape.1, tailIH shape.2⟩


namespace Environment

/-- Resolution carries authority together with the canonical target. -/
structure ResolvedAccess where
  address : Address
  parent : Option Nat

/-- Retained parent records supply ancestry, never their retired own permission. -/
inductive Supported (loans : List Loan) : Nat → Prop where
  | root {node : Nat} {loan : Loan} (found : loans[node]? = some loan)
      (original : loan.parent = none) : Supported loans node
  | child {node parent : Nat} {loan ancestor : Loan}
      (found : loans[node]? = some loan) (derived : loan.parent = some parent)
      (older : parent < node) (parentFound : loans[parent]? = some ancestor)
      (sameRoot : loan.target.root = ancestor.target.root)
      (subaddress : ancestor.target.fields.IsPrefix loan.target.fields)
      (support : Supported loans parent) : Supported loans node

inductive Derived (environment : Environment) : Nat → Nat → Prop where
  | same (node : Nat) : Derived environment node node
  | child {node parent ancestor : Nat} {loan : Loan}
      (found : environment.loans[node]? = some loan) (derived : loan.parent = some parent)
      (rest : Derived environment parent ancestor) : Derived environment node ancestor

/-- Shared/shared overlap is permitted. Selected ancestry conveys authority;
overlapping descendants or independent unique permissions exclude the access. -/
def Permits (mode : BorrowMode) (parent : Option Nat) (address : Address) (environment : Environment) : Prop :=
  ∀ (node : Nat) (loan : Loan), environment.loans[node]? = some loan → loan.own = true →
    (mode = .shared ∧ loan.mode = .shared) ∨
    (∃ selected, parent = some selected ∧ environment.Derived selected node) ∨ address.Apart loan.target

def Usable (node : Nat) (environment : Environment) : Prop :=
  ∃ loan, environment.loans[node]? = some loan ∧ loan.own = true ∧ Supported environment.loans node

def Authorizes (mode : BorrowMode) (access : ResolvedAccess) (environment : Environment) : Prop :=
  match access.parent with
  | none => access.address.root ∈ environment.roots
  | some node => ∃ loan, environment.loans[node]? = some loan ∧ loan.own = true ∧
      Supported environment.loans node ∧ access.address.root = loan.target.root ∧
      loan.target.fields.IsPrefix access.address.fields ∧ (mode = .unique → loan.mode = .unique)

/-- Reading or borrowing through a handle requires its whole target restored.
Masked address resolution itself deliberately does not impose this condition. -/
def AccessReady (access : ResolvedAccess) (environment : Environment) : Prop :=
  ∀ node loan, access.parent = some node → environment.loans[node]? = some loan →
    ∃ value, environment.readAddress loan.target = some value

/-- Shared descendants reserve their own exact targets. Broader inactive parent
regions impose no additional reservation; their address/ancestry records remain. -/
def OwnerFree (address : Address) (environment : Environment) : Prop :=
  ∀ (node : Nat) (loan : Loan), environment.loans[node]? = some loan → loan.own = true → address.Apart loan.target

/-- Normal use and ending require the authoritative referent to be restored.
Low-level access authority stays separate so a unique handle can fill its hole. -/
def Restored (node : Nat) (environment : Environment) : Prop :=
  ∀ loan, environment.loans[node]? = some loan → loan.own = true →
    ∃ value, environment.readAddress loan.target = some value

def ResultUsable (value : Value) (environment : Environment) : Prop :=
  match value with
  | .reference node => environment.Usable node ∧ environment.Restored node
  | value => value.ReferenceFree

/-- Reuse the owner resolver for the handle, then the same canonical field
producer for the referent. No owned copy of the whole referent is performed. -/
def resolveAccess (program : Program) (place : AccessPlace) (environment : Environment) : Option ResolvedAccess := do
  match place with
  | .owner place =>
      let address ← environment.resolvePlace program place
      some ⟨address, none⟩
  | .dereference reference fields =>
      let carrier ← environment.resolvePlace program reference
      let .reference node ← environment.readAddress carrier | none
      let loan ← environment.loans[node]?
      if loan.own then
        let resident ← environment.at loan.target
        let indices ← resident.resolvePath program fields
        some ⟨⟨loan.target.root, loan.target.fields ++ indices⟩, some node⟩
      else none

def addLoan (access : ResolvedAccess) (mode : BorrowMode) (environment : Environment) : Environment :=
  { environment with loans := environment.loans ++ [⟨access.address, access.parent, true, mode⟩] }

/-- Low-level loan-table transition. Ordinary ending uses checked endSlot or
Disposes.reference; this operation alone does not authorize ending a handle. -/
def endOwn (node : Nat) (environment : Environment) : Option Environment := do
  let _ ← environment.loans[node]?
  some { environment with loans := environment.loans.modify node fun loan => { loan with own := false } }

/-- Ordinary slot ending checks the authoritative target before changing own.
Slot indices are checked by the source producer and survive source shadowing. -/
def endSlot (slot : Nat) (environment : Environment) : Option Environment := do
  let binding ← environment.bindings[slot]?
  let .reference node ← environment.store binding.2 | none
  let loan ← environment.loans[node]?
  if loan.own && !(environment.readAddress loan.target).isSome then none
  else environment.endOwn node

/-- Successful ordinary ending consumes restored-target evidence from the pre-state. -/
theorem endSlot_checked {before after : Environment} {slot : Nat}
    (ended : before.endSlot slot = some after) :
    ∃ binding node, before.bindings[slot]? = some binding ∧
      before.store binding.2 = some (.reference node) ∧
      before.Restored node ∧ before.endOwn node = some after := by
  simp only [endSlot, Bind.bind, Option.bind_eq_some_iff] at ended
  obtain ⟨binding, selected, value, stored, ended⟩ := ended
  cases value <;> try cases ended
  case reference node =>
    simp only [Option.bind_eq_some_iff] at ended
    obtain ⟨loan, found, ended⟩ := ended
    split at ended
    · cases ended
    · rename_i permitted
      refine ⟨binding, node, selected, stored, ?_, ended⟩
      intro actual actualFound own
      have same := Option.some.inj (found.symm.trans actualFound)
      subst actual
      cases read : before.readAddress loan.target with
      | none => simp [own, read] at permitted
      | some resident => exact ⟨resident, rfl⟩

inductive Copies : Environment → Value → Value → Environment → Prop where
  | data {environment : Environment} {value : Value} (plain : value.ReferenceFree) :
      Copies environment value value environment
  | reference {environment : Environment} {node : Nat} {loan : Loan}
      (found : environment.loans[node]? = some loan) (shared : loan.mode = .shared)
      (allowed : environment.Usable node) :
      Copies environment (.reference node) (.reference environment.loans.length)
        (environment.addLoan ⟨loan.target, some node⟩ .shared)

/-- Disposition changes the real node table as well as producing logical trace.
Pure structural destruction is used only for reference-free owned data. -/
inductive Disposes (program : Program) : Environment → Value → Environment → Prop where
  | data {environment : Environment} {value : Value} {trace : List (List Nat)}
      (plain : value.ReferenceFree) (destroyed : value.Destroys program trace .vacant) :
      Disposes program environment value environment
  | reference {environment after : Environment} {node : Nat}
      (ready : environment.Restored node)
      (ended : environment.endOwn node = some after) :
      Disposes program environment (.reference node) after


end Environment

/-- Exact storage equality deliberately leaves real loan bookkeeping observable. -/
structure Environment.SameStorage (before after : Environment) : Prop where
  bindings : after.bindings = before.bindings
  store : after.store = before.store
  supply : after.nextRoot = before.nextRoot

theorem Environment.Disposes.storage {before after : Environment} {value : Value}
    (disposed : Disposes program before value after) : before.SameStorage after := by
  cases disposed with
  | data => exact ⟨rfl, rfl, rfl⟩
  | reference _ ended =>
    simp only [Environment.endOwn, Bind.bind, Option.bind_eq_some_iff, Option.some.injEq] at ended
    obtain ⟨_, _, rfl⟩ := ended
    exact ⟨rfl, rfl, rfl⟩

/-- This is only a logical-trace projection, never permission to discard live bits
without executing the node transition. The data constructor requires reference freedom. -/
theorem Environment.Disposes.logical {before after : Environment} {value : Value}
    (disposed : Disposes program before value after) : value.Destroys program value.destructionTrace .vacant := by
  cases disposed with
  | data plain destroyed => simpa only [destroyed.result_order.2] using destroyed
  | @reference after node _ ended =>
    simpa only [Value.destructionTrace, List.nil_append] using
      (Value.Destroys.resident (program := program) (by intro impossible; cases impossible)
        (.owned (.reference node (referent := .unit) .unit) (.reference .unit)) (.nil 0))

inductive DisposesRoots (program : Program) : Environment → List Root → List (Root × List Nat) → Environment → Prop where
  | nil {environment : Environment} : DisposesRoots program environment [] [] environment
  | cons {before middle after : Environment} {root : Root} {roots : List Root}
      {value : Value} {trace : List (Root × List Nat)}
      (found : before.store root = some value) (free : before.OwnerFree ⟨root, []⟩)
      (head : Environment.Disposes program before value middle)
      (tail : DisposesRoots program middle roots trace after) :
      DisposesRoots program before (root :: roots)
        (value.destructionTrace.map (fun path => (root, path)) ++ trace) after

theorem DisposesRoots.storage {before after : Environment} {roots : List Root} {trace : List (Root × List Nat)}
    (disposed : DisposesRoots program before roots trace after) : before.SameStorage after := by
  induction disposed with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons found free head tail ih =>
    exact ⟨ih.bindings.trans head.storage.bindings, ih.store.trans head.storage.store,
      ih.supply.trans head.storage.supply⟩

theorem DisposesRoots.logical {before after : Environment} {roots : List Root} {trace : List (Root × List Nat)}
    (disposed : DisposesRoots program before roots trace after) : DestroysRoots program before.store roots trace := by
  induction disposed with
  | nil => exact .nil
  | cons found free head tail ih =>
    rw [head.storage.store] at ih
    exact .cons found head.logical ih
/-- The former pure destruction is executable only for reference-free cells and
source-derived owner permission; this is a specialization of the real transition. -/
theorem DisposesRoots.of_data {environment : Environment} {roots : List Root} {trace : List (Root × List Nat)}
    (destroyed : DestroysRoots program environment.store roots trace)
    (plain : ∀ root ∈ roots, ∀ value, environment.store root = some value → value.ReferenceFree)
    (free : ∀ root ∈ roots, environment.OwnerFree ⟨root, []⟩) :
    DisposesRoots program environment roots trace environment := by
  induction destroyed with
  | nil => exact .nil
  | @cons root roots value first rest found head tail ih =>
    rw [head.result_order.2]
    exact .cons found (free root (by simp)) (.data (plain root (by simp) value found) head)
      (ih (fun other member => plain other (by simp [member])) (fun other member => free other (by simp [member])))

inductive Cleans (program : Program) (count : Nat) (before : Environment) : List (Root × List Nat) → Environment → Prop where
  | retire {disposed : Environment} {trace : List (Root × List Nat)}
      (destroyed : DisposesRoots program before ((before.bindings.take count).map Prod.snd) trace disposed) :
      Cleans program count before trace (disposed.retire count)

theorem Cleans.suffix {count : Nat} {before after : Environment} {trace : List (Root × List Nat)}
    (executed : Cleans program count before trace after) : (before.retire count).SameStorage after := by
  cases executed with
  | retire destroyed =>
    refine ⟨by simp [Environment.retire, destroyed.storage.bindings], ?_, destroyed.storage.supply⟩
    funext root
    simp only [Environment.retire, destroyed.storage.bindings, destroyed.storage.store]

theorem Cleans.order {count : Nat} {before after : Environment} {trace : List (Root × List Nat)}
    (executed : Cleans program count before trace after) :
    cleanupTrace before.store ((before.bindings.take count).map Prod.snd) = some trace := by
  cases executed with | retire destroyed => exact destroyed.logical.order

theorem Cleans.trace_scoped {count : Nat} {before after : Environment} {trace : List (Root × List Nat)}
    (executed : Cleans program count before trace after) :
    ∀ event ∈ trace, event.1 ∈ (before.bindings.take count).map Prod.snd := by
  cases executed with | retire destroyed => exact destroyed.logical.scoped

theorem Cleans.exactly_once {count : Nat} {before after : Environment} {trace : List (Root × List Nat)}
    (executed : Cleans program count before trace after) (valid : before.Valid) : trace.Nodup := by
  cases executed with
  | retire destroyed =>
    apply destroyed.logical.exactly_once
    simpa only [Environment.roots, List.map_take, List.Nodup] using (valid.distinct.take (i := count))

/-- Retirement invalidates cleaned identities; mere own ending retains the bits. -/
theorem Cleans.retired {count : Nat} {before after : Environment} {trace : List (Root × List Nat)}
    (executed : Cleans program count before trace after) :
    ∀ root ∈ (before.bindings.take count).map Prod.snd, after.store root = none := by
  rw [executed.suffix.store]
  exact fun _ member => before.retire_absent count member

/-- The caller-store frame is exact even when cleanup changes node ownership. -/
theorem Cleans.frame {count : Nat} {before after : Environment} {trace : List (Root × List Nat)}
    (executed : Cleans program count before trace after) :
    ∀ root, root ∉ (before.bindings.take count).map Prod.snd → after.store root = before.store root := by
  rw [executed.suffix.store]
  exact fun _ outside => before.retire_frame count outside


/-- A source-origin disjointness proof is reflected, not assumed, at runtime.
Different formal inputs may alias; equal input bases retain field separation. -/
def Origin.Apart (left right : Origin) : Prop :=
  match left.base, right.base with
  | .binder first, .binder second => first ≠ second ∨ CoordinatesApart left.fields right.fields
  | .binder _, .input _ | .input _, .binder _ => True
  | .input first, .input second => first = second ∧ CoordinatesApart left.fields right.fields

def Origin.Within (child parent : Origin) : Prop :=
  child.base = parent.base ∧ parent.fields.IsPrefix child.fields

def Origin.extend (origin : Origin) (indices : List Nat) : Origin :=
  { origin with fields := origin.fields ++ indices }

def Origin.Bounded (origin : Origin) (context : Context) : Prop :=
  match origin.base with
  | .binder identity => identity < context.nextBinder
  | .input identity => identity < context.inputCount

namespace Context

def empty : Context := ⟨[], fun _ => none, [], 0, 0⟩
def erase (context : Context) : List (String × BindingType) :=
  context.bindings.map fun binding => (binding.1, binding.2.toBindingType)

/-- Update the one authoritative mask at a canonical target. Type, mutability,
binder identity and carrier metadata remain the storage root's metadata. -/
def writeTarget (context : Context) (origin : Origin) (next : Initialization) : Context :=
  { context with storage := fun base => if base = origin.base then
      (context.storage base).map (fun slot => { slot with initialization := slot.initialization.write origin.fields next })
    else context.storage base }

theorem writeTarget_metadata (context : Context) (origin : Origin) (next : Initialization)
    {slot : Slot} (stored : context.storage origin.base = some slot) :
    ∃ updated, (context.writeTarget origin next).storage origin.base = some updated ∧ updated.metadata = slot.metadata :=
  ⟨{ slot with initialization := slot.initialization.write origin.fields next }, by simp [writeTarget, stored], rfl⟩


/-- Commit an owner operation back to stable storage identities. The lexical
view is consumed once; hidden storage is retained. -/
def withSlots (context : Context) (slots : List (String × Slot)) : Context :=
  { context with
    names := slots.map (fun binding => (binding.1, binding.2.binder))
    storage := fun origin =>
      match origin with
      | .binder binder =>
          match slots.find? (fun binding => binding.2.binder == binder) with
          | some binding => some binding.2
          | none => context.storage origin
      | .input _ => context.storage origin }

/-- Finite semantic support of the proof interpretation. Gaps below nextBinder
need no runtime root, so source supply joins never fabricate allocations. -/
def MentionsBinder (context : Context) (binder : Nat) : Prop :=
  (∃ slot, context.storage (.binder binder) = some slot) ∨
    ∃ (node : Nat) (loan : SourceLoan), context.loans[node]? = some loan ∧ loan.target.base = .binder binder


/-- Ancestry comes from actual retained source loan records, not type equality. -/
inductive Derived (context : Context) : Nat → Nat → Prop where
  | same (node : Nat) : context.Derived node node
  | child {node parent origin : Nat} {loan : SourceLoan}
      (found : context.loans[node]? = some loan) (derived : loan.parent = some parent)
      (ancestor : context.Derived parent origin) : context.Derived node origin

def Permits (context : Context) (mode : BorrowMode) (parent : Option Nat) (origin : Origin) : Prop :=
  ∀ (node : Nat) (loan : SourceLoan), context.loans[node]? = some loan → loan.own = true →
    (mode = .shared ∧ loan.mode = .shared) ∨
    (∃ selected, parent = some selected ∧ context.Derived selected node) ∨ origin.Apart loan.target
/-- A canonical binder target is typed from authoritative root storage. The selected
mask is obtained by Access, never retained in a loan record. Inputs remain external. -/
def Target (program : Program) (context : Context) (origin : Origin) (referent : Ty) : Prop :=
  match origin.base with
  | .binder binder => ∃ slot, context.storage (.binder binder) = some slot ∧
      CanonicalPath program slot.type origin.fields referent ∧
      ∃ state, slot.initialization.Access origin.fields state
  | .input _ => True

/-- Readiness is a query of root storage, not a per-reference initialization mask.
External inputs are accounted for separately by runtime input correspondence. -/
def Ready (context : Context) (origin : Origin) : Prop :=
  match origin.base with
  | .binder binder => ∃ slot state, context.storage (.binder binder) = some slot ∧
      slot.initialization.Access origin.fields state ∧ state.Complete
  | .input _ => True

def SourceTarget (program : Program) (context : Context) (loan : SourceLoan) : Prop :=
  context.Target program loan.target loan.referent ∧
  (loan.mode = .shared → context.Ready loan.target) ∧
  (∀ input, loan.target.base = .input input → loan.mode = .shared)

/-- Reads and borrows require the entire parent target, not merely a complete child.
Restoration uses masked access without this operation-specific prerequisite. -/
def AccessReady (context : Context) (target : Origin) (parent : Option Nat) : Prop :=
  context.Ready target ∧ ∀ node loan, parent = some node → context.loans[node]? = some loan →
    context.Ready loan.target

theorem SourceTarget.storage_congr {before after : Context} {loan : SourceLoan}
    (target : before.SourceTarget program loan)
    (same : after.storage loan.target.base = before.storage loan.target.base) : after.SourceTarget program loan := by
  rcases loan with ⟨⟨base, fields⟩, referent, parent, own, mode⟩
  cases base <;> simpa only [Context.SourceTarget, Context.Target, Context.Ready, same] using target

def Free (context : Context) (origin : Origin) : Prop :=
  ∀ (node : Nat) (loan : SourceLoan), context.loans[node]? = some loan → loan.own = true → origin.Apart loan.target

def Own (context : Context) (node : Nat) : Prop :=
  ∃ loan, context.loans[node]? = some loan ∧ loan.own = true


def Restored (context : Context) (node : Nat) : Prop :=
  ∀ loan, context.loans[node]? = some loan → loan.own = true → context.Ready loan.target

def endOwn (context : Context) (node : Nat) : Context :=
  { context with loans := context.loans.modify node fun loan => { loan with own := false } }

def dispose (context : Context) (reference : Option Nat) : Context :=
  match reference with
  | none => context
  | some node => context.endOwn node

def borrow (context : Context) (target : Origin) (referent : Ty) (parent : Option Nat) (mode : BorrowMode) : Context :=
  { context with loans := context.loans ++ [⟨target, referent, parent, true, mode⟩] }

def bind (context : Context) (name : String) (mutable : Bool) (result : ResultType) : Context :=
  { context with
    names := (name, context.nextBinder) :: context.names
    storage := fun origin => if origin = .binder context.nextBinder then
      some ⟨⟨result.type, mutable, .full⟩, context.nextBinder, result.reference⟩
      else context.storage origin
    nextBinder := context.nextBinder + 1 }

def hide (context : Context) : Context := { context with names := [] }

def retire (context : Context) (count : Nat) : Context :=
  { context with
    names := context.names.drop count
    storage := fun origin => match origin with
      | .binder binder => if binder ∈ (context.names.take count).map Prod.snd then none else context.storage origin
      | .input _ => context.storage origin }

/-- Node history and binder supplies are never rewound at scope exit. -/
def disposeSlots (context : Context) (slots : List (String × Slot)) : Context :=
  slots.foldl (fun current slot => current.dispose slot.2.reference) context

def cleanup (context : Context) (count : Nat) : Context :=
  (context.disposeSlots (context.bindings.take count)).retire count

structure WellFormed (program : Program) (context : Context) : Prop where
  distinct : (context.bindings.map (fun binding => binding.2.binder)).Nodup
  supported : ∀ binding ∈ context.bindings, StorageType program.target program.data binding.2.type
  slots : ∀ binding ∈ context.bindings, binding.2.binder < context.nextBinder ∧
    ∀ node, binding.2.reference = some node → ∃ loan, context.loans[node]? = some loan ∧
      binding.2.type = .reference loan.referent loan.mode
  targets : ∀ (node : Nat) (loan : SourceLoan), context.loans[node]? = some loan →
    loan.target.Bounded context ∧ FiniteLayout program.target program.data loan.referent
  parents : ∀ (node : Nat) (loan : SourceLoan) (parent : Nat), context.loans[node]? = some loan →
    loan.parent = some parent → parent < node ∧ ∃ ancestor, context.loans[parent]? = some ancestor ∧
      loan.target.Within ancestor.target
  named : ∀ entry ∈ context.names, ∃ slot, context.storage (.binder entry.2) = some slot
  allocated : ∀ binder slot, context.storage (.binder binder) = some slot →
    slot.binder = binder ∧ binder < context.nextBinder ∧
    StorageType program.target program.data slot.type ∧
    ∀ node, slot.reference = some node → ∃ loan, context.loans[node]? = some loan ∧
      slot.type = .reference loan.referent loan.mode
  parentModes : ∀ (node : Nat) (loan : SourceLoan) (parent : Nat) (ancestor : SourceLoan),
    context.loans[node]? = some loan → loan.parent = some parent → context.loans[parent]? = some ancestor →
    loan.mode = .unique → ancestor.mode = .unique

theorem WellFormed.member_stored {context : Context} (valid : context.WellFormed program)
    (binding : String × Slot) (member : binding ∈ context.bindings) :
    context.storage (.binder binding.2.binder) = some binding.2 := by
  obtain ⟨entry, _, found⟩ := List.mem_filterMap.mp member
  obtain ⟨slot, stored, same⟩ := Option.map_eq_some_iff.mp found
  cases same
  rw [(valid.allocated entry.2 slot stored).1]
  exact stored

theorem WellFormed.member_known {context : Context} (valid : context.WellFormed program)
    (binding : String × Slot) (member : binding ∈ context.bindings) :
    context.MentionsBinder binding.2.binder :=
  .inl ⟨binding.2, valid.member_stored binding member⟩

private theorem filterMap_congr_mem {α β : Type} (entries : List α) (left right : α → Option β)
    (same : ∀ entry ∈ entries, left entry = right entry) :
    entries.filterMap left = entries.filterMap right := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.filterMap_cons, same entry (by simp), ih (fun other member => same other (by simp [member]))]

theorem WellFormed.bindings_binders {context : Context} (valid : context.WellFormed program) :
    context.bindings.map (fun binding => binding.2.binder) = context.names.map Prod.snd := by
  unfold Context.bindings
  rw [List.map_filterMap]
  rw [← List.filterMap_eq_map]
  apply filterMap_congr_mem
  intro entry member
  obtain ⟨slot, found⟩ := valid.named entry member
  simp [found, (valid.allocated entry.2 slot found).1]

theorem WellFormed.bindings_bind {context : Context} (valid : context.WellFormed program)
    (name : String) (mutable : Bool) (result : ResultType) :
    (context.bind name mutable result).bindings =
      (name, ⟨⟨result.type, mutable, .full⟩, context.nextBinder, result.reference⟩) :: context.bindings := by
  simp only [Context.bindings, Context.bind, List.filterMap_cons, ↓reduceIte, Option.map_some]
  congr 1
  apply filterMap_congr_mem
  intro entry member
  obtain ⟨slot, found⟩ := valid.named entry member
  have different : OriginBase.binder entry.2 ≠ .binder context.nextBinder := by
    intro equal
    have same := OriginBase.binder.inj equal
    exact Nat.ne_of_lt (valid.allocated entry.2 slot found).2.1 same
  simp [different]

theorem Derived.unique {context : Context} {node ancestor : Nat} {loan parentLoan : SourceLoan}
    (derived : context.Derived node ancestor) (valid : context.WellFormed program)
    (found : context.loans[node]? = some loan) (ancestorFound : context.loans[ancestor]? = some parentLoan)
    (unique : loan.mode = .unique) : parentLoan.mode = .unique := by
  induction derived generalizing loan with
  | same => cases Option.some.inj (found.symm.trans ancestorFound); exact unique
  | @child node parent ancestor current currentFound parentEq rest ih =>
    cases Option.some.inj (currentFound.symm.trans found)
    obtain ⟨_, parentRecord, parentFound, _⟩ := valid.parents node current parent currentFound parentEq
    exact ih parentFound ancestorFound (valid.parentModes node current parent parentRecord currentFound parentEq parentFound unique)

end Context

def Origin.Known (origin : Origin) (context : Context) : Prop :=
  match origin.base with
  | .binder identity => context.MentionsBinder identity
  | .input identity => identity < context.inputCount

theorem Context.WellFormed.loanKnown {context : Context} (valid : context.WellFormed program)
    {node : Nat} {loan : SourceLoan} (found : context.loans[node]? = some loan) : loan.target.Known context := by
  cases base : loan.target.base with
  | binder identity =>
    change (match loan.target.base with | .binder identity => context.MentionsBinder identity | .input identity => identity < context.inputCount)
    rw [base]
    exact .inr ⟨node, loan, found, base⟩
  | input identity => simpa [Origin.Known, Origin.Bounded, base] using (valid.targets _ _ found).1

namespace Context

theorem endOwn_found (context : Context) (ended : Nat) {node : Nat} {loan : SourceLoan}
    (found : context.loans[node]? = some loan) :
    (context.endOwn ended).loans[node]? = some { loan with own := if ended = node then false else loan.own } := by
  simp only [endOwn, List.getElem?_modify, found]
  split <;> rfl

theorem endOwn_original {context : Context} {ended node : Nat} {loan : SourceLoan}
    (found : (context.endOwn ended).loans[node]? = some loan) :
    ∃ original, context.loans[node]? = some original ∧
      loan = { original with own := if ended = node then false else original.own } := by
  change (context.loans.modify ended fun loan => { loan with own := false })[node]? = some loan at found
  rw [List.getElem?_modify] at found
  obtain ⟨original, found, equal⟩ := Option.map_eq_some_iff.mp found
  refine ⟨original, found, ?_⟩
  cases equal
  split <;> rfl

theorem endOwn_mentions (context : Context) (ended binder : Nat) :
    (context.endOwn ended).MentionsBinder binder ↔ context.MentionsBinder binder := by
  constructor
  · rintro (slot | ⟨node, loan, found, base⟩)
    · exact .inl slot
    · obtain ⟨original, originalFound, rfl⟩ := endOwn_original found
      exact .inr ⟨node, original, originalFound, base⟩
  · rintro (slot | ⟨node, loan, found, base⟩)
    · exact .inl slot
    · exact .inr ⟨node, _, context.endOwn_found ended found, base⟩

theorem WellFormed.endOwn {context : Context} (valid : context.WellFormed program) (ended : Nat) :
    (context.endOwn ended).WellFormed program := by
  refine { valid with slots := ?_, targets := ?_, parents := ?_, allocated := ?_, parentModes := ?_ }
  · intro binding member
    obtain ⟨bound, reference⟩ := valid.slots binding member
    refine ⟨bound, ?_⟩
    intro node selected
    obtain ⟨loan, found, type⟩ := reference node selected
    exact ⟨_, context.endOwn_found ended found, type⟩
  · intro node loan found
    obtain ⟨original, originalFound, rfl⟩ := endOwn_original found
    exact valid.targets node original originalFound
  · intro node loan parent found derived
    obtain ⟨original, originalFound, rfl⟩ := endOwn_original found
    obtain ⟨older, ancestor, parentFound, within⟩ := valid.parents _ _ _ originalFound derived
    exact ⟨older, _, context.endOwn_found ended parentFound, within⟩
  · intro binder slot stored
    obtain ⟨identity, bound, supported, reference⟩ := valid.allocated binder slot stored
    refine ⟨identity, bound, supported, ?_⟩
    intro node selected
    obtain ⟨loan, found, type⟩ := reference node selected
    exact ⟨_, context.endOwn_found ended found, type⟩
  · intro node loan parent ancestor found derived parentFound unique
    obtain ⟨old, oldFound, rfl⟩ := endOwn_original found
    obtain ⟨oldParent, oldParentFound, rfl⟩ := endOwn_original parentFound
    exact valid.parentModes node old parent oldParent oldFound derived oldParentFound unique

end Context

namespace Context

theorem borrow_found {context : Context} {target : Origin} {referent : Ty} {parent : Option Nat} {mode : BorrowMode}
    {node : Nat} {loan : SourceLoan} (found : context.loans[node]? = some loan) :
    (context.borrow target referent parent mode).loans[node]? = some loan := by
  exact List.getElem?_append_left ((List.getElem?_eq_some_iff.mp found).1) |>.trans found

theorem borrow_last (context : Context) (target : Origin) (referent : Ty) (parent : Option Nat) (mode : BorrowMode) :
    (context.borrow target referent parent mode).loans[context.loans.length]? = some ⟨target, referent, parent, true, mode⟩ := by
  simp [borrow]

theorem borrow_cases {context : Context} {target : Origin} {referent : Ty} {parent : Option Nat} {mode : BorrowMode}
    {node : Nat} {loan : SourceLoan} (found : (context.borrow target referent parent mode).loans[node]? = some loan) :
    context.loans[node]? = some loan ∨ (node = context.loans.length ∧ loan = ⟨target, referent, parent, true, mode⟩) := by
  by_cases bound : node < context.loans.length
  · exact .inl (by simpa only [borrow, List.getElem?_append_left bound] using found)
  · simp only [borrow, List.getElem?_append_right (Nat.le_of_not_lt bound)] at found
    cases difference : node - context.loans.length with
    | zero =>
      exact .inr ⟨Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp difference) (Nat.le_of_not_lt bound),
        by simpa only [difference, List.getElem?_cons_zero, Option.some.injEq] using found.symm⟩
    | succ rest => simp [difference] at found

theorem borrow_mentions {context : Context} {target : Origin} {referent : Ty} {parent : Option Nat} {mode : BorrowMode}
    (known : target.Known context) (binder : Nat) :
    (context.borrow target referent parent mode).MentionsBinder binder ↔ context.MentionsBinder binder := by
  constructor
  · intro mentioned
    rcases mentioned with slot | ⟨node, loan, found, base⟩
    · exact .inl slot
    · rcases borrow_cases found with old | ⟨_, rfl⟩
      · exact .inr ⟨node, loan, old, base⟩
      · change target.base = .binder binder at base
        simpa [Origin.Known, base] using known
  · intro mentioned
    rcases mentioned with slot | ⟨node, loan, found, base⟩
    · exact .inl slot
    · exact .inr ⟨node, loan, borrow_found found, base⟩

theorem WellFormed.borrow {context : Context} (valid : context.WellFormed program)
    {target : Origin} {referent : Ty} {parent : Option Nat} {mode : BorrowMode}
    (bounded : target.Bounded context) (finite : FiniteLayout program.target program.data referent)
    (ancestor : ∀ node, parent = some node → ∃ loan, context.loans[node]? = some loan ∧ target.Within loan.target)
    (parentMode : ∀ node loan, parent = some node → context.loans[node]? = some loan → mode = .unique → loan.mode = .unique) :
    (context.borrow target referent parent mode).WellFormed program := by
  refine ⟨valid.distinct, valid.supported, ?_, ?_, ?_, valid.named, ?_, ?_⟩
  · intro binding member
    obtain ⟨bound, reference⟩ := valid.slots binding member
    refine ⟨bound, ?_⟩
    intro node same
    obtain ⟨loan, found, shape⟩ := reference node same
    exact ⟨loan, borrow_found found, shape⟩
  · intro node loan found
    rcases borrow_cases found with old | ⟨_, rfl⟩
    · exact valid.targets node loan old
    · exact ⟨bounded, finite⟩
  · intro node loan parentNode found derived
    rcases borrow_cases found with old | ⟨rfl, rfl⟩
    · obtain ⟨older, ancestor, ancestorFound, within⟩ := valid.parents node loan parentNode old derived
      exact ⟨older, ancestor, borrow_found ancestorFound, within⟩
    · obtain ⟨ancestor, ancestorFound, within⟩ := ancestor parentNode derived
      exact ⟨(List.getElem?_eq_some_iff.mp ancestorFound).1, ancestor, borrow_found ancestorFound, within⟩
  · intro binder slot stored
    obtain ⟨identity, bound, supported, reference⟩ := valid.allocated binder slot stored
    refine ⟨identity, bound, supported, ?_⟩
    intro node selected
    obtain ⟨loan, found, type⟩ := reference node selected
    exact ⟨loan, borrow_found found, type⟩
  · intro node loan parentNode parentLoan found derived parentFound unique
    rcases borrow_cases found with old | ⟨rfl, rfl⟩
    · obtain ⟨_, original, originalFound, _⟩ := valid.parents node loan parentNode old derived
      have same := Option.some.inj ((borrow_found originalFound).symm.trans parentFound)
      subst parentLoan
      exact valid.parentModes node loan parentNode original old derived originalFound unique
    · obtain ⟨original, originalFound, _⟩ := ancestor parentNode derived
      have same := Option.some.inj ((borrow_found originalFound).symm.trans parentFound)
      subst parentLoan
      exact parentMode parentNode original derived originalFound unique

end Context


/-- Proof interpretation only. Runtime end actions use actual carrier values;
no source-identity map is installed in the executable environment. -/
structure Interpretation where
  binder : Nat → Root
  input : Nat → Address
  node : Nat → Nat

def Interpretation.origin (interpretation : Interpretation) (origin : Origin) : Address :=
  match origin.base with
  | .binder identity => ⟨interpretation.binder identity, origin.fields⟩
  | .input identity =>
      let base := interpretation.input identity
      ⟨base.root, base.fields ++ origin.fields⟩

def Slot.Corresponds (interpretation : Interpretation) (slot : Slot) (value : Value) : Prop :=
  match slot.reference with
  | none => value.ReferenceFree
  | some node => value = .reference (interpretation.node node)

inductive SlotsCorrespond (interpretation : Interpretation) (store : Store) :
    List (String × Root) → List (String × Slot) → Prop where
  | nil : SlotsCorrespond interpretation store [] []
  | cons {name : String} {root : Root} {slot : Slot} {bindings : List (String × Root)}
      {slots : List (String × Slot)}
      (identity : root = interpretation.binder slot.binder)
      (resident : ∀ value, store root = some value → slot.Corresponds interpretation value)
      (rest : SlotsCorrespond interpretation store bindings slots) :
      SlotsCorrespond interpretation store ((name, root) :: bindings) ((name, slot) :: slots)

def Interpretation.addNode (interpretation : Interpretation) (source runtime : Nat) : Interpretation :=
  { interpretation with node := fun node => if node = source then runtime else interpretation.node node }

theorem Interpretation.addNode_old (interpretation : Interpretation) {source node runtime : Nat}
    (older : node < source) : (interpretation.addNode source runtime).node node = interpretation.node node := by
  simp [addNode, Nat.ne_of_lt older]

theorem SlotsCorrespond.node_congr {before after : Interpretation} {store : Store}
    {bindings : List (String × Root)} {slots : List (String × Slot)}
    (typed : SlotsCorrespond before store bindings slots)
    (sameBinders : ∀ binder, after.binder binder = before.binder binder)
    (sameNodes : ∀ binding ∈ slots, ∀ node, binding.2.reference = some node → after.node node = before.node node) :
    SlotsCorrespond after store bindings slots := by
  induction typed with
  | nil => exact .nil
  | @cons name root slot bindings slots identity resident rest ih =>
    refine .cons (identity.trans (sameBinders slot.binder).symm) ?_ (ih ?_)
    · intro value stored
      have old := resident value stored
      cases reference : slot.reference with
      | none => simpa [Slot.Corresponds, reference] using old
      | some node =>
        have same := sameNodes (name, slot) (by simp) node reference
        simpa [Slot.Corresponds, reference, same] using old
    · intro binding member node reference
      exact sameNodes binding (by simp [member]) node reference
inductive Carrier where
  | stored (root : Root)
  | held (index : Nat)

def Carries (environment : Environment) (held : List Value) (node : Nat) : Carrier → Prop
  | .stored root => environment.store root = some (.reference node)
  | .held index => held[index]? = some (.reference node)

/-- The concrete held values are evaluated argument prefixes or protected return
payloads, not a future-use oracle. Inactive carrier bits are deliberately inert. -/
def Custody (environment : Environment) (held : List Value) : Prop :=
  ∀ (node : Nat) (loan : Loan), environment.loans[node]? = some loan → loan.own = true →
    ∃ location, Carries environment held node location ∧
      ∀ other, Carries environment held node other → other = location

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

/-- Runtime resolution agrees with the sole source index derivation. -/
theorem PathType.resident {source target : Ty} {keys : List FieldKey} {indices : List Nat} {state selected : Initialization}
    (path : PathType program home source keys indices target) {value : Value}
    (typed : ResidentTyped program state value source) (access : state.Access indices selected) :
    value.resolvePath program keys = some indices ∧
      ∃ resident, value.readIndices indices = some resident ∧ ResidentTyped program selected resident target := by
  induction path generalizing value state selected with
  | nil => cases access; exact ⟨rfl, value, rfl, typed⟩
  | @cons source middle target key keys index indices head tail ih =>
    cases access with
    | child present childAccess =>
      obtain ⟨child, indexed, found, childTyped, _⟩ := head.access typed present
      obtain ⟨resolved, resident, selected, residentTyped⟩ := ih childTyped childAccess
      exact ⟨by simp [Value.resolvePath, indexed, found, resolved], resident,
        by simp [Value.readIndices, found, selected], residentTyped⟩

theorem CanonicalPath.resident {source target : Ty} {indices : List Nat} {state selected : Initialization}
    (path : CanonicalPath program source indices target) {value : Value}
    (typed : ResidentTyped program state value source) (access : state.Access indices selected) :
    ∃ resident, value.readIndices indices = some resident ∧ ResidentTyped program selected resident target := by
  induction path generalizing value state selected with
  | nil => cases access; exact ⟨value, rfl, typed⟩
  | cons head _ ih =>
    cases access with
    | child present childAccess =>
      obtain ⟨child, _, found, childTyped, _⟩ := head.access typed present
      obtain ⟨resident, selected, residentTyped⟩ := ih childTyped childAccess
      exact ⟨resident, by simp [Value.readIndices, found, selected], residentTyped⟩

/-- Componentwise source/runtime state correspondence. Target initialization is
an invariant proved across real transitions; source admission never assumes it. -/
structure StoreTyped (program : Program) (interpretation : Interpretation) (context : Context)
    (environment : Environment) : Prop where
  source : context.WellFormed program
  residents : EnvironmentTyped program environment context.erase
  slots : SlotsCorrespond interpretation environment.store environment.bindings context.bindings
  cells : ∀ binder slot, context.storage (.binder binder) = some slot →
    ∃ value, environment.store (interpretation.binder binder) = some value ∧
      SlotTyped program value slot.toBindingType ∧ slot.Corresponds interpretation value
  binderBound : ∀ binder, context.MentionsBinder binder → interpretation.binder binder < environment.nextRoot
  binderDistinct : ∀ first second, context.MentionsBinder first → context.MentionsBinder second →
    interpretation.binder first = interpretation.binder second → first = second
  inputBound : ∀ input, input < context.inputCount → (interpretation.input input).root < environment.nextRoot
  inputApart : ∀ binder input, context.MentionsBinder binder → input < context.inputCount →
    interpretation.binder binder ≠ (interpretation.input input).root
  nodeOrder : ∀ first second, first < second → second < context.loans.length →
    interpretation.node first < interpretation.node second
  records : ∀ (node : Nat) (loan : SourceLoan), context.loans[node]? = some loan →
    environment.loans[interpretation.node node]? =
      some ⟨interpretation.origin loan.target, loan.parent.map interpretation.node, loan.own, loan.mode⟩
  activeCoverage : ∀ (node : Nat) (loan : Loan), environment.loans[node]? = some loan → loan.own = true →
    ∃ sourceNode sourceLoan, context.loans[sourceNode]? = some sourceLoan ∧ interpretation.node sourceNode = node
  sourceTargets : ∀ (node : Nat) (loan : SourceLoan), context.loans[node]? = some loan → loan.own = true →
    context.SourceTarget program loan
  inputTargets : ∀ (node : Nat) (loan : SourceLoan), context.loans[node]? = some loan → loan.own = true →
    ∀ input, loan.target.base = .input input →
    ∃ value, environment.readAddress (interpretation.origin loan.target) = some value ∧
      ValueHasType program value loan.referent
  storeShape : ∀ root value, environment.store root = some value →
    value.ReferenceFree ∨ ∃ node, value = .reference node ∧ node < environment.loans.length

/-- The masked target theorem consumes global cell correspondence and the canonical
source path. A vacant selected resident is allowed; no successful read is assumed. -/
theorem StoreTyped.targetResident {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) {origin : Origin} {referent : Ty}
    (target : context.Target program origin referent) {binder : Nat} (base : origin.base = .binder binder) :
    ∃ state value, environment.at (interpretation.origin origin) = some value ∧
      ResidentTyped program state value referent := by
  obtain ⟨slot, stored, path, state, access⟩ := (by simpa [Context.Target, base] using target)
  obtain ⟨root, found, rootTyped, _⟩ := typed.cells binder slot stored
  obtain ⟨value, selected, resident⟩ := path.resident rootTyped access
  exact ⟨state, value, by simp [Environment.at, Interpretation.origin, base, found, selected], resident⟩

theorem StoreTyped.targetReady {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) {origin : Origin} {referent : Ty}
    (target : context.Target program origin referent) (ready : context.Ready origin)
    {binder : Nat} (base : origin.base = .binder binder) :
    ∃ value, environment.readAddress (interpretation.origin origin) = some value ∧ ValueHasType program value referent := by
  obtain ⟨slot, stored, path, _, _⟩ := (by simpa [Context.Target, base] using target)
  simp only [Context.Ready, base] at ready
  obtain ⟨readySlot, state, readyStored, access, complete⟩ := ready
  have same := Option.some.inj (stored.symm.trans readyStored)
  subst readySlot
  obtain ⟨root, found, rootTyped, _⟩ := typed.cells binder slot stored
  obtain ⟨value, selected, resident⟩ := path.resident rootTyped access
  obtain ⟨full, initialized⟩ := resident.complete complete
  exact ⟨value, by simp [Environment.readAddress, Environment.at, Interpretation.origin, base, found, selected, initialized], full⟩

theorem StoreTyped.targetsReady {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) (node : Nat) (loan : SourceLoan)
    (found : context.loans[node]? = some loan) (own : loan.own = true) (ready : context.Ready loan.target) :
    ∃ value, environment.readAddress (interpretation.origin loan.target) = some value ∧ ValueHasType program value loan.referent := by
  cases base : loan.target.base with
  | binder binder => exact typed.targetReady (typed.sourceTargets node loan found own).1 ready base
  | input input => exact typed.inputTargets node loan found own input base

theorem StoreTyped.targets {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) (node : Nat) (loan : SourceLoan)
    (found : context.loans[node]? = some loan) (own : loan.own = true) (shared : loan.mode = .shared) :
    ∃ value, environment.readAddress (interpretation.origin loan.target) = some value ∧ ValueHasType program value loan.referent :=
  typed.targetsReady node loan found own ((typed.sourceTargets node loan found own).2.1 shared)

theorem StoreTyped.restored {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) {node : Nat} {loan : SourceLoan}
    (found : context.loans[node]? = some loan) (ready : context.Restored node) :
    environment.Restored (interpretation.node node) := by
  intro actual selected own
  have equal := Option.some.inj ((typed.records node loan found).symm.trans selected)
  subst actual
  obtain ⟨value, read, _⟩ := typed.targetsReady node loan found own (ready loan found own)
  exact ⟨value, read⟩

theorem Context.Ready.storage_congr {before after : Context} {origin : Origin}
    (ready : before.Ready origin) (same : after.storage origin.base = before.storage origin.base) : after.Ready origin := by
  cases origin with
  | mk base fields => cases base <;> simp_all only [Context.Ready]

theorem Context.Restored.endOwn {context : Context} {node : Nat} (ready : context.Restored node) (ended : Nat) :
    (context.endOwn ended).Restored node := by
  intro loan found own
  obtain ⟨original, old, rfl⟩ := Context.endOwn_original found
  have different : ended ≠ node := by intro equal; simp [equal] at own
  exact ready original old (by simpa [different] using own)

theorem Context.Restored.borrow {context : Context} {node : Nat} (ready : context.Restored node)
    (bound : node < context.loans.length) (target : Origin) (referent : Ty) (parent : Option Nat) (mode : BorrowMode) :
    (context.borrow target referent parent mode).Restored node := by
  intro loan found own
  rcases Context.borrow_cases found with old | ⟨same, rfl⟩
  · exact ready loan old own
  · exact False.elim ((Nat.ne_of_lt bound) same)


/-- Every active binder-backed loan, including a unique loan with a hole, retains
exact canonical typing from its authoritative storage root. Dead history is excluded. -/
theorem StoreTyped.canonicalTargets {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) {node : Nat} {loan : SourceLoan}
    (found : context.loans[node]? = some loan) (own : loan.own = true)
    {binder : Nat} (base : loan.target.base = .binder binder) :
    ∃ slot state value, context.storage (.binder binder) = some slot ∧
      CanonicalPath program slot.type loan.target.fields loan.referent ∧
      slot.initialization.Access loan.target.fields state ∧
      environment.at (interpretation.origin loan.target) = some value ∧ ResidentTyped program state value loan.referent := by
  have target := (typed.sourceTargets node loan found own).1
  simp only [Context.Target, base] at target
  obtain ⟨slot, stored, path, state, access⟩ := target
  obtain ⟨root, rootStored, rootTyped, _⟩ := typed.cells binder slot stored
  obtain ⟨value, selected, resident⟩ := path.resident rootTyped access
  exact ⟨slot, state, value, stored, path, access,
    by simp [Environment.at, Interpretation.origin, base, rootStored, selected], resident⟩



/-- Concrete continuation resources extend stored correspondence; they are not
part of the runtime store and cannot be forgotten by argument or return cleanup. -/
structure StateTyped (program : Program) (interpretation : Interpretation) (context : Context)
    (heldNodes : List Nat) (environment : Environment) (held : List Value) : Prop
    extends StoreTyped program interpretation context environment where
  heldShape : held = heldNodes.map (fun node => Value.reference (interpretation.node node))
  heldOwn : ∀ node ∈ heldNodes, context.Own node
  heldReady : ∀ node ∈ heldNodes, context.Restored node
  custody : Custody environment held

private theorem CoordinatesApart.prepend (stem : List Nat) {left right : List Nat}
    (apart : CoordinatesApart left right) : CoordinatesApart (stem ++ left) (stem ++ right) := by
  induction stem with
  | nil => exact apart
  | cons head tail ih => exact .descend ih

theorem Interpretation.within (interpretation : Interpretation) {child parent : Origin}
    (within : child.Within parent) :
    (interpretation.origin child).root = (interpretation.origin parent).root ∧
      (interpretation.origin parent).fields.IsPrefix (interpretation.origin child).fields := by
  rcases child with ⟨childBase, childFields⟩
  rcases parent with ⟨parentBase, parentFields⟩
  rcases within with ⟨same, initial⟩
  cases same
  cases childBase with
  | binder identity => exact ⟨rfl, initial⟩
  | input identity =>
    refine ⟨rfl, ?_⟩
    obtain ⟨suffix, equal⟩ := initial
    exact ⟨suffix, by simpa only [Interpretation.origin, List.append_assoc] using (congrArg ((interpretation.input identity).fields ++ ·) equal)⟩

namespace StoreTyped

variable {interpretation : Interpretation} {context : Context} {environment : Environment}

/-- Static disjointness reflects through injective owned roots, possibly aliased
formal subaddresses, and the existing canonical field-disjointness relation. -/
theorem apart (typed : StoreTyped program interpretation context environment)
    {left right : Origin} (leftBound : left.Known context) (rightBound : right.Known context)
    (apart : left.Apart right) : (interpretation.origin left).Apart (interpretation.origin right) := by
  cases left with
  | mk leftBase leftFields =>
    cases right with
    | mk rightBase rightFields =>
      cases leftBase with
      | binder first =>
        cases rightBase with
        | binder second =>
          rcases apart with different | fields
          · exact .inl (fun same => different (typed.binderDistinct _ _ leftBound rightBound same))
          · exact .inr fields
        | input second => exact .inl (typed.inputApart first second leftBound rightBound)
      | input first =>
        cases rightBase with
        | binder second => exact .inl (Ne.symm (typed.inputApart second first rightBound leftBound))
        | input second =>
          rcases apart with ⟨equal, fields⟩
          cases equal
          exact .inr (fields.prepend (interpretation.input first).fields)

/-- Ancestry permission is derived from source parent records and componentwise
interpretation. No ancestor own bit or ancestor target initialization is used. -/
theorem supported (typed : StoreTyped program interpretation context environment)
    {node : Nat} {loan : SourceLoan} (found : context.loans[node]? = some loan) :
    Environment.Supported environment.loans (interpretation.node node) := by
  induction node using Nat.strongRecOn generalizing loan with
  | ind node ih =>
    cases parent : loan.parent with
    | none => exact .root (typed.records _ _ found) (by simp [parent])
    | some ancestor =>
      obtain ⟨older, parentLoan, parentFound, within⟩ := typed.source.parents _ _ _ found parent
      have translated := interpretation.within within
      exact .child (typed.records _ _ found) (by simp [parent])
        (typed.nodeOrder _ _ older (List.getElem?_eq_some_iff.mp found).1)
        (typed.records _ _ parentFound) translated.1 translated.2 (ih ancestor older parentFound)

theorem usable (typed : StoreTyped program interpretation context environment)
    {node : Nat} (own : context.Own node) : environment.Usable (interpretation.node node) := by
  obtain ⟨loan, found, available⟩ := own
  exact ⟨_, typed.records _ _ found, available, typed.supported found⟩

theorem nodeInjective (typed : StoreTyped program interpretation context environment)
    {first second : Nat} (firstBound : first < context.loans.length) (secondBound : second < context.loans.length)
    (same : interpretation.node first = interpretation.node second) : first = second := by
  rcases Nat.lt_trichotomy first second with less | equal | more
  · exact False.elim ((Nat.ne_of_lt (typed.nodeOrder _ _ less secondBound)) same)
  · exact equal
  · exact False.elim ((Nat.ne_of_lt (typed.nodeOrder _ _ more firstBound)) same.symm)

/-- Stored-state preservation for ending one actual node. The continuation
resource rules separately check whether that node may be consumed or ended. -/
theorem endOwn (typed : StoreTyped program interpretation context environment)
    {ended : Nat} {endedLoan : SourceLoan} (found : context.loans[ended]? = some endedLoan) :
    ∃ after, environment.endOwn (interpretation.node ended) = some after ∧
      StoreTyped program interpretation (context.endOwn ended) after := by
  let after : Environment := { environment with
    loans := environment.loans.modify (interpretation.node ended) fun loan => { loan with own := false } }
  have endedBound := (List.getElem?_eq_some_iff.mp found).1
  have originalRuntime : ∀ (node : Nat) (loan : Loan), after.loans[node]? = some loan →
      ∃ (original : Loan), environment.loans[node]? = some original ∧
        loan = { original with own := if interpretation.node ended = node then false else original.own } := by
    intro node loan selected
    change (environment.loans.modify (interpretation.node ended) fun loan => { loan with own := false })[node]? = some loan at selected
    rw [List.getElem?_modify] at selected
    obtain ⟨original, old, equal⟩ := Option.map_eq_some_iff.mp selected
    refine ⟨original, old, ?_⟩
    cases equal
    split <;> rfl
  refine ⟨after, by simp [Environment.endOwn, typed.records _ _ found, after], ?_⟩
  refine { source := typed.source.endOwn ended
           residents := ⟨⟨typed.residents.valid.bounded, typed.residents.valid.named, typed.residents.valid.distinct⟩,
             typed.residents.residents⟩
           slots := typed.slots
           cells := typed.cells
           binderBound := ?_
           binderDistinct := ?_
           inputBound := typed.inputBound
           inputApart := ?_
           nodeOrder := ?_
           records := ?_
           activeCoverage := ?_
           sourceTargets := by
             intro node loan selected available
             obtain ⟨original, old, rfl⟩ := Context.endOwn_original selected
             have different : ended ≠ node := by intro same; simp [same] at available
             have own : original.own = true := by simpa [different] using available
             exact typed.sourceTargets node original old own
           inputTargets := ?_
           storeShape := ?_ }
  · intro binder included
    exact typed.binderBound binder ((context.endOwn_mentions ended binder).mp included)
  · intro first second firstKnown secondKnown same
    exact typed.binderDistinct first second ((context.endOwn_mentions ended first).mp firstKnown)
      ((context.endOwn_mentions ended second).mp secondKnown) same
  · intro binder input included bound
    exact typed.inputApart binder input ((context.endOwn_mentions ended binder).mp included) bound
  · intro first second older bound
    exact typed.nodeOrder first second older (by simpa [Context.endOwn] using bound)
  · intro node loan selected
    obtain ⟨original, old, rfl⟩ := Context.endOwn_original selected
    have record := typed.records node original old
    change (environment.loans.modify (interpretation.node ended) fun loan => { loan with own := false })[interpretation.node node]? = _
    rw [List.getElem?_modify, record]
    by_cases same : ended = node
    · subst node; simp
    · have different : interpretation.node ended ≠ interpretation.node node :=
        fun equal => same (typed.nodeInjective endedBound (List.getElem?_eq_some_iff.mp old).1 equal)
      simp [same, different]
  · intro node loan selected available
    obtain ⟨original, old, rfl⟩ := originalRuntime node loan selected
    have different : interpretation.node ended ≠ node := by
      intro same
      simp [same] at available
    have own : original.own = true := by simpa [different] using available
    obtain ⟨sourceNode, sourceLoan, sourceFound, equal⟩ := typed.activeCoverage node original old own
    exact ⟨sourceNode, _, context.endOwn_found ended sourceFound, equal⟩
  · intro node loan selected available
    obtain ⟨original, old, rfl⟩ := Context.endOwn_original selected
    have different : ended ≠ node := by intro same; simp [same] at available
    have own : original.own = true := by simpa [different] using available
    exact typed.inputTargets node original old own
  · intro root value stored
    rcases typed.storeShape root value stored with plain | ⟨node, rfl, bound⟩
    · exact .inl plain
    · exact .inr ⟨node, rfl, by simpa [after] using bound⟩


theorem derived (typed : StoreTyped program interpretation context environment)
    {node ancestor : Nat} (source : context.Derived node ancestor) :
    environment.Derived (interpretation.node node) (interpretation.node ancestor) := by
  induction source with
  | same node => exact .same _
  | child found parent rest ih => exact .child (typed.records _ _ found) (by simp [parent]) ih

theorem permits (typed : StoreTyped program interpretation context environment)
    {mode : BorrowMode} {parent : Option Nat} {origin : Origin}
    (known : origin.Known context) (allowed : context.Permits mode parent origin) :
    environment.Permits mode (parent.map interpretation.node) (interpretation.origin origin) := by
  intro runtimeNode runtimeLoan runtimeFound runtimeOwn
  obtain ⟨node, loan, found, same⟩ := typed.activeCoverage runtimeNode runtimeLoan runtimeFound runtimeOwn
  have record := typed.records node loan found
  rw [same, runtimeFound] at record
  cases Option.some.inj record.symm
  rcases allowed node loan found runtimeOwn with shared | ancestral | apart
  · exact .inl shared
  · obtain ⟨selected, parent, path⟩ := ancestral
    exact .inr (.inl ⟨interpretation.node selected, by simp [parent], by rw [← same]; exact typed.derived path⟩)
  · exact .inr (.inr (typed.apart known (typed.source.loanKnown found) apart))

/-- Owner-mutation permission is a conclusion, not an admission callback. -/
theorem ownerFree (typed : StoreTyped program interpretation context environment)
    {origin : Origin} (bound : origin.Known context) (free : context.Free origin) :
    environment.OwnerFree (interpretation.origin origin) := by
  intro runtimeNode runtimeLoan runtimeFound runtimeOwn
  obtain ⟨node, loan, found, sameNode⟩ := typed.activeCoverage _ _ runtimeFound runtimeOwn
  have record := typed.records node loan found
  rw [sameNode, runtimeFound] at record
  cases Option.some.inj record
  exact typed.apart bound (typed.source.loanKnown found) (free node loan found runtimeOwn)

/-- Every active runtime node has an addressable typed target. Unique targets may
be masked; shared targets are initialized even under ended or hidden ancestors. -/
theorem noDangling (typed : StoreTyped program interpretation context environment)
    {node : Nat} {loan : Loan} (found : environment.loans[node]? = some loan) (own : loan.own = true) :
    ∃ value type state, environment.at loan.target = some value ∧ ResidentTyped program state value type ∧
      FiniteLayout program.target program.data type ∧
      (loan.mode = .shared → environment.readAddress loan.target = some value ∧ ValueHasType program value type) := by
  obtain ⟨sourceNode, sourceLoan, sourceFound, sameNode⟩ := typed.activeCoverage _ _ found own
  have record := typed.records sourceNode sourceLoan sourceFound
  rw [sameNode, found] at record
  cases Option.some.inj record
  by_cases shared : sourceLoan.mode = .shared
  · obtain ⟨value, read, typedValue⟩ := typed.targets _ _ sourceFound own shared
    have raw : environment.at (interpretation.origin sourceLoan.target) = some value := by
      simp only [Environment.readAddress, Bind.bind, Option.bind_eq_some_iff] at read
      obtain ⟨resident, raw, live⟩ := read
      split at live <;> simp_all
    exact ⟨value, sourceLoan.referent, .full, raw, typedValue, (typed.source.targets _ _ sourceFound).2, fun _ => ⟨read, typedValue⟩⟩
  · cases base : sourceLoan.target.base with
    | binder binder =>
      obtain ⟨state, value, raw, resident⟩ := typed.targetResident (typed.sourceTargets _ _ sourceFound own).1 base
      exact ⟨value, sourceLoan.referent, state, raw, resident, (typed.source.targets _ _ sourceFound).2, fun same => False.elim (shared same)⟩
    | input input => exact False.elim (shared ((typed.sourceTargets _ _ sourceFound own).2.2 input base))


/-- Widening a static identity supply allocates nothing. Only the existing finite
support has a runtime interpretation; skipped source IDs remain uninterpreted. -/
theorem raiseSupply (typed : StoreTyped program interpretation context environment)
    {supply : Nat} (larger : context.nextBinder ≤ supply) :
    StoreTyped program interpretation { context with nextBinder := supply } environment := by
  have source : Context.WellFormed program { context with nextBinder := supply } := by
    refine { typed.source with slots := ?_, targets := ?_, allocated := ?_ }
    · intro binding member
      have old := typed.source.slots binding member
      exact ⟨Nat.lt_of_lt_of_le old.1 larger, old.2⟩
    · intro node loan found
      obtain ⟨bound, finite⟩ := typed.source.targets node loan found
      refine ⟨?_, finite⟩
      cases base : loan.target.base with
      | binder identity =>
        have old : identity < context.nextBinder := by simpa [Origin.Bounded, base] using bound
        simpa [Origin.Bounded, base] using Nat.lt_of_lt_of_le old larger
      | input identity => simpa [Origin.Bounded, base] using bound
    · intro binder slot stored
      obtain ⟨identity, bound, supported, reference⟩ := typed.source.allocated binder slot stored
      exact ⟨identity, Nat.lt_of_lt_of_le bound larger, supported, reference⟩
  exact { typed with source := source }
theorem borrow (typed : StoreTyped program interpretation context environment)
    {target : Origin} {referent : Ty} {parent : Option Nat} {mode : BorrowMode} {value : Value}
    (known : target.Known context) (bounded : target.Bounded context)
    (finite : FiniteLayout program.target program.data referent)
    (ancestor : ∀ node, parent = some node → ∃ loan, context.loans[node]? = some loan ∧ target.Within loan.target)
    (parentMode : ∀ node loan, parent = some node → context.loans[node]? = some loan → mode = .unique → loan.mode = .unique)
    (sourceTarget : context.SourceTarget program ⟨target, referent, parent, true, mode⟩)
    (selected : environment.readAddress (interpretation.origin target) = some value)
    (valueTyped : ValueHasType program value referent) :
    StoreTyped program (interpretation.addNode context.loans.length environment.loans.length)
      (context.borrow target referent parent mode)
      (environment.addLoan ⟨interpretation.origin target, parent.map interpretation.node⟩ mode) := by
  let next := interpretation.addNode context.loans.length environment.loans.length
  let after := environment.addLoan ⟨interpretation.origin target, parent.map interpretation.node⟩ mode
  have oldNode : ∀ node, node < context.loans.length → next.node node = interpretation.node node := by
    intro node bound
    exact interpretation.addNode_old bound
  have nodeBound : ∀ node, node < context.loans.length → interpretation.node node < environment.loans.length := by
    intro node bound
    exact (List.getElem?_eq_some_iff.mp (typed.records node context.loans[node]
      (List.getElem?_eq_getElem bound))).1
  have parentSame : parent.map next.node = parent.map interpretation.node := by
    cases shape : parent with
    | none => rfl
    | some node =>
      obtain ⟨loan, found, _⟩ := ancestor node shape
      simp only [Option.map_some, oldNode node (List.getElem?_eq_some_iff.mp found).1]
  refine { source := typed.source.borrow bounded finite ancestor parentMode
           residents := ⟨⟨typed.residents.valid.bounded, typed.residents.valid.named, typed.residents.valid.distinct⟩,
             typed.residents.residents⟩
           slots := typed.slots.node_congr (fun _ => rfl) ?_
           cells := by
             intro binder slot stored
             obtain ⟨resident, found, residentTyped, corresponds⟩ := typed.cells binder slot stored
             refine ⟨resident, found, residentTyped, ?_⟩
             cases reference : slot.reference with
             | none => simpa only [Slot.Corresponds, reference] using corresponds
             | some node =>
               obtain ⟨loan, present, _⟩ := (typed.source.allocated binder slot stored).2.2.2 node reference
               simp only [Slot.Corresponds, reference]
               change resident = Value.reference (next.node node)
               rw [oldNode node (List.getElem?_eq_some_iff.mp present).1]
               simpa only [Slot.Corresponds, reference] using corresponds
           binderBound := ?_
           binderDistinct := ?_
           inputBound := typed.inputBound
           inputApart := ?_
           nodeOrder := ?_
           records := ?_
           activeCoverage := ?_
           sourceTargets := by
             intro node loan found own
             rcases Context.borrow_cases found with old | ⟨_, rfl⟩
             · exact typed.sourceTargets node loan old own
             · exact sourceTarget
           inputTargets := ?_
           storeShape := ?_ }
  · intro binding member node reference
    obtain ⟨loan, found, _⟩ := (typed.source.slots binding member).2 node reference
    exact oldNode node (List.getElem?_eq_some_iff.mp found).1
  · intro binder included
    exact typed.binderBound binder ((Context.borrow_mentions known binder).mp included)
  · intro first second firstKnown secondKnown same
    exact typed.binderDistinct first second ((Context.borrow_mentions known first).mp firstKnown)
      ((Context.borrow_mentions known second).mp secondKnown) same
  · intro binder input included inputKnown
    exact typed.inputApart binder input ((Context.borrow_mentions known binder).mp included) inputKnown
  · intro first second less bound
    have secondLe : second ≤ context.loans.length := Nat.lt_succ_iff.mp (by simpa [Context.borrow] using bound)
    change next.node first < next.node second
    rcases Nat.lt_or_eq_of_le secondLe with secondOld | rfl
    · rw [oldNode first (Nat.lt_trans less secondOld), oldNode second secondOld]
      exact typed.nodeOrder first second less secondOld
    · rw [oldNode first less]
      simpa [next, Interpretation.addNode] using nodeBound first less
  · intro node loan found
    rcases Context.borrow_cases found with old | ⟨rfl, rfl⟩
    · have bound := (List.getElem?_eq_some_iff.mp old).1
      have oldParent : loan.parent.map next.node = loan.parent.map interpretation.node := by
        cases shape : loan.parent with
        | none => rfl
        | some parentNode =>
          have older := (typed.source.parents node loan parentNode old shape).1
          simp only [Option.map_some, oldNode parentNode (Nat.lt_trans older bound)]
      change after.loans[next.node node]? = some ⟨next.origin loan.target, loan.parent.map next.node, loan.own, loan.mode⟩
      rw [oldNode node bound, oldParent]
      exact (List.getElem?_append_left (nodeBound node bound)).trans (typed.records node loan old)
    · change after.loans[next.node context.loans.length]? =
        some ⟨next.origin target, parent.map next.node, true, mode⟩
      rw [parentSame]
      simp [after, next, Environment.addLoan, Interpretation.addNode, Interpretation.origin]
  · intro node loan found own
    change after.loans[node]? = some loan at found
    by_cases bound : node < environment.loans.length
    · have old : environment.loans[node]? = some loan := by
        simpa only [after, Environment.addLoan, List.getElem?_append_left bound] using found
      obtain ⟨sourceNode, sourceLoan, sourceFound, same⟩ := typed.activeCoverage node loan old own
      exact ⟨sourceNode, sourceLoan, Context.borrow_found sourceFound,
        (oldNode sourceNode (List.getElem?_eq_some_iff.mp sourceFound).1).trans same⟩
    · simp only [after, Environment.addLoan, List.getElem?_append_right (Nat.le_of_not_lt bound)] at found
      cases difference : node - environment.loans.length with
      | zero =>
        have same : node = environment.loans.length :=
          Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp difference) (Nat.le_of_not_lt bound)
        exact ⟨context.loans.length, ⟨target, referent, parent, true, mode⟩,
          Context.borrow_last context target referent parent mode, by simp [Interpretation.addNode, same]⟩
      | succ rest => simp [difference] at found
  · intro node loan found own input base
    rcases Context.borrow_cases found with old | ⟨_, rfl⟩
    · exact typed.inputTargets node loan old own input base
    · exact ⟨value, selected, valueTyped⟩
  · intro root resident stored
    rcases typed.storeShape root resident stored with plain | ⟨node, rfl, bound⟩
    · exact .inl plain
    · exact .inr ⟨node, rfl, by simpa [Environment.addLoan] using Nat.lt_trans bound (Nat.lt_succ_self environment.loans.length)⟩

end StoreTyped

namespace Environment

theorem endOwn_state {before after : Environment} {node : Nat}
    (ended : before.endOwn node = some after) :
    after = { before with loans := before.loans.modify node fun loan => { loan with own := false } } := by
  cases found : before.loans[node]? with
  | none => simp [endOwn, found] at ended
  | some loan => simpa [endOwn, found] using ended.symm

theorem endOwn_active {before after : Environment} {ended node : Nat} {loan : Loan}
    (step : before.endOwn ended = some after) (found : after.loans[node]? = some loan) (own : loan.own = true) :
    before.loans[node]? = some loan ∧ ended ≠ node := by
  rw [endOwn_state step] at found
  change (before.loans.modify ended fun loan => { loan with own := false })[node]? = some loan at found
  rw [List.getElem?_modify] at found
  obtain ⟨original, found, equal⟩ := Option.map_eq_some_iff.mp found
  split at equal
  · cases equal
    cases own
  · cases equal
    exact ⟨found, by assumption⟩

end Environment
theorem Custody.borrow {environment : Environment} {held : List Value}
    (custody : Custody environment held)
    (bounded : ∀ node location, Carries environment held node location → node < environment.loans.length)
    (access : Environment.ResolvedAccess) (mode : BorrowMode) :
    Custody (environment.addLoan access mode) (held ++ [.reference environment.loans.length]) := by
  let after := environment.addLoan access mode
  let values := held ++ [Value.reference environment.loans.length]
  have lift : ∀ node location, Carries environment held node location → Carries after values node location := by
    intro node location carrier
    cases location with
    | stored root => exact carrier
    | held index =>
      change values[index]? = some (.reference node)
      exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp carrier).1).trans carrier
  have lower : ∀ node, node < environment.loans.length → ∀ location,
      Carries after values node location → Carries environment held node location := by
    intro node older location carrier
    cases location with
    | stored root => exact carrier
    | held index =>
      change values[index]? = some (.reference node) at carrier
      by_cases bound : index < held.length
      · exact (List.getElem?_append_left bound).symm.trans carrier
      · simp only [values, List.getElem?_append_right (Nat.le_of_not_lt bound)] at carrier
        cases difference : index - held.length with
        | zero =>
          have same : environment.loans.length = node := by
            simpa only [difference, List.getElem?_cons_zero, Option.some.injEq, Value.reference.injEq] using carrier
          exact False.elim ((Nat.ne_of_lt older) same.symm)
        | succ rest => simp [difference] at carrier
  intro node loan found own
  by_cases older : node < environment.loans.length
  · have old : environment.loans[node]? = some loan :=
      (List.getElem?_append_left older).symm.trans found
    obtain ⟨location, carrier, unique⟩ := custody node loan old own
    exact ⟨location, lift node location carrier, fun other otherCarrier => unique other (lower node older other otherCarrier)⟩
  · simp only [Environment.addLoan, List.getElem?_append_right (Nat.le_of_not_lt older)] at found
    cases difference : node - environment.loans.length with
    | succ rest => simp [difference] at found
    | zero =>
      have same : node = environment.loans.length :=
        Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp difference) (Nat.le_of_not_lt older)
      subst node
      refine ⟨.held held.length, by simp [Carries], ?_⟩
      intro location carrier
      cases location with
      | stored root => exact False.elim (Nat.lt_irrefl _ (bounded _ (.stored root) carrier))
      | held index =>
        change values[index]? = some (.reference environment.loans.length) at carrier
        by_cases bound : index < held.length
        · have old : held[index]? = some (.reference environment.loans.length) :=
            (List.getElem?_append_left bound).symm.trans carrier
          exact False.elim (Nat.lt_irrefl _ (bounded _ (.held index) old))
        · simp only [values, List.getElem?_append_right (Nat.le_of_not_lt bound)] at carrier
          cases difference : index - held.length with
          | zero =>
            exact congrArg Carrier.held
              (Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp difference) (Nat.le_of_not_lt bound))
          | succ rest => simp [difference] at carrier

namespace StateTyped

variable {interpretation : Interpretation} {context : Context} {heldNodes : List Nat}
variable {environment : Environment} {held : List Value}
theorem carrierBound (typed : StateTyped program interpretation context heldNodes environment held)
    {node : Nat} {location : Carrier} (carrier : Carries environment held node location) :
    node < environment.loans.length := by
  cases location with
  | stored root =>
    rcases typed.storeShape root (.reference node) carrier with plain | ⟨other, same, bound⟩
    · exact False.elim plain
    · cases Value.reference.inj same
      exact bound
  | held index =>
    change held[index]? = some (.reference node) at carrier
    rw [typed.heldShape, List.getElem?_map] at carrier
    obtain ⟨sourceNode, found, same⟩ := Option.map_eq_some_iff.mp carrier
    obtain ⟨loan, loanFound, _⟩ := typed.heldOwn sourceNode (List.mem_of_getElem? found)
    cases Value.reference.inj same
    exact (List.getElem?_eq_some_iff.mp (typed.records sourceNode loan loanFound)).1

theorem borrow (typed : StateTyped program interpretation context heldNodes environment held)
    {target : Origin} {referent : Ty} {parent : Option Nat} {mode : BorrowMode} {value : Value}
    (known : target.Known context) (bounded : target.Bounded context)
    (finite : FiniteLayout program.target program.data referent)
    (ancestor : ∀ node, parent = some node → ∃ loan, context.loans[node]? = some loan ∧ target.Within loan.target)
    (parentMode : ∀ node loan, parent = some node → context.loans[node]? = some loan → mode = .unique → loan.mode = .unique)
    (sourceTarget : context.SourceTarget program ⟨target, referent, parent, true, mode⟩)
    (ready : context.Ready target)
    (selected : environment.readAddress (interpretation.origin target) = some value)
    (valueTyped : ValueHasType program value referent) :
    StateTyped program (interpretation.addNode context.loans.length environment.loans.length)
      (context.borrow target referent parent mode) (heldNodes ++ [context.loans.length])
      (environment.addLoan ⟨interpretation.origin target, parent.map interpretation.node⟩ mode)
      (held ++ [.reference environment.loans.length]) := by
  refine { toStoreTyped := typed.toStoreTyped.borrow known bounded finite ancestor parentMode sourceTarget selected valueTyped
           heldShape := ?_
           heldOwn := ?_
           heldReady := ?_
           custody := typed.custody.borrow (fun _ _ carrier => typed.carrierBound carrier) _ _ }
  · have same : heldNodes.map (fun node => Value.reference
          ((interpretation.addNode context.loans.length environment.loans.length).node node)) = held := by
      rw [typed.heldShape]
      apply List.map_congr_left
      intro node member
      obtain ⟨loan, found, _⟩ := typed.heldOwn node member
      rw [interpretation.addNode_old (List.getElem?_eq_some_iff.mp found).1]
    rw [List.map_append, same]
    simp [Interpretation.addNode]
  · intro node member
    rcases List.mem_append.mp member with old | fresh
    · obtain ⟨loan, found, own⟩ := typed.heldOwn node old
      exact ⟨loan, Context.borrow_found found, own⟩
    · have same : node = context.loans.length := by simpa using fresh
      subst node
      exact ⟨_, Context.borrow_last context target referent parent mode, rfl⟩
  · intro node member loan found own
    rcases List.mem_append.mp member with old | fresh
    · obtain ⟨oldLoan, oldFound, _⟩ := typed.heldOwn node old
      exact (typed.heldReady node old).borrow (List.getElem?_eq_some_iff.mp oldFound).1 target referent parent mode loan found own
    · have same : node = context.loans.length := by simpa using fresh
      subst node
      have equal := Option.some.inj ((Context.borrow_last context target referent parent mode).symm.trans found)
      subst loan
      exact ready

/-- Resident last-use ending retains the actual pending handles and their own
permissions. The source end action must select a non-protected resident carrier. -/
theorem endOwn (typed : StateTyped program interpretation context heldNodes environment held)
    {node : Nat} {loan : SourceLoan} (found : context.loans[node]? = some loan) (unprotected : node ∉ heldNodes) :
    ∃ after, environment.endOwn (interpretation.node node) = some after ∧
      StateTyped program interpretation (context.endOwn node) heldNodes after held := by
  obtain ⟨after, step, stored⟩ := typed.toStoreTyped.endOwn found
  refine ⟨after, step, stored, typed.heldShape, ?_, ?_, ?_⟩
  · intro other included
    obtain ⟨otherLoan, old, own⟩ := typed.heldOwn other included
    have different : node ≠ other := fun same => unprotected (same ▸ included)
    exact ⟨_, context.endOwn_found node old, by simpa [different] using own⟩
  · exact fun other included => (typed.heldReady other included).endOwn node
  · intro other actual selected own
    have previous := (Environment.endOwn_active step selected own).1
    have equality := Environment.endOwn_state step
    subst after
    exact typed.custody other actual previous own

theorem raiseSupply (typed : StateTyped program interpretation context heldNodes environment held)
    {supply : Nat} (larger : context.nextBinder ≤ supply) :
    StateTyped program interpretation { context with nextBinder := supply } heldNodes environment held :=
  ⟨typed.toStoreTyped.raiseSupply larger, typed.heldShape, typed.heldOwn, typed.heldReady, typed.custody⟩

/-- A discarded evaluated reference is removed from the concrete pending suffix
while only that handle's own permission ends. Earlier evaluated handles remain. -/
theorem consume {node : Nat} (typed : StateTyped program interpretation context (heldNodes ++ [node]) environment
      (held ++ [Value.reference (interpretation.node node)]))
    (unprotected : node ∉ heldNodes) :
    ∃ after, environment.endOwn (interpretation.node node) = some after ∧
      StateTyped program interpretation (context.endOwn node) heldNodes after held := by
  obtain ⟨loan, found, _⟩ := typed.heldOwn node (by simp)
  obtain ⟨after, step, stored⟩ := typed.toStoreTyped.endOwn found
  have heldShape : held = heldNodes.map (fun node => Value.reference (interpretation.node node)) := by
    apply List.append_cancel_right
    simpa only [List.map_append, List.map_cons, List.map_nil] using typed.heldShape
  refine ⟨after, step, stored, heldShape, ?_, ?_, ?_⟩
  · intro other included
    obtain ⟨otherLoan, old, own⟩ := typed.heldOwn other (List.mem_append_left _ included)
    have different : node ≠ other := fun same => unprotected (same ▸ included)
    exact ⟨_, context.endOwn_found node old, by simpa [different] using own⟩
  · exact fun other included => (typed.heldReady other (List.mem_append_left _ included)).endOwn node
  · intro other actual selected own
    obtain ⟨previous, different⟩ := Environment.endOwn_active step selected own
    obtain ⟨location, carrier, unique⟩ := typed.custody other actual previous own
    have equality := Environment.endOwn_state step
    subst after
    have retained : Carries environment held other location := by
      cases location with
      | stored root => exact carrier
      | held index =>
        change (held ++ [Value.reference (interpretation.node node)])[index]? = some (.reference other) at carrier
        by_cases bound : index < held.length
        · simpa only [Carries, List.getElem?_append_left bound] using carrier
        · rw [List.getElem?_append_right (Nat.le_of_not_lt bound)] at carrier
          cases difference : index - held.length with
          | zero =>
            simp only [difference, List.getElem?_cons_zero, Option.some.injEq, Value.reference.injEq] at carrier
            exact False.elim (different carrier)
          | succ rest => simp [difference] at carrier
    refine ⟨location, retained, ?_⟩
    intro otherLocation otherCarrier
    apply unique otherLocation
    cases otherLocation with
    | stored root => exact otherCarrier
    | held index =>
      change held[index]? = some (.reference other) at otherCarrier
      have bound := (List.getElem?_eq_some_iff.mp otherCarrier).1
      simpa only [Carries, List.getElem?_append_left bound] using otherCarrier

end StateTyped




mutual
inductive Evaluates (program : Program) : Environment → Core → Value → Environment → Prop where
  | unit {environment : Environment} : Evaluates program environment ⟨.unit, .leaf⟩ .unit environment
  | integer {environment : Environment} {type : IntegerType} {magnitude : Nat}
      (fits : type.Contains program.target magnitude) :
      Evaluates program environment ⟨.integer type magnitude, .leaf⟩ (.integer type magnitude) environment
  | character {environment : Environment} {number : Nat} (valid : UnicodeScalar number) :
      Evaluates program environment ⟨.character number, .leaf⟩ (.character number) environment
  | group {environment after : Environment} {body : Expr} {plan : CorePlan} {value : Value}
      (evaluated : Evaluates program environment ⟨body, plan⟩ value after) :
      Evaluates program environment ⟨.group body, .unary plan⟩ value after
  | read {environment after : Environment} {place : Place} {address : Address} {resident value : Value}
      (resolved : environment.resolvePlace program place = some address)
      (selected : environment.readAddress address = some resident)
      (permitted : environment.Permits .shared none address)
      (copied : Environment.Copies environment resident value after) :
      Evaluates program environment ⟨.read place, .leaf⟩ value after
  | move {environment after : Environment} {place : Place} {address : Address} {value : Value}
      (resolved : environment.resolvePlace program place = some address)
      (free : environment.OwnerFree address) (allowed : environment.ResultUsable value)
      (taken : environment.takeAddress address = some (value, after)) :
      Evaluates program environment ⟨.move place, .leaf⟩ value after
  | implicitMove {environment after : Environment} {place : Place} {value : Value}
      (moved : Evaluates program environment ⟨.move place, .leaf⟩ value after) :
      Evaluates program environment ⟨.read place, .implicitMove⟩ value after
  | borrow {environment : Environment} {place : AccessPlace} {access : Environment.ResolvedAccess} {value : Value}
      {mode : BorrowMode}
      (resolved : environment.resolveAccess program place = some access)
      (allowed : environment.Authorizes mode access)
      (permitted : environment.Permits mode access.parent access.address)
      (ready : environment.AccessReady access)
      (selected : environment.readAddress access.address = some value) (plain : value.ReferenceFree) :
      Evaluates program environment ⟨.borrow mode place, .leaf⟩ (.reference environment.loans.length)
        (environment.addLoan access mode)
  | reborrow {environment : Environment} {place : Place} {access : Environment.ResolvedAccess} {value : Value}
      {mode : BorrowMode}
      (resolved : environment.resolveAccess program (.dereference place []) = some access)
      (allowed : environment.Authorizes mode access)
      (permitted : environment.Permits mode access.parent access.address)
      (ready : environment.AccessReady access)
      (selected : environment.readAddress access.address = some value) (plain : value.ReferenceFree) :
      Evaluates program environment ⟨.read place, .reborrow mode⟩ (.reference environment.loans.length)
        (environment.addLoan access mode)
  | dereference {environment : Environment} {reference : Place} {fields : List FieldKey}
      {access : Environment.ResolvedAccess} {value : Value}
      (resolved : environment.resolveAccess program (.dereference reference fields) = some access)
      (allowed : environment.Authorizes .shared access)
      (permitted : environment.Permits .shared access.parent access.address)
      (ready : environment.AccessReady access)
      (selected : environment.readAddress access.address = some value) (plain : value.ReferenceFree) :
      Evaluates program environment ⟨.dereference reference fields, .leaf⟩ value environment
  | moveIndirect {environment after : Environment} {reference : Place} {fields : List FieldKey}
      {access : Environment.ResolvedAccess} {value : Value}
      (resolved : environment.resolveAccess program (.dereference reference fields) = some access)
      (allowed : environment.Authorizes .unique access)
      (permitted : environment.Permits .unique access.parent access.address)
      (ready : environment.AccessReady access) (plain : value.ReferenceFree)
      (taken : environment.takeAddress access.address = some (value, after)) :
      Evaluates program environment ⟨.moveIndirect reference fields, .leaf⟩ value after
  | assignIndirect {environment middle updated after : Environment} {reference : Place} {fields : List FieldKey}
      {expression rest : Expr} {expressionPlan restPlan : CorePlan} {access : Environment.ResolvedAccess}
      {resident old value : Value} {trace : List (List Nat)}
      (evaluated : Evaluates program environment ⟨expression, expressionPlan⟩ resident middle)
      (resolved : middle.resolveAccess program (.dereference reference fields) = some access)
      (allowed : middle.Authorizes .unique access)
      (permitted : middle.Permits .unique access.parent access.address)
      (previous : middle.at access.address = some old) (plain : old.ReferenceFree)
      (destroyed : old.Destroys program trace .vacant)
      (written : middle.writeAddress access.address resident = some updated)
      (continued : Evaluates program updated ⟨rest, restPlan⟩ value after) :
      Evaluates program environment ⟨.assignIndirect reference fields expression rest, .binary expressionPlan restPlan⟩ value after
  | endOwn {environment ended after : Environment} {expression : Expr} {plan : CorePlan} {slot : Nat} {value : Value}
      (endedOwn : environment.endSlot slot = some ended)
      (continued : Evaluates program ended ⟨expression, plan⟩ value after) :
      Evaluates program environment ⟨expression, .endOwn slot plan⟩ value after
  | endAfter {environment middle after : Environment} {expression : Expr} {plan : CorePlan} {slot : Nat} {value : Value}
      (evaluated : Evaluates program environment ⟨expression, plan⟩ value middle)
      (endedOwn : middle.endSlot slot = some after) (usable : after.ResultUsable value) :
      Evaluates program environment ⟨expression, .endAfter slot plan⟩ value after
  | sequence {environment middle disposed after : Environment} {first rest : Expr} {firstPlan restPlan : CorePlan}
      {discarded value : Value} (head : Evaluates program environment ⟨first, firstPlan⟩ discarded middle)
      (dispose : Environment.Disposes program middle discarded disposed)
      (tail : Evaluates program disposed ⟨rest, restPlan⟩ value after) :
      Evaluates program environment ⟨.sequence first rest, .binary firstPlan restPlan⟩ value after
  | bind {environment middle localAfter after : Environment} {mutable : Bool} {name : String}
      {annotation : Option TypeExpr} {initial body : Expr} {initialPlan bodyPlan : CorePlan} {resident value : Value}
      (initialized : Evaluates program environment ⟨initial, initialPlan⟩ resident middle)
      (allowed : middle.ResultUsable resident)
      (continued : Evaluates program (middle.bind name resident) ⟨body, bodyPlan⟩ value localAfter)
      (cleanup : ∃ trace, Cleans program 1 localAfter trace after) (usable : after.ResultUsable value) :
      Evaluates program environment ⟨.bind mutable name annotation initial body, .binary initialPlan bodyPlan⟩ value after
  | assign {environment middle disposed updated after : Environment} {place : Place}
      {expression rest : Expr} {expressionPlan restPlan : CorePlan} {address : Address} {resident old value : Value}
      (evaluated : Evaluates program environment ⟨expression, expressionPlan⟩ resident middle)
      (resolved : middle.resolvePlace program place = some address) (free : middle.OwnerFree address)
      (previous : middle.at address = some old) (dispose : Environment.Disposes program middle old disposed)
      (allowed : disposed.ResultUsable resident) (written : disposed.writeAddress address resident = some updated)
      (continued : Evaluates program updated ⟨rest, restPlan⟩ value after) :
      Evaluates program environment ⟨.assign place expression rest, .binary expressionPlan restPlan⟩ value after
  | tuple {environment middle after : Environment} {head : Expr} {tail : List Expr}
      {headPlan : CorePlan} {tailPlans : List CorePlan} {first : Value} {rest : List Value}
      (headEval : Evaluates program environment ⟨head, headPlan⟩ first middle)
      (tailEval : EvaluatesMany program middle tail tailPlans rest after)
      (plain : first.ReferenceFree ∧ valuesReferenceFree rest) :
      Evaluates program environment ⟨.tuple head tail, .batch (headPlan :: tailPlans)⟩ (.tuple first rest) after
  | array {environment after : Environment} {elements : List Expr} {plans : List CorePlan} {values : List Value}
      (residents : EvaluatesMany program environment elements plans values after) (plain : valuesReferenceFree values) :
      Evaluates program environment ⟨.array elements, .batch plans⟩ (.array values) after
  | constant {environment constantAfter : Environment} {name : String} {declaration : ConstantDecl}
      {plan : CorePlan} {value : Value} (declared : program.constants name = some declaration)
      (initialized : Evaluates program environment.hide ⟨declaration.body, plan⟩ value constantAfter)
      (plain : value.ReferenceFree) :
      Evaluates program environment ⟨.constant name, .unary plan⟩ value (environment.resume constantAfter)
  | construct {environment after : Environment} {identity : Nat} {tag : Option Nat}
      {fields : List Expr} {plans : List CorePlan} {values : List Value}
      (residents : EvaluatesMany program environment fields plans values after) (plain : valuesReferenceFree values) :
      Evaluates program environment ⟨.construct identity tag fields, .batch plans⟩ (.nominal identity tag values) after
  | field {environment middle after : Environment} {body : Expr} {plan : CorePlan}
      {key : FieldKey} {parent value residual : Value}
      (source : Evaluates program environment ⟨body, plan⟩ parent middle)
      (selected : parent.readField program key = some value) (extracted : parent.takeField program key = some residual)
      (dispose : Environment.Disposes program middle residual after) (usable : after.ResultUsable value) :
      Evaluates program environment ⟨.field body key, .unary plan⟩ value after
  | call {environment middle localAfter cleaned : Environment} {identity : Nat} {arguments : List Expr}
      {argumentPlans : List CorePlan} {bodyPlan : CorePlan} {declaration : FunctionDecl}
      {values : List Value} {value : Value} (declared : program.functions identity = some declaration)
      (inputs : EvaluatesMany program environment arguments argumentPlans values middle)
      (body : Evaluates program (middle.hide.prepare (List.zip (declaration.parameters.map Prod.fst) values))
        ⟨declaration.body, bodyPlan⟩ value localAfter)
      (cleanup : ∃ trace, Cleans program (List.zip (declaration.parameters.map Prod.fst) values).length localAfter trace cleaned)
      (usable : cleaned.ResultUsable value) :
      Evaluates program environment ⟨.call identity arguments, .call argumentPlans bodyPlan⟩ value (middle.resume cleaned)
  | applyPatterns {environment middle localAfter after : Environment} {inputs : List Ty} {arguments : List Expr}
      {arms : List (PatternSource × Expr)} {argumentPlans : List CorePlan} {armPlans : List (PatternPlan × CorePlan)}
      {normalized : List (Pattern × Core)} {values : List Value} {bindings : List (String × Value)} {body : Core} {value : Value}
      (normalization : NormalizesArms program arms armPlans normalized)
      (argumentsEval : EvaluatesMany program environment arguments argumentPlans values middle)
      (plain : valuesReferenceFree values)
      (selected : ConsumesArm program (argumentValue values) normalized bindings body)
      (bodyEval : Evaluates program (middle.prepare bindings) body value localAfter)
      (cleanup : ∃ trace, Cleans program bindings.length localAfter trace after) (usable : after.ResultUsable value) :
      Evaluates program environment ⟨.applyPatterns inputs arguments arms, .patterns argumentPlans armPlans⟩ value after

inductive EvaluatesMany (program : Program) : Environment → List Expr → List CorePlan → List Value → Environment → Prop where
  | nil {environment : Environment} : EvaluatesMany program environment [] [] [] environment
  | cons {environment middle after : Environment} {head : Expr} {tail : List Expr}
      {headPlan : CorePlan} {tailPlans : List CorePlan} {first : Value} {rest : List Value}
      (headEval : Evaluates program environment ⟨head, headPlan⟩ first middle)
      (tailEval : EvaluatesMany program middle tail tailPlans rest after) (usable : after.ResultUsable first) :
      EvaluatesMany program environment (head :: tail) (headPlan :: tailPlans) (first :: rest) after
inductive NormalizesPattern (program : Program) : PatternSource → PatternPlan → Pattern → Prop where
  | wildcard : NormalizesPattern program .wildcard .leaf .wildcard
  | binder (name : String) : NormalizesPattern program (.binder name) .leaf (.binder name)
  | node {head : Head} {source : List PatternSource} {plans : List PatternPlan} {result : List Pattern}
      (fields : NormalizesPatterns program source plans result) :
      NormalizesPattern program (.node head source) (.node plans) (.node head result)
  | constantValue {name : String} {declaration : ConstantDecl} {type : Ty} {value : Value} {plan : CorePlan}
      (declared : program.constants name = some declaration) (resolved : ResolvesType program.aliases declaration.type type)
      {constantAfter : Environment} (evaluated : Evaluates program .empty ⟨.constant name, plan⟩ value constantAfter) :
      NormalizesPattern program (.constant name) (.constant plan) (.literal (some type) value)
inductive NormalizesPatterns (program : Program) : List PatternSource → List PatternPlan → List Pattern → Prop where
  | patternsNil : NormalizesPatterns program [] [] []
  | patternsCons {source : PatternSource} {sources : List PatternSource} {plan : PatternPlan} {plans : List PatternPlan}
      {result : Pattern} {results : List Pattern}
      (head : NormalizesPattern program source plan result) (tail : NormalizesPatterns program sources plans results) :
      NormalizesPatterns program (source :: sources) (plan :: plans) (result :: results)
inductive NormalizesArms (program : Program) : List (PatternSource × Expr) → List (PatternPlan × CorePlan) → List (Pattern × Core) → Prop where
  | armsNil : NormalizesArms program [] [] []
  | armsCons {source : PatternSource} {pattern : Pattern} {body : Expr} {patternPlan : PatternPlan} {bodyPlan : CorePlan}
      {sources : List (PatternSource × Expr)} {plans : List (PatternPlan × CorePlan)} {results : List (Pattern × Core)}
      (head : NormalizesPattern program source patternPlan pattern) (tail : NormalizesArms program sources plans results) :
      NormalizesArms program ((source, body) :: sources) ((patternPlan, bodyPlan) :: plans) ((pattern, ⟨body, bodyPlan⟩) :: results)
end

def ResultType.data (type : Ty) : ResultType := ⟨type, none⟩
def ResultType.nodes (result : ResultType) : List Nat := result.reference.toList
def resultNodes (results : List ResultType) : List Nat := results.flatMap ResultType.nodes

/-- The actual context producer assigns fresh identities when carriers are introduced. -/
def Context.prepare (parameters : List (String × BindingType)) (arguments : List ResultType) (context : Context) : Context :=
  (parameters.zip arguments).foldl (fun current entry => current.bind entry.1.1 entry.1.2.mutable entry.2) context

def Context.resume (caller after : Context) : Context := { after with names := caller.names }

/-- Cleanup checks current source permissions in the same youngest-first order as
runtime destruction. It does not assume that an execution or target lookup succeeds. -/
def Context.Cleanable (program : Program) (heldNodes : List Nat) : Context → List (String × Slot) → Prop
  | _, [] => True
  | context, (_, slot) :: slots =>
      slot.toBindingType.Disposable program ∧ context.Free ⟨.binder slot.binder, []⟩ ∧
      (∀ node, slot.reference = some node → node ∉ heldNodes) ∧
      (∀ node, slot.reference = some node → context.Restored node) ∧
      Context.Cleanable program heldNodes (context.dispose slot.reference) slots

inductive SlotsJoin (program : Program) : List (String × Slot) → List (String × Slot) → Prop where
  | nil : SlotsJoin program [] []
  | cons {name : String} {type : Ty} {mutable : Bool} {before after : Initialization}
      {binder : Nat} {reference : Option Nat} {slots joined : List (String × Slot)}
      (head : Initialization.Joins program.data type before after) (tail : SlotsJoin program slots joined) :
      SlotsJoin program ((name, ⟨⟨type, mutable, before⟩, binder, reference⟩) :: slots)
        ((name, ⟨⟨type, mutable, after⟩, binder, reference⟩) :: joined)

/-- A join changes only the authoritative initialization mask. Storage presence
and its immutable identity, type, and carrier metadata are preserved. -/
inductive CellJoin (program : Program) : Option Slot → Option Slot → Prop where
  | absent : CellJoin program none none
  | resident {type : Ty} {mutable : Bool} {before after : Initialization}
      {binder : Nat} {reference : Option Nat}
      (state : Initialization.Joins program.data type before after) :
      CellJoin program (some ⟨⟨type, mutable, before⟩, binder, reference⟩)
        (some ⟨⟨type, mutable, after⟩, binder, reference⟩)

theorem CellJoin.forward {before after : Option Slot} (joined : CellJoin program before after)
    {slot : Slot} (found : before = some slot) :
    ∃ current, after = some current ∧ current.metadata = slot.metadata ∧
      Initialization.Joins program.data slot.type slot.initialization current.initialization := by
  cases joined with
  | absent => cases found
  | resident state => cases found; exact ⟨_, rfl, rfl, state⟩

theorem CellJoin.backward {before after : Option Slot} (joined : CellJoin program before after)
    {slot : Slot} (found : after = some slot) :
    ∃ original, before = some original ∧ slot.metadata = original.metadata ∧
      Initialization.Joins program.data original.type original.initialization slot.initialization := by
  cases joined with
  | absent => cases found
  | resident state => cases found; exact ⟨_, rfl, rfl, state⟩

/-- Branch joins must preserve exact loan history, origins, handle identities and
input interpretation. Only supported initialization and fresh-ID supply may weaken. -/
structure Context.Joins (program : Program) (before after : Context) : Prop where
  names : after.names = before.names
  storage : ∀ origin, CellJoin program (before.storage origin) (after.storage origin)
  loans : after.loans = before.loans
  inputs : after.inputCount = before.inputCount
  supply : before.nextBinder ≤ after.nextBinder
  targetMasks : ∀ (node : Nat) (loan : SourceLoan), before.loans[node]? = some loan → loan.own = true →
    ∀ (binder : Nat) (old current : Slot) (state : Initialization), loan.target.base = .binder binder →
      before.storage (.binder binder) = some old → after.storage (.binder binder) = some current →
      old.initialization.Access loan.target.fields state →
      ∃ next, current.initialization.Access loan.target.fields next ∧ (state.Complete → next.Complete)

theorem Context.Joins.slots {before after : Context} (joined : Context.Joins program before after) :
    SlotsJoin program before.bindings after.bindings := by
  unfold Context.bindings
  rw [joined.names]
  have view (names : List (String × Nat)) :
      SlotsJoin program
        (names.filterMap fun entry => (before.storage (.binder entry.2)).map fun slot => (entry.1, slot))
        (names.filterMap fun entry => (after.storage (.binder entry.2)).map fun slot => (entry.1, slot)) := by
    induction names with
    | nil => exact .nil
    | cons entry names ih =>
        simp only [List.filterMap_cons]
        have cells := joined.storage (.binder entry.2)
        generalize before.storage (.binder entry.2) = old at cells ⊢
        generalize after.storage (.binder entry.2) = current at cells ⊢
        cases cells with
        | absent => exact ih
        | resident state => exact SlotsJoin.cons state ih
  exact view before.names

inductive AccessType (program : Program) (home : Module) (context : Context) (mode : BorrowMode) : AccessPlace → Origin → Ty → Option Nat → Prop where
  | owner {place : Place} {slot : Slot} {indices : List Nat} {state : Initialization} {type : Ty}
      (selected : lookup place.root context.bindings = some slot)
      (access : slot.initialization.Access indices state)
      (path : PathType program home slot.type place.fields indices type)
      (authority : mode = .unique → slot.mutable = true) :
      AccessType program home context mode (.owner place) ⟨.binder slot.binder, indices⟩ type none
  | dereference {reference : Place} {fields : List FieldKey} {slot : Slot} {node : Nat}
      {loan : SourceLoan} {indices : List Nat} {type : Ty}
      (selected : lookup reference.root context.bindings = some slot) (direct : reference.fields = [])
      (handle : slot.reference = some node) (shape : slot.type = .reference loan.referent loan.mode)
      (initialized : slot.initialization.Complete) (found : context.loans[node]? = some loan) (own : loan.own = true)
      (path : PathType program home loan.referent fields indices type)
      (target : context.Target program (loan.target.extend indices) type)
      (authority : mode = .unique → loan.mode = .unique) :
      AccessType program home context mode (.dereference reference fields) (loan.target.extend indices) type (some node)

/-- Only unambiguous single-reference-input result elision is admitted. Multiple
reference inputs may alias, but cannot yield a reference without an explicit source contract. -/
def Context.Returns (context : Context) (arguments : List ResultType) (result : ResultType) : Prop :=
  match result.reference with
  | none => True
  | some node => ∃ input, resultNodes arguments = [input] ∧ context.Derived node input
mutual
inductive HasType (program : Program) : Module → Context → List Nat → Expr → ResultType → Context → CorePlan → (expected : Option Ty := none) → Prop where
  | unit {home : Module} {context : Context} {held : List Nat} :
      HasType program home context held .unit (.data .unit) context .leaf
  | integer {home : Module} {context : Context} {held : List Nat} {type : IntegerType} {magnitude : Nat}
      (fits : type.Contains program.target magnitude) :
      HasType program home context held (.integer type magnitude) (.data (.integer type)) context .leaf
  | character {home : Module} {context : Context} {held : List Nat} {number : Nat} (valid : UnicodeScalar number) :
      HasType program home context held (.character number) (.data .character) context .leaf
  | group {expected : Option Ty} {home : Module} {context after : Context} {held : List Nat} {body : Expr} {result : ResultType} {plan : CorePlan}
      (typed : HasType program home context held body result after plan expected) :
      HasType program home context held (.group body) result after (.unary plan) expected

  | read {home : Module} {context : Context} {held : List Nat} {place : Place} {slot : Slot}
      {type : Ty} {indices : List Nat} {state : Initialization}
      (selected : lookup place.root context.bindings = some slot) (access : slot.initialization.Access indices state)
      (initialized : state.Complete) (path : PathType program home slot.type place.fields indices type)
      (shape : type.DataShape) (copyable : Duplicable program.data type)
      (permitted : context.Permits .shared none ⟨.binder slot.binder, indices⟩) :
      HasType program home context held (.read place) (.data type) context .leaf
  | copyShared {home : Module} {context : Context} {held : List Nat} {place : Place} {slot : Slot}
      {node : Nat} {loan : SourceLoan}
      (selected : lookup place.root context.bindings = some slot) (direct : place.fields = [])
      (handle : slot.reference = some node) (shape : slot.type = .reference loan.referent loan.mode)
      (initialized : slot.initialization.Complete) (found : context.loans[node]? = some loan) (own : loan.own = true)
      (copyable : Duplicable program.data (.reference loan.referent loan.mode))
      (permitted : context.Permits .shared none ⟨.binder slot.binder, []⟩) :
      HasType program home context held (.read place) ⟨.reference loan.referent, some context.loans.length⟩
        (context.borrow loan.target loan.referent (some node) .shared) .leaf
  | move {home : Module} {context : Context} {held : List Nat} {place : Place} {slot : Slot}
      {type : Ty} {indices : List Nat} {state : Initialization} {slots : List (String × Slot)}
      (selected : lookup place.root context.bindings = some slot) (access : slot.initialization.Access indices state)
      (initialized : state.Complete) (path : PathType program home slot.type place.fields indices type)
      (shape : type.DataShape) (data : slot.reference = none) (free : context.Free ⟨.binder slot.binder, indices⟩)
      (cleared : replaceBinding place.root { slot with initialization := slot.initialization.write indices .vacant }
        context.bindings = some slots) :
      HasType program home context held (.move place) (.data type) (context.withSlots slots) .leaf
  /-- Default owned use shares the explicit transfer contract for data and handles.
  Reference expectations cannot enter this rule: they require a fresh reborrow. -/
  | implicitMove {home : Module} {context after : Context} {held : List Nat} {place : Place} {result : ResultType}
      (noncopy : Nonduplicable program.data result.type)
      (moved : HasType program home context held (.move place) result after .leaf) :
      HasType program home context held (.read place) result after .implicitMove
  | moveReference {home : Module} {context : Context} {held : List Nat} {place : Place} {slot : Slot}
      {node : Nat} {referent : Ty} {mode : BorrowMode} {slots : List (String × Slot)}
      (selected : lookup place.root context.bindings = some slot) (direct : place.fields = [])
      (handle : slot.reference = some node) (shape : slot.type = .reference referent mode)
      (initialized : slot.initialization.Complete) (own : context.Own node)
      (ready : context.Restored node)
      (free : context.Free ⟨.binder slot.binder, []⟩)
      (cleared : replaceBinding place.root { slot with initialization := .vacant, reference := none }
        context.bindings = some slots) :
      HasType program home context held (.move place) ⟨.reference referent mode, some node⟩ (context.withSlots slots) .leaf
  | borrow {home : Module} {context : Context} {held : List Nat} {place : AccessPlace}
      {target : Origin} {referent : Ty} {parent : Option Nat} {mode : BorrowMode}
      (access : AccessType program home context mode place target referent parent)
      (ready : context.AccessReady target parent)
      (permitted : context.Permits mode parent target)
      (finite : FiniteLayout program.target program.data referent) :
      HasType program home context held (.borrow mode place) ⟨.reference referent mode, some context.loans.length⟩
        (context.borrow target referent parent mode) .leaf
  | dereference {home : Module} {context : Context} {held : List Nat} {reference : Place} {fields : List FieldKey}
      {target : Origin} {type : Ty} {parent : Option Nat}
      (access : AccessType program home context .shared (.dereference reference fields) target type parent)
      (ready : context.AccessReady target parent)
      (permitted : context.Permits .shared parent target)
      (copyable : Duplicable program.data type) (shape : type.DataShape) :
      HasType program home context held (.dereference reference fields) (.data type) context .leaf
  | moveIndirect {home : Module} {context : Context} {held : List Nat} {reference : Place} {fields : List FieldKey}
      {target : Origin} {type : Ty} {node : Nat}
      (access : AccessType program home context .unique (.dereference reference fields) target type (some node))
      (ready : context.AccessReady target (some node))
      (permitted : context.Permits .unique (some node) target) (shape : type.DataShape)
      (pending : ∀ heldNode ∈ held, ∀ loan, context.loans[heldNode]? = some loan → loan.own = true → target.Apart loan.target) :
      HasType program home context held (.moveIndirect reference fields) (.data type) (context.writeTarget target .vacant) .leaf
  | assignIndirect {expected : Option Ty} {home : Module} {context middle after : Context} {held : List Nat}
      {reference : Place} {fields : List FieldKey} {value rest : Expr} {target : Origin} {type : Ty} {node : Nat}
      {result : ResultType} {valuePlan restPlan : CorePlan} {slot : Slot} {state : Initialization}
      (resident : HasType program home context held value (.data type) middle valuePlan)
      (access : AccessType program home middle .unique (.dereference reference fields) target type (some node))
      (permitted : middle.Permits .unique (some node) target) (shape : type.DataShape)
      (stored : middle.storage target.base = some slot) (selected : slot.initialization.Access target.fields state)
      (discard : StorageDisposition program state type)
      (continued : HasType program home (middle.writeTarget target .full) held rest result after restPlan expected) :
      HasType program home context held (.assignIndirect reference fields value rest) result after (.binary valuePlan restPlan) expected
  | endOwn {expected : Option Ty} {home : Module} {context after : Context} {held : List Nat} {expression : Expr} {result : ResultType}
      {slotIndex node : Nat} {binding : String × Slot} {plan : CorePlan}
      (selected : context.bindings[slotIndex]? = some binding) (handle : binding.2.reference = some node)
      (unprotected : node ∉ held) (ready : context.Restored node)
      (continued : HasType program home (context.endOwn node) held expression result after plan expected) :
      HasType program home context held expression result after (.endOwn slotIndex plan) expected

  | endAfter {expected : Option Ty} {home : Module} {context middle : Context} {held : List Nat} {expression : Expr} {result : ResultType}
      {slotIndex node : Nat} {binding : String × Slot} {plan : CorePlan}
      (evaluated : HasType program home context held expression result middle plan expected)
      (selected : middle.bindings[slotIndex]? = some binding) (handle : binding.2.reference = some node)
      (unprotected : node ∉ held ++ result.nodes) (ready : middle.Restored node) :
      HasType program home context held expression result (middle.endOwn node) (.endAfter slotIndex plan) expected

  | raiseSupply {expected : Option Ty} {home : Module} {context after : Context} {held : List Nat} {expression : Expr}
      {result : ResultType} {plan : CorePlan} {supply : Nat}
      (typed : HasType program home context held expression result after plan expected) (larger : after.nextBinder ≤ supply) :
      HasType program home context held expression result { after with nextBinder := supply } plan expected

  | sequence {expected : Option Ty} {home : Module} {context middle after : Context} {held : List Nat} {first rest : Expr}
      {discarded result : ResultType} {firstPlan restPlan : CorePlan}
      (head : HasType program home context held first discarded middle firstPlan) (drop : MayDiscard program.data discarded.type)
      (tail : HasType program home (middle.dispose discarded.reference) held rest result after restPlan expected) :
      HasType program home context held (.sequence first rest) result after (.binary firstPlan restPlan) expected

  | bind {expected : Option Ty} {home : Module} {context middle bodyAfter : Context} {held : List Nat} {mutable : Bool} {name : String}
      {annotation : Option TypeExpr} {initial body : Expr} {localType result : ResultType} {initialPlan bodyPlan : CorePlan}
      (initialized : HasType program home context held initial localType middle initialPlan (annotation.map (fun _ => localType.type)))
      (annotated : Annotation program.aliases annotation localType.type)
      (continued : HasType program home (middle.bind name mutable localType) held body result bodyAfter bodyPlan expected)
      (cleanup : bodyAfter.Cleanable program (held ++ result.nodes) (bodyAfter.bindings.take 1)) :
      HasType program home context held (.bind mutable name annotation initial body) result
        (bodyAfter.cleanup 1) (.binary initialPlan bodyPlan) expected

  | tuple {home : Module} {context middle after : Context} {held : List Nat} {head : Expr} {tail : List Expr}
      {first : Ty} {rest : List Ty} {headPlan : CorePlan} {tailPlans : List CorePlan}
      (headTyped : HasType program home context held head (.data first) middle headPlan)
      (tailTyped : HasTypes program home middle held tail (rest.map ResultType.data) after tailPlans)
      (shape : first.DataShape ∧ typesDataShape rest) :
      HasType program home context held (.tuple head tail) (.data (.tuple first rest)) after (.batch (headPlan :: tailPlans))
  | array {home : Module} {context after : Context} {held : List Nat} {elements : List Expr}
      {element : Ty} {length : Nat} {plans : List CorePlan}
      (residents : HasTypes program home context held elements (List.replicate length (.data element)) after plans)
      (elementValid : FiniteLayout program.target program.data element) (size : length < 2 ^ program.target.pointerBits) :
      HasType program home context held (.array elements) (.data (.array element length)) after (.batch plans)
  | constant {home : Module} {context constantAfter : Context} {held : List Nat} {name : String}
      {declaration : ConstantDecl} {type : Ty} {plan : CorePlan} (declared : program.constants name = some declaration)
      (visible : declaration.visibility.Allows declaration.home home) (resolved : ResolvesType program.aliases declaration.type type)
      (structural : Structural declaration.body) (shape : type.DataShape)
      (initialized : HasType program declaration.home context.hide held declaration.body (.data type) constantAfter plan) :
      HasType program home context held (.constant name) (.data type) (context.resume constantAfter) (.unary plan)
  | construct {home : Module} {context after : Context} {held : List Nat} {identity : Nat} {tag : Option Nat}
      {declaration : DataDecl} {schema : Fields} {fields : List Expr} {plans : List CorePlan}
      (declared : program.data identity = some declaration) (chosen : declaration.constructor tag = some schema)
      (finite : FiniteLayout program.target program.data (.nominal identity))
      (capability : UsePermission program.data (.nominal identity) .exact) (visible : declaration.visibility.Allows declaration.home home)
      (access : ∀ field ∈ schema.residents, field.visibility.Allows declaration.home home)
      (residents : HasTypes program home context held fields (schema.residents.map (fun field => ResultType.data field.type)) after plans) :
      HasType program home context held (.construct identity tag fields) (.data (.nominal identity)) after (.batch plans)
  | field {home : Module} {context after : Context} {held : List Nat} {body : Expr} {key : FieldKey}
      {parentType type : Ty} {index : Nat} {plan : CorePlan}
      (source : HasType program home context held body (.data parentType) after plan)
      (discard : StorageDisposition program (Initialization.full.setChild index .vacant) parentType)
      (selected : ProjectionType program home parentType key index type) (shape : type.DataShape) :
      HasType program home context held (.field body key) (.data type) after (.unary plan)
  | call {home : Module} {context middle bodyAfter : Context} {held : List Nat} {identity : Nat}
      {arguments : List Expr} {argumentTypes : List ResultType} {result : ResultType}
      {argumentPlans : List CorePlan} {bodyPlan : CorePlan} {declaration : FunctionDecl}
      (declared : program.functions identity = some declaration) (visible : declaration.visibility.Allows declaration.home home)
      (distinct : (declaration.parameters.map Prod.fst).Nodup)
      (initialized : ∀ parameter ∈ declaration.parameters, parameter.2.initialization = .full)
      (inputs : HasTypes program home context held arguments argumentTypes middle argumentPlans
        (some (declaration.parameters.map (fun parameter => parameter.2.type))))
      (body : HasType program declaration.home (middle.hide.prepare declaration.parameters argumentTypes) held
        declaration.body result bodyAfter bodyPlan (some declaration.result))
      (resultType : result.type = declaration.result) (origin : bodyAfter.Returns argumentTypes result)
      (cleanup : bodyAfter.Cleanable program (held ++ result.nodes) (bodyAfter.bindings.take declaration.parameters.length)) :
      HasType program home context held (.call identity arguments) result
        (middle.resume (bodyAfter.cleanup declaration.parameters.length)) (.call argumentPlans bodyPlan)
  | assign {expected : Option Ty} {home : Module} {context middle after : Context} {held : List Nat} {place : Place}
      {value rest : Expr} {slot : Slot} {target : Ty} {result : ResultType} {valuePlan restPlan : CorePlan}
      {indices : List Nat} {state : Initialization} {slots : List (String × Slot)}
      (resident : HasType program home context held value (.data target) middle valuePlan)
      (selected : lookup place.root middle.bindings = some slot) (writable : slot.mutable = true)
      (available : slot.initialization.Access indices state) (path : PathType program home slot.type place.fields indices target)
      (shape : target.DataShape) (data : slot.reference = none) (discard : StorageDisposition program state target)
      (free : middle.Free ⟨.binder slot.binder, indices⟩)
      (written : replaceBinding place.root { slot with initialization := slot.initialization.write indices .full }
        middle.bindings = some slots)
      (continued : HasType program home (middle.withSlots slots) held rest result after restPlan expected) :
      HasType program home context held (.assign place value rest) result after (.binary valuePlan restPlan) expected

  | assignReference {expected : Option Ty} {home : Module} {context middle after : Context} {held : List Nat} {place : Place}
      {value rest : Expr} {slot : Slot} {referent : Ty} {mode : BorrowMode} {node : Nat} {result : ResultType}
      {valuePlan restPlan : CorePlan} {slots : List (String × Slot)}
      (resident : HasType program home context held value ⟨.reference referent mode, some node⟩ middle valuePlan
        (some (.reference referent mode)))
      (selected : lookup place.root middle.bindings = some slot) (writable : slot.mutable = true)
      (direct : place.fields = []) (shape : slot.type = .reference referent mode)
      (free : middle.Free ⟨.binder slot.binder, []⟩)
      (unprotected : ∀ old, slot.reference = some old → old ∉ held ++ [node])
      (ready : ∀ old, slot.reference = some old → middle.Restored old)
      (written : replaceBinding place.root { slot with initialization := .full, reference := some node }
        middle.bindings = some slots)
      (continued : HasType program home ((middle.dispose slot.reference).withSlots slots) held rest result after restPlan expected) :
      HasType program home context held (.assign place value rest) result after (.binary valuePlan restPlan) expected

  | applyPatterns {expected : Option Ty} {home : Module} {context middle after : Context} {held : List Nat} {inputs : List Ty}
      {arguments : List Expr} {arms : List (PatternSource × Expr)} {result : ResultType}
      {argumentPlans : List CorePlan} {armPlans : List (PatternPlan × CorePlan)}
      (argumentsTyped : HasTypes program home context held arguments (inputs.map ResultType.data) middle argumentPlans)
      (shape : typesDataShape inputs) (nonempty : arms ≠ []) (constants : ArmConstantsTyped program home arms armPlans)
      (covered : ∀ normalized, NormalizesArms program arms armPlans normalized →
        Covers program [argumentType inputs] (normalized.map (fun arm => [arm.1])))
      (bodies : ∀ normalized, NormalizesArms program arms armPlans normalized →
        ArmsType program home middle held (argumentType inputs) result [] normalized after expected) :
      HasType program home context held (.applyPatterns inputs arguments arms) result after (.patterns argumentPlans armPlans) expected

  | expectedData {home : Module} {context after : Context} {held : List Nat} {expression : Expr}
      {result : ResultType} {plan : CorePlan}
      (typed : HasType program home context held expression result after plan) (shape : result.type.DataShape) :
      HasType program home context held expression result after plan (some result.type)
  | expectedMove {home : Module} {context after : Context} {held : List Nat} {place : Place}
      {result : ResultType} {plan : CorePlan}
      (typed : HasType program home context held (.move place) result after plan) :
      HasType program home context held (.move place) result after plan (some result.type)
  | expectedBorrow {home : Module} {context after : Context} {held : List Nat} {place : AccessPlace}
      {mode : BorrowMode} {result : ResultType} {plan : CorePlan}
      (typed : HasType program home context held (.borrow mode place) result after plan) :
      HasType program home context held (.borrow mode place) result after plan (some result.type)
  | expectedCall {home : Module} {context after : Context} {held : List Nat} {identity : Nat} {arguments : List Expr}
      {result : ResultType} {plan : CorePlan}
      (typed : HasType program home context held (.call identity arguments) result after plan) :
      HasType program home context held (.call identity arguments) result after plan (some result.type)
  | reborrow {home : Module} {context : Context} {held : List Nat} {place : Place}
      {target : Origin} {referent : Ty} {parent : Option Nat} {mode : BorrowMode}
      (access : AccessType program home context mode (.dereference place []) target referent parent)
      (ready : context.AccessReady target parent) (permitted : context.Permits mode parent target)
      (finite : FiniteLayout program.target program.data referent) :
      HasType program home context held (.read place) ⟨.reference referent mode, some context.loans.length⟩
        (context.borrow target referent parent mode) (.reborrow mode) (some (.reference referent mode))

inductive HasTypes (program : Program) : Module → Context → List Nat → List Expr → List ResultType → Context → List CorePlan → (expected : Option (List Ty) := none) → Prop where
  | nil {home : Module} {context : Context} {held : List Nat} : HasTypes program home context held [] [] context []
  | cons {home : Module} {context middle after : Context} {held : List Nat} {head : Expr} {tail : List Expr}
      {first : ResultType} {rest : List ResultType} {headPlan : CorePlan} {tailPlans : List CorePlan}
      (headTyped : HasType program home context held head first middle headPlan)
      (tailTyped : HasTypes program home middle (held ++ first.nodes) tail rest after tailPlans) :
      HasTypes program home context held (head :: tail) (first :: rest) after (headPlan :: tailPlans)
  | expectedNil {home : Module} {context : Context} {held : List Nat} :
      HasTypes program home context held [] [] context [] (some [])
  | expectedCons {home : Module} {context middle after : Context} {held : List Nat} {head : Expr} {tail : List Expr}
      {first : ResultType} {rest : List ResultType} {headPlan : CorePlan} {tailPlans : List CorePlan} {types : List Ty}
      (headTyped : HasType program home context held head first middle headPlan (some first.type))
      (tailTyped : HasTypes program home middle (held ++ first.nodes) tail rest after tailPlans (some types)) :
      HasTypes program home context held (head :: tail) (first :: rest) after (headPlan :: tailPlans) (some (first.type :: types))
inductive ArmsType (program : Program) :
    Module → Context → List Nat → Ty → ResultType → List Pattern → List (Pattern × Core) → Context → (expected : Option Ty := none) → Prop where
  | empty {expected : Option Ty} {home : Module} {context after : Context} {held : List Nat} {subject : Ty} {result : ResultType} {previous : List Pattern} :
      ArmsType program home context held subject result previous [] after expected
  | clause {expected : Option Ty} {home : Module} {context bodyAfter after : Context} {held : List Nat} {subject : Ty} {result : ResultType}
      {previous : List Pattern} {pattern : Pattern} {body : Core} {rest : List (Pattern × Core)}
      {bindings : List (String × BindingType)} (patternTyped : PatternType program home pattern subject bindings)
      (distinct : (bindings.map Prod.fst).Nodup) (useful : Useful program subject previous pattern)
      (bodyTyped : HasType program home (context.prepare bindings (bindings.map (fun binding => ResultType.data binding.2.type)))
        held body.source result bodyAfter body.plan expected)
      (cleanup : bodyAfter.Cleanable program (held ++ result.nodes) (bodyAfter.bindings.take bindings.length))
      (joined : (bodyAfter.cleanup bindings.length).Joins program after)
      (tailTyped : ArmsType program home context held subject result (previous ++ [pattern]) rest after expected) :
      ArmsType program home context held subject result previous ((pattern, body) :: rest) after expected
/-- Constant plans are emitted by the same producer before normalization; no
successful normalization, transition or future-world witness is an admission input. -/
inductive PatternConstantsTyped (program : Program) : Module → PatternSource → PatternPlan → Prop where
  | patternWildcard {home : Module} : PatternConstantsTyped program home .wildcard .leaf
  | patternBinder {home : Module} (name : String) : PatternConstantsTyped program home (.binder name) .leaf
  | patternNode {home : Module} {head : Head} {fields : List PatternSource} {plans : List PatternPlan}
      (headSource : head.Source) (constants : PatternsConstantsTyped program home fields plans) :
      PatternConstantsTyped program home (.node head fields) (.node plans)
  | patternConstant {home : Module} {name : String} {type : Ty} {plan : CorePlan}
      (typed : HasType program home .empty [] (.constant name) (.data type) .empty plan) :
      PatternConstantsTyped program home (.constant name) (.constant plan)
inductive PatternsConstantsTyped (program : Program) : Module → List PatternSource → List PatternPlan → Prop where
  | patternsEmpty {home : Module} : PatternsConstantsTyped program home [] []
  | patternsCons {home : Module} {first : PatternSource} {rest : List PatternSource} {plan : PatternPlan} {plans : List PatternPlan}
      (head : PatternConstantsTyped program home first plan) (tail : PatternsConstantsTyped program home rest plans) :
      PatternsConstantsTyped program home (first :: rest) (plan :: plans)
inductive ArmConstantsTyped (program : Program) : Module → List (PatternSource × Expr) → List (PatternPlan × CorePlan) → Prop where
  | armsEmpty {home : Module} : ArmConstantsTyped program home [] []
  | armsCons {home : Module} {pattern : PatternSource} {body : Expr} {rest : List (PatternSource × Expr)}
      {patternPlan : PatternPlan} {bodyPlan : CorePlan} {plans : List (PatternPlan × CorePlan)}
      (head : PatternConstantsTyped program home pattern patternPlan) (tail : ArmConstantsTyped program home rest plans) :
      ArmConstantsTyped program home ((pattern, body) :: rest) ((patternPlan, bodyPlan) :: plans)
end



theorem Value.replaceChild_readback {value replacement updated : Value} {index : Nat}
    (written : value.replaceChild index replacement = some updated) :
    updated.children[index]? = some replacement := by
  cases value with
  | vacant | unit | integer | character | array | reference => simp [Value.replaceChild] at written
  | tuple head tail =>
    cases index with
    | zero => cases Option.some.inj written; rfl
    | succ index =>
      obtain ⟨old, found, same⟩ := Option.map_eq_some_iff.mp written
      cases same
      obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
      simp [Value.children, bound]
  | nominal identity tag fields =>
    obtain ⟨old, found, same⟩ := Option.map_eq_some_iff.mp written
    cases same
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
    simp [Value.children, bound]

theorem Value.replaceChild_fieldIndex {value replacement updated : Value} {index : Nat}
    (written : value.replaceChild index replacement = some updated) :
    ∀ key, updated.fieldIndex program key = value.fieldIndex program key := by
  cases value with
  | vacant | unit | integer | character | array | reference => simp [Value.replaceChild] at written
  | tuple head tail =>
    cases index with
    | zero => cases Option.some.inj written; intro key; cases key <;> rfl
    | succ index =>
      obtain ⟨old, _, same⟩ := Option.map_eq_some_iff.mp written
      cases same
      intro key; cases key <;> rfl
  | nominal identity tag fields =>
    obtain ⟨old, _, same⟩ := Option.map_eq_some_iff.mp written
    cases same
    intro key; cases tag <;> cases key <;> rfl

theorem Value.replaceChild_frame {value replacement updated : Value} {index other : Nat}
    (written : value.replaceChild index replacement = some updated) (different : other ≠ index) :
    updated.children[other]? = value.children[other]? := by
  cases value with
  | vacant | unit | integer | character | array | reference => simp [Value.replaceChild] at written
  | tuple head tail =>
    cases index with
    | zero =>
      cases Option.some.inj written
      cases other with
      | zero => exact False.elim (different rfl)
      | succ other => rfl
    | succ index =>
      obtain ⟨old, _, same⟩ := Option.map_eq_some_iff.mp written
      cases same
      cases other with
      | zero => rfl
      | succ other =>
        have unequal : other ≠ index := fun equal => different (congrArg Nat.succ equal)
        simp [Value.children, Ne.symm unequal]
  | nominal identity tag fields =>
    obtain ⟨old, _, same⟩ := Option.map_eq_some_iff.mp written
    cases same
    simp [Value.children, Ne.symm different]

/-- Exact resident framing, not just preservation of initialization masks. -/
theorem Value.writeIndices_frame {value replacement updated : Value} {indices observed : List Nat}
    (written : value.writeIndices indices replacement = some updated) (apart : CoordinatesApart indices observed) :
    updated.readIndices observed = value.readIndices observed := by
  induction apart generalizing value updated with
  | siblings different =>
    simp only [Value.writeIndices, Bind.bind, Option.bind_eq_some_iff] at written
    obtain ⟨child, _, next, _, replaced⟩ := written
    simp only [Value.readIndices, Value.replaceChild_frame replaced (Ne.symm different)]
  | descend apart ih =>
    simp only [Value.writeIndices, Bind.bind, Option.bind_eq_some_iff] at written
    obtain ⟨child, found, next, changed, replaced⟩ := written
    simp only [Value.readIndices, Bind.bind, Value.replaceChild_readback replaced, found, Option.bind_some, ih changed]

theorem Value.writeIndices_readback {value replacement updated : Value} {indices : List Nat}
    (written : value.writeIndices indices replacement = some updated) :
    updated.readIndices indices = some replacement := by
  induction indices generalizing value updated with
  | nil => cases Option.some.inj written; rfl
  | cons index indices ih =>
    simp only [Value.writeIndices, Bind.bind, Option.bind_eq_some_iff] at written
    obtain ⟨child, found, next, changed, replaced⟩ := written
    have readback := Value.replaceChild_readback replaced
    simp [Value.readIndices, readback, ih changed]

/-- Updating a selected slot preserves the resolution of its source spelling. -/
theorem Value.resolvePath_write {value replacement updated : Value} {keys : List FieldKey} {indices : List Nat}
    (resolved : value.resolvePath program keys = some indices)
    (written : value.writeIndices indices replacement = some updated) :
    updated.resolvePath program keys = some indices := by
  induction keys generalizing value updated indices with
  | nil => simp only [Value.resolvePath, Option.some.injEq] at resolved; subst indices; rfl
  | cons key keys ih =>
    simp only [Value.resolvePath, Bind.bind, Option.bind_eq_some_iff] at resolved
    obtain ⟨index, indexed, child, found, rest, tail, same⟩ := resolved
    cases same
    simp only [Value.writeIndices, Bind.bind, found, Option.bind_some, Option.bind_eq_some_iff] at written
    obtain ⟨next, changed, replaced⟩ := written
    have indexSame := Value.replaceChild_fieldIndex (program := program) replaced
    have readback := Value.replaceChild_readback replaced
    simp [Value.resolvePath, indexSame, indexed, readback, ih tail changed]

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

theorem Environment.writeAddress_readback {address : Address} {replacement : Value} {before after : Environment}
    (written : before.writeAddress address replacement = some after) :
    after.at address = some replacement := by
  simp only [Environment.writeAddress, Bind.bind, Option.bind_eq_some_iff] at written
  obtain ⟨parent, found, updated, changed, same⟩ := written
  cases same
  simp [Environment.at, Environment.put, Value.writeIndices_readback changed]

/-- The concrete update contract preserves every disjoint address, including
siblings below a shared aggregate prefix; it also returns the exact written slot. -/
structure Environment.AddressUpdate (before after : Environment) (address : Address) (replacement : Value) : Prop where
  bindings : after.bindings = before.bindings
  supply : after.nextRoot = before.nextRoot
  readback : after.at address = some replacement
  frame : ∀ observed, address.Apart observed → after.at observed = before.at observed

theorem Environment.writeAddress_update {address : Address} {replacement : Value} {before after : Environment}
    (written : before.writeAddress address replacement = some after) : before.AddressUpdate after address replacement := by
  have readback := Environment.writeAddress_readback written
  simp only [Environment.writeAddress, Bind.bind, Option.bind_eq_some_iff] at written
  obtain ⟨parent, found, updated, changed, same⟩ := written
  cases same
  refine ⟨rfl, rfl, readback, ?_⟩
  intro observed apart
  rcases apart with different | apart
  · simp [Environment.at, Environment.put, Ne.symm different]
  · by_cases equal : observed.root = address.root
    · simp [Environment.at, Environment.put, equal, found, Value.writeIndices_frame changed apart]
    · simp [Environment.at, Environment.put, equal]


theorem Environment.resolvePlace_write {place : Place} {address : Address} {replacement : Value} {before after : Environment}
    (resolved : before.resolvePlace program place = some address)
    (written : before.writeAddress address replacement = some after) :
    after.resolvePlace program place = some address := by
  simp only [Environment.resolvePlace, Bind.bind, Option.bind_eq_some_iff] at resolved
  obtain ⟨root, named, parent, found, indices, path, same⟩ := resolved
  cases same
  simp only [Environment.writeAddress, Bind.bind, found, Option.bind_some, Option.bind_eq_some_iff] at written
  obtain ⟨updated, changed, same⟩ := written
  cases same
  simp [Environment.resolvePlace, Environment.put, named, Value.resolvePath_write path changed]

theorem Environment.takeAddress_eq_some {address : Address} {before after : Environment} {value : Value} :
    before.takeAddress address = some (value, after) ↔
      before.readAddress address = some value ∧ before.writeAddress address .vacant = some after := by
  simp [Environment.takeAddress, Bind.bind, Option.bind_eq_some_iff]


theorem Environment.takeAddress_invalidates {address : Address} {before after : Environment} {value : Value}
    (taken : before.takeAddress address = some (value, after)) : after.readAddress address = none := by
  have readback := (Environment.writeAddress_update (Environment.takeAddress_eq_some.mp taken).2).readback
  simp [Environment.readAddress, readback, Value.initialized]

/-- An actual move keeps the canonical source address and invalidates its resident. -/
theorem Evaluates.move_invalidates {place : Place} {before after : Environment} {value : Value}
    (evaluated : Evaluates program before ⟨.move place, .leaf⟩ value after) :
    ∃ address, before.resolvePlace program place = some address ∧
      after.resolvePlace program place = some address ∧ after.readAddress address = none := by
  cases evaluated with
  | move resolved free allowed taken => exact ⟨_, resolved,
      Environment.resolvePlace_write resolved (Environment.takeAddress_eq_some.mp taken).2,
      Environment.takeAddress_invalidates taken⟩

/-- Default transfer invalidates exactly the same source resident as explicit move. -/
theorem Evaluates.implicitMove_invalidates {place : Place} {before after : Environment} {value : Value}
    (evaluated : Evaluates program before ⟨.read place, .implicitMove⟩ value after) :
    ∃ address, before.resolvePlace program place = some address ∧
      after.resolvePlace program place = some address ∧ after.readAddress address = none := by
  cases evaluated with
  | implicitMove moved => exact moved.move_invalidates

/-- Owned projection transfers its child before cleanup. No event can target
that child's former slot or descendants, even when its type is not Copy. -/
theorem Evaluates.field_protects_result {before after : Environment} {body : Expr} {plan : CorePlan} {key : FieldKey} {value : Value}
    (evaluated : Evaluates program before ⟨.field body key, .unary plan⟩ value after) :
    ∃ (middle : Environment) (parent residual : Value) (index : Nat) (trace : List (List Nat)),
      Evaluates program before ⟨body, plan⟩ parent middle ∧
      parent.readField program key = some value ∧ parent.fieldIndex program key = some index ∧
      residual.children[index]? = some .vacant ∧ Environment.Disposes program middle residual after ∧
      residual.Destroys program trace .vacant ∧ ∀ suffix, index :: suffix ∉ trace := by
  cases evaluated with
  | field source selected extracted dispose usable =>
    simp only [Value.takeField, Bind.bind, Option.bind_eq_some_iff] at extracted
    obtain ⟨index, indexed, child, found, written⟩ := extracted
    have vacant := Value.replaceChild_readback written
    exact ⟨_, _, _, index, _, source, selected, indexed, vacant, dispose, dispose.logical,
      fun suffix => dispose.logical.skips_vacant_field vacant suffix⟩

theorem Value.replaceChild_inverse {value resident replacement updated : Value} {index : Nat}
    (found : value.children[index]? = some resident)
    (written : value.replaceChild index replacement = some updated) :
    updated.replaceChild index resident = some value := by
  cases value with
  | vacant | unit | integer | character | array | reference => simp [Value.replaceChild] at written
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

theorem Value.writeIndices_inverse {value resident replacement updated : Value} {indices : List Nat}
    (read : value.readIndices indices = some resident)
    (written : value.writeIndices indices replacement = some updated) :
    updated.writeIndices indices resident = some value := by
  induction indices generalizing value updated with
  | nil => cases Option.some.inj read; cases Option.some.inj written; rfl
  | cons index indices ih =>
    simp only [Value.writeIndices, Bind.bind, Option.bind_eq_some_iff] at written
    obtain ⟨child, found, next, changed, replaced⟩ := written
    have childRead : child.readIndices indices = some resident := by simpa [Value.readIndices, found] using read
    have childAfter := Value.replaceChild_readback replaced
    have parentRestored := Value.replaceChild_inverse found replaced
    simp [Value.writeIndices, childAfter, ih childRead changed, parentRestored]

theorem Environment.writeAddress_inverse {address : Address} {resident replacement : Value} {before after : Environment}
    (read : before.at address = some resident)
    (written : before.writeAddress address replacement = some after) :
    after.writeAddress address resident = some before := by
  simp only [Environment.writeAddress, Bind.bind, Option.bind_eq_some_iff] at written
  obtain ⟨parent, found, updated, changed, same⟩ := written
  cases same
  have rawRead : parent.readIndices address.fields = some resident := by simpa [Environment.at, found] using read
  have restored := Value.writeIndices_inverse rawRead changed
  have restore : (before.put address.root updated).put address.root parent = before := by
    cases before with
    | mk bindings store nextRoot =>
      simp only [Environment.put]
      congr 1
      funext other
      by_cases equal : other = address.root
      · subst other; simpa only [↓reduceIte] using found.symm
      · simp [equal]
  simpa [Environment.writeAddress, Environment.put, restored] using congrArg some restore

/-- Restoration uses the same address, preserving siblings, holes and shadowed roots. -/
theorem Evaluates.move_restore {place : Place} {before after : Environment} {value : Value}
    (evaluated : Evaluates program before ⟨.move place, .leaf⟩ value after) :
    ∃ address, before.resolvePlace program place = some address ∧
      after.resolvePlace program place = some address ∧ after.writeAddress address value = some before := by
  cases evaluated with
  | move resolved free allowed taken =>
    obtain ⟨read, written⟩ := Environment.takeAddress_eq_some.mp taken
    simp only [Environment.readAddress, Bind.bind, Option.bind_eq_some_iff] at read
    obtain ⟨resident, found, live⟩ := read
    split at live
    · cases Option.some.inj live
      exact ⟨_, resolved, Environment.resolvePlace_write resolved written, Environment.writeAddress_inverse found written⟩
    · cases live

/-- Indirect extraction creates a real canonical vacancy; writing the extracted
resident back recovers the entire original store, including hidden cells. -/
theorem Evaluates.moveIndirect_restore {reference : Place} {fields : List FieldKey}
    {before after : Environment} {value : Value}
    (evaluated : Evaluates program before ⟨.moveIndirect reference fields, .leaf⟩ value after) :
    ∃ access, before.resolveAccess program (.dereference reference fields) = some access ∧
      after.at access.address = some .vacant ∧ after.readAddress access.address = none ∧
      after.writeAddress access.address value = some before := by
  cases evaluated with
  | moveIndirect resolved _ _ _ _ taken =>
    obtain ⟨read, written⟩ := Environment.takeAddress_eq_some.mp taken
    simp only [Environment.readAddress, Bind.bind, Option.bind_eq_some_iff] at read
    obtain ⟨resident, found, live⟩ := read
    split at live
    · cases Option.some.inj live
      exact ⟨_, resolved, Environment.writeAddress_readback written,
        Environment.takeAddress_invalidates taken, Environment.writeAddress_inverse found written⟩
    · cases live

theorem ValueHasType.initialized {value : Value} {type : Ty}
    (typed : ValueHasType program value type) : value.initialized = true := by
  exact (typed.complete .full).2

theorem ResidentTyped.fully_initialized {state : Initialization} {value : Value} {type : Ty}
    (typed : ResidentTyped program state value type) (live : value.initialized = true) : ValueHasType program value type := by
  induction typed using ResidentTyped.rec
    (motive_2 := fun states values types _ => valuesInitialized values = true → ValuesHaveTypes program values types) with
  | vacant => simp [Value.initialized] at live
  | uncertain actual permission ih => exact ih live
  | unit => exact .unit
  | integer fits => exact .integer fits
  | character valid => exact .character valid
  | reference node finite => exact .reference node finite
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
  obtain ⟨_, vacancy, selected, vacantTyped⟩ := path.resident typed access
  have absent := ResidentTyped.vacant_value vacantTyped
  subst vacancy
  cases live : value.initialized with
  | false => rfl
  | true =>
    obtain ⟨_, resident, found, residentTyped⟩ := path.resident (typed.fully_initialized live) (Initialization.Access.full indices)
    have same := Option.some.inj (selected.symm.trans found)
    subst resident
    have impossible := (residentTyped.complete .full).2
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

theorem CanonicalPath.write {source target : Ty} {indices : List Nat} {state selected next : Initialization}
    (path : CanonicalPath program source indices target) {value replacement : Value}
    (typed : ResidentTyped program state value source) (access : state.Access indices selected)
    (resident : ResidentTyped program next replacement target) :
    ∃ updated, value.writeIndices indices replacement = some updated ∧
      ResidentTyped program (state.write indices next) updated source ∧ updated.readIndices indices = some replacement := by
  induction path generalizing value state selected with
  | nil => exact ⟨replacement, rfl, resident, rfl⟩
  | @cons source middle target index indices home key head tail ih =>
    cases access with
    | child present childAccess =>
      obtain ⟨child, _, found, childTyped, replace⟩ := head.access typed present
      obtain ⟨updatedChild, written, updatedChildTyped, _⟩ := ih childTyped childAccess resident
      obtain ⟨updated, replaced, updatedTyped⟩ := replace updatedChild _ updatedChildTyped
      have pathWritten : value.writeIndices (index :: indices) replacement = some updated := by
        simp [Value.writeIndices, found, written, replaced]
      exact ⟨updated, pathWritten, updatedTyped, Value.writeIndices_readback pathWritten⟩

theorem PathType.write {source target : Ty} {keys : List FieldKey} {indices : List Nat} {state selected next : Initialization}
    (path : PathType program home source keys indices target) {value replacement : Value}
    (typed : ResidentTyped program state value source) (access : state.Access indices selected)
    (resident : ResidentTyped program next replacement target) :
    ∃ updated, value.writeIndices indices replacement = some updated ∧
      ResidentTyped program (state.write indices next) updated source ∧ updated.readIndices indices = some replacement :=
  path.canonical.write typed access resident

/-- One root-update proof serves lexical owners and canonical indirect targets.
The root type is derived from storage and the checked path, never from post-write admission. -/
theorem StoreTyped.writeCanonical {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) {binder : Nat} {slot : Slot}
    {indices : List Nat} {state next : Initialization} {target : Ty} {replacement : Value}
    (stored : context.storage (.binder binder) = some slot)
    (path : CanonicalPath program slot.type indices target) (access : slot.initialization.Access indices state)
    (resident : ResidentTyped program next replacement target) :
    ∃ parent updated, environment.store (interpretation.binder binder) = some parent ∧
      parent.writeIndices indices replacement = some updated ∧
      ResidentTyped program (slot.initialization.write indices next) updated slot.type ∧
      environment.writeAddress ⟨interpretation.binder binder, indices⟩ replacement =
        some (environment.put (interpretation.binder binder) updated) := by
  obtain ⟨parent, found, rootTyped, _⟩ := typed.cells binder slot stored
  obtain ⟨updated, written, updatedTyped, _⟩ := path.write rootTyped access resident
  exact ⟨parent, updated, found, written, updatedTyped, by simp [Environment.writeAddress, found, written]⟩

/-- A data target update reconstructs root typing and global cell correspondence
from the same canonical path used by owner writes; no post-write typing premise. -/
theorem StoreTyped.writeTarget_cells {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) {origin : Origin} {referent : Ty}
    (target : context.Target program origin referent) {binder : Nat} (base : origin.base = .binder binder)
    {next : Initialization} {replacement : Value} (shape : referent.DataShape)
    (resident : ResidentTyped program next replacement referent) :
    ∃ after, environment.writeAddress (interpretation.origin origin) replacement = some after ∧
      ∀ binder slot, (context.writeTarget origin next).storage (.binder binder) = some slot →
        ∃ value, after.store (interpretation.binder binder) = some value ∧
          SlotTyped program value slot.toBindingType ∧ slot.Corresponds interpretation value := by
  simp only [Context.Target, base] at target
  obtain ⟨slot, stored, path, state, access⟩ := target
  have rootShape := path.dataShape (typed.source.allocated binder slot stored).2.2.1 shape
  have noReference : slot.reference = none := by
    cases reference : slot.reference with
    | none => rfl
    | some node =>
      obtain ⟨loan, _, type⟩ := (typed.source.allocated binder slot stored).2.2.2 node reference
      rw [type] at rootShape
      exact False.elim rootShape
  obtain ⟨parent, updated, _, _, updatedTyped, written⟩ := typed.writeCanonical stored path access resident
  refine ⟨environment.put (interpretation.binder binder) updated, ?_, ?_⟩
  · simpa only [Interpretation.origin, base] using written
  · intro other current selected
    by_cases same : other = binder
    · subst other
      simp only [Context.writeTarget, base, ↓reduceIte, stored, Option.map_some, Option.some.injEq] at selected
      subst current
      exact ⟨updated, by simp [Environment.put], updatedTyped,
        by simpa only [Slot.Corresponds, noReference] using updatedTyped.referenceFree rootShape⟩
    · have oldStored : context.storage (.binder other) = some current := by
        simpa [Context.writeTarget, base, same] using selected
      obtain ⟨value, found, valueTyped, corresponds⟩ := typed.cells other current oldStored
      have different : interpretation.binder other ≠ interpretation.binder binder := by
        intro equal
        exact same (typed.binderDistinct other binder (.inl ⟨current, oldStored⟩) (.inl ⟨slot, stored⟩) equal)
      exact ⟨value, by simpa [Environment.put, different] using found, valueTyped, corresponds⟩



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

theorem cleanup {environment : Environment} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) (count : Nat)
    (allowed : ∀ entry ∈ context.take count, entry.2.Disposable program)
    (plain : ∀ root ∈ (environment.bindings.take count).map Prod.snd, ∀ value, environment.store root = some value → value.ReferenceFree)
    (free : ∀ root ∈ (environment.bindings.take count).map Prod.snd, environment.OwnerFree ⟨root, []⟩) :
    ∃ trace, Cleans program count environment trace (environment.retire count) := by
  obtain ⟨values, stored, residents⟩ := typed.residents
  obtain ⟨trace, destroyed⟩ := DestroysRoots.exists (stored.take count) ((residents.take count).disposable allowed)
  exact ⟨trace, .retire (DisposesRoots.of_data destroyed plain free)⟩

theorem put {environment : Environment} {context afterContext : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) {name : String} {slot : BindingType} {root : Root}
    (named : Grounded.lookup name environment.bindings = some root)
    (changed : replaceBinding name slot context = some afterContext) {replacement : Value}
    (resident : SlotTyped program replacement slot) :
    EnvironmentTyped program (environment.put root replacement) afterContext := by
  obtain ⟨values, stored, residents⟩ := typed.residents
  obtain ⟨next, changedValues, nextTyped, _⟩ := residents.replace changed resident
  obtain ⟨selected, old, found, present, nextStored⟩ := stored.replace typed.valid.distinct changedValues
  cases Option.some.inj (found.symm.trans named)
  exact ⟨typed.valid.put (typed.valid.bounded _ _ present) replacement, next, nextStored, nextTyped⟩

theorem lookup {environment : Environment} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) {name : String} {type : BindingType}
    (selected : Grounded.lookup name context = some type) :
    ∃ value, environment.get name = some value ∧ SlotTyped program value type := by
  obtain ⟨values, stored, residents⟩ := typed.residents
  obtain ⟨value, found, valueTyped⟩ := residents.lookup selected
  exact ⟨value, (stored.lookup name).trans found, valueTyped⟩

end EnvironmentTyped

/-- Source admission and resident typing derive both the root and exact canonical
indices. No successful runtime lookup or agreement certificate is a premise. -/
theorem EnvironmentTyped.resolvePlace {environment : Environment} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) {place : Place} {slot : BindingType} {target : Ty} {indices : List Nat} {state : Initialization}
    (selected : Grounded.lookup place.root context = some slot) (access : slot.initialization.Access indices state)
    (path : PathType program home slot.type place.fields indices target) :
    ∃ root resident, environment.resolvePlace program place = some ⟨root, indices⟩ ∧
      environment.at ⟨root, indices⟩ = some resident ∧ ResidentTyped program state resident target := by
  obtain ⟨parent, found, parentTyped⟩ := typed.lookup selected
  simp only [Environment.get, Bind.bind, Option.bind_eq_some_iff] at found
  obtain ⟨root, named, stored⟩ := found
  obtain ⟨resolved, resident, read, residentTyped⟩ := path.resident parentTyped access
  exact ⟨root, resident, by simp [Environment.resolvePlace, named, stored, resolved],
    by simp [Environment.at, stored, read], residentTyped⟩

/-- A successful runtime result has precisely the indices proved at source admission. -/
theorem EnvironmentTyped.resolution_fidelity {environment : Environment} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) {place : Place} {slot : BindingType} {target : Ty} {indices : List Nat} {state : Initialization}
    (selected : Grounded.lookup place.root context = some slot) (access : slot.initialization.Access indices state)
    (path : PathType program home slot.type place.fields indices target) {address : Address}
    (resolved : environment.resolvePlace program place = some address) : address.fields = indices := by
  obtain ⟨root, _, produced, _⟩ := typed.resolvePlace selected access path
  cases Option.some.inj (resolved.symm.trans produced)
  rfl

theorem EnvironmentTyped.writeAddress {environment : Environment} {context afterContext : List (String × BindingType)}
    (typed : EnvironmentTyped program environment context) {place : Place} {slot : BindingType} {target : Ty} {indices : List Nat} {state next : Initialization}
    (selected : Grounded.lookup place.root context = some slot)
    (access : slot.initialization.Access indices state) (path : PathType program home slot.type place.fields indices target)
    {address : Address} (resolved : environment.resolvePlace program place = some address)
    (changed : replaceBinding place.root { slot with initialization := slot.initialization.write indices next } context = some afterContext)
    {replacement : Value} (resident : ResidentTyped program next replacement target) :
    ∃ after, environment.writeAddress address replacement = some after ∧ EnvironmentTyped program after afterContext ∧
      after.at address = some replacement := by
  have fidelity := typed.resolution_fidelity selected access path resolved
  obtain ⟨parent, found, parentTyped⟩ := typed.lookup selected
  simp only [Environment.resolvePlace, Bind.bind, Option.bind_eq_some_iff] at resolved
  obtain ⟨root, named, actual, stored, fields, _, same⟩ := resolved
  cases same
  have parentSame : actual = parent := by simpa [Environment.get, named, stored] using found
  subst actual
  change fields = indices at fidelity
  subst fields
  obtain ⟨updated, written, updatedTyped, _⟩ := path.write parentTyped access resident
  have addressWritten : environment.writeAddress ⟨root, indices⟩ replacement = some (environment.put root updated) := by
    simp [Environment.writeAddress, stored, written]
  have update := Environment.writeAddress_update addressWritten
  exact ⟨_, addressWritten, typed.put named changed updatedTyped, update.readback⟩

/-- Runtime typing produces the constructor signature consumed by both pattern
binding and exhaustive dispatch; neither consumer guesses resident types. -/
theorem ValueHasType.decompose {value : Value} {type : Ty} (typed : ValueHasType program value type) :
    ∃ fields, HeadType program value.head type fields ∧ ValuesHaveTypes program value.children fields := by
  cases typed with
  | unit => exact ⟨[], .unit, .nil⟩
  | integer fits => exact ⟨[], .integer fits, .nil⟩
  | character valid => exact ⟨[], .character valid, .nil⟩
  | reference node finite => exact ⟨[], .reference node _, .nil⟩
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
theorem Covers.selectArm {α : Type} {type : Ty} {arms : List (Pattern × α)} {value : Value}
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
  have noneMeansMissing : ∀ (arms : List (Pattern × α)), Grounded.selectArm value arms = none →
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
    (leftFrame : left.hide.Evolution first) (rightFrame : right.hide.Evolution last)
    (leftShared : ∀ root, ¬ left.UniqueRoot root) (rightShared : ∀ root, ¬ right.UniqueRoot root) :
    (left.resume first).Agrees (right.resume last) := by
  obtain ⟨values, leftStored, rightStored⟩ := same.values
  exact ⟨same.leftValid.resume firstValid leftFrame.supply, same.rightValid.resume lastValid rightFrame.supply, values,
    leftStored.frame (fun root _ => leftFrame.frame root (by simpa [Environment.MutationRoot, Environment.UniqueRoot, Environment.roots, Environment.hide] using leftShared root)),
    rightStored.frame (fun root _ => rightFrame.frame root (by simpa [Environment.MutationRoot, Environment.UniqueRoot, Environment.roots, Environment.hide] using rightShared root))⟩

theorem put {left right : Environment} (same : left.Agrees right) {name : String} {value : Value} {first last : Root}
    (leftName : Grounded.lookup name left.bindings = some first)
    (rightName : Grounded.lookup name right.bindings = some last) :
    (left.put first value).Agrees (right.put last value) := by
  obtain ⟨values, leftStored, rightStored⟩ := same.values
  have available : ∃ old, Grounded.lookup name values = some old := by
    cases found : Grounded.lookup name values with
    | some old => exact ⟨old, rfl⟩
    | none =>
      have rootPresent : ∀ {bindings values}, StoredBindings left.store bindings values →
          Grounded.lookup name bindings = some first → ∃ resident, left.store first = some resident := by
        intro bindings values stored
        induction stored with
        | nil => simp [Grounded.lookup]
        | cons present rest ih =>
          intro selected
          simp only [Grounded.lookup] at selected
          split at selected
          · cases selected; exact ⟨_, present⟩
          · exact ih selected
      obtain ⟨resident, present⟩ := rootPresent leftStored leftName
      have observed := leftStored.lookup name
      simp [leftName, present, found] at observed
  obtain ⟨old, available⟩ := available
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
  obtain ⟨leftRoot, leftOld, leftNamed, leftPresent, leftNext⟩ := leftStored.replace same.leftValid.distinct changed
  obtain ⟨rightRoot, rightOld, rightNamed, rightPresent, rightNext⟩ := rightStored.replace same.rightValid.distinct changed
  cases Option.some.inj (leftNamed.symm.trans leftName)
  cases Option.some.inj (rightNamed.symm.trans rightName)
  exact ⟨same.leftValid.put (same.leftValid.bounded _ _ leftPresent) value,
    same.rightValid.put (same.rightValid.bounded _ _ rightPresent) value, next, leftNext, rightNext⟩

end Environment.Agrees

/-- Admission/observation transports resident types, never fabricates a cell. -/
theorem EnvironmentTyped.agrees {left right : Environment} {context : List (String × BindingType)}
    (typed : EnvironmentTyped program left context) (same : left.Agrees right) : EnvironmentTyped program right context := by
  obtain ⟨values, stored, residents⟩ := typed.residents
  obtain ⟨observed, first, second⟩ := same.values
  cases stored.unique first
  exact ⟨same.rightValid, values, second, residents⟩

/-- Equal logical observations resolve to equal indices, not equal roots. -/
theorem Environment.Agrees.resolvePlace {left right : Environment} (same : left.Agrees right)
    {place : Place} {address : Address} (resolved : left.resolvePlace program place = some address) :
    ∃ otherAddress, right.resolvePlace program place = some otherAddress ∧ otherAddress.fields = address.fields ∧
      right.at otherAddress = left.at address ∧
      ∀ replacement after, left.writeAddress address replacement = some after →
        ∃ other, right.writeAddress otherAddress replacement = some other ∧ after.Agrees other := by
  simp only [Environment.resolvePlace, Bind.bind, Option.bind_eq_some_iff] at resolved
  obtain ⟨root, named, parent, stored, indices, path, equal⟩ := resolved
  cases equal
  have otherGet : right.get place.root = some parent := by
    rw [← same.get]
    simp [Environment.get, named, stored]
  simp only [Environment.get, Bind.bind, Option.bind_eq_some_iff] at otherGet
  obtain ⟨otherRoot, otherName, otherStored⟩ := otherGet
  refine ⟨⟨otherRoot, indices⟩, by simp [Environment.resolvePlace, otherName, otherStored, path], rfl,
    by simp [Environment.at, stored, otherStored], ?_⟩
  intro replacement after written
  simp only [Environment.writeAddress, Bind.bind, stored, Option.bind_some, Option.bind_eq_some_iff] at written
  obtain ⟨updated, changed, equal⟩ := written
  cases equal
  exact ⟨right.put otherRoot updated, by simp [Environment.writeAddress, otherStored, changed],
    same.put named otherName⟩

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
    (cleaned : Cleans program count left trace after) (same : left.Agrees right)
    (plain : ∀ root ∈ (right.bindings.take count).map Prod.snd, ∀ value, right.store root = some value → value.ReferenceFree)
    (free : ∀ root ∈ (right.bindings.take count).map Prod.snd, right.OwnerFree ⟨root, []⟩) :
    ∃ otherTrace, Cleans program count right otherTrace (right.retire count) := by
  obtain ⟨values, first, second⟩ := same.values
  cases cleaned with
  | retire destroyed =>
    obtain ⟨otherTrace, otherDestroyed⟩ := DestroysRoots.exists (second.take count) (destroyed.logical.allowed (first.take count))
    exact ⟨otherTrace, .retire (DisposesRoots.of_data otherDestroyed plain free)⟩

theorem Environment.writeAddress_evolution {address : Address} {value : Value} {before after : Environment}
    (authority : before.MutationRoot address.root)
    (written : before.writeAddress address value = some after) (valid : before.Valid) :
    after.Valid ∧ before.Evolution after := by
  simp only [Environment.writeAddress, Bind.bind, Option.bind_eq_some_iff] at written
  obtain ⟨parent, found, updated, _, equal⟩ := written
  cases equal
  have bound := valid.bounded address.root parent found
  refine ⟨valid.put bound updated, rfl, Nat.le_refl _, ?_, fun _ live => .inl (.inr live), ?_, ?_⟩
  · intro root outside
    have different : root ≠ address.root := fun same => outside (same ▸ authority)
    simp only [Environment.put, if_neg different]
  · intro root _ missing
    have different : root ≠ address.root := by
      intro same; subst root; rw [found] at missing; cases missing
    simpa only [Environment.put, if_neg different] using missing
  · intro root fresh
    have different : root ≠ address.root := fun same => Nat.not_lt_of_ge fresh (same ▸ bound)
    simpa only [Environment.put, if_neg different] using (Environment.Evolution.refl before valid).fresh root fresh

theorem Environment.writeAddress_storage {place : Place} {address : Address} {value : Value} {before after : Environment}
    (resolved : before.resolvePlace program place = some address)
    (written : before.writeAddress address value = some after) (valid : before.Valid) :
    after.Valid ∧ before.Evolution after := by
  have named : Grounded.lookup place.root before.bindings = some address.root := by
    simp only [Environment.resolvePlace, Bind.bind, Option.bind_eq_some_iff] at resolved
    obtain ⟨root, named, parent, _, indices, _, equal⟩ := resolved
    cases equal
    exact named
  exact Environment.writeAddress_evolution (.inl (Environment.lookup_mem named)) written valid

theorem Environment.SameStorage.valid {before after : Environment} (same : before.SameStorage after)
    (valid : before.Valid) : after.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · intro root value found
    rw [same.store] at found
    rw [same.supply]
    exact valid.bounded root value found
  · simpa [Environment.roots, same.bindings, same.supply] using valid.named
  · simpa [Environment.roots, same.bindings] using valid.distinct

theorem Environment.SameStorage.evolution {before after : Environment} (same : before.SameStorage after)
    (valid : before.Valid)
    (authority : ∀ root, after.UniqueRoot root → before.MutationRoot root ∨ before.nextRoot ≤ root) :
    before.Evolution after := by
  refine ⟨same.bindings, Nat.le_of_eq same.supply.symm, fun root _ => congrFun same.store root, authority, ?_, ?_⟩
  · intro root _ missing; simpa only [same.store] using missing
  · intro root fresh; simpa only [same.store] using (Environment.Evolution.refl before valid).fresh root fresh

theorem Environment.SameStorage.resolvePlace {before after : Environment} (same : before.SameStorage after) (place : Place) :
    after.resolvePlace program place = before.resolvePlace program place := by
  simp only [Environment.resolvePlace, same.bindings, same.store]

theorem Environment.Copies.storage {before after : Environment} {resident value : Value}
    (copied : Copies before resident value after) : before.SameStorage after := by
  cases copied <;> exact ⟨rfl, rfl, rfl⟩

theorem Environment.endSlot_storage {before after : Environment} {slot : Nat}
    (ended : before.endSlot slot = some after) : before.SameStorage after := by
  obtain ⟨_, _, _, _, _, transition⟩ := endSlot_checked ended
  cases Environment.endOwn_state transition
  exact ⟨rfl, rfl, rfl⟩

/-- New unique authority must come from the actual canonical access. -/
theorem Environment.Authorizes.mutationRoot {environment : Environment} {access : Environment.ResolvedAccess}
    (allowed : environment.Authorizes .unique access) : environment.MutationRoot access.address.root := by
  cases parent : access.parent with
  | none => exact .inl (by simpa [Environment.Authorizes, parent] using allowed)
  | some node =>
    obtain ⟨loan, found, own, _, root, _, mode⟩ := (by simpa [Environment.Authorizes, parent] using allowed)
    exact .inr ⟨node, loan, found, own, mode, root.symm⟩

theorem Environment.addLoan_unique {environment : Environment} {access : Environment.ResolvedAccess}
    {root : Root} {mode : BorrowMode} (live : (environment.addLoan access mode).UniqueRoot root) :
    environment.UniqueRoot root ∨ (mode = .unique ∧ access.address.root = root) := by
  obtain ⟨node, loan, found, own, unique, target⟩ := live
  by_cases old : node < environment.loans.length
  · exact .inl ⟨node, loan, by simpa only [Environment.addLoan, List.getElem?_append_left old] using found, own, unique, target⟩
  · simp only [Environment.addLoan, List.getElem?_append_right (Nat.le_of_not_lt old)] at found
    cases offset : node - environment.loans.length with
    | zero =>
      simp only [offset, List.getElem?_cons_zero, Option.some.injEq] at found
      cases found
      exact .inr ⟨unique, target⟩
    | succ index => simp [offset] at found
theorem Environment.endOwn_unique {before after : Environment} {node root : Nat}
    (ended : before.endOwn node = some after) (live : after.UniqueRoot root) : before.UniqueRoot root := by
  obtain ⟨other, loan, found, own, mode, target⟩ := live
  exact ⟨other, loan, (Environment.endOwn_active ended found own).1, own, mode, target⟩

theorem Environment.endSlot_unique {before after : Environment} {slot root : Nat}
    (ended : before.endSlot slot = some after) (live : after.UniqueRoot root) : before.UniqueRoot root := by
  obtain ⟨_, _, _, _, _, transition⟩ := endSlot_checked ended
  exact Environment.endOwn_unique transition live

theorem Environment.endSlot_evolution {before after : Environment} {slot : Nat}
    (ended : before.endSlot slot = some after) (valid : before.Valid) : before.Evolution after :=
  (Environment.endSlot_storage ended).evolution valid
    (fun _ live => .inl (.inr (Environment.endSlot_unique ended live)))

theorem Environment.Copies.uniqueRoots {before after : Environment} {resident value : Value}
    (copied : Copies before resident value after) {root : Root} (live : after.UniqueRoot root) : before.UniqueRoot root := by
  cases copied with
  | data => exact live
  | reference found shared allowed =>
    rcases Environment.addLoan_unique live with old | ⟨impossible, _⟩
    · exact old
    · cases impossible

theorem Environment.Copies.evolution {before after : Environment} {resident value : Value}
    (copied : Copies before resident value after) (valid : before.Valid) : before.Evolution after :=
  copied.storage.evolution valid (fun _ live => .inl (.inr (copied.uniqueRoots live)))

theorem Environment.Disposes.uniqueRoots {before after : Environment} {value : Value}
    (disposed : Disposes program before value after) {root : Root} (live : after.UniqueRoot root) : before.UniqueRoot root := by
  cases disposed with
  | data => exact live
  | reference _ ended => exact Environment.endOwn_unique ended live

theorem Environment.Disposes.evolution {before after : Environment} {value : Value}
    (disposed : Disposes program before value after) (valid : before.Valid) : before.Evolution after :=
  disposed.storage.evolution valid (fun _ live => .inl (.inr (disposed.uniqueRoots live)))

theorem DisposesRoots.uniqueRoots {before after : Environment} {roots : List Root} {trace : List (Root × List Nat)}
    (disposed : DisposesRoots program before roots trace after) {root : Root} (live : after.UniqueRoot root) : before.UniqueRoot root := by
  induction disposed with
  | nil => exact live
  | cons found free head tail ih => exact head.uniqueRoots (ih live)

theorem Cleans.uniqueRoots {before after : Environment} {count : Nat} {trace : List (Root × List Nat)}
    (cleaned : Cleans program count before trace after) {root : Root} (live : after.UniqueRoot root) : before.UniqueRoot root := by
  cases cleaned with
  | retire disposed => exact disposed.uniqueRoots live

theorem Cleans.suffix_evolution {before after : Environment} {count : Nat} {trace : List (Root × List Nat)}
    (cleaned : Cleans program count before trace after) (valid : before.Valid) :
    (before.retire count).Evolution after :=
  cleaned.suffix.evolution (valid.retire count) (fun _ live => .inl (.inr (cleaned.uniqueRoots live)))

theorem Cleans.valid {before after : Environment} {count : Nat} {trace : List (Root × List Nat)}
    (cleaned : Cleans program count before trace after) (valid : before.Valid) : after.Valid :=
  cleaned.suffix.valid (valid.retire count)

/-- Every real operation preserves stable lexical roots, the monotone supply,
and all storage outside its incoming owners. Fresh-root availability is derived
inside the bind/parameter preparation steps from Valid, not admission. -/
theorem Evaluates.storage {before after : Environment} {core : Core} {value : Value}
    (evaluated : Evaluates program before core value after) :
    before.Valid → after.Valid ∧ before.Evolution after := by
  induction evaluated using Evaluates.rec
    (motive_2 := fun before _ _ _ after _ => before.Valid → after.Valid ∧ before.Evolution after)
    (motive_3 := fun _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) (motive_5 := fun _ _ _ _ => True) with
  | unit | integer | character | dereference => exact fun valid => ⟨valid, .refl _ valid⟩
  | read _ _ _ copied => exact fun valid => ⟨copied.storage.valid valid, copied.evolution valid⟩
  | @borrow environment place access resident mode resolved allowed permitted ready selected plain
  | @reborrow environment place access resident mode resolved allowed permitted ready selected plain =>
    intro valid
    have same : environment.SameStorage (environment.addLoan access mode) := ⟨rfl, rfl, rfl⟩
    refine ⟨same.valid valid, same.evolution valid ?_⟩
    intro root live
    rcases Environment.addLoan_unique live with old | ⟨unique, target⟩
    · exact .inl (.inr old)
    · subst mode
      rw [← target]
      exact .inl allowed.mutationRoot
  | group _ ih | implicitMove _ ih => exact ih
  | move resolved free allowed taken =>
    exact Environment.writeAddress_storage resolved (Environment.takeAddress_eq_some.mp taken).2
  | moveIndirect _ allowed _ _ _ taken =>
    exact Environment.writeAddress_evolution allowed.mutationRoot (Environment.takeAddress_eq_some.mp taken).2
  | assignIndirect _ _ allowed _ _ _ _ written _ initialIH bodyIH =>
    intro valid
    obtain ⟨middleValid, initial⟩ := initialIH valid
    obtain ⟨updatedValid, update⟩ := Environment.writeAddress_evolution allowed.mutationRoot written middleValid
    obtain ⟨afterValid, body⟩ := bodyIH updatedValid
    exact ⟨afterValid, initial.trans (update.trans body)⟩
  | endOwn ended _ ih =>
    intro valid
    have same := Environment.endSlot_storage ended
    obtain ⟨afterValid, evolved⟩ := ih (same.valid valid)
    exact ⟨afterValid, (Environment.endSlot_evolution ended valid).trans evolved⟩
  | endAfter _ ended _ ih =>
    intro valid
    obtain ⟨middleValid, evolved⟩ := ih valid
    have same := Environment.endSlot_storage ended
    exact ⟨same.valid middleValid, evolved.trans (Environment.endSlot_evolution ended middleValid)⟩
  | sequence _ dispose _ headIH tailIH =>
    intro valid
    obtain ⟨middleValid, first⟩ := headIH valid
    obtain ⟨afterValid, rest⟩ := tailIH (dispose.storage.valid middleValid)
    exact ⟨afterValid, first.trans ((dispose.evolution middleValid).trans rest)⟩
  | bind _ _ _ cleanup _ initialIH bodyIH =>
    intro valid
    obtain ⟨middleValid, initial⟩ := initialIH valid
    obtain ⟨afterValid, body⟩ := bodyIH (middleValid.bind _ _)
    obtain ⟨_, cleaned⟩ := cleanup
    exact ⟨cleaned.valid afterValid, initial.trans ((body.unbind middleValid).trans (cleaned.suffix_evolution afterValid))⟩
  | assign _ resolved _ _ dispose _ written _ initialIH bodyIH =>
    intro valid
    obtain ⟨middleValid, initial⟩ := initialIH valid
    have resolvedAfter := (dispose.storage.resolvePlace _).trans resolved
    obtain ⟨updatedValid, update⟩ := Environment.writeAddress_storage resolvedAfter written (dispose.storage.valid middleValid)
    obtain ⟨afterValid, body⟩ := bodyIH updatedValid
    exact ⟨afterValid, initial.trans ((dispose.evolution middleValid).trans (update.trans body))⟩
  | tuple _ _ _ headIH tailIH =>
    intro valid
    obtain ⟨middleValid, first⟩ := headIH valid
    obtain ⟨afterValid, rest⟩ := tailIH middleValid
    exact ⟨afterValid, first.trans rest⟩
  | array _ _ ih | construct _ _ ih => exact ih
  | constant _ _ _ ih =>
    intro valid
    obtain ⟨afterValid, body⟩ := ih valid.hide
    exact ⟨valid.resume afterValid body.supply, body.resume⟩
  | field _ _ _ dispose _ ih =>
    intro valid
    obtain ⟨middleValid, body⟩ := ih valid
    exact ⟨dispose.storage.valid middleValid, body.trans (dispose.evolution middleValid)⟩
  | call _ _ _ cleanup _ inputsIH bodyIH =>
    intro valid
    obtain ⟨middleValid, inputs⟩ := inputsIH valid
    obtain ⟨afterValid, body⟩ := bodyIH (middleValid.hide.prepare _)
    obtain ⟨_, cleaned⟩ := cleanup
    have returned := (body.scope middleValid.hide _).trans (cleaned.suffix_evolution afterValid)
    exact ⟨middleValid.resume (cleaned.valid afterValid) returned.supply, inputs.trans returned.resume⟩
  | applyPatterns _ _ _ _ _ cleanup _ _ argumentsIH bodyIH =>
    intro valid
    obtain ⟨middleValid, arguments⟩ := argumentsIH valid
    obtain ⟨afterValid, body⟩ := bodyIH (middleValid.prepare _)
    obtain ⟨_, cleaned⟩ := cleanup
    exact ⟨cleaned.valid afterValid, arguments.trans ((body.scope middleValid _).trans (cleaned.suffix_evolution afterValid))⟩
  | nil => exact ⟨by assumption, .refl _ (by assumption)⟩
  | cons _ _ _ headIH tailIH =>
    rename_i valid
    obtain ⟨middleValid, first⟩ := headIH valid
    obtain ⟨afterValid, rest⟩ := tailIH middleValid
    exact ⟨afterValid, first.trans rest⟩
  | wildcard | binder | node | constantValue | patternsNil | patternsCons | armsNil | armsCons => trivial


/-- Once an actual scope cleanup retires a root, no subsequent owned execution
can make that identity resolve again. The proof uses its real continuation and
monotone supply, not an allocation-success or future-state certificate. -/
theorem Cleans.retired_stays_absent {before after final : Environment} {count : Nat}
    {trace : List (Root × List Nat)} {expression : Core} {value : Value}
    (cleaned : Cleans program count before trace after) (valid : before.Valid)
    (continued : Evaluates program after expression value final) :
    ∀ root ∈ (before.bindings.take count).map Prod.snd, final.store root = none ∧ root < final.nextRoot := by
  have returned := cleaned.suffix
  have evolved := (continued.storage (cleaned.valid valid)).2
  intro root retired
  have inPrefix : root ∈ before.roots.take count := by simpa [Environment.roots, List.map_take] using retired
  have bound := valid.named root (List.mem_of_mem_take inPrefix)
  exact ⟨evolved.absent root (cleaned.retired root retired),
    Nat.lt_of_lt_of_le (by simpa only [returned.supply, Environment.retire] using bound) evolved.supply⟩

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

theorem EvaluatesMany.storage {before after : Environment} {expressions : List Expr} {plans : List CorePlan} {values : List Value}
    (evaluated : EvaluatesMany program before expressions plans values after) :
    before.Valid → after.Valid ∧ before.Evolution after := by
  induction evaluated using EvaluatesMany.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) (motive_5 := fun _ _ _ _ => True) with
  | nil => exact fun valid => ⟨valid, .refl _ valid⟩
  | cons head tail usable _ ih =>
    intro valid
    obtain ⟨middleValid, first⟩ := head.storage valid
    obtain ⟨afterValid, rest⟩ := ih middleValid
    exact ⟨afterValid, first.trans rest⟩
  | unit | integer | character | group | implicitMove | read | move | borrow | reborrow | dereference | moveIndirect | assignIndirect | endOwn | endAfter
  | sequence | bind | assign | tuple | array | constant | construct | field | call | applyPatterns
  | wildcard | binder | node | constantValue | patternsNil | patternsCons | armsNil | armsCons => trivial

/-- Implicit reborrowing allocates a fresh child without changing any existing
handle cell, binding, or owner storage. Loan readiness and authority are supplied
by the same runtime access contract as explicit borrowing. -/
theorem Evaluates.reborrow_preserves_storage {before after : Environment} {place : Place}
    {mode : BorrowMode} {value : Value}
    (evaluated : Evaluates program before ⟨.read place, .reborrow mode⟩ value after) :
    before.SameStorage after ∧ value = .reference before.loans.length ∧
      after.loans.length = before.loans.length + 1 := by
  cases evaluated with
  | reborrow => exact ⟨⟨rfl, rfl, rfl⟩, rfl, by simp [Environment.addLoan]⟩

/-- A call preserves post-argument caller cells outside incoming unique-target
roots. Shared-only calls retain the entire store. Actual callee writes remain
in the authoritative store when caller names are restored. -/
theorem Evaluates.call_frame {before after : Environment} {identity : Nat} {arguments : List Expr} {value : Value}
    {argumentPlans : List CorePlan} {bodyPlan : CorePlan}
    (evaluated : Evaluates program before ⟨.call identity arguments, .call argumentPlans bodyPlan⟩ value after) (valid : before.Valid) :
    ∃ middle values declaration localAfter,
      program.functions identity = some declaration ∧ EvaluatesMany program before arguments argumentPlans values middle ∧
      Evaluates program (middle.hide.prepare (List.zip (declaration.parameters.map Prod.fst) values)) ⟨declaration.body, bodyPlan⟩ value localAfter ∧
      (∀ root, root < middle.nextRoot →
        (middle.hide.prepare (List.zip (declaration.parameters.map Prod.fst) values)).store root = middle.store root ∧
        root ∉ (middle.hide.prepare (List.zip (declaration.parameters.map Prod.fst) values)).roots) ∧
      after.bindings = middle.bindings ∧
      (∀ root, ¬ middle.UniqueRoot root → after.store root = middle.store root) ∧ middle.nextRoot ≤ after.nextRoot := by
  cases evaluated with
  | call declared inputs body cleanup usable =>
    have middleValid := (inputs.storage valid).1
    obtain ⟨_, cleaned⟩ := cleanup
    have returned := ((body.storage (middleValid.hide.prepare _)).2.scope middleValid.hide _).trans
      (cleaned.suffix_evolution (body.storage (middleValid.hide.prepare _)).1)
    refine ⟨_, _, _, _, declared, inputs, body, ?_, rfl, ?_, returned.supply⟩
    · intro root older
      constructor
      · exact (Environment.prepare_old (Environment.hide _) _ older).1
      · intro retained
        have membership := (Environment.prepare_old (Environment.hide _) _ older).2.mp retained
        simp [Environment.roots, Environment.hide] at membership
    · intro root shared
      exact returned.frame root (by simpa [Environment.MutationRoot, Environment.UniqueRoot, Environment.roots, Environment.hide] using shared)


/-- A result has either reference-free data shape or exactly one direct source
handle. Usability is supplied by the actual protected-resource state. -/
structure ResultTyped (program : Program) (interpretation : Interpretation) (context : Context)
    (value : Value) (result : ResultType) : Prop where
  resident : ValueHasType program value result.type
  shape : match result.reference with
    | none => result.type.DataShape ∧ value.ReferenceFree
    | some node => value = .reference (interpretation.node node) ∧
        ∃ loan, context.loans[node]? = some loan ∧ result.type = .reference loan.referent loan.mode

def Value.referenceValues : Value → List Value
  | .reference node => [.reference node]
  | _ => []

def referenceValues (values : List Value) : List Value := values.flatMap Value.referenceValues

theorem Value.ReferenceFree.referenceValues {value : Value} (plain : value.ReferenceFree) :
    value.referenceValues = [] := by
  cases value <;> simp_all [Value.ReferenceFree, Value.referenceValues]

theorem ResultTyped.referenceValues {interpretation : Interpretation} {context : Context}
    {value : Value} {result : ResultType} (typed : ResultTyped program interpretation context value result) :
    value.referenceValues = result.nodes.map (fun node => Value.reference (interpretation.node node)) := by
  cases reference : result.reference with
  | none =>
    have shape := typed.shape
    rw [reference] at shape
    simpa [ResultType.nodes, reference] using shape.2.referenceValues
  | some node =>
    have shape := typed.shape
    rw [reference] at shape
    simp [shape.1, Value.referenceValues, ResultType.nodes, reference]

theorem ResultTyped.usable {interpretation : Interpretation} {context : Context}
    {environment : Environment} {value : Value} {result : ResultType}
    (typed : ResultTyped program interpretation context value result)
    (store : StoreTyped program interpretation context environment)
    (own : ∀ node ∈ result.nodes, context.Own node)
    (ready : ∀ node ∈ result.nodes, context.Restored node) : environment.ResultUsable value := by
  cases reference : result.reference with
  | none =>
    have shape := typed.shape
    rw [reference] at shape
    cases value <;> try exact shape.2
    exact False.elim shape.2
  | some node =>
    have shape := typed.shape
    rw [reference] at shape
    rw [shape.1]
    have member : node ∈ result.nodes := by simp [ResultType.nodes, reference]
    obtain ⟨loan, found, _⟩ := own node member
    exact ⟨store.usable (own node member), store.restored found (ready node member)⟩

theorem lookup_mapValue {α β : Type} (f : α → β) {bindings : List (String × α)} {name : String} {value : α}
    (found : lookup name bindings = some value) :
    lookup name (bindings.map fun entry => (entry.1, f entry.2)) = some (f value) := by
  induction bindings with
  | nil => simp [lookup] at found
  | cons entry rest ih =>
    obtain ⟨key, resident⟩ := entry
    simp only [lookup] at found
    simp only [List.map_cons, lookup]
    split at found
    · cases Option.some.inj found
      simp [*]
    · simp [*, ih found]

theorem lookup_member {α : Type} {bindings : List (String × α)} {name : String} {value : α}
    (found : lookup name bindings = some value) : (name, value) ∈ bindings := by
  induction bindings with
  | nil => simp [lookup] at found
  | cons entry rest ih =>
    obtain ⟨key, resident⟩ := entry
    simp only [lookup] at found
    split at found
    · rename_i same
      cases Option.some.inj found
      simp [same]
    · exact List.mem_cons_of_mem _ (ih found)

theorem SlotsCorrespond.lookup {interpretation : Interpretation} {store : Store}
    {bindings : List (String × Root)} {slots : List (String × Slot)}
    (correspond : SlotsCorrespond interpretation store bindings slots) {name : String} {slot : Slot}
    (selected : lookup name slots = some slot) :
    lookup name bindings = some (interpretation.binder slot.binder) ∧
      ∀ value, store (interpretation.binder slot.binder) = some value → slot.Corresponds interpretation value := by
  induction correspond generalizing slot with
  | nil => simp [Grounded.lookup] at selected
  | @cons key root head bindings slots identity resident rest ih =>
    simp only [Grounded.lookup] at selected
    split at selected
    · rename_i same
      cases Option.some.inj selected
      exact ⟨by simp [Grounded.lookup, same, identity], by simpa only [identity] using resident⟩
    · rename_i different
      obtain ⟨named, resident⟩ := ih selected
      exact ⟨by simp [Grounded.lookup, different, named], resident⟩

theorem StoreTyped.resolvePlace {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) {place : Place} {slot : Slot}
    {target : Ty} {indices : List Nat} {state : Initialization}
    (selected : lookup place.root context.bindings = some slot) (access : slot.initialization.Access indices state)
    (path : PathType program home slot.type place.fields indices target) :
    ∃ resident, environment.resolvePlace program place = some ⟨interpretation.binder slot.binder, indices⟩ ∧
      environment.at ⟨interpretation.binder slot.binder, indices⟩ = some resident ∧
      ResidentTyped program state resident target := by
  have selectedErased := lookup_mapValue Slot.toBindingType selected
  obtain ⟨root, resident, resolved, read, residentTyped⟩ := typed.residents.resolvePlace selectedErased access path
  have named := (typed.slots.lookup selected).1
  have sameRoot : root = interpretation.binder slot.binder := by
    simp only [Environment.resolvePlace, Bind.bind, Option.bind_eq_some_iff] at resolved
    obtain ⟨actual, found, value, _, fields, _, same⟩ := resolved
    cases Option.some.inj same
    exact Option.some.inj (found.symm.trans named)
  cases sameRoot
  exact ⟨resident, resolved, read, residentTyped⟩

theorem StoredBindings.present {store : Store} {bindings : List (String × Root)} {values : BindingValues}
    (stored : StoredBindings store bindings values) {root : Root} (member : root ∈ bindings.map Prod.snd) :
    ∃ value, store root = some value := by
  induction stored with
  | nil => simp at member
  | cons found rest ih =>
    simp only [List.map_cons, List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨_, found⟩
    · exact ih member

theorem SlotsCorrespond.index {interpretation : Interpretation} {store : Store}
    {bindings : List (String × Root)} {slots : List (String × Slot)}
    (correspond : SlotsCorrespond interpretation store bindings slots) {index : Nat} {binding : String × Slot}
    (selected : slots[index]? = some binding) :
    bindings[index]? = some (binding.1, interpretation.binder binding.2.binder) ∧
      ∀ value, store (interpretation.binder binding.2.binder) = some value → binding.2.Corresponds interpretation value := by
  induction correspond generalizing index with
  | nil => simp at selected
  | @cons name root slot bindings slots identity resident rest ih =>
    cases index with
    | zero =>
      cases Option.some.inj selected
      exact ⟨by simp [identity], by simpa only [identity] using resident⟩
    | succ index => exact ih selected

theorem StoreTyped.endSlot {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) {index node : Nat} {binding : String × Slot}
    (selected : context.bindings[index]? = some binding) (handle : binding.2.reference = some node)
    (ready : context.Restored node) :
    environment.endSlot index = environment.endOwn (interpretation.node node) := by
  obtain ⟨indexed, correspondence⟩ := typed.slots.index selected
  obtain ⟨values, stored, _⟩ := typed.residents.residents
  obtain ⟨value, found⟩ := stored.present (List.mem_map_of_mem (List.mem_of_getElem? indexed))
  have shape := correspondence value found
  simp only [Slot.Corresponds, handle] at shape
  cases shape
  obtain ⟨loan, sourceFound, _⟩ := (typed.source.slots binding (List.mem_of_getElem? selected)).2 node handle
  have runtimeFound := typed.records node loan sourceFound
  have restored := typed.restored sourceFound ready
  simp only [Environment.endSlot, indexed, Bind.bind, Option.bind_some, found]
  rw [runtimeFound]
  simp only [Option.bind_some]
  by_cases own : loan.own = true
  · obtain ⟨resident, read⟩ := restored _ runtimeFound own
    simp [read]
  · have off : loan.own = false := Bool.eq_false_iff.mpr own
    simp [off]

theorem Value.readIndices_append (value : Value) (first second : List Nat) :
    value.readIndices (first ++ second) = (value.readIndices first >>= fun value => value.readIndices second) := by
  induction first generalizing value with
  | nil => rfl
  | cons index rest ih =>
    simp only [List.cons_append, Value.readIndices]
    cases value.children[index]? <;> simp [ih]

theorem Environment.readAddress_at {environment : Environment} {address : Address} {value : Value}
    (read : environment.readAddress address = some value) : environment.at address = some value := by
  simp only [Environment.readAddress, Bind.bind, Option.bind_eq_some_iff] at read
  obtain ⟨actual, found, selected⟩ := read
  split at selected
  · cases Option.some.inj selected; exact found
  · cases selected

theorem Environment.at_subaddress {environment : Environment} {address : Address} {parent value : Value}
    (read : environment.at address = some parent) {indices : List Nat}
    (selected : parent.readIndices indices = some value) :
    environment.at ⟨address.root, address.fields ++ indices⟩ = some value := by
  simp only [Environment.at, Bind.bind, Option.bind_eq_some_iff] at read
  obtain ⟨rootValue, stored, path⟩ := read
  simp [Environment.at, stored, Value.readIndices_append, path, selected]

theorem Environment.readAddress_subaddress {environment : Environment} {address : Address} {parent value : Value}
    (read : environment.readAddress address = some parent) {indices : List Nat}
    (selected : parent.readIndices indices = some value) (live : value.initialized = true) :
    environment.readAddress ⟨address.root, address.fields ++ indices⟩ = some value := by
  simp only [Environment.readAddress, Bind.bind, Option.bind_eq_some_iff] at read
  obtain ⟨actual, found, selectedParent⟩ := read
  split at selectedParent
  · cases Option.some.inj selectedParent
    simp only [Environment.at, Bind.bind, Option.bind_eq_some_iff] at found
    obtain ⟨rootValue, rootStored, path⟩ := found
    simp [Environment.readAddress, Environment.at, rootStored, Value.readIndices_append, path, selected, live]
  · cases selectedParent

theorem Interpretation.origin_extend (interpretation : Interpretation) (origin : Origin) (indices : List Nat) :
    interpretation.origin (origin.extend indices) =
      ⟨(interpretation.origin origin).root, (interpretation.origin origin).fields ++ indices⟩ := by
  cases origin with
  | mk base fields => cases base <;> simp [Interpretation.origin, Origin.extend, List.append_assoc]

/-- Canonical target typing is independent of operation readiness. -/
theorem AccessType.canonicalTarget {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) {place : AccessPlace} {target : Origin}
    {referent : Ty} {parent : Option Nat} {mode : BorrowMode}
    (access : AccessType program home context mode place target referent parent) :
    context.Target program target referent := by
  cases access with
  | owner selected available path _ =>
    exact ⟨_, typed.source.member_stored _ (lookup_member selected), path.canonical, _, available⟩
  | dereference _ _ _ _ _ _ _ _ target _ => exact target

/-- Positive unique authority is distinct from conflict exclusion and readiness. -/
theorem AccessType.uniqueAuthority {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) {place : AccessPlace} {target : Origin}
    {referent : Ty} {parent : Option Nat}
    (access : AccessType program home context .unique place target referent parent) :
    (parent = none ∧ ∃ slot, context.storage target.base = some slot ∧ slot.mutable = true) ∨
    ∃ node loan, parent = some node ∧ context.loans[node]? = some loan ∧ loan.own = true ∧
      loan.mode = .unique ∧ target.Within loan.target := by
  cases access with
  | owner selected _ _ authority =>
    exact .inl ⟨rfl, _, typed.source.member_stored _ (lookup_member selected), authority rfl⟩
  | @dereference reference fields slot node loan indices type _ _ _ _ _ found own _ _ authority =>
    exact .inr ⟨node, loan, rfl, found, own, authority rfl, rfl, indices, rfl⟩

theorem AccessType.uniqueTarget {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) {place : AccessPlace} {target : Origin}
    {referent : Ty} {node : Nat}
    (access : AccessType program home context .unique place target referent (some node)) :
    ∃ loan binder, context.loans[node]? = some loan ∧ loan.own = true ∧ loan.mode = .unique ∧
      target.Within loan.target ∧ target.base = .binder binder := by
  rcases access.uniqueAuthority typed with ⟨impossible, _⟩ | ⟨selected, loan, same, found, own, unique, within⟩
  · cases impossible
  · cases Option.some.inj same
    cases base : target.base with
    | binder binder => exact ⟨loan, binder, found, own, unique, within, rfl⟩
    | input input =>
      have shared := (typed.sourceTargets node loan found own).2.2 input (within.1.symm.trans base)
      cases unique.symm.trans shared

theorem AccessType.parentMode {context : Context} {place : AccessPlace} {target : Origin}
    {referent : Ty} {parent : Option Nat} {mode : BorrowMode}
    (access : AccessType program home context mode place target referent parent) :
    ∀ node loan, parent = some node → context.loans[node]? = some loan → mode = .unique → loan.mode = .unique := by
  cases access with
  | owner => intro node loan impossible; cases impossible
  | dereference _ _ _ _ _ found _ _ _ authority =>
    intro node loan same other unique
    cases Option.some.inj same
    cases Option.some.inj (found.symm.trans other)
    exact authority unique

theorem AccessType.sourceTarget {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) {place : AccessPlace} {target : Origin}
    {referent : Ty} {parent : Option Nat} {mode : BorrowMode}
    (access : AccessType program home context mode place target referent parent)
    (ready : context.AccessReady target parent) :
    context.SourceTarget program ⟨target, referent, parent, true, mode⟩ := by
  refine ⟨access.canonicalTarget typed, fun _ => ready.1, ?_⟩
  cases access with
  | owner => intro input impossible; cases impossible
  | dereference _ _ _ _ _ found own _ _ authority =>
    intro input base
    have shared := (typed.sourceTargets _ _ found own).2.2 input base
    cases mode with
    | shared => rfl
    | unique => cases shared.symm.trans (authority rfl)

/-- Readiness-free positive capability: conflict exclusion is a separate check. -/
theorem StoreTyped.accessAuthority {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) {place : AccessPlace} {target : Origin}
    {referent : Ty} {parent : Option Nat} {mode : BorrowMode}
    (access : AccessType program home context mode place target referent parent) :
    environment.Authorizes mode ⟨interpretation.origin target, parent.map interpretation.node⟩ := by
  cases access with
  | owner selected _ _ _ =>
    exact List.mem_map.mpr ⟨_, lookup_member (typed.slots.lookup selected).1, rfl⟩
  | @dereference reference fields slot node loan indices type _ _ _ _ _ found own _ _ authority =>
    have record := typed.records node loan found
    obtain ⟨actual, actualFound, _, support⟩ := typed.usable (show context.Own node from ⟨loan, found, own⟩)
    cases Option.some.inj (actualFound.symm.trans record)
    exact ⟨_, record, own, support, by simp [Interpretation.origin_extend],
      by simp [Interpretation.origin_extend], authority⟩

private theorem Context.ready_complete {context : Context} {origin : Origin} {binder : Nat}
    {slot : Slot} {state : Initialization} (base : origin.base = .binder binder)
    (stored : context.storage (.binder binder) = some slot)
    (access : slot.initialization.Access origin.fields state) (ready : context.Ready origin) : state.Complete := by
  simp only [Context.Ready, base] at ready
  obtain ⟨actual, selected, actualStored, actualAccess, complete⟩ := ready
  cases Option.some.inj (actualStored.symm.trans stored)
  exact (actualAccess.deterministic access) ▸ complete

/-- The one canonical field producer resolves a masked parent. Only ancestors of
its selected child need be present; the child itself may be vacant. -/
private theorem StoreTyped.projectAccess {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) {node : Nat} {loan : SourceLoan}
    {fields : List FieldKey} {indices : List Nat} {referent : Ty}
    (found : context.loans[node]? = some loan) (own : loan.own = true)
    (path : PathType program home loan.referent fields indices referent)
    (target : context.Target program (loan.target.extend indices) referent) :
    ∃ state resident value, environment.at (interpretation.origin loan.target) = some resident ∧
      resident.resolvePath program fields = some indices ∧
      environment.at (interpretation.origin (loan.target.extend indices)) = some value ∧
      ResidentTyped program state value referent ∧ (context.Ready (loan.target.extend indices) → state.Complete) := by
  cases base : loan.target.base with
  | binder binder =>
    obtain ⟨slot, stored, parentPath, _, _⟩ := (by simpa [Context.Target, base] using (typed.sourceTargets node loan found own).1)
    obtain ⟨childSlot, childStored, _, state, access⟩ := (by simpa [Context.Target, Origin.extend, base] using target)
    cases Option.some.inj (childStored.symm.trans stored)
    obtain ⟨middle, front, back⟩ := access.split
    obtain ⟨root, rootStored, rootTyped, _⟩ := typed.cells binder slot stored
    obtain ⟨resident, parentRead, parentTyped⟩ := parentPath.resident rootTyped front
    obtain ⟨resolved, value, selected, valueTyped⟩ := path.resident parentTyped back
    have raw : environment.at (interpretation.origin loan.target) = some resident := by
      simp [Environment.at, Interpretation.origin, base, rootStored, parentRead]
    refine ⟨state, resident, value, raw, resolved, ?_, valueTyped, ?_⟩
    · rw [Interpretation.origin_extend]
      exact Environment.at_subaddress raw selected
    · exact Context.ready_complete (by simpa [Origin.extend] using base) stored access
  | input input =>
    obtain ⟨resident, read, residentTyped⟩ := typed.inputTargets node loan found own input base
    obtain ⟨resolved, value, selected, valueTyped⟩ := path.resident residentTyped (.full indices)
    refine ⟨.full, resident, value, Environment.readAddress_at read, resolved, ?_, valueTyped, fun _ => .full⟩
    rw [Interpretation.origin_extend]
    exact Environment.at_subaddress (Environment.readAddress_at read) selected

/-- Actual masked resolution and target typing, independent of whole-parent
readiness. Restoration consumes this theorem rather than the read/borrow rule. -/
theorem StoreTyped.resolveAccessMasked {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) {place : AccessPlace} {target : Origin}
    {referent : Ty} {parent : Option Nat} {mode : BorrowMode}
    (access : AccessType program home context mode place target referent parent) :
    target.Known context ∧ target.Bounded context ∧
    (∀ node, parent = some node → ∃ loan, context.loans[node]? = some loan ∧ target.Within loan.target) ∧
    environment.resolveAccess program place = some ⟨interpretation.origin target, parent.map interpretation.node⟩ ∧
    environment.Authorizes mode ⟨interpretation.origin target, parent.map interpretation.node⟩ ∧
    ∃ state value, environment.at (interpretation.origin target) = some value ∧
      ResidentTyped program state value referent ∧ (context.Ready target → state.Complete) := by
  have authority := typed.accessAuthority access
  cases access with
  | @owner place slot indices state type selected available path _ =>
    have member := lookup_member selected
    obtain ⟨value, resolved, raw, resident⟩ := typed.resolvePlace selected available path
    refine ⟨typed.source.member_known _ member, (typed.source.slots _ member).1, ?_, ?_, authority, state, value,
      raw, resident, ?_⟩
    · intro node impossible; cases impossible
    · simp [Environment.resolveAccess, resolved, Interpretation.origin]
    · exact Context.ready_complete rfl (typed.source.member_stored _ member) available
  | @dereference reference fields slot node loan indices type selected direct handle shape initialized found own path target _ =>
    have handlePath : PathType program home slot.type reference.fields [] slot.type := by rw [direct]; exact .nil _
    obtain ⟨carrier, resolved, raw, _⟩ := typed.resolvePlace selected (.here _) handlePath
    have stored : environment.store (interpretation.binder slot.binder) = some carrier := by
      simpa [Environment.at, Value.readIndices] using raw
    have carrierShape := (typed.slots.lookup selected).2 carrier stored
    simp only [Slot.Corresponds, handle] at carrierShape
    cases carrierShape
    have readCarrier : environment.readAddress ⟨interpretation.binder slot.binder, []⟩ =
        some (.reference (interpretation.node node)) := by
      simp [Environment.readAddress, raw, Value.initialized]
    obtain ⟨state, resident, value, parentAt, fieldsResolved, targetAt, valueTyped, complete⟩ :=
      typed.projectAccess found own path target
    refine ⟨?_, ?_, ?_, ?_, authority, state, value, targetAt, valueTyped, complete⟩
    · simpa [Origin.Known, Origin.extend] using typed.source.loanKnown found
    · simpa [Origin.Bounded, Origin.extend] using (typed.source.targets node loan found).1
    · intro parent same
      cases Option.some.inj same
      exact ⟨loan, found, rfl, indices, rfl⟩
    · simp [Environment.resolveAccess, resolved, readCarrier, typed.records node loan found, own,
        parentAt, fieldsResolved, Interpretation.origin_extend]

theorem StoreTyped.accessReady {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) {place : AccessPlace} {target : Origin}
    {referent : Ty} {parent : Option Nat} {mode : BorrowMode}
    (access : AccessType program home context mode place target referent parent)
    (ready : context.AccessReady target parent) :
    environment.AccessReady ⟨interpretation.origin target, parent.map interpretation.node⟩ := by
  cases access with
  | owner => intro node loan impossible; cases impossible
  | @dereference reference fields slot node loan indices type _ _ _ _ _ found own _ _ _ =>
    intro actualNode actualLoan same actualFound
    cases Option.some.inj same
    have record := typed.records node loan found
    cases Option.some.inj (actualFound.symm.trans record)
    obtain ⟨value, read, _⟩ := typed.targetsReady node loan found own (ready.2 node loan rfl found)
    exact ⟨value, read⟩

theorem StoreTyped.resolveAccess {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) {place : AccessPlace} {target : Origin}
    {referent : Ty} {parent : Option Nat} {mode : BorrowMode}
    (access : AccessType program home context mode place target referent parent)
    (ready : context.AccessReady target parent) :
    target.Known context ∧ target.Bounded context ∧
    (∀ node, parent = some node → ∃ loan, context.loans[node]? = some loan ∧ target.Within loan.target) ∧
    ∃ value, environment.resolveAccess program place = some ⟨interpretation.origin target, parent.map interpretation.node⟩ ∧
      environment.Authorizes mode ⟨interpretation.origin target, parent.map interpretation.node⟩ ∧
      environment.readAddress (interpretation.origin target) = some value ∧ ValueHasType program value referent := by
  obtain ⟨known, bounded, ancestor, resolved, authority, state, value, raw, resident, complete⟩ := typed.resolveAccessMasked access
  obtain ⟨valueTyped, initialized⟩ := resident.complete (complete ready.1)
  exact ⟨known, bounded, ancestor, value, resolved, authority, by simp [Environment.readAddress, raw, initialized], valueTyped⟩

theorem Environment.Copies.deterministic {before firstAfter secondAfter : Environment} {value first second : Value}
    (left : Copies before value first firstAfter) (right : Copies before value second secondAfter) :
    first = second ∧ firstAfter = secondAfter := by
  cases left with
  | data plain => cases right with
    | data => exact ⟨rfl, rfl⟩
    | reference => cases plain
  | reference found allowed => cases right with
    | data plain => cases plain
    | reference otherFound => cases Option.some.inj (found.symm.trans otherFound); exact ⟨rfl, rfl⟩

theorem Environment.Disposes.deterministic {before firstAfter secondAfter : Environment} {value : Value}
    (left : Disposes program before value firstAfter) (right : Disposes program before value secondAfter) :
    firstAfter = secondAfter := by
  cases left with
  | data plain destroyed => cases right with
    | data => rfl
    | reference => cases plain
  | reference _ ended => cases right with
    | data plain => cases plain
    | reference _ otherEnded => exact Option.some.inj (ended.symm.trans otherEnded)

theorem DisposesRoots.deterministic {before firstAfter secondAfter : Environment} {roots : List Root}
    {firstTrace secondTrace : List (Root × List Nat)}
    (left : DisposesRoots program before roots firstTrace firstAfter)
    (right : DisposesRoots program before roots secondTrace secondAfter) :
    firstTrace = secondTrace ∧ firstAfter = secondAfter := by
  induction left generalizing secondTrace secondAfter with
  | nil => cases right; exact ⟨rfl, rfl⟩
  | cons found free head tail ih =>
    cases right with
    | cons otherFound otherFree otherHead otherTail =>
      cases Option.some.inj (found.symm.trans otherFound)
      cases head.deterministic otherHead
      obtain ⟨rfl, rfl⟩ := ih otherTail
      exact ⟨rfl, rfl⟩

theorem Cleans.deterministic {before firstAfter secondAfter : Environment} {count : Nat}
    {firstTrace secondTrace : List (Root × List Nat)}
    (left : Cleans program count before firstTrace firstAfter)
    (right : Cleans program count before secondTrace secondAfter) :
    firstTrace = secondTrace ∧ firstAfter = secondAfter := by
  cases left with
  | retire first => cases right with
    | retire second => obtain ⟨rfl, rfl⟩ := first.deterministic second; exact ⟨rfl, rfl⟩

theorem ResolvesType.deterministic {aliases : Aliases} {source : TypeExpr} {first second : Ty}
    (left : ResolvesType aliases source first) (right : ResolvesType aliases source second) : first = second := by
  induction left using ResolvesType.rec
    (motive_2 := fun sources types _ => ∀ others, ResolvesTypes aliases sources others → types = others)
    generalizing second with
  | concrete => cases right; rfl
  | alias declared expanded ih =>
    cases right with
    | alias otherDeclared otherExpanded =>
      cases Option.some.inj (declared.symm.trans otherDeclared)
      exact ih otherExpanded
  | tuple head tail headIH tailIH =>
    cases right with
    | tuple otherHead otherTail => cases headIH otherHead; cases tailIH _ otherTail; rfl
  | array length resolved ih => cases right with
    | array _ other => cases ih other; rfl
  | nil => rename_i others other; cases other; rfl
  | cons head tail headIH tailIH =>
    rename_i others other
    cases other with
    | cons otherHead otherTail => cases headIH otherHead; cases tailIH _ otherTail; rfl

theorem Evaluates.deterministic {before firstAfter secondAfter : Environment} {core : Core} {first second : Value}
    (left : Evaluates program before core first firstAfter) (right : Evaluates program before core second secondAfter) :
    first = second ∧ firstAfter = secondAfter := by
  induction left using Evaluates.rec
    (motive_2 := fun before expressions plans values after _ => ∀ other otherAfter,
      EvaluatesMany program before expressions plans other otherAfter → values = other ∧ after = otherAfter)
    (motive_3 := fun source plan result _ => ∀ other,
      NormalizesPattern program source plan other → result = other)
    (motive_4 := fun sources plans results _ => ∀ others,
      NormalizesPatterns program sources plans others → results = others)
    (motive_5 := fun sources plans results _ => ∀ others,
      NormalizesArms program sources plans others → results = others)
    generalizing second secondAfter with
  | unit | integer | character => cases right; exact ⟨rfl, rfl⟩
  | group evaluated ih => cases right with
    | group other => exact ih other
  | implicitMove _ ih => cases right with
    | implicitMove other => exact ih other
  | read resolved selected _ copied => cases right with
    | read otherResolved otherSelected _ otherCopied =>
      cases Option.some.inj (resolved.symm.trans otherResolved)
      cases Option.some.inj (selected.symm.trans otherSelected)
      exact copied.deterministic otherCopied
  | move resolved free allowed taken => cases right with
    | move otherResolved otherFree otherAllowed otherTaken =>
      cases Option.some.inj (resolved.symm.trans otherResolved)
      exact Prod.mk.inj (Option.some.inj (taken.symm.trans otherTaken))
  | borrow resolved allowed permitted ready selected plain => cases right with
    | borrow otherResolved otherAllowed otherPermitted otherReady otherSelected otherPlain =>
      cases Option.some.inj (resolved.symm.trans otherResolved)
      exact ⟨rfl, rfl⟩
  | reborrow resolved allowed permitted ready selected plain => cases right with
    | reborrow otherResolved otherAllowed otherPermitted otherReady otherSelected otherPlain =>
      cases Option.some.inj (resolved.symm.trans otherResolved)
      exact ⟨rfl, rfl⟩
  | dereference resolved allowed permitted ready selected plain => cases right with
    | dereference otherResolved otherAllowed otherPermitted otherReady otherSelected otherPlain =>
      cases Option.some.inj (resolved.symm.trans otherResolved)
      exact ⟨Option.some.inj (selected.symm.trans otherSelected), rfl⟩
  | moveIndirect resolved _ _ _ _ taken => cases right with
    | moveIndirect otherResolved _ _ _ _ otherTaken =>
      cases Option.some.inj (resolved.symm.trans otherResolved)
      exact Prod.mk.inj (Option.some.inj (taken.symm.trans otherTaken))
  | assignIndirect evaluated resolved _ _ _ _ _ written continued firstIH restIH => cases right with
    | assignIndirect otherEvaluated otherResolved _ _ _ _ _ otherWritten otherContinued =>
      obtain ⟨rfl, rfl⟩ := firstIH otherEvaluated
      cases Option.some.inj (resolved.symm.trans otherResolved)
      cases Option.some.inj (written.symm.trans otherWritten)
      exact restIH otherContinued
  | endOwn ended continued ih => cases right with
    | endOwn otherEnded otherContinued =>
      cases Option.some.inj (ended.symm.trans otherEnded)
      exact ih otherContinued
  | endAfter evaluated ended usable ih => cases right with
    | endAfter otherEvaluated otherEnded otherUsable =>
      obtain ⟨rfl, rfl⟩ := ih otherEvaluated
      exact ⟨rfl, Option.some.inj (ended.symm.trans otherEnded)⟩
  | sequence head dispose tail headIH tailIH => cases right with
    | sequence otherHead otherDispose otherTail =>
      obtain ⟨rfl, rfl⟩ := headIH otherHead
      cases dispose.deterministic otherDispose
      exact tailIH otherTail
  | bind initialized allowed continued cleanup usable initialIH bodyIH => cases right with
    | bind otherInitialized otherAllowed otherContinued otherCleanup otherUsable =>
      obtain ⟨rfl, rfl⟩ := initialIH otherInitialized
      obtain ⟨rfl, rfl⟩ := bodyIH otherContinued
      obtain ⟨_, cleanup⟩ := cleanup
      obtain ⟨_, otherCleanup⟩ := otherCleanup
      exact ⟨rfl, (cleanup.deterministic otherCleanup).2⟩
  | assign evaluated resolved free previous dispose allowed written continued valueIH restIH => cases right with
    | assign otherEvaluated otherResolved otherFree otherPrevious otherDispose otherAllowed otherWritten otherContinued =>
      obtain ⟨rfl, rfl⟩ := valueIH otherEvaluated
      cases Option.some.inj (resolved.symm.trans otherResolved)
      cases Option.some.inj (previous.symm.trans otherPrevious)
      cases dispose.deterministic otherDispose
      cases Option.some.inj (written.symm.trans otherWritten)
      exact restIH otherContinued
  | tuple head tail plain headIH tailIH => cases right with
    | tuple otherHead otherTail otherPlain =>
      obtain ⟨rfl, rfl⟩ := headIH otherHead
      obtain ⟨rfl, rfl⟩ := tailIH _ _ otherTail
      exact ⟨rfl, rfl⟩
  | array residents plain ih => cases right with
    | array otherResidents otherPlain =>
      obtain ⟨rfl, rfl⟩ := ih _ _ otherResidents
      exact ⟨rfl, rfl⟩
  | construct residents plain ih => cases right with
    | construct otherResidents otherPlain =>
      obtain ⟨rfl, rfl⟩ := ih _ _ otherResidents
      exact ⟨rfl, rfl⟩
  | constant declared initialized plain ih => cases right with
    | constant otherDeclared otherInitialized otherPlain =>
      cases Option.some.inj (declared.symm.trans otherDeclared)
      obtain ⟨rfl, rfl⟩ := ih otherInitialized
      exact ⟨rfl, rfl⟩
  | field source selected extracted dispose usable ih => cases right with
    | field otherSource otherSelected otherExtracted otherDispose otherUsable =>
      obtain ⟨rfl, rfl⟩ := ih otherSource
      cases Option.some.inj (selected.symm.trans otherSelected)
      cases Option.some.inj (extracted.symm.trans otherExtracted)
      exact ⟨rfl, dispose.deterministic otherDispose⟩
  | call declared inputs body cleanup usable inputsIH bodyIH => cases right with
    | call otherDeclared otherInputs otherBody otherCleanup otherUsable =>
      cases Option.some.inj (declared.symm.trans otherDeclared)
      obtain ⟨rfl, rfl⟩ := inputsIH _ _ otherInputs
      obtain ⟨rfl, rfl⟩ := bodyIH otherBody
      obtain ⟨_, cleanup⟩ := cleanup
      obtain ⟨_, otherCleanup⟩ := otherCleanup
      cases (cleanup.deterministic otherCleanup).2
      exact ⟨rfl, rfl⟩
  | applyPatterns normalization arguments plain selected body cleanup usable normalizeIH argumentsIH bodyIH => cases right with
    | applyPatterns otherNormalization otherArguments otherPlain otherSelected otherBody otherCleanup otherUsable =>
      cases normalizeIH _ otherNormalization
      obtain ⟨rfl, rfl⟩ := argumentsIH _ _ otherArguments
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (selected.matches.symm.trans otherSelected.matches))
      obtain ⟨rfl, rfl⟩ := bodyIH otherBody
      obtain ⟨_, cleanup⟩ := cleanup
      obtain ⟨_, otherCleanup⟩ := otherCleanup
      exact ⟨rfl, (cleanup.deterministic otherCleanup).2⟩
  | nil => rename_i other otherAfter otherEval; cases otherEval; exact ⟨rfl, rfl⟩
  | cons head tail usable headIH tailIH =>
      rename_i other otherAfter otherEval
      cases otherEval with
      | cons otherHead otherTail otherUsable =>
        obtain ⟨rfl, rfl⟩ := headIH otherHead
        obtain ⟨rfl, rfl⟩ := tailIH _ _ otherTail
        exact ⟨rfl, rfl⟩
  | wildcard | binder => rename_i other otherEval; cases otherEval; rfl
  | node fields ih =>
      rename_i other otherEval
      cases otherEval with
      | node otherFields => cases ih _ otherFields; rfl
  | constantValue declared resolved evaluated ih =>
      rename_i other otherEval
      cases otherEval with
      | constantValue otherDeclared otherResolved otherEvaluated =>
        cases Option.some.inj (declared.symm.trans otherDeclared)
        cases resolved.deterministic otherResolved
        obtain ⟨rfl, rfl⟩ := ih otherEvaluated
        rfl
  | patternsNil | armsNil => rename_i other otherEval; cases otherEval; rfl
  | patternsCons head tail headIH tailIH =>
      rename_i other otherEval
      cases otherEval with
      | patternsCons otherHead otherTail => cases headIH _ otherHead; cases tailIH _ otherTail; rfl
  | armsCons head tail headIH tailIH =>
      rename_i other otherEval
      cases otherEval with
      | armsCons otherHead otherTail => cases headIH _ otherHead; cases tailIH _ otherTail; rfl

theorem EvaluatesMany.deterministic {before firstAfter secondAfter : Environment}
    {expressions : List Expr} {plans : List CorePlan} {first second : List Value}
    (left : EvaluatesMany program before expressions plans first firstAfter)
    (right : EvaluatesMany program before expressions plans second secondAfter) :
    first = second ∧ firstAfter = secondAfter := by
  induction expressions generalizing before plans first firstAfter second secondAfter with
  | nil => cases left; cases right; exact ⟨rfl, rfl⟩
  | cons expression expressions ih =>
    cases left with
    | cons head tail usable => cases right with
      | cons otherHead otherTail otherUsable =>
        obtain ⟨rfl, rfl⟩ := head.deterministic otherHead
        obtain ⟨rfl, rfl⟩ := ih tail otherTail
        exact ⟨rfl, rfl⟩

theorem NormalizesPattern.deterministic {source : PatternSource} {plan : PatternPlan} {first second : Pattern}
    (left : NormalizesPattern program source plan first)
    (right : NormalizesPattern program source plan second) : first = second := by
  induction left using NormalizesPattern.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ _ => True)
    (motive_4 := fun sources plans results _ => ∀ others,
      NormalizesPatterns program sources plans others → results = others)
    (motive_5 := fun _ _ _ _ => True)
    generalizing second with
  | wildcard | binder => cases right; rfl
  | node fields ih => cases right with
    | node otherFields => cases ih _ otherFields; rfl
  | constantValue declared resolved evaluated ih => cases right with
    | constantValue otherDeclared otherResolved otherEvaluated =>
      cases Option.some.inj (declared.symm.trans otherDeclared)
      cases resolved.deterministic otherResolved
      obtain ⟨rfl, rfl⟩ := evaluated.deterministic otherEvaluated
      rfl
  | patternsNil => rename_i other otherEval; cases otherEval; rfl
  | patternsCons head tail headIH tailIH =>
    rename_i other otherEval
    cases otherEval with
    | patternsCons otherHead otherTail => cases headIH otherHead; cases tailIH _ otherTail; rfl
  | _ => trivial

theorem NormalizesPatterns.deterministic {sources : List PatternSource} {plans : List PatternPlan}
    {first second : List Pattern}
    (left : NormalizesPatterns program sources plans first)
    (right : NormalizesPatterns program sources plans second) : first = second := by
  induction sources generalizing plans first second with
  | nil => cases left; cases right; rfl
  | cons source sources ih => cases left with
    | patternsCons head tail => cases right with
      | patternsCons otherHead otherTail =>
        cases head.deterministic otherHead
        cases ih tail otherTail
        rfl

theorem NormalizesArms.deterministic {sources : List (PatternSource × Expr)}
    {plans : List (PatternPlan × CorePlan)} {first second : List (Pattern × Core)}
    (left : NormalizesArms program sources plans first)
    (right : NormalizesArms program sources plans second) : first = second := by
  induction sources generalizing plans first second with
  | nil => cases left; cases right; rfl
  | cons source sources ih => cases left with
    | armsCons head tail => cases right with
      | armsCons otherHead otherTail =>
        cases head.deterministic otherHead
        cases ih tail otherTail
        rfl

theorem Environment.endOwn_length {before after : Environment} {node : Nat}
    (ended : before.endOwn node = some after) : after.loans.length = before.loans.length := by
  simp only [endOwn, Bind.bind, Option.bind_eq_some_iff, Option.some.injEq] at ended
  obtain ⟨loan, _, rfl⟩ := ended
  simp

theorem Environment.endSlot_length {before after : Environment} {slot : Nat}
    (ended : before.endSlot slot = some after) : after.loans.length = before.loans.length := by
  obtain ⟨_, _, _, _, _, transition⟩ := endSlot_checked ended
  exact endOwn_length transition

theorem Environment.Disposes.loans_length {before after : Environment} {value : Value}
    (disposed : Disposes program before value after) : after.loans.length = before.loans.length := by
  cases disposed with
  | data => rfl
  | reference _ ended => exact endOwn_length ended

theorem DisposesRoots.loans_length {before after : Environment} {roots : List Root} {trace}
    (disposed : DisposesRoots program before roots trace after) : after.loans.length = before.loans.length := by
  induction disposed with
  | nil => rfl
  | cons _ _ head _ ih => exact ih.trans head.loans_length

theorem Cleans.loans_length {before after : Environment} {count trace}
    (cleaned : Cleans program count before trace after) : after.loans.length = before.loans.length := by
  cases cleaned with | retire disposed => exact disposed.loans_length

theorem Environment.prepare_loans (values : BindingValues) (before : Environment) :
    (before.prepare values).loans = before.loans := by
  induction values generalizing before with
  | nil => rfl
  | cons entry rest ih => exact ih _

theorem Environment.writeAddress_loans {before after : Environment} {address : Address} {value : Value}
    (written : before.writeAddress address value = some after) : after.loans = before.loans := by
  simp only [writeAddress, Bind.bind, Option.bind_eq_some_iff, Option.some.injEq] at written
  obtain ⟨parent, _, updated, _, rfl⟩ := written
  rfl

theorem Evaluates.loans_mono {before after : Environment} {core : Core} {value : Value}
    (evaluated : Evaluates program before core value after) : before.loans.length ≤ after.loans.length := by
  induction evaluated using Evaluates.rec
    (motive_2 := fun before _ _ _ after _ => before.loans.length ≤ after.loans.length)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True) with
  | unit | integer | character => exact Nat.le_refl _
  | group _ ih | implicitMove _ ih => exact ih
  | read _ _ _ copied => cases copied <;> simp [Environment.addLoan]
  | move _ _ _ taken =>
    exact Nat.le_of_eq (congrArg List.length (Environment.writeAddress_loans (Environment.takeAddress_eq_some.mp taken).2)).symm
  | moveIndirect _ _ _ _ _ taken =>
    exact Nat.le_of_eq (congrArg List.length (Environment.writeAddress_loans (Environment.takeAddress_eq_some.mp taken).2)).symm
  | assignIndirect _ _ _ _ _ _ _ written _ first rest =>
    rw [Environment.writeAddress_loans written] at rest
    exact Nat.le_trans first rest
  | borrow | reborrow => simp [Environment.addLoan]
  | dereference => exact Nat.le_refl _
  | endOwn ended _ ih => simpa only [Environment.endSlot_length ended] using ih
  | endAfter _ ended _ ih => simpa only [Environment.endSlot_length ended] using ih
  | sequence _ dispose _ first rest => exact Nat.le_trans first (by simpa only [dispose.loans_length] using rest)
  | bind _ _ _ cleanup _ first rest =>
    obtain ⟨trace, cleaned⟩ := cleanup
    rw [cleaned.loans_length]
    exact Nat.le_trans first rest
  | assign _ _ _ _ dispose _ written _ first rest =>
    rw [Environment.writeAddress_loans written, dispose.loans_length] at rest
    exact Nat.le_trans first rest
  | tuple _ _ _ first rest => exact Nat.le_trans first rest
  | array _ _ ih => exact ih
  | constant _ _ _ ih => exact ih
  | construct _ _ ih => exact ih
  | field _ _ _ dispose _ ih => simpa only [dispose.loans_length] using ih
  | call _ _ _ cleanup _ first rest =>
    obtain ⟨trace, cleaned⟩ := cleanup
    simp only [Environment.resume, cleaned.loans_length]
    simp only [Environment.prepare_loans, Environment.hide] at rest
    exact Nat.le_trans first rest
  | applyPatterns _ _ _ _ _ cleanup _ _ first rest =>
    obtain ⟨trace, cleaned⟩ := cleanup
    rw [cleaned.loans_length]
    simp only [Environment.prepare_loans] at rest
    exact Nat.le_trans first rest
  | nil => exact Nat.le_refl _
  | cons _ _ _ first rest => exact Nat.le_trans first rest
  | wildcard | binder | node | constantValue | patternsNil | patternsCons | armsNil | armsCons => trivial


theorem empty_of_length_le {α β : Type} {xs : List α} {ys : List β}
    (le : xs.length ≤ ys.length) (empty : ys = []) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons head tail => simp [empty] at le

theorem Evaluates.empty_before {before after : Environment} {core : Core} {value : Value}
    (evaluated : Evaluates program before core value after) (empty : after.loans = []) : before.loans = [] :=
  empty_of_length_le evaluated.loans_mono empty

theorem EvaluatesMany.loans_mono {before after : Environment} {expressions plans values}
    (evaluated : EvaluatesMany program before expressions plans values after) : before.loans.length ≤ after.loans.length := by
  induction expressions generalizing before plans values with
  | nil => cases evaluated; exact Nat.le_refl _
  | cons head tail ih =>
    cases evaluated with
    | cons first rest _ => exact Nat.le_trans first.loans_mono (ih rest)

theorem EvaluatesMany.empty_before {before after : Environment} {expressions plans values}
    (evaluated : EvaluatesMany program before expressions plans values after) (empty : after.loans = []) : before.loans = [] :=
  empty_of_length_le evaluated.loans_mono empty

theorem Environment.empty_endOwn {before after : Environment} {node : Nat} (empty : before.loans = [])
    (ended : before.endOwn node = some after) : False := by
  simp [endOwn, empty] at ended

theorem Environment.empty_endSlot {before after : Environment} {slot : Nat} (empty : before.loans = [])
    (ended : before.endSlot slot = some after) : False := by
  obtain ⟨_, _, _, _, _, transition⟩ := endSlot_checked ended
  exact empty_endOwn empty transition

theorem Environment.empty_ownerFree {before : Environment} (empty : before.loans = []) (address : Address) :
    before.OwnerFree address := by
  intro node loan found
  simp [empty] at found

theorem Environment.ResultUsable.plain {before : Environment} {value : Value}
    (usable : before.ResultUsable value) (empty : before.loans = []) : value.ReferenceFree := by
  cases value <;> simp_all [ResultUsable, Usable, Value.ReferenceFree]

theorem Environment.ResultUsable.of_plain {before : Environment} {value : Value}
    (plain : value.ReferenceFree) : before.ResultUsable value := by
  cases value <;> simp_all [ResultUsable, Value.ReferenceFree]

theorem Environment.Disposes.empty {before after : Environment} {value : Value}
    (disposed : Disposes program before value after) (empty : before.loans = []) :
    after = before ∧ value.ReferenceFree := by
  cases disposed with
  | data plain _ => exact ⟨rfl, plain⟩
  | reference _ ended => exact False.elim (empty_endOwn empty ended)

theorem DisposesRoots.empty {before after : Environment} {roots trace}
    (disposed : DisposesRoots program before roots trace after) (empty : before.loans = []) : after = before := by
  induction disposed with
  | nil => rfl
  | cons _ _ head _ ih =>
    obtain ⟨rfl, _⟩ := head.empty empty
    exact ih empty

theorem Cleans.empty {before after : Environment} {count trace}
    (cleaned : Cleans program count before trace after) (empty : after.loans = []) :
    before.loans = [] ∧ after = before.retire count := by
  have initial := empty_of_length_le (Nat.le_of_eq cleaned.loans_length.symm) empty
  refine ⟨initial, ?_⟩
  cases cleaned with
  | retire disposed => rw [disposed.empty initial]

theorem DisposesRoots.agrees_stored {left right after : Environment} {leftBindings rightBindings : List (String × Root)}
    {values : BindingValues} {trace}
    (first : StoredBindings left.store leftBindings values)
    (second : StoredBindings right.store rightBindings values)
    (disposed : DisposesRoots program left (leftBindings.map Prod.snd) trace after)
    (leftEmpty : left.loans = []) (rightEmpty : right.loans = []) :
    ∃ otherTrace, DisposesRoots program right (rightBindings.map Prod.snd) otherTrace right := by
  induction first generalizing rightBindings trace after with
  | nil => cases second; exact ⟨[], .nil⟩
  | cons found rest ih =>
    cases second with
    | cons otherFound otherRest =>
      cases disposed with
      | cons selected _ head tail =>
        cases Option.some.inj (found.symm.trans selected)
        obtain ⟨rfl, plain⟩ := head.empty leftEmpty
        obtain ⟨otherTrace, otherTail⟩ := ih otherRest tail
        exact ⟨_, .cons otherFound (Environment.empty_ownerFree rightEmpty _) (.data plain head.logical) otherTail⟩

theorem Cleans.agrees_empty {left right after : Environment} {count trace}
    (cleaned : Cleans program count left trace after) (same : left.Agrees right)
    (leftEmpty : after.loans = []) (rightEmpty : right.loans = []) :
    ∃ otherTrace, Cleans program count right otherTrace (right.retire count) ∧ after.Agrees (right.retire count) := by
  obtain ⟨initial, final⟩ := cleaned.empty leftEmpty
  obtain ⟨values, first, second⟩ := same.values
  have other : ∃ otherTrace, Cleans program count right otherTrace (right.retire count) := by
    cases cleaned with
    | retire disposed =>
      obtain ⟨trace, transported⟩ := disposed.agrees_stored (first.take count) (second.take count) initial rightEmpty
      exact ⟨trace, .retire transported⟩
  obtain ⟨trace, other⟩ := other
  exact ⟨trace, other, final ▸ same.retire count⟩


theorem Evaluates.agrees {left after : Environment} {core : Core} {value : Value}
    (evaluated : Evaluates program left core value after) :
    after.loans = [] → ∀ right, left.Agrees right → right.loans = [] →
      ∃ other, Evaluates program right core value other ∧ after.Agrees other ∧ other.loans = [] := by
  induction evaluated using Evaluates.rec
    (motive_2 := fun left expressions plans values after _ =>
      after.loans = [] → ∀ right, left.Agrees right → right.loans = [] →
        ∃ other, EvaluatesMany program right expressions plans values other ∧ after.Agrees other ∧ other.loans = [])
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True) with
  | unit => intro _ right same empty; exact ⟨right, .unit, same, empty⟩
  | integer fits => intro _ right same empty; exact ⟨right, .integer fits, same, empty⟩
  | character valid => intro _ right same empty; exact ⟨right, .character valid, same, empty⟩
  | group _ ih =>
    intro final right same empty
    obtain ⟨other, body, agreed, final⟩ := ih final right same empty
    exact ⟨other, .group body, agreed, final⟩
  | implicitMove _ ih =>
    intro final right same empty
    obtain ⟨other, body, agreed, final⟩ := ih final right same empty
    exact ⟨other, .implicitMove body, agreed, final⟩
  | read resolved selected _ copied =>
    intro final right same empty
    cases copied with
    | data plain =>
      obtain ⟨address, otherResolved, _, atSame, _⟩ := same.resolvePlace resolved
      exact ⟨right, .read otherResolved (by simpa only [Environment.readAddress, atSame] using selected)
        (by intro node loan found; simp [empty] at found) (.data plain), same, empty⟩
    | reference => simp [Environment.addLoan] at final
  | move resolved _ allowed taken =>
    intro final right same empty
    obtain ⟨read, written⟩ := Environment.takeAddress_eq_some.mp taken
    have initial : _ = [] := (Environment.writeAddress_loans written).symm.trans final
    obtain ⟨address, otherResolved, _, atSame, update⟩ := same.resolvePlace resolved
    obtain ⟨other, written, agreed⟩ := update _ _ written
    exact ⟨other, .move otherResolved (Environment.empty_ownerFree empty _) (.of_plain (allowed.plain initial))
      (Environment.takeAddress_eq_some.mpr ⟨by simpa only [Environment.readAddress, atSame] using read, written⟩),
      agreed, (Environment.writeAddress_loans written).trans empty⟩
  | borrow | reborrow => intro final; simp [Environment.addLoan] at final
  | dereference resolved =>
    intro final
    simp only [Environment.resolveAccess, Bind.bind, Option.bind_eq_some_iff] at resolved
    obtain ⟨carrier, _, resident, _, resolved⟩ := resolved
    cases resident <;> simp_all
  | moveIndirect resolved _ _ _ _ taken =>
    intro final
    have empty := (Environment.writeAddress_loans (Environment.takeAddress_eq_some.mp taken).2).symm.trans final
    simp only [Environment.resolveAccess, Bind.bind, Option.bind_eq_some_iff] at resolved
    obtain ⟨carrier, _, resident, _, resolved⟩ := resolved
    cases resident <;> simp_all
  | assignIndirect _ resolved _ _ _ _ _ written continued _ _ =>
    intro final
    have empty := (Environment.writeAddress_loans written).symm.trans (continued.empty_before final)
    simp only [Environment.resolveAccess, Bind.bind, Option.bind_eq_some_iff] at resolved
    obtain ⟨carrier, _, resident, _, resolved⟩ := resolved
    cases resident <;> simp_all
  | endOwn ended body ih =>
    intro final
    have endedEmpty := body.empty_before final
    have initial := empty_of_length_le (Nat.le_of_eq (Environment.endSlot_length ended).symm) endedEmpty
    exact False.elim (Environment.empty_endSlot initial ended)
  | endAfter body ended _ ih =>
    intro final
    have initial := empty_of_length_le (Nat.le_of_eq (Environment.endSlot_length ended).symm) final
    exact False.elim (Environment.empty_endSlot initial ended)
  | sequence head dispose tail headIH tailIH =>
    intro final right same empty
    have disposedEmpty := tail.empty_before final
    have middleEmpty := empty_of_length_le (Nat.le_of_eq dispose.loans_length.symm) disposedEmpty
    obtain ⟨rfl, plain⟩ := dispose.empty middleEmpty
    obtain ⟨middle, first, middleSame, middleEmpty⟩ := headIH middleEmpty right same empty
    obtain ⟨other, rest, afterSame, otherEmpty⟩ := tailIH final middle middleSame middleEmpty
    exact ⟨other, .sequence first (.data plain dispose.logical) rest, afterSame, otherEmpty⟩
  | bind initial allowed body cleanup usable initialIH bodyIH =>
    intro final right same empty
    obtain ⟨trace, cleaned⟩ := cleanup
    obtain ⟨localEmpty, _⟩ := cleaned.empty final
    have middleEmpty := body.empty_before localEmpty
    obtain ⟨middle, initial, middleSame, middleEmpty'⟩ := initialIH middleEmpty right same empty
    obtain ⟨other, body, afterSame, otherEmpty⟩ := bodyIH localEmpty _ (middleSame.bind _ _) middleEmpty'
    obtain ⟨trace, cleaned, agreed⟩ := cleaned.agrees_empty afterSame final otherEmpty
    exact ⟨other.retire 1, .bind initial (.of_plain (allowed.plain middleEmpty)) body ⟨trace, cleaned⟩
      (.of_plain (usable.plain final)), agreed, otherEmpty⟩
  | assign initial resolved _ previous dispose allowed written body initialIH bodyIH =>
    intro final right same empty
    have updatedEmpty := body.empty_before final
    have disposedEmpty := (Environment.writeAddress_loans written).symm.trans updatedEmpty
    have middleEmpty := empty_of_length_le (Nat.le_of_eq dispose.loans_length.symm) disposedEmpty
    obtain ⟨rfl, plain⟩ := dispose.empty middleEmpty
    obtain ⟨middle, initial, middleSame, middleEmpty'⟩ := initialIH middleEmpty right same empty
    obtain ⟨address, otherResolved, _, atSame, update⟩ := middleSame.resolvePlace resolved
    obtain ⟨updated, written, updatedSame⟩ := update _ _ written
    obtain ⟨other, body, afterSame, otherEmpty⟩ := bodyIH final updated updatedSame ((Environment.writeAddress_loans written).trans middleEmpty')
    exact ⟨other, .assign initial otherResolved (Environment.empty_ownerFree middleEmpty' _) (atSame.trans previous)
      (.data plain dispose.logical) (.of_plain (allowed.plain disposedEmpty)) written body, afterSame, otherEmpty⟩
  | tuple _ tail plain headIH tailIH =>
    intro final right same empty
    obtain ⟨middle, first, middleSame, middleEmpty⟩ := headIH (tail.empty_before final) right same empty
    obtain ⟨other, rest, afterSame, otherEmpty⟩ := tailIH final middle middleSame middleEmpty
    exact ⟨other, .tuple first rest plain, afterSame, otherEmpty⟩
  | array _ plain ih =>
    intro final right same empty
    obtain ⟨other, elements, afterSame, otherEmpty⟩ := ih final right same empty
    exact ⟨other, .array elements plain, afterSame, otherEmpty⟩
  | constant declared initialized plain ih =>
    intro final right same empty
    obtain ⟨other, body, afterSame, otherEmpty⟩ := ih final right.hide same.hide empty
    have initialEmpty := initialized.empty_before final
    simp only [Environment.hide] at initialEmpty
    exact ⟨right.resume other, .constant declared body plain, same.resume afterSame.leftValid afterSame.rightValid
      (initialized.storage same.leftValid.hide).2 (body.storage same.rightValid.hide).2
      (fun root => by simp [Environment.UniqueRoot, initialEmpty])
      (fun root => by simp [Environment.UniqueRoot, empty]), otherEmpty⟩
  | construct _ plain ih =>
    intro final right same empty
    obtain ⟨other, elements, afterSame, otherEmpty⟩ := ih final right same empty
    exact ⟨other, .construct elements plain, afterSame, otherEmpty⟩
  | field _ selected extracted dispose usable ih =>
    intro final right same empty
    have middleEmpty := empty_of_length_le (Nat.le_of_eq dispose.loans_length.symm) final
    obtain ⟨rfl, plain⟩ := dispose.empty middleEmpty
    obtain ⟨other, body, afterSame, otherEmpty⟩ := ih final right same empty
    exact ⟨other, .field body selected extracted (.data plain dispose.logical) (.of_plain (usable.plain final)), afterSame, otherEmpty⟩
  | call declared _ body cleanup usable inputsIH bodyIH =>
    intro final right same empty
    obtain ⟨trace, cleaned⟩ := cleanup
    obtain ⟨localEmpty, cleanedEq⟩ := cleaned.empty final
    have middleEmpty := body.empty_before localEmpty
    simp only [Environment.prepare_loans, Environment.hide] at middleEmpty
    obtain ⟨middle, inputs, middleSame, middleEmpty'⟩ := inputsIH middleEmpty right same empty
    obtain ⟨other, otherBody, afterSame, otherEmpty⟩ := bodyIH localEmpty _ (middleSame.hide.prepare _)
      (by simpa only [Environment.prepare_loans, Environment.hide] using middleEmpty')
    obtain ⟨trace, otherCleaned, agreed⟩ := cleaned.agrees_empty afterSame final otherEmpty
    have leftFrame := (body.storage (middleSame.leftValid.hide.prepare _)).2.scope middleSame.leftValid.hide _
    have rightFrame := (otherBody.storage (middleSame.rightValid.hide.prepare _)).2.scope middleSame.rightValid.hide _
    rw [← cleanedEq] at leftFrame
    exact ⟨_, .call declared inputs otherBody ⟨trace, otherCleaned⟩ (.of_plain (usable.plain final)),
      middleSame.resume agreed.leftValid agreed.rightValid leftFrame rightFrame
        (fun root => by simp [Environment.UniqueRoot, middleEmpty])
        (fun root => by simp [Environment.UniqueRoot, middleEmpty']), otherEmpty⟩
  | applyPatterns normalization _ plain selected _ cleanup usable _ argumentsIH bodyIH =>
    intro final right same empty
    obtain ⟨trace, cleaned⟩ := cleanup
    obtain ⟨localEmpty, _⟩ := cleaned.empty final
    have middleEmpty := Evaluates.empty_before ‹Evaluates _ _ _ _ _› localEmpty
    simp only [Environment.prepare_loans] at middleEmpty
    obtain ⟨middle, arguments, middleSame, middleEmpty'⟩ := argumentsIH middleEmpty right same empty
    obtain ⟨other, body, afterSame, otherEmpty⟩ := bodyIH localEmpty _ (middleSame.prepare _)
      (by simpa only [Environment.prepare_loans] using middleEmpty')
    obtain ⟨trace, otherCleaned, agreed⟩ := cleaned.agrees_empty afterSame final otherEmpty
    exact ⟨_, .applyPatterns normalization arguments plain selected body ⟨trace, otherCleaned⟩
      (.of_plain (usable.plain final)), agreed, otherEmpty⟩
  | nil => rename_i final right same empty; exact ⟨right, .nil, same, empty⟩
  | cons _ tail usable headIH tailIH =>
    rename_i final right same empty
    obtain ⟨middle, first, middleSame, middleEmpty⟩ := headIH (tail.empty_before final) right same empty
    obtain ⟨other, rest, afterSame, otherEmpty⟩ := tailIH final middle middleSame middleEmpty
    exact ⟨other, .cons first rest (.of_plain (usable.plain final)), afterSame, otherEmpty⟩
  | wildcard | binder | node | constantValue | patternsNil | patternsCons | armsNil | armsCons => trivial



/-- Actual reference-free results, not raw equality of potentially renamed handles. -/
theorem Evaluates.referenceFree_of_empty {before after : Environment} {core : Core} {value : Value}
    (evaluated : Evaluates program before core value after) : after.loans = [] → value.ReferenceFree := by
  induction evaluated using Evaluates.rec
    (motive_2 := fun _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True) with
  | unit | integer | character => intro _; trivial
  | group _ ih | implicitMove _ ih => exact ih
  | read _ _ _ copied =>
    intro empty
    cases copied with
    | data plain => exact plain
    | reference => simp [Environment.addLoan] at empty
  | move _ _ usable taken =>
    intro empty
    exact usable.plain ((Environment.writeAddress_loans (Environment.takeAddress_eq_some.mp taken).2).symm.trans empty)
  | borrow | reborrow => intro empty; simp [Environment.addLoan] at empty
  | dereference _ _ _ _ _ plain => exact fun _ => plain
  | moveIndirect _ _ _ _ plain _ => exact fun _ => plain
  | assignIndirect _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | endOwn _ _ ih => exact ih
  | endAfter _ _ usable _ => exact usable.plain
  | sequence _ _ _ _ ih => exact ih
  | bind _ _ _ _ usable _ _ => exact usable.plain
  | assign _ _ _ _ _ _ _ _ _ ih => exact ih
  | tuple _ _ plain _ _ => exact fun _ => plain
  | array _ plain _ => exact fun _ => plain
  | constant _ _ plain _ => exact fun _ => plain
  | construct _ plain _ => exact fun _ => plain
  | field _ _ _ _ usable _ => exact usable.plain
  | call _ _ _ _ usable _ _ => exact usable.plain
  | applyPatterns _ _ _ _ _ _ usable _ _ _ => exact usable.plain
  | nil | cons | wildcard | binder | node | constantValue | patternsNil | patternsCons | armsNil | armsCons => trivial

/-- Conservative old-world specialization of the sole Core evaluator. Old worlds
may have distinct logical roots, supplies and hidden caller cells. The returned
value is owned data; evaluation and visible post-state agreement are proved,
not supplied by the restriction. Empty final history excludes even ended loans,
because the runtime retains records and `Evaluates.loans_mono` proves monotonicity. -/
theorem Evaluates.referenceFree_agreement {left right after : Environment} {core : Core} {value : Value}
    (evaluated : Evaluates program left core value after)
    (rightEmpty : right.loans = []) (same : left.Agrees right) (finalWorld : after.loans = []) :
    value.ReferenceFree ∧ ∃ other, Evaluates program right core value other ∧ after.Agrees other ∧
      other.loans = [] ∧ left.Evolution after ∧ right.Evolution other := by
  obtain ⟨other, transported, agreed, empty⟩ := evaluated.agrees finalWorld right same rightEmpty
  exact ⟨evaluated.referenceFree_of_empty finalWorld, other, transported, agreed, empty,
    (evaluated.storage same.leftValid).2, (transported.storage same.rightValid).2⟩


mutual
/-- The old owned-data source fragment. This is only a syntax restriction: no
execution, output state, or agreement conclusion occurs in its definition.
Calls retain arbitrary recursion; their declaration bodies are covered separately
by `Program.ReferenceFree`. Core plans are deliberately not reconstructed. -/
def Expr.ReferenceFree : Expr → Prop
  | .borrow _ _ | .dereference _ _ | .moveIndirect _ _ | .assignIndirect _ _ _ _ => False
  | .group body | .field body _ => body.ReferenceFree
  | .sequence first rest | .assign _ first rest | .bind _ _ _ first rest =>
      first.ReferenceFree ∧ rest.ReferenceFree
  | .tuple first rest => first.ReferenceFree ∧ expressionsReferenceFree rest
  | .array elements | .construct _ _ elements | .call _ elements => expressionsReferenceFree elements
  | .applyPatterns _ arguments arms => expressionsReferenceFree arguments ∧ armsReferenceFree arms
  | _ => True
def expressionsReferenceFree : List Expr → Prop
  | [] => True
  | head :: tail => head.ReferenceFree ∧ expressionsReferenceFree tail
def armsReferenceFree : List (PatternSource × Expr) → Prop
  | [] => True
  | (_, body) :: tail => body.ReferenceFree ∧ armsReferenceFree tail
end

/-- Every resolvable declaration belongs to the owned fragment; this does not
assume termination, typing, successful lookup, or a future execution state. -/
def Program.ReferenceFree (program : Program) : Prop :=
  (∀ name declaration, program.constants name = some declaration → declaration.body.ReferenceFree) ∧
  (∀ identity declaration, program.functions identity = some declaration → declaration.body.ReferenceFree)

theorem NormalizesArms.referenceFree_bodies {sources plans normalized}
    (normalization : NormalizesArms program sources plans normalized)
    (plain : armsReferenceFree sources) : ∀ arm ∈ normalized, arm.2.source.ReferenceFree := by
  induction sources generalizing plans normalized with
  | nil => cases normalization; simp
  | cons entry rest ih =>
    cases normalization with
    | armsCons _ tail =>
      intro arm member
      rcases List.mem_cons.mp member with rfl | member
      · exact plain.1
      · exact ih tail plain.2 arm member

theorem ConsumesArm.referenceFree_body {value bindings body} {arms : List (Pattern × Core)}
    (selected : ConsumesArm program value arms bindings body)
    (plain : ∀ arm ∈ arms, arm.2.source.ReferenceFree) : body.source.ReferenceFree := by
  induction selected with
  | hit => exact plain _ (List.mem_cons_self)
  | miss _ _ ih => exact ih (fun arm member => plain arm (by simp [member]))

theorem Evaluates.empty_of_referenceFree {before after : Environment} {core : Core} {value : Value}
    (evaluated : Evaluates program before core value after) (declarations : program.ReferenceFree) :
    core.source.ReferenceFree → before.loans = [] → after.loans = [] := by
  induction evaluated using Evaluates.rec
    (motive_2 := fun before expressions _ _ after _ =>
      expressionsReferenceFree expressions → before.loans = [] → after.loans = [])
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True) with
  | unit | integer | character => exact fun _ empty => empty
  | group _ ih | implicitMove _ ih => exact ih
  | read _ _ _ copied =>
    intro _ empty
    cases copied with
    | data => exact empty
    | reference found => simp [empty] at found
  | move _ _ _ taken =>
    intro _ empty
    exact (Environment.writeAddress_loans (Environment.takeAddress_eq_some.mp taken).2).trans empty
  | borrow | dereference | moveIndirect | assignIndirect => intro impossible; exact False.elim impossible
  | reborrow resolved =>
    intro _ empty
    simp only [Environment.resolveAccess, Bind.bind, Option.bind_eq_some_iff] at resolved
    obtain ⟨carrier, _, resident, _, resolved⟩ := resolved
    cases resident <;> simp_all
  | endOwn ended _ _ => intro _ empty; exact False.elim (Environment.empty_endSlot empty ended)
  | endAfter _ ended _ ih =>
    intro plain empty
    exact False.elim (Environment.empty_endSlot (ih plain empty) ended)
  | sequence _ dispose _ first rest =>
    intro plain empty
    have middleEmpty := first plain.1 empty
    obtain ⟨rfl, _⟩ := dispose.empty middleEmpty
    exact rest plain.2 middleEmpty
  | bind _ _ _ cleanup _ first rest =>
    intro plain empty
    have localEmpty := rest plain.2 (first plain.1 empty)
    obtain ⟨trace, cleaned⟩ := cleanup
    exact empty_of_length_le (Nat.le_of_eq cleaned.loans_length) localEmpty
  | assign _ _ _ _ dispose _ written _ first rest =>
    intro plain empty
    have middleEmpty := first plain.1 empty
    have disposedEmpty := empty_of_length_le (Nat.le_of_eq dispose.loans_length) middleEmpty
    exact rest plain.2 ((Environment.writeAddress_loans written).trans disposedEmpty)
  | tuple _ _ _ first rest => exact fun plain empty => rest plain.2 (first plain.1 empty)
  | array _ _ ih => exact ih
  | constant declared _ _ ih => exact fun _ empty => ih (declarations.1 _ _ declared) empty
  | construct _ _ ih => exact ih
  | field _ _ _ dispose _ ih =>
    intro plain empty
    exact empty_of_length_le (Nat.le_of_eq dispose.loans_length) (ih plain empty)
  | call declared _ _ cleanup _ first rest =>
    intro plain empty
    have middleEmpty := first plain empty
    have localEmpty := rest (declarations.2 _ _ declared)
      (by simpa only [Environment.prepare_loans, Environment.hide] using middleEmpty)
    obtain ⟨trace, cleaned⟩ := cleanup
    exact empty_of_length_le (Nat.le_of_eq cleaned.loans_length) localEmpty
  | applyPatterns normalization _ _ selected _ cleanup _ _ first rest =>
    intro plain empty
    have middleEmpty := first plain.1 empty
    have localEmpty := rest (selected.referenceFree_body (normalization.referenceFree_bodies plain.2))
      (by simpa only [Environment.prepare_loans] using middleEmpty)
    obtain ⟨trace, cleaned⟩ := cleanup
    exact empty_of_length_le (Nat.le_of_eq cleaned.loans_length) localEmpty
  | nil => rename_i plain empty; exact empty
  | cons _ _ _ first rest => rename_i plain empty; exact rest plain.2 (first plain.1 empty)
  | wildcard | binder | node | constantValue | patternsNil | patternsCons | armsNil | armsCons => trivial

/-- Prior-source conservation with no post-execution restriction among premises.
The syntax and declaration boundary produces the empty-history fact consumed
by actual evaluator transport. Open vacant cells and hidden caller stores need
no stronger condition than the pre-existing logical agreement relation. -/
theorem Evaluates.referenceFree_source_agreement {left right after : Environment} {core : Core} {value : Value}
    (evaluated : Evaluates program left core value after)
    (declarations : program.ReferenceFree) (source : core.source.ReferenceFree)
    (leftEmpty : left.loans = []) (rightEmpty : right.loans = []) (same : left.Agrees right) :
    value.ReferenceFree ∧ ∃ other, Evaluates program right core value other ∧ after.Agrees other ∧
      other.loans = [] ∧ left.Evolution after ∧ right.Evolution other :=
  evaluated.referenceFree_agreement rightEmpty same (evaluated.empty_of_referenceFree declarations source leftEmpty)
namespace Context

theorem WellFormed.bind {context : Context} (valid : context.WellFormed program)
    (name : String) (mutable : Bool) (result : ResultType)
    (supported : StorageType program.target program.data result.type)
    (reference : ∀ node, result.reference = some node → ∃ loan,
      context.loans[node]? = some loan ∧ result.type = .reference loan.referent loan.mode) :
    (context.bind name mutable result).WellFormed program := by
  refine ⟨?_, ?_, ?_, ?_, valid.parents, ?_, ?_, valid.parentModes⟩
  · rw [valid.bindings_bind name mutable result, List.map_cons, List.nodup_cons]
    refine ⟨?_, valid.distinct⟩
    intro member
    obtain ⟨binding, member, same⟩ := List.mem_map.mp member
    have bound := (valid.slots binding member).1
    change binding.2.binder = context.nextBinder at same
    omega
  · intro binding member
    rw [valid.bindings_bind name mutable result] at member
    rcases List.mem_cons.mp member with rfl | member
    · exact supported
    · exact valid.supported binding member
  · intro binding member
    rw [valid.bindings_bind name mutable result] at member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨Nat.lt_succ_self _, reference⟩
    · obtain ⟨bound, references⟩ := valid.slots binding member
      exact ⟨Nat.lt_succ_of_lt bound, references⟩
  · intro node loan found
    obtain ⟨bound, finite⟩ := valid.targets node loan found
    refine ⟨?_, finite⟩
    cases base : loan.target.base <;> simp_all [Origin.Bounded, Context.bind]
    omega
  · intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨⟨⟨result.type, mutable, .full⟩, context.nextBinder, result.reference⟩, by simp [Context.bind]⟩
    · obtain ⟨slot, found⟩ := valid.named entry member
      have different := Nat.ne_of_lt (valid.allocated entry.2 slot found).2.1
      exact ⟨slot, by simpa [Context.bind, different] using found⟩
  · intro binder slot stored
    simp only [Context.bind] at stored
    split at stored
    · rename_i same
      have identity := OriginBase.binder.inj same
      cases stored
      exact ⟨identity.symm, identity ▸ Nat.lt_succ_self _, supported, reference⟩
    · obtain ⟨identity, bound, supported, reference⟩ := valid.allocated binder slot stored
      exact ⟨identity, Nat.lt_succ_of_lt bound, supported, reference⟩

theorem WellFormed.hide {context : Context} (valid : context.WellFormed program) :
    context.hide.WellFormed program := by
  exact ⟨by simp [Context.hide, Context.bindings], by simp [Context.hide, Context.bindings],
    by simp [Context.hide, Context.bindings], valid.targets, valid.parents,
    by simp [Context.hide], valid.allocated, valid.parentModes⟩

theorem WellFormed.retire_retained {context : Context} (valid : context.WellFormed program)
    (count : Nat) {binder : Nat} (member : binder ∈ (context.names.drop count).map Prod.snd) :
    (context.retire count).storage (.binder binder) = context.storage (.binder binder) := by
  have distinct : ((context.names.map Prod.snd).take count ++ (context.names.map Prod.snd).drop count).Nodup := by
    simpa [← valid.bindings_binders] using valid.distinct
  have disjoint := (List.nodup_append.mp distinct).2.2
  have absent : binder ∉ (context.names.take count).map Prod.snd := by
    intro included
    exact disjoint _ (by simpa only [List.map_take] using included) _
      (by simpa only [List.map_drop] using member) rfl
  simp only [Context.retire, if_neg absent]

private theorem filterMap_drop_of_some {α β : Type} (entries : List α) (f : α → Option β)
    (total : ∀ entry ∈ entries, ∃ value, f entry = some value) (count : Nat) :
    (entries.drop count).filterMap f = (entries.filterMap f).drop count := by
  induction count generalizing entries with
  | zero => rfl
  | succ count ih =>
      cases entries with
      | nil => rfl
      | cons entry entries =>
          obtain ⟨value, found⟩ := total entry (by simp)
          simpa [List.filterMap_cons, found] using
            ih entries (fun other member => total other (by simp [member]))

theorem WellFormed.bindings_retire {context : Context} (valid : context.WellFormed program)
    (count : Nat) : (context.retire count).bindings = context.bindings.drop count := by
  unfold Context.bindings
  change (context.names.drop count).filterMap _ = _
  calc
    _ = (context.names.drop count).filterMap (fun entry =>
        (context.storage (.binder entry.2)).map fun slot => (entry.1, slot)) := by
      apply filterMap_congr_mem
      intro entry member
      rw [valid.retire_retained count (List.mem_map.mpr ⟨entry, member, rfl⟩)]
    _ = _ := filterMap_drop_of_some context.names _ (by
      intro entry member
      obtain ⟨slot, found⟩ := valid.named entry member
      exact ⟨(entry.1, slot), by simp [found]⟩) count

theorem WellFormed.retire {context : Context} (valid : context.WellFormed program) (count : Nat) :
    (context.retire count).WellFormed program := by
  refine ⟨?_, ?_, ?_, valid.targets, valid.parents, ?_, ?_, valid.parentModes⟩
  · rw [valid.bindings_retire count, List.map_drop]
    exact valid.distinct.drop
  · intro binding member
    rw [valid.bindings_retire count] at member
    exact valid.supported binding (List.mem_of_mem_drop member)
  · intro binding member
    rw [valid.bindings_retire count] at member
    exact valid.slots binding (List.mem_of_mem_drop member)
  · intro entry member
    obtain ⟨slot, found⟩ := valid.named entry (List.mem_of_mem_drop member)
    exact ⟨slot, (valid.retire_retained count (List.mem_map.mpr ⟨entry, member, rfl⟩)).trans found⟩
  · intro binder slot stored
    simp only [Context.retire] at stored
    split at stored
    · cases stored
    · exact valid.allocated binder slot stored

theorem WellFormed.dispose {context : Context} (valid : context.WellFormed program) (reference : Option Nat) :
    (context.dispose reference).WellFormed program := by
  cases reference with
  | none => exact valid
  | some node => exact valid.endOwn node

theorem WellFormed.disposeSlots {context : Context} (valid : context.WellFormed program)
    (slots : List (String × Slot)) : (context.disposeSlots slots).WellFormed program := by
  induction slots generalizing context with
  | nil => exact valid
  | cons slot slots ih => exact ih (valid.dispose slot.2.reference)

theorem WellFormed.cleanup {context : Context} (valid : context.WellFormed program) (count : Nat) :
    (context.cleanup count).WellFormed program :=
  (valid.disposeSlots (context.bindings.take count)).retire count

@[simp] theorem disposeSlots_bindings (context : Context) (slots : List (String × Slot)) :
    (context.disposeSlots slots).bindings = context.bindings := by
  induction slots generalizing context with
  | nil => rfl
  | cons slot slots ih =>
    change ((context.dispose slot.2.reference).disposeSlots slots).bindings = _
    rw [ih]
    cases slot.2.reference <;> rfl

@[simp] theorem disposeSlots_supply (context : Context) (slots : List (String × Slot)) :
    (context.disposeSlots slots).nextBinder = context.nextBinder := by
  induction slots generalizing context with
  | nil => rfl
  | cons slot slots ih =>
    change ((context.dispose slot.2.reference).disposeSlots slots).nextBinder = _
    rw [ih]
    cases slot.2.reference <;> rfl

@[simp] theorem disposeSlots_inputs (context : Context) (slots : List (String × Slot)) :
    (context.disposeSlots slots).inputCount = context.inputCount := by
  induction slots generalizing context with
  | nil => rfl
  | cons slot slots ih =>
    change ((context.dispose slot.2.reference).disposeSlots slots).inputCount = _
    rw [ih]
    cases slot.2.reference <;> rfl

theorem WellFormed.prepare {context : Context} (valid : context.WellFormed program)
    (parameters : List (String × BindingType)) (arguments : List ResultType)
    (supported : ∀ result ∈ arguments, StorageType program.target program.data result.type)
    (reference : ∀ result ∈ arguments, ∀ node, result.reference = some node → ∃ loan,
      context.loans[node]? = some loan ∧ result.type = .reference loan.referent loan.mode) :
    (Context.prepare parameters arguments context).WellFormed program := by
  induction parameters generalizing arguments context with
  | nil => exact valid
  | cons parameter parameters ih =>
    cases arguments with
    | nil => exact valid
    | cons argument arguments =>
      exact ih (valid.bind parameter.1 parameter.2.mutable argument
        (supported argument (by simp)) (reference argument (by simp))) arguments
        (fun result member => supported result (by simp [member]))
        (fun result member => reference result (by simp [member]))

end Context


/-- Static record retention, not an operational progress premise. -/
structure Context.History (before after : Context) : Prop where
  records : ∀ (node : Nat) (loan : SourceLoan), before.loans[node]? = some loan → ∃ retained : SourceLoan,
    after.loans[node]? = some retained ∧ retained.target = loan.target ∧
    retained.referent = loan.referent ∧ retained.parent = loan.parent ∧ retained.mode = loan.mode ∧
    (retained.own = true → loan.own = true)
  inputs : after.inputCount = before.inputCount
  supply : before.nextBinder ≤ after.nextBinder
  visible : ∀ binder ∈ after.names.map Prod.snd, binder < before.nextBinder →
    binder ∈ before.names.map Prod.snd
  retained : ∀ binder slot, binder < before.nextBinder → before.storage (.binder binder) = some slot →
    binder ∉ before.names.map Prod.snd → ∃ current, after.storage (.binder binder) = some current ∧
      current.metadata = slot.metadata

namespace Context
namespace History

theorem refl (context : Context) : History context context :=
  ⟨fun _ loan found => ⟨loan, found, rfl, rfl, rfl, rfl, id⟩, rfl, Nat.le_refl _,
    fun _ member _ => member, fun _ slot _ found _ => ⟨slot, found, rfl⟩⟩

theorem trans {before middle after : Context} (first : History before middle)
    (second : History middle after) : History before after := by
  refine ⟨?_, second.inputs.trans first.inputs, Nat.le_trans first.supply second.supply, ?_, ?_⟩
  · intro node loan found
    obtain ⟨middleLoan, middleFound, target, referent, parent, mode, own⟩ := first.records node loan found
    obtain ⟨lastLoan, lastFound, lastTarget, lastReferent, lastParent, lastMode, lastOwn⟩ := second.records node middleLoan middleFound
    exact ⟨lastLoan, lastFound, lastTarget.trans target, lastReferent.trans referent,
      lastParent.trans parent, lastMode.trans mode, fun live => own (lastOwn live)⟩
  · intro binder member old
    exact first.visible binder (second.visible binder member (Nat.lt_of_lt_of_le old first.supply)) old
  · intro binder slot old stored hidden
    obtain ⟨middleSlot, middleStored, middleMetadata⟩ := first.retained binder slot old stored hidden
    have middleHidden : binder ∉ middle.names.map Prod.snd := fun member => hidden (first.visible binder member old)
    obtain ⟨afterSlot, afterStored, afterMetadata⟩ := second.retained binder middleSlot
      (Nat.lt_of_lt_of_le old first.supply) middleStored middleHidden
    exact ⟨afterSlot, afterStored, afterMetadata.trans middleMetadata⟩

theorem endOwn (context : Context) (node : Nat) : History context (context.endOwn node) := by
  refine ⟨?_, rfl, Nat.le_refl _, fun _ member _ => member, fun _ slot _ found _ => ⟨slot, found, rfl⟩⟩
  intro old loan found
  refine ⟨_, context.endOwn_found node found, rfl, rfl, rfl, rfl, ?_⟩
  split <;> simp_all

theorem dispose (context : Context) (reference : Option Nat) : History context (context.dispose reference) := by
  cases reference with
  | none => exact refl context
  | some node => exact endOwn context node

theorem disposeSlots (context : Context) (slots : List (String × Slot)) :
    History context (context.disposeSlots slots) := by
  induction slots generalizing context with
  | nil => exact refl context
  | cons slot slots ih => exact (dispose context slot.2.reference).trans (ih _)

theorem bind (context : Context) (name : String) (mutable : Bool) (result : ResultType) :
    History context (context.bind name mutable result) := by
  refine ⟨fun _ loan found => ⟨loan, found, rfl, rfl, rfl, rfl, id⟩, rfl, Nat.le_succ _, ?_, ?_⟩
  · intro binder member old
    rcases List.mem_cons.mp member with same | member
    · exact False.elim (Nat.ne_of_lt old same)
    · exact member
  · intro binder slot old stored _
    exact ⟨slot, by simpa [Context.bind, Nat.ne_of_lt old] using stored, rfl⟩

theorem hide (context : Context) : History context context.hide :=
  ⟨fun _ loan found => ⟨loan, found, rfl, rfl, rfl, rfl, id⟩, rfl, Nat.le_refl _,
    by simp [Context.hide], fun _ slot _ found _ => ⟨slot, found, rfl⟩⟩

theorem retire (context : Context) (count : Nat) : History context (context.retire count) := by
  refine ⟨fun _ loan found => ⟨loan, found, rfl, rfl, rfl, rfl, id⟩, rfl, Nat.le_refl _, ?_, ?_⟩
  · intro binder member _
    exact List.mem_of_mem_drop (by simpa [Context.retire, List.map_drop] using member)
  · intro binder slot _ stored hidden
    have absent : binder ∉ (context.names.take count).map Prod.snd := by
      intro member
      exact hidden (List.mem_of_mem_take (by simpa only [List.map_take] using member))
    exact ⟨slot, by simpa only [Context.retire, if_neg absent] using stored, rfl⟩

theorem cleanup (context : Context) (count : Nat) : History context (context.cleanup count) :=
  (disposeSlots context (context.bindings.take count)).trans (retire _ count)

theorem borrow (context : Context) (target : Origin) (referent : Ty) (parent : Option Nat) (mode : BorrowMode) :
    History context (context.borrow target referent parent mode) :=
  ⟨fun _ loan found => ⟨loan, borrow_found found, rfl, rfl, rfl, rfl, id⟩, rfl, Nat.le_refl _,
    fun _ member _ => member, fun _ slot _ found _ => ⟨slot, found, rfl⟩⟩

theorem prepare (context : Context) (parameters : List (String × BindingType)) (arguments : List ResultType) :
    History context (Context.prepare parameters arguments context) := by
  induction parameters generalizing arguments context with
  | nil => exact refl context
  | cons parameter parameters ih =>
    cases arguments with
    | nil => exact refl context
    | cons argument arguments => exact (bind context parameter.1 parameter.2.mutable argument).trans (ih _ _)

end History

/-- Raising the unused source-ID supply does not create semantic support. -/
theorem bind_mentions_old {context : Context} {name : String} {mutable : Bool} {result : ResultType}
    {binder : Nat} (old : binder < context.nextBinder) :
    (context.bind name mutable result).MentionsBinder binder ↔ context.MentionsBinder binder := by
  simp only [Context.MentionsBinder, Context.bind, OriginBase.binder.injEq, if_neg (Nat.ne_of_lt old)]

theorem hide_mentions {context : Context} {binder : Nat} :
    context.hide.MentionsBinder binder → context.MentionsBinder binder := id

theorem retire_mentions {context : Context} {count binder : Nat} :
    (context.retire count).MentionsBinder binder → context.MentionsBinder binder := by
  rintro (⟨slot, stored⟩ | loan)
  · simp only [Context.retire] at stored
    split at stored
    · cases stored
    · exact .inl ⟨slot, stored⟩
  · exact .inr loan

theorem dispose_mentions (context : Context) (reference : Option Nat) (binder : Nat) :
    (context.dispose reference).MentionsBinder binder ↔ context.MentionsBinder binder := by
  cases reference with
  | none => exact Iff.rfl
  | some node => exact context.endOwn_mentions node binder

theorem disposeSlots_mentions (context : Context) (slots : List (String × Slot)) (binder : Nat) :
    (context.disposeSlots slots).MentionsBinder binder ↔ context.MentionsBinder binder := by
  induction slots generalizing context with
  | nil => exact Iff.rfl
  | cons slot slots ih => exact (ih _).trans (dispose_mentions _ _ _)

theorem cleanup_mentions {context : Context} {count binder : Nat} :
    (context.cleanup count).MentionsBinder binder → context.MentionsBinder binder :=
  fun mentioned => (disposeSlots_mentions _ _ _).mp (retire_mentions mentioned)

theorem prepare_mentions_old {context : Context} (parameters : List (String × BindingType))
    (arguments : List ResultType) {binder : Nat} (old : binder < context.nextBinder) :
    (Context.prepare parameters arguments context).MentionsBinder binder ↔ context.MentionsBinder binder := by
  induction parameters generalizing arguments context with
  | nil => exact Iff.rfl
  | cons parameter parameters ih =>
    cases arguments with
    | nil => exact Iff.rfl
    | cons argument arguments =>
      exact (ih arguments (Nat.lt_succ_of_lt old)).trans (bind_mentions_old old)
end Context


theorem SlotsJoin.layout {before after : List (String × Slot)} (joined : SlotsJoin program before after) :
    after.map (fun binding => (binding.1, binding.2.type, binding.2.mutable, binding.2.binder, binding.2.reference)) =
    before.map (fun binding => (binding.1, binding.2.type, binding.2.mutable, binding.2.binder, binding.2.reference)) := by
  induction joined with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, ih]

theorem SlotsJoin.binders {before after : List (String × Slot)} (joined : SlotsJoin program before after) :
    after.map (fun binding => binding.2.binder) = before.map (fun binding => binding.2.binder) := by
  induction joined with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, ih]

theorem SlotsJoin.member {before after : List (String × Slot)} (joined : SlotsJoin program before after)
    {binding : String × Slot} (member : binding ∈ after) :
    ∃ original ∈ before, binding.2.type = original.2.type ∧
      binding.2.binder = original.2.binder ∧ binding.2.reference = original.2.reference := by
  induction joined with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, List.mem_cons_self, rfl, rfl, rfl⟩
    · obtain ⟨original, originalMember, shape⟩ := ih member
      exact ⟨original, List.mem_cons_of_mem _ originalMember, shape⟩

namespace Context

theorem Joins.wellFormed {before after : Context} (joined : Joins program before after)
    (valid : before.WellFormed program) : after.WellFormed program := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [joined.slots.binders]
    exact valid.distinct
  · intro binding member
    obtain ⟨original, member, type, _, _⟩ := joined.slots.member member
    rw [type]
    exact valid.supported original member
  · intro binding member
    obtain ⟨original, member, type, binder, reference⟩ := joined.slots.member member
    obtain ⟨bound, references⟩ := valid.slots original member
    refine ⟨?_, ?_⟩
    · rw [binder]
      exact Nat.lt_of_lt_of_le bound joined.supply
    · intro node selected
      obtain ⟨loan, found, shape⟩ := references node (reference ▸ selected)
      exact ⟨loan, joined.loans.symm ▸ found, type.trans shape⟩
  · intro node loan found
    obtain ⟨bounded, finite⟩ := valid.targets node loan (joined.loans ▸ found)
    refine ⟨?_, finite⟩
    cases base : loan.target.base with
    | binder identity =>
      simp only [Origin.Bounded, base] at bounded ⊢
      exact Nat.lt_of_lt_of_le bounded joined.supply
    | input identity => simpa only [Origin.Bounded, base, joined.inputs] using bounded
  · intro node loan parent found derived
    obtain ⟨older, ancestor, ancestorFound, within⟩ := valid.parents node loan parent (joined.loans ▸ found) derived
    exact ⟨older, ancestor, joined.loans.symm ▸ ancestorFound, within⟩
  · intro entry member
    obtain ⟨slot, stored⟩ := valid.named entry (joined.names ▸ member)
    obtain ⟨current, found, _, _⟩ := (joined.storage (.binder entry.2)).forward stored
    exact ⟨current, found⟩
  · intro binder slot stored
    obtain ⟨original, found, metadata, _⟩ := (joined.storage (.binder binder)).backward stored
    obtain ⟨identity, bound, supported, reference⟩ := valid.allocated binder original found
    rcases (show slot.type = original.type ∧ slot.mutable = original.mutable ∧
        slot.binder = original.binder ∧ slot.reference = original.reference from
      by simpa only [Slot.metadata, Prod.mk.injEq] using metadata) with ⟨type, _, binderEq, referenceEq⟩
    refine ⟨binderEq.trans identity, Nat.lt_of_lt_of_le bound joined.supply, type.symm ▸ supported, ?_⟩
    intro node selected
    obtain ⟨loan, found, shape⟩ := reference node (referenceEq ▸ selected)
    exact ⟨loan, joined.loans.symm ▸ found, type.trans shape⟩
  · intro node loan parent ancestor found derived parentFound unique
    exact valid.parentModes node loan parent ancestor (joined.loans ▸ found) derived (joined.loans ▸ parentFound) unique

theorem Joins.mentions {before after : Context} (joined : Joins program before after) (binder : Nat) :
    after.MentionsBinder binder ↔ before.MentionsBinder binder := by
  constructor
  · rintro (⟨slot, stored⟩ | loan)
    · obtain ⟨original, found, _, _⟩ := (joined.storage (.binder binder)).backward stored
      exact .inl ⟨original, found⟩
    · exact .inr (joined.loans ▸ loan)
  · rintro (⟨slot, stored⟩ | loan)
    · obtain ⟨current, found, _, _⟩ := (joined.storage (.binder binder)).forward stored
      exact .inl ⟨current, found⟩
    · exact .inr (joined.loans.symm ▸ loan)

theorem Joins.history {before after : Context} (joined : Joins program before after) : History before after := by
  refine ⟨fun _ loan found => ⟨loan, joined.loans.symm ▸ found, rfl, rfl, rfl, rfl, id⟩,
    joined.inputs, joined.supply, fun _ member _ => joined.names ▸ member, ?_⟩
  intro binder slot _ stored _
  obtain ⟨current, found, metadata, _⟩ := (joined.storage (.binder binder)).forward stored
  exact ⟨current, found, metadata⟩

/-- Only support actually mentioned by slots or loan history is reflected. -/
def ReflectsSupport (before after : Context) : Prop :=
  ∀ binder, after.MentionsBinder binder → binder < before.nextBinder → before.MentionsBinder binder

namespace ReflectsSupport

theorem refl (context : Context) : ReflectsSupport context context := fun _ mentioned _ => mentioned

theorem trans {before middle after : Context} (first : ReflectsSupport before middle)
    (second : ReflectsSupport middle after) (supply : before.nextBinder ≤ middle.nextBinder) :
    ReflectsSupport before after :=
  fun binder mentioned old => first binder (second binder mentioned (Nat.lt_of_lt_of_le old supply)) old

theorem bind (context : Context) (name : String) (mutable : Bool) (result : ResultType) :
    ReflectsSupport context (context.bind name mutable result) :=
  fun _ mentioned old => (bind_mentions_old old).mp mentioned

theorem hide (context : Context) : ReflectsSupport context context.hide :=
  fun _ mentioned _ => hide_mentions mentioned

theorem retire (context : Context) (count : Nat) : ReflectsSupport context (context.retire count) :=
  fun _ mentioned _ => retire_mentions mentioned

theorem endOwn (context : Context) (node : Nat) : ReflectsSupport context (context.endOwn node) :=
  fun binder mentioned _ => (context.endOwn_mentions node binder).mp mentioned

theorem dispose (context : Context) (reference : Option Nat) : ReflectsSupport context (context.dispose reference) :=
  fun binder mentioned _ => (dispose_mentions context reference binder).mp mentioned

theorem disposeSlots (context : Context) (slots : List (String × Slot)) :
    ReflectsSupport context (context.disposeSlots slots) :=
  fun binder mentioned _ => (disposeSlots_mentions context slots binder).mp mentioned

theorem cleanup (context : Context) (count : Nat) : ReflectsSupport context (context.cleanup count) :=
  fun _ mentioned _ => cleanup_mentions mentioned

theorem borrow {context : Context} {target : Origin} {referent : Ty} {parent : Option Nat} {mode : BorrowMode}
    (known : target.Known context) : ReflectsSupport context (context.borrow target referent parent mode) :=
  fun binder mentioned _ => (borrow_mentions known binder).mp mentioned

theorem prepare (context : Context) (parameters : List (String × BindingType)) (arguments : List ResultType) :
    ReflectsSupport context (Context.prepare parameters arguments context) :=
  fun _ mentioned old => (prepare_mentions_old parameters arguments old).mp mentioned

theorem joins {before after : Context} (joined : Joins program before after) : ReflectsSupport before after :=
  fun binder mentioned _ => (joined.mentions binder).mp mentioned

end ReflectsSupport
end Context

namespace Context

theorem History.resume {caller after : Context} (evolved : History caller.hide after) :
    History caller (caller.resume after) :=
  ⟨evolved.records, evolved.inputs, evolved.supply, fun _ member _ => member,
    fun binder slot old stored _ => evolved.retained binder slot old stored (by simp [Context.hide])⟩

theorem WellFormed.resume {caller after : Context} (callerValid : caller.WellFormed program)
    (afterValid : after.WellFormed program) (evolved : History caller.hide after) :
    (caller.resume after).WellFormed program := by
  have named : ∀ entry ∈ caller.names, ∃ slot, after.storage (.binder entry.2) = some slot := by
    intro entry member
    obtain ⟨slot, found⟩ := callerValid.named entry member
    obtain ⟨current, stored, _⟩ := evolved.retained entry.2 slot
      (callerValid.allocated entry.2 slot found).2.1 found (by simp [Context.hide])
    exact ⟨current, stored⟩
  have binders : (caller.resume after).bindings.map (fun binding => binding.2.binder) = caller.names.map Prod.snd := by
    unfold Context.bindings
    rw [List.map_filterMap, ← List.filterMap_eq_map]
    apply filterMap_congr_mem
    intro entry member
    obtain ⟨slot, found⟩ := named entry member
    simp [Context.resume, found, (afterValid.allocated entry.2 slot found).1]
  refine ⟨?_, ?_, ?_, afterValid.targets, afterValid.parents, named, afterValid.allocated, afterValid.parentModes⟩
  · rw [binders, ← callerValid.bindings_binders]
    exact callerValid.distinct
  · intro binding member
    obtain ⟨entry, _, found⟩ := List.mem_filterMap.mp member
    obtain ⟨slot, stored, same⟩ := Option.map_eq_some_iff.mp found
    cases same
    exact (afterValid.allocated entry.2 slot stored).2.2.1
  · intro binding member
    obtain ⟨entry, _, found⟩ := List.mem_filterMap.mp member
    obtain ⟨slot, stored, same⟩ := Option.map_eq_some_iff.mp found
    cases same
    obtain ⟨identity, bound, _, reference⟩ := afterValid.allocated entry.2 slot stored
    exact ⟨identity.symm ▸ bound, reference⟩

/-- Visibility restoration does not change the authoritative storage support. -/
theorem resume_mentions {caller after : Context} {binder : Nat} :
    (caller.resume after).MentionsBinder binder → caller.MentionsBinder binder ∨ after.MentionsBinder binder :=
  fun mentioned => .inr mentioned

theorem ReflectsSupport.resume {caller after : Context} (reflected : ReflectsSupport caller.hide after) :
    ReflectsSupport caller (caller.resume after) := by
  intro binder mentioned old
  rcases resume_mentions mentioned with callerMentioned | afterMentioned
  · exact callerMentioned
  · exact hide_mentions (reflected binder afterMentioned old)

end Context

private theorem held_append_shared {held : List Value} {node other index : Nat} :
    (held ++ [Value.reference node])[index]? = some (.reference other) ↔
      held[index]? = some (.reference other) ∨ (index = held.length ∧ node = other) := by
  by_cases bound : index < held.length
  · simp only [List.getElem?_append_left bound]
    simp [Nat.ne_of_lt bound]
  · rw [List.getElem?_append_right (Nat.le_of_not_lt bound)]
    have absent := List.getElem?_eq_none (Nat.le_of_not_lt bound)
    cases difference : index - held.length with
    | zero =>
      have same : index = held.length := by omega
      simp [same]
    | succ rest =>
      have different : index ≠ held.length := by omega
      simp [absent, different]

theorem Custody.install {environment : Environment} {held : List Value} {node root : Nat}
    (custody : Custody environment (held ++ [.reference node]))
    (cleared : ∀ other loan, environment.loans[other]? = some loan → loan.own = true →
      environment.store root ≠ some (.reference other)) :
    Custody (environment.put root (.reference node)) held := by
  intro other loan found own
  obtain ⟨location, carrier, unique⟩ := custody other loan found own
  by_cases same : node = other
  · subst other
    have last : Carries environment (held ++ [.reference node]) node (.held held.length) := by
      simp [Carries]
    refine ⟨.stored root, by simp [Carries, Environment.put], ?_⟩
    intro second carried
    cases second with
    | stored cell =>
      by_cases equal : cell = root
      · subst cell; rfl
      · have old : Carries environment (held ++ [.reference node]) node (.stored cell) := by
          simpa [Carries, Environment.put, equal] using carried
        have impossible := (unique _ old).trans (unique _ last).symm
        cases impossible
    | held index =>
      have old : Carries environment (held ++ [.reference node]) node (.held index) :=
        held_append_shared.mpr (.inl carried)
      have equal := (unique _ old).trans (unique _ last).symm
      have indices := Carrier.held.inj equal
      have bound := (List.getElem?_eq_some_iff.mp carried).1
      omega
  · have equivalent : ∀ place, Carries (environment.put root (.reference node)) held other place ↔
        Carries environment (held ++ [.reference node]) other place := by
      intro place
      cases place with
      | stored cell =>
        by_cases equal : cell = root
        · subst cell
          simp [Carries, Environment.put, same, cleared other loan found own]
        · simp [Carries, Environment.put, equal]
      | held index => simp [Carries, held_append_shared, same]
    exact ⟨location, (equivalent location).mpr carrier,
      fun second carried => unique second ((equivalent second).mp carried)⟩

theorem Custody.move {environment : Environment} {held : List Value} {node root : Nat}
    (custody : Custody environment held)
    (stored : environment.store root = some (.reference node)) :
    Custody (environment.put root .vacant) (held ++ [.reference node]) := by
  intro other loan found own
  obtain ⟨location, carrier, unique⟩ := custody other loan found own
  by_cases same : node = other
  · subst other
    refine ⟨.held held.length, by simp [Carries], ?_⟩
    intro second carried
    cases second with
    | stored cell =>
      by_cases equal : cell = root
      · simp [Carries, Environment.put, equal] at carried
      · have old : Carries environment held node (.stored cell) := by
          simpa [Carries, Environment.put, equal] using carried
        have indices := Carrier.stored.inj ((unique _ old).trans (unique (.stored root) stored).symm)
        exact False.elim (equal indices)
    | held index =>
      rcases held_append_shared.mp carried with old | ⟨equal, _⟩
      · have impossible := (unique (.held index) old).trans (unique (.stored root) stored).symm
        cases impossible
      · subst index; rfl
  · have equivalent : ∀ place, Carries (environment.put root .vacant) (held ++ [.reference node]) other place ↔
        Carries environment held other place := by
      intro place
      cases place with
      | stored cell =>
        by_cases equal : cell = root
        · subst cell; simp [Carries, Environment.put, stored, same]
        · simp [Carries, Environment.put, equal]
      | held index => simp [Carries, held_append_shared, same]
    exact ⟨location, (equivalent location).mpr carrier,
      fun second carried => unique second ((equivalent second).mp carried)⟩

theorem Custody.endOwn {before after : Environment} {held : List Value} {node : Nat}
    (custody : Custody before held) (ended : before.endOwn node = some after) : Custody after held := by
  intro other loan found own
  have old := Environment.endOwn_active ended found own
  obtain ⟨location, carrier, unique⟩ := custody other loan old.1 own
  have stores : after.store = before.store := by rw [Environment.endOwn_state ended]
  have equivalent : ∀ place, Carries after held other place ↔ Carries before held other place := by
    intro place; cases place <;> simp [Carries, stores]
  exact ⟨location, (equivalent _).mpr carrier, fun second carried => unique second ((equivalent _).mp carried)⟩

theorem Custody.retire {environment : Environment} {held : List Value} {count : Nat}
    (custody : Custody environment held)
    (cleared : ∀ root ∈ (environment.bindings.take count).map Prod.snd,
      ∀ node loan, environment.loans[node]? = some loan → loan.own = true →
        environment.store root ≠ some (.reference node)) : Custody (environment.retire count) held := by
  intro node loan found own
  obtain ⟨location, carrier, unique⟩ := custody node loan found own
  have equivalent : ∀ place, Carries (environment.retire count) held node place ↔ Carries environment held node place := by
    intro place
    cases place with
    | held index => rfl
    | stored root =>
      by_cases removed : root ∈ (environment.bindings.take count).map Prod.snd
      · simp only [Carries, Environment.retire, if_pos removed]
        simp [cleared root removed node loan found own]
      · simp only [Carries, Environment.retire, if_neg removed]
  exact ⟨location, (equivalent _).mpr carrier, fun second carried => unique second ((equivalent _).mp carried)⟩


variable {program : Program}

theorem Custody.bindReference {environment : Environment} {held : List Value} {node : Nat}
    (custody : Custody environment (held ++ [.reference node])) (valid : environment.Valid) (name : String) :
    Custody (environment.bind name (.reference node)) held := by
  have installed := custody.install (root := environment.nextRoot)
    (by intro other loan found own; simp [valid.fresh])
  exact installed

theorem Environment.Disposes.active {before after : Environment} {value : Value}
    (disposed : Environment.Disposes program before value after)
    {node : Nat} {loan : Loan} (found : after.loans[node]? = some loan) (own : loan.own = true) :
    before.loans[node]? = some loan ∧ value ≠ .reference node := by
  cases disposed with
  | data plain =>
    refine ⟨found, ?_⟩
    intro equal; subst value; exact plain
  | reference _ ended =>
    have active := Environment.endOwn_active ended found own
    exact ⟨active.1, fun equal => active.2 (Value.reference.inj equal)⟩

theorem Custody.dispose {before after : Environment} {held : List Value} {value : Value}
    (custody : Custody before held) (disposed : Environment.Disposes program before value after) :
    Custody after held := by
  cases disposed with
  | data => exact custody
  | reference _ ended => exact custody.endOwn ended

theorem Custody.assignReference {before disposed : Environment} {held : List Value} {node root : Nat} {old : Value}
    (custody : Custody before (held ++ [.reference node])) (stored : before.store root = some old)
    (disposal : Environment.Disposes program before old disposed) :
    Custody (disposed.put root (.reference node)) held := by
  apply (custody.dispose disposal).install
  intro other loan found own carried
  rw [disposal.storage.store, stored] at carried
  exact (disposal.active found own).2 (Option.some.inj carried)

theorem Custody.restoreReference {environment : Environment} {held : List Value} {node root : Nat}
    (custody : Custody environment (held ++ [.reference node]))
    (vacant : environment.store root = some .vacant) :
    Custody (environment.put root (.reference node)) held := by
  apply custody.install
  intro other loan found own
  simp [vacant]

theorem DisposesRoots.active {before after : Environment} {roots : List Root}
    {trace : List (Root × List Nat)} (disposed : DisposesRoots program before roots trace after)
    {node : Nat} {loan : Loan} (found : after.loans[node]? = some loan) (own : loan.own = true) :
    before.loans[node]? = some loan ∧
      ∀ root ∈ roots, after.store root ≠ some (.reference node) := by
  induction disposed with
  | nil => exact ⟨found, by simp⟩
  | @cons before middle after root roots value trace stored free head tail ih =>
    have rest := ih found
    have first := head.active rest.1 own
    refine ⟨first.1, ?_⟩
    intro cell member
    rcases List.mem_cons.mp member with rfl | member
    · rw [tail.storage.store, head.storage.store, stored]
      exact fun equal => first.2 (Option.some.inj equal)
    · exact rest.2 cell member

theorem Custody.disposesRoots {before after : Environment} {held : List Value} {roots : List Root}
    {trace : List (Root × List Nat)} (custody : Custody before held)
    (disposed : DisposesRoots program before roots trace after) : Custody after held := by
  induction disposed with
  | nil => exact custody
  | cons stored free head tail ih => exact ih (custody.dispose head)

theorem Custody.cleans {before after : Environment} {held : List Value} {count : Nat}
    {trace : List (Root × List Nat)} (custody : Custody before held)
    (cleaned : Cleans program count before trace after) : Custody after held := by
  cases cleaned with
  | retire disposed =>
    apply (custody.disposesRoots disposed).retire
    intro root member node loan found own
    exact (disposed.active found own).2 root (by simpa only [disposed.storage.bindings] using member)



private theorem Value.writeIndices_not_shared {value replacement updated : Value} {fields : List Nat}
    (plain : replacement.ReferenceFree) (written : value.writeIndices fields replacement = some updated)
    (node : Nat) : updated ≠ .reference node := by
  cases fields with
  | nil =>
    have equal : replacement = updated := by simpa [Value.writeIndices] using written
    subst updated
    intro equal; subst replacement; exact plain
  | cons index rest =>
    simp only [Value.writeIndices, Bind.bind, Option.bind_eq_some_iff] at written
    obtain ⟨child, _, next, _, written⟩ := written
    cases value <;> simp only [Value.replaceChild] at written
    all_goals try cases written
    case tuple head tail =>
      cases index with
      | zero => cases written; simp
      | succ index =>
        obtain ⟨_, _, equal⟩ := Option.map_eq_some_iff.mp written
        cases equal; simp
    case nominal identity tag values =>
      obtain ⟨_, _, equal⟩ := Option.map_eq_some_iff.mp written
      cases equal; simp

theorem Custody.writeAddress {before after : Environment} {held : List Value} {address : Address}
    {replacement parent : Value} (custody : Custody before held)
    (stored : before.store address.root = some parent) (oldPlain : parent.ReferenceFree)
    (plain : replacement.ReferenceFree) (written : before.writeAddress address replacement = some after) :
    Custody after held := by
  simp only [Environment.writeAddress, stored, Bind.bind, Option.bind_some, Option.bind_eq_some_iff,
    Option.some.injEq] at written
  obtain ⟨updated, update, rfl⟩ := written
  intro node loan found own
  obtain ⟨location, carrier, unique⟩ := custody node loan found own
  have noOld : parent ≠ .reference node := by intro equal; subst parent; exact oldPlain
  have noNew := Value.writeIndices_not_shared plain update node
  have equivalent : ∀ place, Carries (before.put address.root updated) held node place ↔
      Carries before held node place := by
    intro place
    cases place with
    | held index => rfl
    | stored root =>
      by_cases equal : root = address.root
      · subst root; simp [Carries, Environment.put, stored, noOld, noNew]
      · simp [Carries, Environment.put, equal]
  exact ⟨location, (equivalent _).mpr carrier, fun other carried => unique other ((equivalent _).mp carried)⟩

theorem Custody.writeAddress_selected {before after : Environment} {held : List Value} {address : Address}
    {replacement selected : Value} (custody : Custody before held)
    (shape : ∀ root value, before.store root = some value →
      value.ReferenceFree ∨ ∃ node, value = .reference node ∧ node < before.loans.length)
    (read : before.at address = some selected) (oldPlain : selected.ReferenceFree)
    (plain : replacement.ReferenceFree) (written : before.writeAddress address replacement = some after) :
    Custody after held := by
  simp only [Environment.at, Bind.bind, Option.bind_eq_some_iff] at read
  obtain ⟨parent, stored, selectedAt⟩ := read
  apply custody.writeAddress stored _ plain written
  rcases shape address.root parent stored with free | ⟨node, rfl, _⟩
  · exact free
  · cases fields : address.fields with
    | nil =>
      have equal : Value.reference node = selected := by simpa [Value.readIndices, fields] using selectedAt
      subst selected; exact False.elim oldPlain
    | cons index rest => simp [Value.readIndices, Value.children, fields] at selectedAt

theorem Custody.takeReference {before after : Environment} {held : List Value} {root node : Nat}
    (custody : Custody before held)
    (taken : before.takeAddress ⟨root, []⟩ = some (.reference node, after)) :
    Custody after (held ++ [.reference node]) := by
  simp only [Environment.takeAddress, Bind.bind, Option.bind_eq_some_iff, Option.some.injEq] at taken
  obtain ⟨value, read, next, written, equal⟩ := taken
  cases equal
  simp only [Environment.readAddress, Environment.at, Value.readIndices, Bind.bind,
    Option.bind_eq_some_iff] at read
  obtain ⟨parent, ⟨resident, stored, equal⟩, read⟩ := read
  cases equal
  split at read
  · have equal : parent = .reference node := Option.some.inj read
    subst parent
    have equal : before.put root .vacant = after := by
      simpa [Environment.writeAddress, Value.writeIndices, stored] using written
    subst after
    exact custody.move stored
  · cases read


variable {program : Program}

theorem Custody.assignReferenceAddress {before disposed : Environment} {held : List Value}
    {node root : Nat} {old : Value}
    (custody : Custody before (held ++ [.reference node])) (stored : before.store root = some old)
    (disposal : Environment.Disposes program before old disposed) :
    disposed.writeAddress ⟨root, []⟩ (.reference node) = some (disposed.put root (.reference node)) ∧
      Custody (disposed.put root (.reference node)) held := by
  refine ⟨?_, custody.assignReference stored disposal⟩
  simp [Environment.writeAddress, Value.writeIndices, disposal.storage.store, stored]

theorem Custody.restoreReferenceAddress {environment : Environment} {held : List Value} {node root : Nat}
    (custody : Custody environment (held ++ [.reference node]))
    (vacant : environment.store root = some .vacant) :
    environment.writeAddress ⟨root, []⟩ (.reference node) = some (environment.put root (.reference node)) ∧
      Custody (environment.put root (.reference node)) held := by
  exact ⟨by simp [Environment.writeAddress, Value.writeIndices, vacant], custody.restoreReference vacant⟩



theorem EnvironmentTyped.index {environment : Environment} {slots : List (String × BindingType)}
    (typed : EnvironmentTyped program environment slots) {index : Nat} {name : String} {slot : BindingType}
    (selected : slots[index]? = some (name, slot)) :
    ∃ root value, environment.bindings[index]? = some (name, root) ∧ environment.store root = some value ∧
      SlotTyped program value slot := by
  obtain ⟨values, stored, residents⟩ := typed.residents
  clear typed
  generalize environment.bindings = bindings at stored ⊢
  induction residents generalizing index bindings with
  | nil => simp at selected
  | @cons key value head values slots resident rest ih =>
    cases stored with
    | cons found stored =>
      cases index with
      | zero => cases Option.some.inj selected; exact ⟨_, _, rfl, found, resident⟩
      | succ index =>
        obtain ⟨root, value, indexed, found, resident⟩ := ih selected _ stored
        exact ⟨root, value, indexed, found, resident⟩

theorem StoreTyped.member {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) {binding : String × Slot}
    (member : binding ∈ context.bindings) :
    ∃ value, environment.store (interpretation.binder binding.2.binder) = some value ∧
      SlotTyped program value binding.2.toBindingType ∧ binding.2.Corresponds interpretation value := by
  obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp member
  have selected : context.bindings[index]? = some binding := (List.getElem?_eq_getElem bound).trans (congrArg some equal)
  have selectedErased : context.erase[index]? = some (binding.1, binding.2.toBindingType) := by
    simp [Context.erase, List.getElem?_map, selected]
  obtain ⟨root, value, indexed, stored, resident⟩ := typed.residents.index selectedErased
  obtain ⟨mapped, correspondence⟩ := typed.slots.index selected
  have same := Prod.mk.inj (Option.some.inj (indexed.symm.trans mapped))
  cases same.2
  exact ⟨value, stored, resident, correspondence value stored⟩

theorem StateTyped.disposeSlot {interpretation : Interpretation} {context : Context} {heldNodes : List Nat}
    {environment : Environment} {held : List Value}
    (typed : StateTyped program interpretation context heldNodes environment held) {binding : String × Slot}
    (member : binding ∈ context.bindings) (allowed : binding.2.toBindingType.Disposable program)
    (unprotected : ∀ node, binding.2.reference = some node → node ∉ heldNodes)
    (ready : ∀ node, binding.2.reference = some node → context.Restored node) :
    ∃ value after, environment.store (interpretation.binder binding.2.binder) = some value ∧
      Environment.Disposes program environment value after ∧
      StateTyped program interpretation (context.dispose binding.2.reference) heldNodes after held := by
  obtain ⟨value, stored, resident, corresponds⟩ := typed.toStoreTyped.member member
  cases reference : binding.2.reference with
  | none =>
    have plain : value.ReferenceFree := by simpa [Slot.Corresponds, reference] using corresponds
    exact ⟨value, environment, stored, .data plain (StorageDisposition.realized allowed resident).destroys, typed⟩
  | some node =>
    have shape : value = .reference (interpretation.node node) := by simpa [Slot.Corresponds, reference] using corresponds
    cases shape
    obtain ⟨loan, found, _⟩ := (typed.source.slots binding member).2 node reference
    obtain ⟨after, ended, afterTyped⟩ := typed.endOwn found (unprotected node reference)
    exact ⟨_, after, stored, .reference (typed.toStoreTyped.restored found (ready node reference)) ended, by simpa [Context.dispose, reference] using afterTyped⟩

theorem Environment.Disposes.ownerFree {before after : Environment} {value : Value}
    (disposed : Disposes program before value after) {address : Address} (free : before.OwnerFree address) :
    after.OwnerFree address := by
  intro node loan found own
  exact free node loan (disposed.active found own).1 own

theorem DisposesRoots.ownerFree {before after : Environment} {roots : List Root} {trace : List (Root × List Nat)}
    (disposed : DisposesRoots program before roots trace after) {address : Address} (free : before.OwnerFree address) :
    after.OwnerFree address := by
  induction disposed with
  | nil => exact free
  | cons found allowed head tail ih => exact ih (head.ownerFree free)

theorem DisposesRoots.freed {before after : Environment} {roots : List Root} {trace : List (Root × List Nat)}
    (disposed : DisposesRoots program before roots trace after) :
    ∀ root ∈ roots, after.OwnerFree ⟨root, []⟩ := by
  induction disposed with
  | nil => simp
  | cons found allowed head tail ih =>
    intro root member
    rcases List.mem_cons.mp member with rfl | member
    · exact tail.ownerFree (head.ownerFree allowed)
    · exact ih root member

theorem SlotsCorrespond.roots {interpretation : Interpretation} {store : Store}
    {bindings : List (String × Root)} {slots : List (String × Slot)}
    (typed : SlotsCorrespond interpretation store bindings slots) :
    bindings.map Prod.snd = slots.map (fun binding => interpretation.binder binding.2.binder) := by
  induction typed with
  | nil => rfl
  | cons identity resident rest ih => simp [identity, ih]

theorem StateTyped.disposeSlots {interpretation : Interpretation} {context : Context} {heldNodes : List Nat}
    {environment : Environment} {held : List Value}
    (typed : StateTyped program interpretation context heldNodes environment held) {slots : List (String × Slot)}
    (members : ∀ binding ∈ slots, binding ∈ context.bindings)
    (allowed : context.Cleanable program heldNodes slots) :
    ∃ after trace, DisposesRoots program environment (slots.map fun binding => interpretation.binder binding.2.binder) trace after ∧
      StateTyped program interpretation (context.disposeSlots slots) heldNodes after held := by
  induction slots generalizing context environment with
  | nil => exact ⟨environment, [], .nil, typed⟩
  | cons binding slots ih =>
    obtain ⟨drop, free, unprotected, ready, rest⟩ := allowed
    have member := members binding (by simp)
    have known : (Origin.mk (.binder binding.2.binder) []).Known context := typed.source.member_known binding member
    have runtimeFree := typed.toStoreTyped.ownerFree known free
    obtain ⟨value, middle, found, disposed, middleTyped⟩ := typed.disposeSlot member drop unprotected ready
    have tailMembers : ∀ slot ∈ slots, slot ∈ (context.dispose binding.2.reference).bindings := by
      intro slot included
      have old := members slot (by simp [included])
      cases binding.2.reference <;> exact old
    obtain ⟨after, trace, tail, afterTyped⟩ := ih middleTyped tailMembers rest
    exact ⟨after, _, .cons found runtimeFree disposed tail, afterTyped⟩

theorem SlotsCorrespond.drop {interpretation : Interpretation} {store : Store}
    {bindings : List (String × Root)} {slots : List (String × Slot)}
    (typed : SlotsCorrespond interpretation store bindings slots) (count : Nat) :
    SlotsCorrespond interpretation store (bindings.drop count) (slots.drop count) := by
  induction count generalizing bindings slots with
  | zero => exact typed
  | succ count ih => cases typed with
    | nil => exact .nil
    | cons identity resident tail => exact ih tail

theorem SlotsCorrespond.frame {interpretation : Interpretation} {before after : Store}
    {bindings : List (String × Root)} {slots : List (String × Slot)}
    (typed : SlotsCorrespond interpretation before bindings slots)
    (same : ∀ root ∈ bindings.map Prod.snd, after root = before root) :
    SlotsCorrespond interpretation after bindings slots := by
  induction typed with
  | nil => exact .nil
  | cons identity resident tail ih =>
    refine .cons identity ?_ (ih ?_)
    · intro value found
      apply resident value
      rwa [same _ (by simp)] at found
    · intro root member
      exact same root (by simp [member])

theorem StoreTyped.retire {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) (count : Nat)
    (free : ∀ root ∈ (environment.bindings.take count).map Prod.snd, environment.OwnerFree ⟨root, []⟩) :
    StoreTyped program interpretation (context.retire count) (environment.retire count) := by
  refine { typed with
    source := typed.source.retire count
    residents := ?_
    slots := ?_
    cells := by
      intro binder slot stored
      simp only [Context.retire] at stored
      split at stored
      · cases stored
      · rename_i absent
        obtain ⟨value, found, resident, corresponds⟩ := typed.cells binder slot stored
        have outside : interpretation.binder binder ∉ (environment.bindings.take count).map Prod.snd := by
          intro included
          rw [List.map_take, typed.slots.roots, ← List.map_take] at included
          obtain ⟨binding, member, equal⟩ := List.mem_map.mp included
          have identity := typed.binderDistinct binding.2.binder binder
            (typed.source.member_known binding (List.mem_of_mem_take member)) (.inl ⟨slot, stored⟩) equal
          apply absent
          rw [List.map_take, ← typed.source.bindings_binders, ← List.map_take]
          exact List.mem_map.mpr ⟨binding, member, identity⟩
        exact ⟨value, by simpa only [Environment.retire, if_neg outside] using found, resident, corresponds⟩
    binderBound := ?_
    binderDistinct := ?_
    inputApart := ?_
    sourceTargets := by
      intro node loan found own
      apply (typed.sourceTargets node loan found own).storage_congr
      cases base : loan.target.base with
      | input input => rfl
      | binder binder =>
        have outside : binder ∉ (context.names.take count).map Prod.snd := by
          intro removed
          have runtimeRemoved : interpretation.binder binder ∈ (environment.bindings.take count).map Prod.snd := by
            rw [List.map_take, typed.slots.roots]
            have included : interpretation.binder binder ∈ ((context.names.take count).map Prod.snd).map interpretation.binder :=
              List.mem_map.mpr ⟨binder, removed, rfl⟩
            simpa only [List.map_take, ← typed.source.bindings_binders, List.map_map, Function.comp_def] using included
          have apart := free _ runtimeRemoved (interpretation.node node) _ (typed.records node loan found) own
          simp only [Address.Apart, Interpretation.origin, base] at apart
          rcases apart with different | fields
          · exact different rfl
          · cases fields
        simp only [Context.retire, if_neg outside]
    inputTargets := ?_
    storeShape := ?_ }
  · simpa only [Context.erase, typed.source.bindings_retire count, List.map_drop] using typed.residents.retire count
  · rw [typed.source.bindings_retire count]
    apply (typed.slots.drop count).frame
    intro root retained
    apply Environment.retire_frame
    intro removed
    have distinct : ((environment.roots.take count) ++ environment.roots.drop count).Nodup := by
      simpa using typed.residents.valid.distinct
    exact (List.nodup_append.mp distinct).2.2 root
      (by simpa [Environment.roots, List.map_take] using removed) root
      (by simpa [Environment.roots, List.map_drop] using retained) rfl
  · intro binder known
    exact typed.binderBound binder (Context.retire_mentions known)
  · intro first second firstKnown secondKnown same
    exact typed.binderDistinct first second (Context.retire_mentions firstKnown) (Context.retire_mentions secondKnown) same
  · intro binder input known bound
    exact typed.inputApart binder input (Context.retire_mentions known) bound
  · intro node loan found own input base
    obtain ⟨value, read, valueTyped⟩ := typed.inputTargets node loan found own input base
    have outside : (interpretation.origin loan.target).root ∉ (environment.bindings.take count).map Prod.snd := by
      intro removed
      have apart := free _ removed (interpretation.node node) _ (typed.records node loan found) own
      rcases apart with different | fields
      · exact different rfl
      · cases fields
    refine ⟨value, ?_, valueTyped⟩
    simpa only [Environment.readAddress, Environment.at, Environment.retire, if_neg outside] using read
  · intro root value stored
    simp only [Environment.retire] at stored
    split at stored
    · cases stored
    · exact typed.storeShape root value stored

theorem Context.Ready.retire {context : Context} {origin : Origin} {referent : Ty} {count : Nat}
    (ready : context.Ready origin) (target : (context.retire count).Target program origin referent) :
    (context.retire count).Ready origin := by
  apply ready.storage_congr
  cases base : origin.base with
  | input input => rfl
  | binder binder =>
    simp only [Context.Target, base] at target
    obtain ⟨slot, stored, _⟩ := target
    have outside : binder ∉ (context.names.take count).map Prod.snd := by
      intro removed
      simp only [Context.retire, if_pos removed] at stored
      cases stored
    simp only [Context.retire, if_neg outside]

theorem Context.Restored.bind {context : Context} {node : Nat} (ready : context.Restored node)
    (valid : context.WellFormed program) (name : String) (mutable : Bool) (result : ResultType) :
    (context.bind name mutable result).Restored node := by
  intro loan found own
  apply (ready loan found own).storage_congr
  cases base : loan.target.base with
  | input input => simp [Context.bind]
  | binder binder =>
    have bound : binder < context.nextBinder := by
      simpa [Origin.Bounded, base] using (valid.targets node loan found).1
    simp [Context.bind, Nat.ne_of_lt bound]

theorem StateTyped.cleanup {interpretation : Interpretation} {context : Context} {heldNodes : List Nat}
    {environment : Environment} {held : List Value}
    (typed : StateTyped program interpretation context heldNodes environment held) (count : Nat)
    (allowed : context.Cleanable program heldNodes (context.bindings.take count)) :
    ∃ after trace, Cleans program count environment trace after ∧
      StateTyped program interpretation (context.cleanup count) heldNodes after held := by
  obtain ⟨disposed, trace, destroyed, disposedTyped⟩ := typed.disposeSlots
    (fun _ member => List.mem_of_mem_take member) allowed
  have roots : (environment.bindings.take count).map Prod.snd =
      (context.bindings.take count).map (fun binding => interpretation.binder binding.2.binder) := by
    rw [List.map_take, typed.slots.roots, ← List.map_take]
  have destroyedRoots : DisposesRoots program environment ((environment.bindings.take count).map Prod.snd) trace disposed := by
    simpa only [roots] using destroyed
  have cleaned : Cleans program count environment trace (disposed.retire count) := .retire destroyedRoots
  have free : ∀ root ∈ (disposed.bindings.take count).map Prod.snd, disposed.OwnerFree ⟨root, []⟩ := by
    simpa only [destroyed.storage.bindings, roots] using destroyed.freed
  refine ⟨disposed.retire count, trace, cleaned, ?_⟩
  let stored := disposedTyped.toStoreTyped.retire count free
  exact { stored with
    heldShape := disposedTyped.heldShape
    heldOwn := disposedTyped.heldOwn
    heldReady := fun node member loan found own =>
      (disposedTyped.heldReady node member loan found own).retire (stored.sourceTargets node loan found own).1
    custody := typed.custody.cleans cleaned }

theorem StoreTyped.hide {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) :
    StoreTyped program interpretation context.hide environment.hide := by
  exact { typed with
    source := typed.source.hide
    residents := typed.residents.hide
    slots := .nil
    binderBound := fun binder known => typed.binderBound binder (Context.hide_mentions known)
    binderDistinct := fun first second a b same => typed.binderDistinct first second
      (Context.hide_mentions a) (Context.hide_mentions b) same
    inputApart := fun binder input known bound => typed.inputApart binder input (Context.hide_mentions known) bound }

theorem StateTyped.hide {interpretation : Interpretation} {context : Context} {heldNodes : List Nat}
    {environment : Environment} {held : List Value}
    (typed : StateTyped program interpretation context heldNodes environment held) :
    StateTyped program interpretation context.hide heldNodes environment.hide held :=
  { typed.toStoreTyped.hide with
    heldShape := typed.heldShape
    heldOwn := typed.heldOwn
    heldReady := typed.heldReady
    custody := typed.custody }

/-- Frame facts concern the proof interpretation only, including skipped source
IDs. Bounds remain restricted to semantic support, never invented allocations. -/
structure Interpretation.Extends (before after : Interpretation) (context : Context) : Prop where
  binders : ∀ binder, binder < context.nextBinder → after.binder binder = before.binder binder
  nodes : ∀ node, node < context.loans.length → after.node node = before.node node
  inputs : after.input = before.input

structure StateProgress (beforeContext afterContext : Context) (before after : Environment)
    (first last : Interpretation) : Prop where
  history : beforeContext.History afterContext
  support : beforeContext.ReflectsSupport afterContext
  interpretation : first.Extends last beforeContext
  fresh : ∀ binder, beforeContext.nextBinder ≤ binder → afterContext.MentionsBinder binder →
    before.nextRoot ≤ last.binder binder
  loanCount : after.loans.length + beforeContext.loans.length = before.loans.length + afterContext.loans.length

theorem ResultTyped.transport {before after : Context} {first last : Interpretation} {value : Value} {result : ResultType}
    (typed : ResultTyped program first before value result) (history : before.History after)
    (same : first.Extends last before) : ResultTyped program last after value result := by
  refine ⟨typed.resident, ?_⟩
  cases reference : result.reference with
  | none => simpa [reference] using typed.shape
  | some node =>
    have shape := typed.shape
    rw [reference] at shape
    obtain ⟨valueShape, loan, found, typeShape⟩ := shape
    obtain ⟨retained, kept, _, referent, _, mode, _⟩ := history.records node loan found
    exact ⟨valueShape.trans (congrArg Value.reference (same.nodes node (List.getElem?_eq_some_iff.mp found).1).symm),
      retained, kept, typeShape.trans (by rw [referent, mode])⟩

theorem SlotsJoin.erased {before after : List (String × Slot)} (joined : SlotsJoin program before after) :
    ContextJoins program (before.map fun binding => (binding.1, binding.2.toBindingType))
      (after.map fun binding => (binding.1, binding.2.toBindingType)) := by
  induction joined with
  | nil => exact .nil
  | cons head tail ih => exact .cons head ih

theorem SlotsCorrespond.join {interpretation : Interpretation} {store : Store}
    {bindings : List (String × Root)} {before after : List (String × Slot)}
    (typed : SlotsCorrespond interpretation store bindings before) (joined : SlotsJoin program before after) :
    SlotsCorrespond interpretation store bindings after := by
  induction joined generalizing bindings with
  | nil => cases typed; exact .nil
  | cons head tail ih => cases typed with
    | cons identity resident rest => exact .cons identity resident (ih rest)

theorem StoreTyped.join {interpretation : Interpretation} {context afterContext : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) (joined : context.Joins program afterContext) :
    StoreTyped program interpretation afterContext environment := by
  refine { typed with
    source := joined.wellFormed typed.source
    residents := typed.residents.join joined.slots.erased
    slots := typed.slots.join joined.slots
    cells := by
      intro binder slot stored
      obtain ⟨original, sourceStored, metadata, state⟩ := (joined.storage (.binder binder)).backward stored
      obtain ⟨value, found, resident, corresponds⟩ := typed.cells binder original sourceStored
      have equal : slot.type = original.type ∧ slot.mutable = original.mutable ∧
          slot.binder = original.binder ∧ slot.reference = original.reference := by
        simpa only [Slot.metadata, Prod.mk.injEq] using metadata
      refine ⟨value, found, ?_, ?_⟩
      · simpa only [SlotTyped, equal.1] using resident.join state
      · simpa only [Slot.Corresponds, equal.2.2.2] using corresponds
    binderBound := ?_
    binderDistinct := ?_
    inputBound := ?_
    inputApart := ?_
    nodeOrder := ?_
    records := ?_
    activeCoverage := ?_
    sourceTargets := by
      intro node loan found own
      have oldFound : context.loans[node]? = some loan := joined.loans ▸ found
      obtain ⟨target, ready, inputShared⟩ := typed.sourceTargets node loan oldFound own
      refine ⟨?_, ?_, inputShared⟩
      · cases base : loan.target.base with
        | input input => simp [Context.Target, base]
        | binder binder =>
          obtain ⟨slot, stored, path, state, access⟩ := (by simpa [Context.Target, base] using target)
          obtain ⟨current, currentStored, metadata, _⟩ := (joined.storage (.binder binder)).forward stored
          have type : current.type = slot.type := congrArg Prod.fst metadata
          obtain ⟨next, nextAccess, _⟩ := joined.targetMasks node loan oldFound own binder slot current state base stored currentStored access
          simp only [Context.Target, base]
          exact ⟨current, currentStored, type ▸ path, next, nextAccess⟩
      · intro shared
        have oldReady := ready shared
        cases base : loan.target.base with
        | input input => simp [Context.Ready, base]
        | binder binder =>
          simp only [Context.Ready, base] at oldReady ⊢
          obtain ⟨slot, state, stored, access, complete⟩ := oldReady
          obtain ⟨current, currentStored, _, _⟩ := (joined.storage (.binder binder)).forward stored
          obtain ⟨next, nextAccess, nextComplete⟩ := joined.targetMasks node loan oldFound own binder slot current state base stored currentStored access
          exact ⟨current, next, currentStored, nextAccess, nextComplete complete⟩
    inputTargets := ?_ }
  · intro binder known
    exact typed.binderBound binder ((joined.mentions binder).mp known)
  · intro first second firstKnown secondKnown same
    exact typed.binderDistinct first second ((joined.mentions first).mp firstKnown) ((joined.mentions second).mp secondKnown) same
  · intro input bound
    exact typed.inputBound input (by simpa only [joined.inputs] using bound)
  · intro binder input known bound
    exact typed.inputApart binder input ((joined.mentions binder).mp known) (by simpa only [joined.inputs] using bound)
  · simpa only [joined.loans] using typed.nodeOrder
  · simpa only [joined.loans] using typed.records
  · simpa only [joined.loans] using typed.activeCoverage
  · simpa only [joined.loans] using typed.inputTargets

theorem StateTyped.join {interpretation : Interpretation} {context afterContext : Context} {heldNodes : List Nat}
    {environment : Environment} {held : List Value}
    (typed : StateTyped program interpretation context heldNodes environment held) (joined : context.Joins program afterContext) :
    StateTyped program interpretation afterContext heldNodes environment held := by
  exact { typed.toStoreTyped.join joined with
    heldShape := typed.heldShape
    heldOwn := by simpa only [Context.Own, joined.loans] using typed.heldOwn
    heldReady := by
      intro node member loan found own
      have oldFound : context.loans[node]? = some loan := joined.loans ▸ found
      have ready := typed.heldReady node member loan oldFound own
      cases base : loan.target.base with
      | input input => simp [Context.Ready, base]
      | binder binder =>
        simp only [Context.Ready, base] at ready ⊢
        obtain ⟨slot, state, stored, access, complete⟩ := ready
        obtain ⟨current, currentStored, _, _⟩ := (joined.storage (.binder binder)).forward stored
        obtain ⟨next, nextAccess, nextComplete⟩ := joined.targetMasks node loan oldFound own binder slot current state base stored currentStored access
        exact ⟨current, next, currentStored, nextAccess, nextComplete complete⟩
    custody := typed.custody }

def Interpretation.addBinder (interpretation : Interpretation) (source runtime : Nat) : Interpretation :=
  { interpretation with binder := fun binder => if binder = source then runtime else interpretation.binder binder }

theorem Context.WellFormed.mentionedBound {context : Context} (valid : context.WellFormed program)
    {binder : Nat} (mentioned : context.MentionsBinder binder) : binder < context.nextBinder := by
  rcases mentioned with ⟨slot, stored⟩ | ⟨node, loan, found, base⟩
  · exact (valid.allocated binder slot stored).2.1
  · simpa [Origin.Bounded, base] using (valid.targets node loan found).1

theorem Context.bind_mentions (context : Context) (name : String) (mutable : Bool) (result : ResultType)
    (binder : Nat) : (context.bind name mutable result).MentionsBinder binder ↔
      binder = context.nextBinder ∨ context.MentionsBinder binder := by
  by_cases same : binder = context.nextBinder
  · subst binder
    simp [Context.MentionsBinder, Context.bind]
  · simp [Context.MentionsBinder, Context.bind, same]

theorem StoreTyped.bind {interpretation : Interpretation} {context : Context} {environment : Environment}
    {value : Value} {result : ResultType}
    (typed : StoreTyped program interpretation context environment)
    (valueTyped : ResultTyped program interpretation context value result) (name : String) (mutable : Bool) :
    StoreTyped program (interpretation.addBinder context.nextBinder environment.nextRoot)
      (context.bind name mutable result) (environment.bind name value) := by
  let next := interpretation.addBinder context.nextBinder environment.nextRoot
  have oldBinder : ∀ binder, context.MentionsBinder binder → next.binder binder = interpretation.binder binder := by
    intro binder mentioned
    simp [next, Interpretation.addBinder, Nat.ne_of_lt (typed.source.mentionedBound mentioned)]
  have freshBinder : next.binder context.nextBinder = environment.nextRoot := by simp [next, Interpretation.addBinder]
  have oldOrigin : ∀ (node : Nat) (loan : SourceLoan), context.loans[node]? = some loan → next.origin loan.target = interpretation.origin loan.target := by
    intro node loan found
    cases base : loan.target.base with
    | binder binder => simp [Interpretation.origin, base, oldBinder binder (.inr ⟨node, loan, found, base⟩)]
    | input input => simp [Interpretation.origin, base, next, Interpretation.addBinder]
  have rootOld : ∀ (node : Nat) (loan : SourceLoan), context.loans[node]? = some loan → (interpretation.origin loan.target).root < environment.nextRoot := by
    intro node loan found
    cases base : loan.target.base with
    | binder binder => simpa [Interpretation.origin, base] using typed.binderBound binder (.inr ⟨node, loan, found, base⟩)
    | input input =>
      simp only [Interpretation.origin, base]
      apply typed.inputBound input
      simpa [Origin.Bounded, base] using (typed.source.targets node loan found).1
  have reference : ∀ node, result.reference = some node → ∃ loan,
      context.loans[node]? = some loan ∧ result.type = .reference loan.referent loan.mode := by
    intro node equal
    have shape := valueTyped.shape
    rw [equal] at shape
    exact shape.2
  have supported : StorageType program.target program.data result.type := by
    cases equal : result.reference with
    | none =>
      have shape := valueTyped.shape
      rw [equal] at shape
      exact .data shape.1
    | some node =>
      obtain ⟨loan, found, shape⟩ := reference node equal
      rw [shape]
      exact .reference (typed.source.targets node loan found).2
  refine { source := typed.source.bind name mutable result supported reference
           residents := by
             simpa only [Context.erase, typed.source.bindings_bind name mutable result, List.map_cons] using
               typed.residents.bind (name := name) (slot := ⟨result.type, mutable, .full⟩) valueTyped.resident
           slots := ?_
           cells := by
             intro binder slot stored
             by_cases same : binder = context.nextBinder
             · subst binder
               simp only [Context.bind] at stored
               cases stored
               refine ⟨value, ?_, valueTyped.resident, ?_⟩
               · simp [Environment.bind, Interpretation.addBinder]
               · cases reference : result.reference with
                 | none =>
                   have shape := valueTyped.shape
                   rw [reference] at shape
                   exact shape.2
                 | some node =>
                   have shape := valueTyped.shape
                   rw [reference] at shape
                   exact shape.1
             · have oldStored : context.storage (.binder binder) = some slot := by
                 simpa [Context.bind, same] using stored
               obtain ⟨resident, found, residentTyped, corresponds⟩ := typed.cells binder slot oldStored
               have known : context.MentionsBinder binder := .inl ⟨slot, oldStored⟩
               refine ⟨resident, ?_, residentTyped, corresponds⟩
               change (environment.bind name value).store (next.binder binder) = some resident
               rw [oldBinder binder known]
               simpa [Environment.bind, Nat.ne_of_lt (typed.binderBound binder known)] using found
           binderBound := ?_
           binderDistinct := ?_
           inputBound := ?_
           inputApart := ?_
           nodeOrder := typed.nodeOrder
           records := ?_
           activeCoverage := typed.activeCoverage
           sourceTargets := by
             intro node loan found own
             apply (typed.sourceTargets node loan found own).storage_congr
             cases base : loan.target.base with
             | input input => simp [Context.bind]
             | binder binder =>
               have bound : binder < context.nextBinder := by
                 simpa [Origin.Bounded, base] using (typed.source.targets node loan found).1
               simp [Context.bind, Nat.ne_of_lt bound]
           inputTargets := ?_
           storeShape := ?_ }
  · rw [typed.source.bindings_bind name mutable result]
    apply SlotsCorrespond.cons freshBinder.symm
    · intro resident stored
      have equal : value = resident := by simpa [Environment.bind] using stored
      subst resident
      cases equal : result.reference with
      | none =>
        have shape := valueTyped.shape
        rw [equal] at shape
        exact shape.2
      | some node =>
        have shape := valueTyped.shape
        rw [equal] at shape
        exact shape.1
    · have preserve : ∀ {bindings slots}, SlotsCorrespond interpretation environment.store bindings slots →
          (∀ binding ∈ slots, context.MentionsBinder binding.2.binder) →
          SlotsCorrespond next (environment.bind name value).store bindings slots := by
        intro bindings slots correspondence
        induction correspondence with
        | nil => intro _; exact .nil
        | @cons key root slot bindings slots identity resident rest ih =>
          intro members
          have mention := members (key, slot) (by simp)
          have below : root < environment.nextRoot := by rw [identity]; exact typed.binderBound slot.binder mention
          refine .cons (identity.trans (oldBinder slot.binder mention).symm) ?_ (ih (fun binding member => members binding (by simp [member])))
          intro old stored
          exact resident old (by simpa [Environment.bind, Nat.ne_of_lt below] using stored)
      exact preserve typed.slots (fun binding member => typed.source.member_known binding member)
  · intro binder mentioned
    rcases (Context.bind_mentions _ _ _ _ _).mp mentioned with rfl | old
    · simp [Interpretation.addBinder, Environment.bind]
    · change next.binder binder < environment.nextRoot + 1
      rw [oldBinder binder old]
      exact Nat.lt_succ_of_lt (typed.binderBound binder old)
  · intro first second firstMention secondMention equal
    rcases (Context.bind_mentions _ _ _ _ _).mp firstMention with rfl | firstOld <;>
      rcases (Context.bind_mentions _ _ _ _ _).mp secondMention with rfl | secondOld
    · rfl
    · change next.binder context.nextBinder = next.binder second at equal
      rw [freshBinder, oldBinder second secondOld] at equal
      have bound := typed.binderBound second secondOld
      exact False.elim ((Nat.ne_of_lt bound) equal.symm)
    · change next.binder first = next.binder context.nextBinder at equal
      rw [oldBinder first firstOld, freshBinder] at equal
      have bound := typed.binderBound first firstOld
      exact False.elim ((Nat.ne_of_lt bound) equal)
    · apply typed.binderDistinct first second firstOld secondOld
      change next.binder first = next.binder second at equal
      simpa [oldBinder first firstOld, oldBinder second secondOld] using equal
  · intro input bound
    exact Nat.lt_succ_of_lt (typed.inputBound input bound)
  · intro binder input mentioned bound
    rcases (Context.bind_mentions _ _ _ _ _).mp mentioned with rfl | old
    · change next.binder context.nextBinder ≠ (interpretation.input input).root
      rw [freshBinder]
      exact Nat.ne_of_gt (typed.inputBound input bound)
    · change next.binder binder ≠ (interpretation.input input).root
      rw [oldBinder binder old]
      exact typed.inputApart binder input old bound
  · intro node loan found
    change environment.loans[interpretation.node node]? = some ⟨next.origin loan.target, loan.parent.map interpretation.node, loan.own, loan.mode⟩
    rw [oldOrigin node loan found]
    exact typed.records node loan found
  · intro node loan found own input base
    obtain ⟨resident, read, residentTyped⟩ := typed.inputTargets node loan found own input base
    refine ⟨resident, ?_, residentTyped⟩
    change (environment.bind name value).readAddress (next.origin loan.target) = some resident
    rw [oldOrigin node loan found]
    simpa [Environment.readAddress, Environment.at, Environment.bind, Nat.ne_of_lt (rootOld node loan found)] using read
  · intro root resident stored
    by_cases equal : root = environment.nextRoot
    · subst root
      have same : value = resident := by simpa [Environment.bind] using stored
      subst resident
      cases equal : result.reference with
      | none =>
        have shape := valueTyped.shape
        rw [equal] at shape
        exact .inl shape.2
      | some node =>
        have shape := valueTyped.shape
        rw [equal] at shape
        obtain ⟨loan, found, _⟩ := shape.2
        exact .inr ⟨interpretation.node node, shape.1, (List.getElem?_eq_some_iff.mp (typed.records node loan found)).1⟩
    · exact typed.storeShape root resident (by simpa [Environment.bind, equal] using stored)

theorem StateTyped.bind {interpretation : Interpretation} {context : Context} {environment : Environment}
    {heldNodes : List Nat} {held : List Value} {value : Value} {result : ResultType}
    (typed : StateTyped program interpretation context (heldNodes ++ result.nodes)
      environment (held ++ value.referenceValues))
    (valueTyped : ResultTyped program interpretation context value result) (name : String) (mutable : Bool) :
    StateTyped program (interpretation.addBinder context.nextBinder environment.nextRoot)
      (context.bind name mutable result) heldNodes (environment.bind name value) held := by
  refine { toStoreTyped := typed.toStoreTyped.bind valueTyped name mutable
           heldShape := ?_
           heldOwn := ?_
           heldReady := fun node member =>
             (typed.heldReady node (List.mem_append_left _ member)).bind typed.source name mutable result
           custody := ?_ }
  · have shape := typed.heldShape
    rw [List.map_append, ← valueTyped.referenceValues] at shape
    exact List.append_cancel_right shape
  · intro node member
    exact typed.heldOwn node (List.mem_append_left _ member)
  · cases reference : result.reference with
    | some node =>
      have shape := valueTyped.shape
      rw [reference] at shape
      have custody : Custody environment (held ++ [.reference (interpretation.node node)]) := by
        simpa [shape.1, Value.referenceValues] using typed.custody
      simpa [shape.1] using custody.bindReference typed.residents.valid name
    | none =>
      have shape := valueTyped.shape
      rw [reference] at shape
      have custody : Custody environment held := by
        simpa [shape.2.referenceValues] using typed.custody
      intro node loan found own
      obtain ⟨location, carried, unique⟩ := custody node loan found own
      have equivalent : ∀ place, Carries (environment.bind name value) held node place ↔
          Carries environment held node place := by
        intro place
        cases place with
        | held index => rfl
        | stored root =>
          by_cases equal : root = environment.nextRoot
          · subst root
            have notShared : value ≠ .reference node := by
              intro same; subst value; exact shape.2
            simp [Carries, Environment.bind, typed.residents.valid.fresh, notShared]
          · simp [Carries, Environment.bind, equal]
      exact ⟨location, (equivalent location).mpr carried,
        fun other carried => unique other ((equivalent other).mp carried)⟩


theorem Context.History.loanLength {before after : Context} (history : before.History after) :
    before.loans.length ≤ after.loans.length := by
  apply Nat.le_of_not_gt
  intro bound
  obtain ⟨retained, kept, _⟩ := history.records after.loans.length before.loans[after.loans.length]
    (List.getElem?_eq_getElem bound)
  simp at kept

theorem Interpretation.Extends.refl (interpretation : Interpretation) (context : Context) :
    interpretation.Extends interpretation context := ⟨fun _ _ => rfl, fun _ _ => rfl, rfl⟩

theorem Interpretation.Extends.trans {first middle last : Interpretation} {before after : Context}
    (front : first.Extends middle before) (back : middle.Extends last after) (history : before.History after) :
    first.Extends last before := by
  refine ⟨?_, ?_, back.inputs.trans front.inputs⟩
  · intro binder bound
    exact (back.binders binder (Nat.lt_of_lt_of_le bound history.supply)).trans (front.binders binder bound)
  · intro node bound
    exact (back.nodes node (Nat.lt_of_lt_of_le bound history.loanLength)).trans (front.nodes node bound)

theorem StateProgress.refl {interpretation : Interpretation} {context : Context} {environment : Environment}
    (valid : context.WellFormed program) : StateProgress context context environment environment interpretation interpretation :=
  ⟨.refl _, .refl _, .refl _ _, fun _ large known => False.elim (Nat.not_lt_of_ge large (valid.mentionedBound known)), rfl⟩

theorem StateProgress.trans {firstContext middleContext lastContext : Context} {first middle last : Environment}
    {firstMap middleMap lastMap : Interpretation}
    (front : StateProgress firstContext middleContext first middle firstMap middleMap)
    (back : StateProgress middleContext lastContext middle last middleMap lastMap)
    (supply : first.nextRoot ≤ middle.nextRoot) : StateProgress firstContext lastContext first last firstMap lastMap := by
  refine ⟨front.history.trans back.history, front.support.trans back.support front.history.supply,
    front.interpretation.trans back.interpretation front.history, ?_, ?_⟩
  · intro binder large known
    by_cases old : binder < middleContext.nextBinder
    · rw [back.interpretation.binders binder old]
      exact front.fresh binder large (back.support binder known old)
    · exact Nat.le_trans supply (back.fresh binder (Nat.le_of_not_lt old) known)
  · have a := front.loanCount
    have b := back.loanCount
    omega

theorem Context.dispose_loans_length (context : Context) (reference : Option Nat) :
    (context.dispose reference).loans.length = context.loans.length := by
  cases reference <;> simp [Context.dispose, Context.endOwn]

theorem Context.disposeSlots_loans_length (context : Context) (slots : List (String × Slot)) :
    (context.disposeSlots slots).loans.length = context.loans.length := by
  induction slots generalizing context with
  | nil => rfl
  | cons slot slots ih => exact (ih _).trans (context.dispose_loans_length slot.2.reference)

theorem Context.cleanup_loans_length (context : Context) (count : Nat) :
    (context.cleanup count).loans.length = context.loans.length := context.disposeSlots_loans_length _

theorem StateProgress.endOwn {interpretation : Interpretation} {context : Context} {before after : Environment}
    {node : Nat} (valid : context.WellFormed program) (ended : before.endOwn (interpretation.node node) = some after) :
    StateProgress context (context.endOwn node) before after interpretation interpretation := by
  refine ⟨.endOwn _ _, .endOwn _ _, .refl _ _, ?_, ?_⟩
  · intro binder large known
    exact False.elim (Nat.not_lt_of_ge large (valid.mentionedBound ((context.endOwn_mentions node binder).mp known)))
  · simp only [Environment.endOwn_length ended, Context.endOwn, List.length_modify]

theorem StateProgress.dispose {interpretation : Interpretation} {context : Context} {before after : Environment}
    {reference : Option Nat} {value : Value} (valid : context.WellFormed program)
    (disposed : Environment.Disposes program before value after) :
    StateProgress context (context.dispose reference) before after interpretation interpretation := by
  refine ⟨.dispose _ _, .dispose _ _, .refl _ _, ?_, ?_⟩
  · intro binder large known
    exact False.elim (Nat.not_lt_of_ge large (valid.mentionedBound ((Context.dispose_mentions _ _ _).mp known)))
  · rw [disposed.loans_length, Context.dispose_loans_length]

theorem StateProgress.cleanup {interpretation : Interpretation} {context : Context} {before after : Environment}
    {count : Nat} {trace : List (Root × List Nat)} (valid : context.WellFormed program)
    (cleaned : Cleans program count before trace after) :
    StateProgress context (context.cleanup count) before after interpretation interpretation := by
  refine ⟨.cleanup _ _, .cleanup _ _, .refl _ _, ?_, ?_⟩
  · intro binder large known
    exact False.elim (Nat.not_lt_of_ge large (valid.mentionedBound (Context.cleanup_mentions known)))
  · rw [cleaned.loans_length, Context.cleanup_loans_length]

theorem StateProgress.bind {interpretation : Interpretation} {context : Context} {environment : Environment}
    (valid : context.WellFormed program) (name : String) (mutable : Bool) (result : ResultType) (value : Value) :
    StateProgress context (context.bind name mutable result) environment (environment.bind name value)
      interpretation (interpretation.addBinder context.nextBinder environment.nextRoot) := by
  refine ⟨.bind _ _ _ _, .bind _ _ _ _, ?_, ?_, rfl⟩
  · refine ⟨?_, fun _ _ => rfl, rfl⟩
    intro binder bound
    simp [Interpretation.addBinder, Nat.ne_of_lt bound]
  · intro binder large known
    rcases (Context.bind_mentions _ _ _ _ _).mp known with rfl | old
    · simp [Interpretation.addBinder]
    · exact False.elim (Nat.not_lt_of_ge large (valid.mentionedBound old))

theorem StateProgress.borrow {interpretation : Interpretation} {context : Context} {environment : Environment}
    {target : Origin} {referent : Ty} {parent : Option Nat} {mode : BorrowMode} (valid : context.WellFormed program)
    (known : target.Known context) :
    StateProgress context (context.borrow target referent parent mode) environment
      (environment.addLoan ⟨interpretation.origin target, parent.map interpretation.node⟩ mode)
      interpretation (interpretation.addNode context.loans.length environment.loans.length) := by
  refine ⟨.borrow _ _ _ _ _, .borrow known, ?_, ?_, ?_⟩
  · refine ⟨fun _ _ => rfl, ?_, rfl⟩
    intro node bound
    simp [Interpretation.addNode, Nat.ne_of_lt bound]
  · intro binder large mentioned
    exact False.elim (Nat.not_lt_of_ge large (valid.mentionedBound ((Context.borrow_mentions known binder).mp mentioned)))
  · simp [Context.borrow, Environment.addLoan]
    omega

theorem StateProgress.join {interpretation : Interpretation} {context afterContext : Context} {environment : Environment}
    (valid : context.WellFormed program) (joined : context.Joins program afterContext) :
    StateProgress context afterContext environment environment interpretation interpretation := by
  refine ⟨joined.history, .joins joined, .refl _ _, ?_, ?_⟩
  · intro binder large known
    exact False.elim (Nat.not_lt_of_ge large (valid.mentionedBound ((joined.mentions binder).mp known)))
  · rw [joined.loans]

theorem StateProgress.raiseSupply {interpretation : Interpretation} {context : Context} {environment : Environment}
    (valid : context.WellFormed program) {supply : Nat} (larger : context.nextBinder ≤ supply) :
    StateProgress context {context with nextBinder := supply} environment environment interpretation interpretation := by
  refine ⟨⟨fun _ loan found => ⟨loan, found, rfl, rfl, rfl, rfl, id⟩, rfl, larger,
      fun _ member _ => member, fun _ slot _ found _ => ⟨slot, found, rfl⟩⟩,
    fun _ mentioned _ => mentioned, .refl _ _, ?_, rfl⟩
  intro binder large known
  exact False.elim (Nat.not_lt_of_ge large (valid.mentionedBound known))

theorem replaceBinding_map {α β : Type} (f : α → β) {name : String} {value : α}
    {before after : List (String × α)} (changed : replaceBinding name value before = some after) :
    replaceBinding name (f value) (before.map fun x => (x.1, f x.2)) =
      some (after.map fun x => (x.1, f x.2)) := by
  induction before generalizing after with
  | nil => simp [replaceBinding] at changed
  | cons entry rest ih =>
    obtain ⟨key, old⟩ := entry
    simp only [replaceBinding] at changed
    split at changed
    · cases Option.some.inj changed
      simp_all [replaceBinding]
    · obtain ⟨next, changed, rfl⟩ := Option.map_eq_some_iff.mp changed
      simp_all [replaceBinding]

theorem replaceBinding_map_same {α β : Type} (f : α → β) {name : String} {old value : α}
    {before after : List (String × α)} (selected : lookup name before = some old)
    (changed : replaceBinding name value before = some after) (same : f value = f old) :
    after.map (fun x => f x.2) = before.map (fun x => f x.2) := by
  induction before generalizing after with
  | nil => simp [lookup] at selected
  | cons entry rest ih =>
    obtain ⟨key, resident⟩ := entry
    simp only [lookup] at selected
    simp only [replaceBinding] at changed
    split at selected
    · rename_i equal
      rw [if_pos equal.symm] at changed
      cases Option.some.inj selected
      cases Option.some.inj changed
      simp [same]
    · rename_i different
      rw [if_neg (Ne.symm different)] at changed
      obtain ⟨next, tailChanged, rfl⟩ := Option.map_eq_some_iff.mp changed
      simp [ih selected tailChanged]

theorem replaceBinding_members {α : Type} {name : String} {value : α}
    {before after : List (String × α)} (changed : replaceBinding name value before = some after)
    {binding : String × α} (member : binding ∈ after) : binding = (name, value) ∨ binding ∈ before := by
  induction before generalizing after with
  | nil => simp [replaceBinding] at changed
  | cons entry rest ih =>
    obtain ⟨key, old⟩ := entry
    simp only [replaceBinding] at changed
    split at changed
    · rename_i equal
      cases Option.some.inj changed
      rcases List.mem_cons.mp member with rfl | member
      · exact Or.inl (by simp [equal])
      · exact Or.inr (List.mem_cons_of_mem _ member)
    · obtain ⟨next, tailChanged, rfl⟩ := Option.map_eq_some_iff.mp changed
      rcases List.mem_cons.mp member with rfl | member
      · exact Or.inr (by simp)
      · rcases ih tailChanged member with same | old
        · exact Or.inl same
        · exact Or.inr (List.mem_cons_of_mem _ old)

 theorem StoreTyped.write_inputTargets {program : Program} {interpretation : Interpretation}
    {context : Context} {before after : Environment} (typed : StoreTyped program interpretation context before)
    {origin : Origin} {replacement : Value} (known : origin.Known context) (free : context.Free origin)
    (written : before.writeAddress (interpretation.origin origin) replacement = some after) :
    ∀ (node : Nat) (loan : SourceLoan), context.loans[node]? = some loan → loan.own = true →
      ∀ input, loan.target.base = .input input →
      ∃ value, after.readAddress (interpretation.origin loan.target) = some value ∧
        ValueHasType program value loan.referent := by
  intro node loan found own input base
  obtain ⟨value, read, resident⟩ := typed.inputTargets node loan found own input base
  have apart := typed.ownerFree known free (interpretation.node node)
    ⟨interpretation.origin loan.target, loan.parent.map interpretation.node, loan.own, loan.mode⟩
    (typed.records node loan found) own
  have frame := (Environment.writeAddress_update written).frame _ apart
  exact ⟨value, by simpa only [Environment.readAddress, frame] using read, resident⟩

private theorem findSlot {slots : List (String × Slot)}
    (distinct : (slots.map (fun binding => binding.2.binder)).Nodup)
    {binding : String × Slot} (member : binding ∈ slots) :
    slots.find? (fun entry => entry.2.binder == binding.2.binder) = some binding := by
  induction slots with
  | nil => cases member
  | cons first rest ih =>
      obtain ⟨absent, tailDistinct⟩ := List.nodup_cons.mp distinct
      rcases List.mem_cons.mp member with rfl | member
      · simp
      · have different : first.2.binder ≠ binding.2.binder := by
          intro same
          exact absent (List.mem_map.mpr ⟨binding, member, same.symm⟩)
        simpa [List.find?_cons, different] using ih tailDistinct member

theorem Context.withSlots_bindings (context : Context) {slots : List (String × Slot)}
    (distinct : (slots.map (fun binding => binding.2.binder)).Nodup) :
    (context.withSlots slots).bindings = slots := by
  simp only [Context.bindings, Context.withSlots, List.filterMap_map]
  have equal := Context.filterMap_congr_mem slots
    (fun binding => ((context.withSlots slots).storage (.binder binding.2.binder)).map fun slot => (binding.1, slot))
    some (by
      intro binding member
      simp only [Context.withSlots, findSlot distinct member, Option.map_some])
  simpa only [Context.withSlots, List.filterMap_some_fun, Function.comp_def, id_eq] using equal

theorem Context.withSlots_storage_cases {context : Context} {slots : List (String × Slot)}
    {binder : Nat} {slot : Slot} (stored : (context.withSlots slots).storage (.binder binder) = some slot) :
    (∃ binding ∈ slots, binding.2 = slot ∧ binding.2.binder = binder) ∨
      context.storage (.binder binder) = some slot := by
  cases chosen : slots.find? (fun binding => binding.2.binder == binder) with
  | none => exact .inr (by simpa only [Context.withSlots, chosen] using stored)
  | some binding =>
      have same : binding.2 = slot := by simpa only [Context.withSlots, chosen, Option.some.injEq] using stored
      exact .inl ⟨binding, List.mem_of_find?_eq_some chosen, same, by simpa using List.find?_some chosen⟩

theorem Context.WellFormed.replaceSlot_storage {context : Context} (valid : context.WellFormed program)
    {name : String} {slot replacement : Slot} {slots : List (String × Slot)}
    (selected : lookup name context.bindings = some slot)
    (changed : replaceBinding name replacement context.bindings = some slots)
    (sameBinder : replacement.binder = slot.binder) (binder : Nat) :
    (context.withSlots slots).storage (.binder binder) =
      if binder = slot.binder then some replacement else context.storage (.binder binder) := by
  have distinct : (slots.map (fun binding => binding.2.binder)).Nodup := by
    rw [replaceBinding_map_same Slot.binder selected changed sameBinder]
    exact valid.distinct
  by_cases same : binder = slot.binder
  · subst binder
    have found := findSlot distinct (lookup_member (replaceBinding_lookup changed))
    have target : slots.find? (fun entry => entry.2.binder == slot.binder) = some (name, replacement) := by
      simpa only [sameBinder] using found
    simp [Context.withSlots, target]
  · rw [if_neg same]
    cases chosen : slots.find? (fun binding => binding.2.binder == binder) with
    | none => simp only [Context.withSlots, chosen]
    | some binding =>
      have identity : binding.2.binder = binder := by simpa using List.find?_some chosen
      rcases replaceBinding_members changed (List.mem_of_find?_eq_some chosen) with rfl | retained
      · exact False.elim (same (sameBinder.symm.trans identity).symm)
      · have stored := valid.member_stored binding retained
        simpa only [Context.withSlots, chosen, identity] using stored.symm

theorem Context.WellFormed.replaceSlot {program : Program} {context : Context}
    (valid : context.WellFormed program) {name : String} {slot replacement : Slot}
    {slots : List (String × Slot)} (selected : lookup name context.bindings = some slot)
    (changed : replaceBinding name replacement context.bindings = some slots)
    (binder : replacement.binder = slot.binder) (type : replacement.type = slot.type)
    (reference : ∀ node, replacement.reference = some node → ∃ loan,
      context.loans[node]? = some loan ∧ replacement.type = .reference loan.referent loan.mode) :
    ((context.withSlots slots) : Context).WellFormed program := by
  have member := lookup_member selected
  have distinct : (slots.map (fun binding => binding.2.binder)).Nodup := by
    rw [replaceBinding_map_same Slot.binder selected changed binder]
    exact valid.distinct
  have view := context.withSlots_bindings distinct
  have properties : ∀ binding ∈ slots, StorageType program.target program.data binding.2.type ∧
      binding.2.binder < context.nextBinder ∧
      ∀ node, binding.2.reference = some node → ∃ loan, context.loans[node]? = some loan ∧
        binding.2.type = .reference loan.referent loan.mode := by
    intro binding memberNew
    rcases replaceBinding_members changed memberNew with rfl | retained
    · exact ⟨type.symm ▸ valid.supported (name, slot) member,
        binder.symm ▸ (valid.slots (name, slot) member).1, reference⟩
    · exact ⟨valid.supported binding retained, valid.slots binding retained⟩
  refine ⟨by simpa only [view] using distinct, ?_, ?_, valid.targets, valid.parents, ?_, ?_, valid.parentModes⟩
  · intro binding memberNew
    exact (properties binding (view ▸ memberNew)).1
  · intro binding memberNew
    exact (properties binding (view ▸ memberNew)).2
  · intro entry memberNew
    obtain ⟨binding, memberIn, rfl⟩ := List.mem_map.mp memberNew
    exact ⟨binding.2, by simp only [Context.withSlots, findSlot distinct memberIn]⟩
  · intro identity current stored
    rcases Context.withSlots_storage_cases stored with ⟨binding, memberNew, rfl, equal⟩ | old
    · obtain ⟨supported, bound, reference⟩ := properties binding memberNew
      exact ⟨equal, equal ▸ bound, supported, reference⟩
    · exact valid.allocated identity current old

theorem Context.replaceSlot_mentions {context : Context} (valid : context.WellFormed program)
    {name : String} {slot replacement : Slot} {slots : List (String × Slot)}
    (selected : lookup name context.bindings = some slot)
    (changed : replaceBinding name replacement context.bindings = some slots)
    (binder : replacement.binder = slot.binder) {id : Nat}
    (mentioned : (context.withSlots slots).MentionsBinder id) : context.MentionsBinder id := by
  rcases mentioned with ⟨current, stored⟩ | loan
  · rcases Context.withSlots_storage_cases stored with ⟨binding, member, _, same⟩ | old
    · rcases replaceBinding_members changed member with rfl | retained
      · exact (binder.symm.trans same) ▸ valid.member_known (name, slot) (lookup_member selected)
      · exact same ▸ valid.member_known binding retained
    · exact .inl ⟨current, old⟩
  · exact .inr loan

theorem SlotsCorrespond.store_frame {interpretation : Interpretation} {before after : Store}
    {bindings : List (String × Root)} {slots : List (String × Slot)}
    (typed : SlotsCorrespond interpretation before bindings slots)
    (same : ∀ root ∈ bindings.map Prod.snd, after root = before root) :
    SlotsCorrespond interpretation after bindings slots := by
  induction typed with
  | nil => exact .nil
  | @cons name root slot bindings slots identity resident rest ih =>
    exact .cons identity (fun value stored => resident value (by rw [← same root (by simp)]; exact stored))
      (ih (fun root member => same root (by simp [member])))

theorem SlotsCorrespond.replace_put {interpretation : Interpretation} {store : Store}
    {bindings : List (String × Root)} {slots next : List (String × Slot)}
    (typed : SlotsCorrespond interpretation store bindings slots)
    (distinct : (bindings.map Prod.snd).Nodup) {name : String} {old replacement : Slot} {value : Value}
    (selected : Grounded.lookup name slots = some old)
    (changed : replaceBinding name replacement slots = some next)
    (binder : replacement.binder = old.binder) (shape : replacement.Corresponds interpretation value) :
    SlotsCorrespond interpretation
      (fun root => if root = interpretation.binder old.binder then some value else store root) bindings next := by
  induction typed generalizing next with
  | nil => simp [Grounded.lookup] at selected
  | @cons key root slot bindings slots identity resident rest ih =>
    have distincts := List.nodup_cons.mp distinct
    simp only [Grounded.lookup] at selected
    simp only [replaceBinding] at changed
    split at selected
    · rename_i same
      rw [if_pos same.symm] at changed
      cases Option.some.inj selected
      cases Option.some.inj changed
      refine .cons (identity.trans (congrArg interpretation.binder binder).symm) ?_ ?_
      · intro actual stored
        simp only [identity] at stored
        cases stored
        exact shape
      · apply rest.store_frame
        intro other member
        have different : other ≠ interpretation.binder old.binder := by
          intro equal
          apply distincts.1
          simpa [identity, equal] using member
        simp [different]
    · rename_i different
      rw [if_neg (Ne.symm different)] at changed
      obtain ⟨tail, tailChanged, rfl⟩ := Option.map_eq_some_iff.mp changed
      have named := (rest.lookup selected).1
      have member := lookup_member named
      have rootDifferent : root ≠ interpretation.binder old.binder := by
        intro equal
        apply distincts.1
        rw [equal]
        exact List.mem_map.mpr ⟨(name, interpretation.binder old.binder), member, rfl⟩
      exact .cons identity (fun actual stored => resident actual (by simpa [rootDifferent] using stored))
        (ih distincts.2 selected tailChanged)

theorem Context.Restored.writeSlot {context : Context} {node : Nat}
    (ready : context.Restored node) (valid : context.WellFormed program)
    {name : String} {slot nextSlot : Slot} {slots : List (String × Slot)}
    {indices : List Nat} {state next : Initialization}
    (selected : lookup name context.bindings = some slot)
    (changed : replaceBinding name nextSlot context.bindings = some slots)
    (sameBinder : nextSlot.binder = slot.binder)
    (initialization : nextSlot.initialization = slot.initialization.write indices next)
    (access : slot.initialization.Access indices state)
    (free : context.Free ⟨.binder slot.binder, indices⟩) : (context.withSlots slots).Restored node := by
  intro loan found own
  have previous := ready loan found own
  cases base : loan.target.base with
  | input input => simp [Context.Ready, base]
  | binder binder =>
    by_cases same : binder = slot.binder
    · subst binder
      have apart : CoordinatesApart indices loan.target.fields := by
        simpa [Origin.Apart, base] using free node loan found own
      simp only [Context.Ready, base] at previous ⊢
      obtain ⟨oldSlot, mask, stored, available, complete⟩ := previous
      have equal := Option.some.inj (stored.symm.trans (valid.member_stored (name, slot) (lookup_member selected)))
      subst oldSlot
      refine ⟨nextSlot, mask, ?_, initialization.symm ▸ access.write_frame available apart next, complete⟩
      rw [valid.replaceSlot_storage selected changed sameBinder]; simp
    · apply previous.storage_congr
      rw [base, valid.replaceSlot_storage selected changed sameBinder, if_neg same]

theorem Context.Restored.dispose {context : Context} {node : Nat} (ready : context.Restored node)
    (reference : Option Nat) : (context.dispose reference).Restored node := by
  cases reference with
  | none => exact ready
  | some ended => exact ready.endOwn ended

theorem StoreTyped.writeSlot {program : Program} {home : Module} {interpretation : Interpretation}
    {context : Context} {environment : Environment} (typed : StoreTyped program interpretation context environment)
    {place : Place} {slot nextSlot : Slot} {slots : List (String × Slot)} {target : Ty}
    {indices : List Nat} {state next : Initialization} {replacement : Value}
    (selected : lookup place.root context.bindings = some slot)
    (access : slot.initialization.Access indices state)
    (path : PathType program home slot.type place.fields indices target)
    (changed : replaceBinding place.root nextSlot context.bindings = some slots)
    (sameBinder : nextSlot.binder = slot.binder) (sameType : nextSlot.type = slot.type)
    (initialization : nextSlot.initialization = slot.initialization.write indices next)
    (reference : ∀ node, nextSlot.reference = some node → ∃ loan,
      context.loans[node]? = some loan ∧ nextSlot.type = .reference loan.referent loan.mode)
    (resident : ResidentTyped program next replacement target)
    (mode : (slot.type.DataShape ∧ nextSlot.reference = none) ∨
      (indices = [] ∧ nextSlot.Corresponds interpretation replacement))
    (free : context.Free ⟨.binder slot.binder, indices⟩) :
    ∃ after, environment.resolvePlace program place = some ⟨interpretation.binder slot.binder, indices⟩ ∧
      environment.writeAddress ⟨interpretation.binder slot.binder, indices⟩ replacement = some after ∧
      StoreTyped program interpretation (context.withSlots slots) after := by
  have named := (typed.slots.lookup selected).1
  have rootStored := typed.source.member_stored (place.root, slot) (lookup_member selected)
  obtain ⟨parent, updated, stored, written, updatedTyped, write⟩ :=
    typed.writeCanonical rootStored path.canonical access resident
  obtain ⟨old, resolved, raw, oldTyped⟩ := typed.resolvePlace selected access path
  have correspondence : nextSlot.Corresponds interpretation updated := by
    rcases mode with ⟨data, noReference⟩ | ⟨direct, shape⟩
    · simpa [Slot.Corresponds, noReference] using updatedTyped.referenceFree data
    · subst indices
      have same : updated = replacement := (Option.some.inj written).symm
      simpa [same] using shape
  have nextTyped : SlotTyped program updated nextSlot.toBindingType := by
    simpa only [SlotTyped, sameType, initialization] using updatedTyped
  have bound : ∀ binder, ((context.withSlots slots) : Context).MentionsBinder binder → context.MentionsBinder binder :=
    fun _ => Context.replaceSlot_mentions typed.source selected changed sameBinder
  have known : (⟨.binder slot.binder, indices⟩ : Origin).Known context :=
    typed.source.member_known (place.root, slot) (lookup_member selected)
  have distinct : (slots.map (fun binding => binding.2.binder)).Nodup := by
    rw [replaceBinding_map_same Slot.binder selected changed sameBinder]
    exact typed.source.distinct
  have view := context.withSlots_bindings distinct
  refine ⟨_, resolved, write, ?_⟩
  refine { source := typed.source.replaceSlot selected changed sameBinder sameType reference
           residents := by
             simpa only [Context.erase, view] using
               typed.residents.put named (replaceBinding_map Slot.toBindingType changed) nextTyped
           slots := by
             rw [view]
             exact typed.slots.replace_put typed.residents.valid.distinct selected changed sameBinder correspondence
           cells := by
             intro binder actual storedCell
             rw [typed.source.replaceSlot_storage selected changed sameBinder binder] at storedCell
             by_cases same : binder = slot.binder
             · subst binder
               rw [if_pos rfl] at storedCell
               cases storedCell
               exact ⟨updated, by simp [Environment.put], nextTyped, correspondence⟩
             · rw [if_neg same] at storedCell
               obtain ⟨value, found, resident, shape⟩ := typed.cells binder actual storedCell
               have different : interpretation.binder binder ≠ interpretation.binder slot.binder :=
                 fun equal => same (typed.binderDistinct binder slot.binder (.inl ⟨actual, storedCell⟩) known equal)
               exact ⟨value, by simpa [Environment.put, different] using found, resident, shape⟩
           binderBound := fun binder mention => typed.binderBound binder (bound binder mention)
           binderDistinct := fun first second a b => typed.binderDistinct first second (bound first a) (bound second b)
           inputBound := typed.inputBound
           inputApart := fun binder input mention => typed.inputApart binder input (bound binder mention)
           nodeOrder := typed.nodeOrder
           records := typed.records
           activeCoverage := typed.activeCoverage
           sourceTargets := by
             intro node loan found own
             have old := typed.sourceTargets node loan found own
             cases base : loan.target.base with
             | input input => simpa [Context.SourceTarget, Context.Target, Context.Ready, base] using old
             | binder binder =>
               by_cases same : binder = slot.binder
               · subst binder
                 have apart : CoordinatesApart indices loan.target.fields := by
                   have apart := free node loan found own
                   simpa [Origin.Apart, base] using apart
                 obtain ⟨target, ready, inputShared⟩ := old
                 simp only [Context.Target, base] at target
                 obtain ⟨targetSlot, targetStored, targetPath, targetState, targetAccess⟩ := target
                 have rootStored := typed.source.member_stored (place.root, slot) (lookup_member selected)
                 have equal := Option.some.inj (targetStored.symm.trans rootStored)
                 subst targetSlot
                 have newStored : (context.withSlots slots).storage (.binder slot.binder) = some nextSlot := by
                   rw [typed.source.replaceSlot_storage selected changed sameBinder]; simp
                 refine ⟨?_, ?_, inputShared⟩
                 · simp only [Context.Target, base]
                   exact ⟨nextSlot, newStored, sameType ▸ targetPath, targetState,
                     initialization.symm ▸ access.write_frame targetAccess apart next⟩
                 · intro shared
                   have sourceReady := ready shared
                   simp only [Context.Ready, base] at sourceReady ⊢
                   obtain ⟨readySlot, readyState, readyStored, readyAccess, complete⟩ := sourceReady
                   have equal := Option.some.inj (readyStored.symm.trans rootStored)
                   subst readySlot
                   exact ⟨nextSlot, readyState, newStored,
                     initialization.symm ▸ access.write_frame readyAccess apart next, complete⟩
               · apply old.storage_congr
                 rw [base, typed.source.replaceSlot_storage selected changed sameBinder, if_neg same]
           inputTargets := typed.write_inputTargets known free write
           storeShape := ?_ }
  intro root value found
  by_cases same : root = interpretation.binder slot.binder
  · simp only [Environment.put, same] at found
    cases found
    cases referenceCase : nextSlot.reference with
    | none => exact Or.inl (by simpa [Slot.Corresponds, referenceCase] using correspondence)
    | some node =>
      have shape : updated = .reference (interpretation.node node) := by
        simpa [Slot.Corresponds, referenceCase] using correspondence
      obtain ⟨loan, loanFound, _⟩ := reference node referenceCase
      exact Or.inr ⟨interpretation.node node, shape,
        (List.getElem?_eq_some_iff.mp (typed.records node loan loanFound)).1⟩
  · exact typed.storeShape root value (by simpa [Environment.put, same] using found)

theorem StoreTyped.writeData {program : Program} {home : Module} {interpretation : Interpretation}
    {context : Context} {environment : Environment} (typed : StoreTyped program interpretation context environment)
    {place : Place} {slot : Slot} {slots : List (String × Slot)} {target : Ty}
    {indices : List Nat} {state next : Initialization} {replacement : Value}
    (selected : lookup place.root context.bindings = some slot)
    (access : slot.initialization.Access indices state)
    (path : PathType program home slot.type place.fields indices target)
    (data : slot.reference = none) (shape : target.DataShape)
    (changed : replaceBinding place.root { slot with initialization := slot.initialization.write indices next }
      context.bindings = some slots)
    (resident : ResidentTyped program next replacement target)
    (free : context.Free ⟨.binder slot.binder, indices⟩) :
    ∃ after, environment.resolvePlace program place = some ⟨interpretation.binder slot.binder, indices⟩ ∧
      environment.writeAddress ⟨interpretation.binder slot.binder, indices⟩ replacement = some after ∧
      StoreTyped program interpretation (context.withSlots slots) after := by
  have sourceShape := path.canonical.dataShape
    (typed.source.supported (place.root, slot) (lookup_member selected)) shape
  exact typed.writeSlot selected access path changed rfl rfl rfl
    (by intro node impossible; simp [data] at impossible) resident (Or.inl ⟨sourceShape, data⟩) free

theorem StoreTyped.takeData {program : Program} {home : Module} {interpretation : Interpretation}
    {context : Context} {environment : Environment} (typed : StoreTyped program interpretation context environment)
    {place : Place} {slot : Slot} {slots : List (String × Slot)} {target : Ty}
    {indices : List Nat} {state : Initialization}
    (selected : lookup place.root context.bindings = some slot)
    (access : slot.initialization.Access indices state) (initialized : state.Complete)
    (path : PathType program home slot.type place.fields indices target)
    (data : slot.reference = none) (shape : target.DataShape)
    (changed : replaceBinding place.root { slot with initialization := slot.initialization.write indices .vacant }
      context.bindings = some slots)
    (free : context.Free ⟨.binder slot.binder, indices⟩) :
    ∃ value after, environment.resolvePlace program place = some ⟨interpretation.binder slot.binder, indices⟩ ∧
      environment.takeAddress ⟨interpretation.binder slot.binder, indices⟩ = some (value, after) ∧
      StoreTyped program interpretation (context.withSlots slots) after ∧
      ResultTyped program interpretation (context.withSlots slots) value (.data target) := by
  obtain ⟨value, resolved, raw, resident⟩ := typed.resolvePlace selected access path
  obtain ⟨after, _, written, afterTyped⟩ := typed.writeData selected access path data shape changed .vacant free
  have complete := resident.complete initialized
  refine ⟨value, after, resolved, Environment.takeAddress_eq_some.mpr ⟨?_, written⟩, afterTyped, ?_⟩
  · simp [Environment.readAddress, raw, complete.2]
  · exact ⟨complete.1, shape, resident.referenceFree shape⟩

theorem StoreTyped.writeWhole {program : Program} {home : Module} {interpretation : Interpretation}
    {context : Context} {environment : Environment} (typed : StoreTyped program interpretation context environment)
    {place : Place} {slot : Slot} {slots : List (String × Slot)} {next : Initialization}
    {reference : Option Nat} {replacement : Value}
    (selected : lookup place.root context.bindings = some slot) (direct : place.fields = [])
    (changed : replaceBinding place.root { slot with initialization := next, reference := reference }
      context.bindings = some slots)
    (resident : ResidentTyped program next replacement slot.type)
    (correspondence : ({ slot with initialization := next, reference := reference } : Slot).Corresponds interpretation replacement)
    (sourceReference : ∀ node, reference = some node → ∃ loan,
      context.loans[node]? = some loan ∧ slot.type = .reference loan.referent loan.mode)
    (free : context.Free ⟨.binder slot.binder, []⟩) :
    ∃ after, environment.resolvePlace program place = some ⟨interpretation.binder slot.binder, []⟩ ∧
      environment.writeAddress ⟨interpretation.binder slot.binder, []⟩ replacement = some after ∧
      StoreTyped program interpretation (context.withSlots slots) after := by
  have path : PathType program home slot.type place.fields [] slot.type := by rw [direct]; exact .nil _
  exact typed.writeSlot selected (.here _) path changed rfl rfl rfl sourceReference resident
    (Or.inr ⟨rfl, correspondence⟩) free

theorem StoreTyped.takeReference {program : Program} {home : Module} {interpretation : Interpretation}
    {context : Context} {environment : Environment} (typed : StoreTyped program interpretation context environment)
    {place : Place} {slot : Slot} {slots : List (String × Slot)} {node : Nat} {referent : Ty} {mode : BorrowMode}
    (selected : lookup place.root context.bindings = some slot) (direct : place.fields = [])
    (handle : slot.reference = some node) (shape : slot.type = .reference referent mode)
    (initialized : slot.initialization.Complete)
    (changed : replaceBinding place.root { slot with initialization := .vacant, reference := none }
      context.bindings = some slots)
    (free : context.Free ⟨.binder slot.binder, []⟩) :
    ∃ after, environment.resolvePlace program place = some ⟨interpretation.binder slot.binder, []⟩ ∧
      environment.takeAddress ⟨interpretation.binder slot.binder, []⟩ = some (.reference (interpretation.node node), after) ∧
      StoreTyped program interpretation (context.withSlots slots) after ∧
      ResultTyped program interpretation (context.withSlots slots) (.reference (interpretation.node node))
        ⟨.reference referent mode, some node⟩ := by
  have path : PathType program home slot.type place.fields [] slot.type := by rw [direct]; exact .nil _
  obtain ⟨value, resolved, raw, resident⟩ := typed.resolvePlace selected (.here _) path
  have stored : environment.store (interpretation.binder slot.binder) = some value := by
    simpa [Environment.at, Value.readIndices] using raw
  have correspondence := (typed.slots.lookup selected).2 value stored
  have same : value = .reference (interpretation.node node) := by
    simpa [Slot.Corresponds, handle] using correspondence
  subst value
  obtain ⟨after, _, written, afterTyped⟩ := typed.writeWhole (home := home) selected direct changed .vacant
    (show Value.ReferenceFree .vacant from trivial) (by intro n impossible; cases impossible) free
  have complete := resident.complete initialized
  refine ⟨after, resolved, Environment.takeAddress_eq_some.mpr ⟨?_, written⟩, afterTyped, ?_⟩
  · simp [Environment.readAddress, raw, Value.initialized]
  · refine ⟨by simpa [shape] using complete.1, rfl, ?_⟩
    obtain ⟨loan, found, type⟩ := (typed.source.slots (place.root, slot) (lookup_member selected)).2 node handle
    exact ⟨loan, found, shape.symm.trans type⟩

theorem StoreTyped.writeReference {program : Program} {home : Module} {interpretation : Interpretation}
    {context : Context} {environment : Environment} (typed : StoreTyped program interpretation context environment)
    {place : Place} {slot : Slot} {slots : List (String × Slot)} {node : Nat} {referent : Ty} {mode : BorrowMode} {value : Value}
    (selected : lookup place.root context.bindings = some slot) (direct : place.fields = [])
    (shape : slot.type = .reference referent mode)
    (changed : replaceBinding place.root { slot with initialization := .full, reference := some node }
      context.bindings = some slots)
    (result : ResultTyped program interpretation context value ⟨.reference referent mode, some node⟩)
    (free : context.Free ⟨.binder slot.binder, []⟩) :
    ∃ after, environment.resolvePlace program place = some ⟨interpretation.binder slot.binder, []⟩ ∧
      environment.writeAddress ⟨interpretation.binder slot.binder, []⟩ value = some after ∧
      StoreTyped program interpretation (context.withSlots slots) after := by
  have resultShape := result.shape
  obtain ⟨same, loan, found, loanType⟩ := resultShape
  exact typed.writeWhole (home := home) selected direct changed (by simpa [shape] using result.resident) same
    (by intro other equal; cases Option.some.inj equal; exact ⟨loan, found, shape.trans loanType⟩) free

theorem ResidentTyped.reference_shape {program : Program} {state : Initialization} {value : Value} {type : Ty}
    (typed : ResidentTyped program state value type) {referent : Ty} {mode : BorrowMode} (shape : type = .reference referent mode) :
    value = .vacant ∨ ∃ node, value = .reference node := by
  induction typed using ResidentTyped.rec
    (motive_2 := fun _ _ _ _ => True) with
  | vacant => exact Or.inl rfl
  | uncertain actual permission ih => exact ih shape
  | reference node finite => exact Or.inr ⟨node, rfl⟩
  | unit | integer | character | tuple | array | nominal => cases shape
  | nil | cons => trivial

theorem StoreTyped.disposeReferenceSlot {program : Program} {home : Module} {interpretation : Interpretation}
    {context : Context} {environment : Environment} (typed : StoreTyped program interpretation context environment)
    {place : Place} {slot : Slot} {referent : Ty} {mode : BorrowMode}
    (selected : lookup place.root context.bindings = some slot) (direct : place.fields = [])
    (shape : slot.type = .reference referent mode)
    (ready : ∀ node, slot.reference = some node → context.Restored node) :
    ∃ old disposed, environment.resolvePlace program place = some ⟨interpretation.binder slot.binder, []⟩ ∧
      environment.at ⟨interpretation.binder slot.binder, []⟩ = some old ∧
      Environment.Disposes program environment old disposed ∧
      StoreTyped program interpretation (context.dispose slot.reference) disposed := by
  have path : PathType program home slot.type place.fields [] slot.type := by rw [direct]; exact .nil _
  obtain ⟨old, resolved, raw, resident⟩ := typed.resolvePlace selected (.here _) path
  have stored : environment.store (interpretation.binder slot.binder) = some old := by
    simpa [Environment.at, Value.readIndices] using raw
  have correspondence := (typed.slots.lookup selected).2 old stored
  cases handle : slot.reference with
  | none =>
    have plain : old.ReferenceFree := by simpa [Slot.Corresponds, handle] using correspondence
    have vacancy : old = .vacant := by
      rcases resident.reference_shape shape with vacant | ⟨node, rfl⟩
      · exact vacant
      · exact False.elim plain
    subst old
    exact ⟨_, environment, resolved, raw, .data trivial .vacant, by simpa [Context.dispose, handle] using typed⟩
  | some node =>
    have same : old = .reference (interpretation.node node) := by simpa [Slot.Corresponds, handle] using correspondence
    obtain ⟨loan, found, _⟩ := (typed.source.slots (place.root, slot) (lookup_member selected)).2 node handle
    obtain ⟨disposed, ended, afterTyped⟩ := typed.endOwn found
    exact ⟨old, disposed, resolved, raw, by rw [same]; exact .reference (typed.restored found (ready node handle)) ended,
      by simpa [Context.dispose, handle] using afterTyped⟩

theorem Context.Free.dispose {context : Context} {origin : Origin} (free : context.Free origin)
    (reference : Option Nat) : (context.dispose reference).Free origin := by
  cases reference with
  | none => exact free
  | some ended =>
    intro node loan found own
    obtain ⟨original, originalFound, rfl⟩ := Context.endOwn_original found
    have different : ended ≠ node := by intro equal; simp [equal] at own
    exact free node original originalFound (by simpa [different] using own)

theorem ResultTyped.dispose {program : Program} {interpretation : Interpretation} {context : Context}
    {value : Value} {result : ResultType} (typed : ResultTyped program interpretation context value result)
    (reference : Option Nat) : ResultTyped program interpretation (context.dispose reference) value result := by
  refine ⟨typed.resident, ?_⟩
  cases handle : result.reference with
  | none => simpa [handle] using typed.shape
  | some node =>
    obtain ⟨same, loan, found, type⟩ := (show value = .reference (interpretation.node node) ∧
      ∃ loan, context.loans[node]? = some loan ∧ result.type = .reference loan.referent loan.mode from by
        simpa [handle] using typed.shape)
    cases reference with
    | none => exact ⟨same, loan, found, type⟩
    | some ended => exact ⟨same, _, context.endOwn_found ended found, type⟩

theorem StoreTyped.assignReference {program : Program} {home : Module} {interpretation : Interpretation}
    {context : Context} {environment : Environment} (typed : StoreTyped program interpretation context environment)
    {place : Place} {slot : Slot} {slots : List (String × Slot)} {node : Nat} {referent : Ty} {mode : BorrowMode} {value : Value}
    (selected : lookup place.root context.bindings = some slot) (direct : place.fields = [])
    (shape : slot.type = .reference referent mode)
    (changed : replaceBinding place.root { slot with initialization := .full, reference := some node }
      context.bindings = some slots)
    (result : ResultTyped program interpretation context value ⟨.reference referent mode, some node⟩)
    (free : context.Free ⟨.binder slot.binder, []⟩)
    (ready : ∀ old, slot.reference = some old → context.Restored old) :
    ∃ old disposed after, environment.resolvePlace program place = some ⟨interpretation.binder slot.binder, []⟩ ∧
      environment.at ⟨interpretation.binder slot.binder, []⟩ = some old ∧
      Environment.Disposes program environment old disposed ∧
      disposed.writeAddress ⟨interpretation.binder slot.binder, []⟩ value = some after ∧
      StoreTyped program interpretation ((context.dispose slot.reference).withSlots slots) after := by
  obtain ⟨old, disposed, resolved, raw, disposal, disposedTyped⟩ := typed.disposeReferenceSlot (home := home) selected direct shape ready
  have bindings : (context.dispose slot.reference).bindings = context.bindings := by
    cases slot.reference <;> rfl
  obtain ⟨after, _, written, afterTyped⟩ := disposedTyped.writeReference (home := home)
    (by simpa [bindings] using selected) direct shape (by simpa [bindings] using changed)
    (result.dispose slot.reference) (free.dispose slot.reference)
  exact ⟨old, disposed, after, resolved, raw, disposal, written, afterTyped⟩

theorem StoreTyped.assignReference_custody {program : Program} {home : Module} {interpretation : Interpretation}
    {context : Context} {environment : Environment} (typed : StoreTyped program interpretation context environment)
    {place : Place} {slot : Slot} {slots : List (String × Slot)} {node : Nat} {referent : Ty} {mode : BorrowMode} {value : Value}
    {held : List Value} (custody : Custody environment (held ++ [value]))
    (selected : lookup place.root context.bindings = some slot) (direct : place.fields = [])
    (shape : slot.type = .reference referent mode)
    (changed : replaceBinding place.root { slot with initialization := .full, reference := some node }
      context.bindings = some slots)
    (result : ResultTyped program interpretation context value ⟨.reference referent mode, some node⟩)
    (free : context.Free ⟨.binder slot.binder, []⟩)
    (ready : ∀ old, slot.reference = some old → context.Restored old) :
    ∃ old disposed after, environment.resolvePlace program place = some ⟨interpretation.binder slot.binder, []⟩ ∧
      environment.at ⟨interpretation.binder slot.binder, []⟩ = some old ∧
      Environment.Disposes program environment old disposed ∧
      disposed.writeAddress ⟨interpretation.binder slot.binder, []⟩ value = some after ∧
      StoreTyped program interpretation ((context.dispose slot.reference).withSlots slots) after ∧
      Custody after held := by
  obtain ⟨old, disposed, after, resolved, raw, disposal, written, afterTyped⟩ :=
    typed.assignReference (home := home) selected direct shape changed result free ready
  have stored : environment.store (interpretation.binder slot.binder) = some old := by
    simpa [Environment.at, Value.readIndices] using raw
  have same : value = .reference (interpretation.node node) := result.shape.1
  subst value
  obtain ⟨canonical, transferred⟩ := custody.assignReferenceAddress stored disposal
  have equal := Option.some.inj (written.symm.trans canonical)
  exact ⟨old, disposed, after, resolved, raw, disposal, written, afterTyped, equal ▸ transferred⟩

theorem StoreTyped.takeReference_custody {program : Program} {home : Module} {interpretation : Interpretation}
    {context : Context} {environment : Environment} (typed : StoreTyped program interpretation context environment)
    {place : Place} {slot : Slot} {slots : List (String × Slot)} {node : Nat} {referent : Ty} {mode : BorrowMode}
    {held : List Value} (custody : Custody environment held)
    (selected : lookup place.root context.bindings = some slot) (direct : place.fields = [])
    (handle : slot.reference = some node) (shape : slot.type = .reference referent mode)
    (initialized : slot.initialization.Complete)
    (changed : replaceBinding place.root { slot with initialization := .vacant, reference := none }
      context.bindings = some slots)
    (free : context.Free ⟨.binder slot.binder, []⟩) :
    ∃ after, environment.resolvePlace program place = some ⟨interpretation.binder slot.binder, []⟩ ∧
      environment.takeAddress ⟨interpretation.binder slot.binder, []⟩ = some (.reference (interpretation.node node), after) ∧
      StoreTyped program interpretation (context.withSlots slots) after ∧
      ResultTyped program interpretation (context.withSlots slots) (.reference (interpretation.node node))
        ⟨.reference referent mode, some node⟩ ∧ Custody after (held ++ [.reference (interpretation.node node)]) := by
  obtain ⟨after, resolved, taken, afterTyped, result⟩ :=
    typed.takeReference (home := home) selected direct handle shape initialized changed free
  exact ⟨after, resolved, taken, afterTyped, result, custody.takeReference taken⟩

theorem StoreTyped.writeData_custody {program : Program} {home : Module} {interpretation : Interpretation}
    {context : Context} {environment : Environment} (typed : StoreTyped program interpretation context environment)
    {place : Place} {slot : Slot} {slots : List (String × Slot)} {target : Ty}
    {indices : List Nat} {state next : Initialization} {replacement : Value}
    {held : List Value} (custody : Custody environment held)
    (selected : lookup place.root context.bindings = some slot)
    (access : slot.initialization.Access indices state)
    (path : PathType program home slot.type place.fields indices target)
    (data : slot.reference = none) (shape : target.DataShape)
    (changed : replaceBinding place.root { slot with initialization := slot.initialization.write indices next }
      context.bindings = some slots)
    (resident : ResidentTyped program next replacement target)
    (free : context.Free ⟨.binder slot.binder, indices⟩) :
    ∃ after, environment.resolvePlace program place = some ⟨interpretation.binder slot.binder, indices⟩ ∧
      environment.writeAddress ⟨interpretation.binder slot.binder, indices⟩ replacement = some after ∧
      StoreTyped program interpretation (context.withSlots slots) after ∧ Custody after held := by
  obtain ⟨after, resolved, written, afterTyped⟩ := typed.writeData selected access path data shape changed resident free
  obtain ⟨old, _, raw, oldTyped⟩ := typed.resolvePlace selected access path
  exact ⟨after, resolved, written, afterTyped,
    custody.writeAddress_selected typed.storeShape raw (oldTyped.referenceFree shape) (resident.referenceFree shape) written⟩

theorem StoreTyped.takeData_custody {program : Program} {home : Module} {interpretation : Interpretation}
    {context : Context} {environment : Environment} (typed : StoreTyped program interpretation context environment)
    {place : Place} {slot : Slot} {slots : List (String × Slot)} {target : Ty}
    {indices : List Nat} {state : Initialization} {held : List Value} (custody : Custody environment held)
    (selected : lookup place.root context.bindings = some slot)
    (access : slot.initialization.Access indices state) (initialized : state.Complete)
    (path : PathType program home slot.type place.fields indices target)
    (data : slot.reference = none) (shape : target.DataShape)
    (changed : replaceBinding place.root { slot with initialization := slot.initialization.write indices .vacant }
      context.bindings = some slots)
    (free : context.Free ⟨.binder slot.binder, indices⟩) :
    ∃ value after, environment.resolvePlace program place = some ⟨interpretation.binder slot.binder, indices⟩ ∧
      environment.takeAddress ⟨interpretation.binder slot.binder, indices⟩ = some (value, after) ∧
      StoreTyped program interpretation (context.withSlots slots) after ∧
      ResultTyped program interpretation (context.withSlots slots) value (.data target) ∧ Custody after held := by
  obtain ⟨value, after, resolved, taken, afterTyped, result⟩ := typed.takeData selected access initialized path data shape changed free
  obtain ⟨old, _, raw, oldTyped⟩ := typed.resolvePlace selected access path
  exact ⟨value, after, resolved, taken, afterTyped, result,
    custody.writeAddress_selected typed.storeShape raw (oldTyped.referenceFree shape) (show Value.ReferenceFree .vacant from trivial)
      (Environment.takeAddress_eq_some.mp taken).2⟩

theorem StoreTyped.assignData {program : Program} {home : Module} {interpretation : Interpretation}
    {context : Context} {environment : Environment} (typed : StoreTyped program interpretation context environment)
    {place : Place} {slot : Slot} {slots : List (String × Slot)} {target : Ty}
    {indices : List Nat} {state : Initialization} {value : Value} {held : List Value}
    (custody : Custody environment held)
    (selected : lookup place.root context.bindings = some slot)
    (access : slot.initialization.Access indices state)
    (path : PathType program home slot.type place.fields indices target)
    (data : slot.reference = none) (shape : target.DataShape)
    (changed : replaceBinding place.root { slot with initialization := slot.initialization.write indices .full }
      context.bindings = some slots)
    (resident : ValueHasType program value target) (discard : StorageDisposition program state target)
    (free : context.Free ⟨.binder slot.binder, indices⟩) :
    ∃ old after, environment.resolvePlace program place = some ⟨interpretation.binder slot.binder, indices⟩ ∧
      environment.at ⟨interpretation.binder slot.binder, indices⟩ = some old ∧
      Environment.Disposes program environment old environment ∧
      environment.writeAddress ⟨interpretation.binder slot.binder, indices⟩ value = some after ∧
      StoreTyped program interpretation (context.withSlots slots) after ∧ Custody after held := by
  obtain ⟨old, resolved, raw, oldTyped⟩ := typed.resolvePlace selected access path
  obtain ⟨after, _, written, afterTyped, afterCustody⟩ :=
    typed.writeData_custody custody selected access path data shape changed resident free
  exact ⟨old, after, resolved, raw, .data (oldTyped.referenceFree shape) (discard.realized oldTyped).destroys,
    written, afterTyped, afterCustody⟩


/-- The final evaluated node is distinct from the protected prefix because each
usable node has one actual carrier. This is derived, not a source restriction. -/
theorem StateTyped.finalUnprotected {interpretation : Interpretation} {context : Context} {environment : Environment}
    {heldNodes : List Nat} {held : List Value} {node : Nat}
    (typed : StateTyped program interpretation context (heldNodes ++ [node]) environment
      (held ++ [.reference (interpretation.node node)])) : node ∉ heldNodes := by
  intro member
  obtain ⟨index, bound, selected⟩ := List.mem_iff_getElem.mp member
  have shape : held = heldNodes.map (fun node => Value.reference (interpretation.node node)) := by
    apply List.append_cancel_right
    simpa only [List.map_append, List.map_cons, List.map_nil] using typed.heldShape
  have length : held.length = heldNodes.length := by rw [shape, List.length_map]
  obtain ⟨loan, found, own⟩ := typed.heldOwn node (by simp)
  obtain ⟨location, _, unique⟩ := typed.custody (interpretation.node node)
    ⟨interpretation.origin loan.target, loan.parent.map interpretation.node, loan.own, loan.mode⟩ (typed.records node loan found) own
  have earlier : Carries environment (held ++ [.reference (interpretation.node node)]) (interpretation.node node) (.held index) := by
    change (held ++ [.reference (interpretation.node node)])[index]? = _
    rw [List.getElem?_append_left (length ▸ bound), shape, List.getElem?_map, List.getElem?_eq_getElem bound, selected]
    rfl
  have final : Carries environment (held ++ [.reference (interpretation.node node)]) (interpretation.node node) (.held held.length) := by
    simp [Carries]
  have same := Carrier.held.inj ((unique _ earlier).trans (unique _ final).symm)
  omega

theorem StateTyped.disposeResult {interpretation : Interpretation} {context : Context} {environment : Environment}
    {heldNodes : List Nat} {held : List Value} {value : Value} {result : ResultType}
    (typed : StateTyped program interpretation context (heldNodes ++ result.nodes) environment (held ++ value.referenceValues))
    (valueTyped : ResultTyped program interpretation context value result) (drop : MayDiscard program.data result.type) :
    ∃ after, Environment.Disposes program environment value after ∧
      StateTyped program interpretation (context.dispose result.reference) heldNodes after held := by
  cases reference : result.reference with
  | none =>
    have shape := valueTyped.shape
    rw [reference] at shape
    exact ⟨environment, .data shape.2 (valueTyped.resident.disposable drop).destroys,
      by simpa [Context.dispose, ResultType.nodes, reference, shape.2.referenceValues] using typed⟩
  | some node =>
    have shape := valueTyped.shape
    rw [reference] at shape
    have pending : StateTyped program interpretation context (heldNodes ++ [node]) environment
        (held ++ [.reference (interpretation.node node)]) := by
      simpa [ResultType.nodes, reference, shape.1, Value.referenceValues] using typed
    obtain ⟨loan, found, _⟩ := shape.2
    have ready := pending.toStoreTyped.restored found (pending.heldReady node (by simp))
    obtain ⟨after, ended, afterTyped⟩ := pending.consume pending.finalUnprotected
    exact ⟨after, by rw [shape.1]; exact .reference ready ended,
      by simpa [Context.dispose, reference] using afterTyped⟩

def Interpretation.empty : Interpretation := ⟨id, fun root => ⟨root, []⟩, id⟩

theorem StateTyped.empty : StateTyped program .empty .empty [] .empty [] := by
  refine {
    source := ?_
    residents := EnvironmentTyped.empty
    slots := .nil
    cells := by intro binder slot stored; cases stored
    binderBound := ?_
    binderDistinct := ?_
    inputBound := ?_
    inputApart := ?_
    nodeOrder := ?_
    records := ?_
    activeCoverage := ?_
    sourceTargets := by intro node loan found; simp [Context.empty] at found
    inputTargets := ?_
    storeShape := ?_
    heldShape := rfl
    heldOwn := ?_
    heldReady := by intro node member; cases member
    custody := ?_ }
  · constructor <;> simp [Context.empty, Context.bindings]
  · intro binder mentioned
    rcases mentioned with ⟨slot, stored⟩ | ⟨node, loan, found, _⟩
    · cases stored
    · simp [Context.empty] at found
  · intro first second _ _ same; exact same
  · intro input bound; exact False.elim (Nat.not_lt_zero _ bound)
  · intro binder input _ bound; exact False.elim (Nat.not_lt_zero _ bound)
  · intro first second _ bound; exact False.elim (Nat.not_lt_zero _ bound)
  · intro node loan found; simp [Context.empty] at found
  · intro node loan found; simp [Environment.empty] at found
  · intro node loan found; simp [Context.empty] at found
  · intro root value found; cases found
  · intro node member; cases member
  · intro node loan found; simp [Environment.empty] at found

theorem Context.WellFormed.replaceSlot_history {context : Context} (valid : context.WellFormed program)
    {name : String} {slot replacement : Slot} {slots : List (String × Slot)}
    (selected : lookup name context.bindings = some slot)
    (changed : replaceBinding name replacement context.bindings = some slots)
    (sameBinder : replacement.binder = slot.binder) : context.History (context.withSlots slots) := by
  have names : (context.withSlots slots).names.map Prod.snd = context.names.map Prod.snd := by
    simp only [Context.withSlots, List.map_map, Function.comp_def]
    rw [replaceBinding_map_same Slot.binder selected changed sameBinder, valid.bindings_binders]
  refine ⟨fun _ loan found => ⟨loan, found, rfl, rfl, rfl, rfl, id⟩, rfl, Nat.le_refl _,
    fun _ member _ => names ▸ member, ?_⟩
  intro binder current _ stored hidden
  have different : binder ≠ slot.binder := by
    intro same
    apply hidden
    rw [← valid.bindings_binders]
    exact List.mem_map.mpr ⟨(name, slot), lookup_member selected, same.symm⟩
  exact ⟨current, by rw [valid.replaceSlot_storage selected changed sameBinder binder, if_neg different]; exact stored, rfl⟩

theorem StateProgress.replaceSlot {interpretation : Interpretation} {context : Context} {before after : Environment}
    (valid : context.WellFormed program) {name : String} {slot replacement : Slot} {slots : List (String × Slot)}
    (selected : lookup name context.bindings = some slot) (changed : replaceBinding name replacement context.bindings = some slots)
    (binder : replacement.binder = slot.binder) (loans : after.loans.length = before.loans.length) :
    StateProgress context (context.withSlots slots) before after interpretation interpretation := by
  refine ⟨valid.replaceSlot_history selected changed binder,
    fun _ mentioned _ => Context.replaceSlot_mentions valid selected changed binder mentioned, .refl _ _, ?_, ?_⟩
  · intro id large known
    exact False.elim (Nat.not_lt_of_ge large (valid.mentionedBound (Context.replaceSlot_mentions valid selected changed binder known)))
  · simp only [Context.withSlots, loans]

theorem Context.Own.dispose {context : Context} {node : Nat} (own : context.Own node) (reference : Option Nat)
    (unprotected : ∀ ended, reference = some ended → ended ≠ node) : (context.dispose reference).Own node := by
  cases reference with
  | none => exact own
  | some ended =>
    obtain ⟨loan, found, available⟩ := own
    exact ⟨_, context.endOwn_found ended found, by simpa [unprotected ended rfl] using available⟩

theorem Context.WellFormed.bindings_names {context : Context} (valid : context.WellFormed program) :
    context.bindings.map (fun binding => (binding.1, binding.2.binder)) = context.names := by
  simp only [Context.bindings, List.map_filterMap]
  have equal := Context.filterMap_congr_mem context.names
    (fun entry => ((context.storage (.binder entry.2)).map (fun slot => (entry.1, slot))).map
      (fun binding => (binding.1, binding.2.binder))) some (by
        intro entry member
        obtain ⟨slot, found⟩ := valid.named entry member
        simp only [found, Option.map_some, (valid.allocated entry.2 slot found).1])
  simpa only [List.filterMap_some_fun, id_eq] using equal

theorem SlotsCorrespond.bindings {interpretation : Interpretation} {store : Store}
    {bindings : List (String × Root)} {slots : List (String × Slot)}
    (typed : SlotsCorrespond interpretation store bindings slots) :
    bindings = slots.map (fun binding => (binding.1, interpretation.binder binding.2.binder)) := by
  induction typed with
  | nil => rfl
  | cons identity _ _ ih => simp only [List.map_cons, identity, ih]

theorem Context.reconstruct {context : Context} {environment : Environment} {interpretation : Interpretation}
    (valid : context.WellFormed program) (runtimeValid : environment.Valid)
    (names : environment.bindings = context.names.map (fun entry => (entry.1, interpretation.binder entry.2)))
    (cells : ∀ binder slot, context.storage (.binder binder) = some slot →
      ∃ value, environment.store (interpretation.binder binder) = some value ∧
        SlotTyped program value slot.toBindingType ∧ slot.Corresponds interpretation value) :
    EnvironmentTyped program environment context.erase ∧
      SlotsCorrespond interpretation environment.store environment.bindings context.bindings := by
  let view (entries : List (String × Nat)) := entries.filterMap fun entry =>
    (context.storage (.binder entry.2)).map fun slot => (entry.1, slot)
  have assemble : ∀ entries : List (String × Nat),
      (∀ entry ∈ entries, ∃ slot, context.storage (.binder entry.2) = some slot) →
      ∃ values, StoredBindings environment.store (entries.map fun entry => (entry.1, interpretation.binder entry.2)) values ∧
        ValuesBindingsTyped program values ((view entries).map fun binding => (binding.1, binding.2.toBindingType)) ∧
        SlotsCorrespond interpretation environment.store
          (entries.map fun entry => (entry.1, interpretation.binder entry.2)) (view entries) := by
    intro entries
    induction entries with
    | nil => intro _; exact ⟨[], .nil, .nil, .nil⟩
    | cons entry entries ih =>
      intro present
      obtain ⟨slot, found⟩ := present entry (by simp)
      obtain ⟨value, stored, resident, corresponds⟩ := cells entry.2 slot found
      obtain ⟨values, storedRest, residents, slots⟩ := ih (fun other member => present other (by simp [member]))
      have identity := (valid.allocated entry.2 slot found).1
      simp only [view, List.filterMap_cons, found, Option.map_some, List.map_cons]
      refine ⟨(entry.1, value) :: values, .cons stored storedRest, .cons resident residents, ?_⟩
      exact .cons (congrArg interpretation.binder identity.symm)
        (fun actual read => (Option.some.inj (stored.symm.trans read)) ▸ corresponds) slots
  obtain ⟨values, stored, residents, slots⟩ := assemble context.names valid.named
  refine ⟨⟨runtimeValid, values, ?_, residents⟩, ?_⟩
  · rw [names]; exact stored
  · rw [names]; exact slots

/-- Canonical mutation changes initialization only, including hidden storage. -/
theorem Context.writeTarget_stored (context : Context) (origin : Origin) (next : Initialization)
    {base : OriginBase} {slot : Slot} (stored : context.storage base = some slot) :
    ∃ current, (context.writeTarget origin next).storage base = some current ∧ current.metadata = slot.metadata := by
  by_cases same : base = origin.base
  · subst base
    exact context.writeTarget_metadata origin next stored
  · exact ⟨slot, by simp [Context.writeTarget, same, stored], rfl⟩

theorem Context.writeTarget_original {context : Context} {origin : Origin} {next : Initialization}
    {base : OriginBase} {slot : Slot} (stored : (context.writeTarget origin next).storage base = some slot) :
    ∃ original, context.storage base = some original ∧ slot.metadata = original.metadata := by
  by_cases same : base = origin.base
  · simp only [Context.writeTarget, if_pos same] at stored
    obtain ⟨original, found, equal⟩ := Option.map_eq_some_iff.mp stored
    cases equal
    exact ⟨original, found, rfl⟩
  · exact ⟨slot, by simpa [Context.writeTarget, same] using stored, rfl⟩

theorem Context.writeTarget_mentions (context : Context) (origin : Origin) (next : Initialization) (binder : Nat) :
    (context.writeTarget origin next).MentionsBinder binder ↔ context.MentionsBinder binder := by
  constructor
  · rintro (⟨slot, stored⟩ | loan)
    · obtain ⟨original, found, _⟩ := Context.writeTarget_original stored
      exact .inl ⟨original, found⟩
    · exact .inr loan
  · rintro (⟨slot, stored⟩ | loan)
    · obtain ⟨current, found, _⟩ := context.writeTarget_stored origin next stored
      exact .inl ⟨current, found⟩
    · exact .inr loan

theorem Context.WellFormed.writeTarget {context : Context} (valid : context.WellFormed program)
    (origin : Origin) (next : Initialization) : (context.writeTarget origin next).WellFormed program := by
  have allocated : ∀ binder slot, (context.writeTarget origin next).storage (.binder binder) = some slot →
      slot.binder = binder ∧ binder < context.nextBinder ∧ StorageType program.target program.data slot.type ∧
      ∀ node, slot.reference = some node → ∃ loan, context.loans[node]? = some loan ∧
        slot.type = .reference loan.referent loan.mode := by
    intro binder slot stored
    obtain ⟨original, found, metadata⟩ := Context.writeTarget_original stored
    have equal : slot.type = original.type ∧ slot.mutable = original.mutable ∧
        slot.binder = original.binder ∧ slot.reference = original.reference := by
      simpa only [Slot.metadata, Prod.mk.injEq] using metadata
    simpa only [equal.1, equal.2.2.1, equal.2.2.2] using valid.allocated binder original found
  have named : ∀ entry ∈ context.names, ∃ slot, (context.writeTarget origin next).storage (.binder entry.2) = some slot := by
    intro entry member
    obtain ⟨slot, stored⟩ := valid.named entry member
    obtain ⟨current, found, _⟩ := context.writeTarget_stored origin next stored
    exact ⟨current, found⟩
  have bindingStored : ∀ binding ∈ (context.writeTarget origin next).bindings,
      (context.writeTarget origin next).storage (.binder binding.2.binder) = some binding.2 := by
    intro binding member
    obtain ⟨entry, _, found⟩ := List.mem_filterMap.mp member
    obtain ⟨slot, stored, equal⟩ := Option.map_eq_some_iff.mp found
    cases equal
    rw [(allocated entry.2 slot stored).1]
    exact stored
  refine ⟨?_, ?_, ?_, valid.targets, valid.parents, named, allocated, valid.parentModes⟩
  · have binders : (context.writeTarget origin next).bindings.map (fun binding => binding.2.binder) =
        context.names.map Prod.snd := by
      unfold Context.bindings
      rw [List.map_filterMap, ← List.filterMap_eq_map]
      apply Context.filterMap_congr_mem
      intro entry member
      obtain ⟨slot, stored⟩ := named entry member
      simp [stored, (allocated entry.2 slot stored).1]
    rw [binders, ← valid.bindings_binders]
    exact valid.distinct
  · intro binding member
    exact (allocated _ _ (bindingStored binding member)).2.2.1
  · intro binding member
    have facts := allocated _ _ (bindingStored binding member)
    exact ⟨facts.2.1, facts.2.2.2⟩

/-- An ancestor remains addressable even when a nested resident becomes vacant. -/
theorem Initialization.Access.write_prefix {state selected : Initialization} {indices observed : List Nat}
    (access : state.Access indices selected) (initial : observed.IsPrefix indices) (next : Initialization) :
    ∃ retained, (state.write indices next).Access observed retained := by
  obtain ⟨suffix, rfl⟩ := initial
  induction observed generalizing state with
  | nil => exact ⟨_, .here _⟩
  | cons index rest ih =>
    cases access with
    | child present access =>
      obtain ⟨retained, kept⟩ := ih access
      exact ⟨retained, .child (by simp [Initialization.write, Initialization.setChild])
        (by simpa only [List.cons_append, Initialization.write, Initialization.child_setChild present, ↓reduceIte] using kept)⟩

/-- A complete replacement restores the selected target even if it was a hole. -/
theorem Context.Target.writeTarget_ready {context : Context} {origin : Origin} {referent : Ty}
    (target : context.Target program origin referent) {binder : Nat} (base : origin.base = .binder binder)
    {next : Initialization} (complete : next.Complete) : (context.writeTarget origin next).Ready origin := by
  obtain ⟨slot, stored, _, state, access⟩ := (by simpa [Context.Target, base] using target)
  simp only [Context.Ready, base]
  exact ⟨{ slot with initialization := slot.initialization.write origin.fields next }, next,
    by simp [Context.writeTarget, base, stored], access.write next, complete⟩



theorem Context.Ready.writeTarget_apart {context : Context} {origin observed : Origin} {referent : Ty}
    (target : context.Target program origin referent) {binder : Nat} (base : origin.base = .binder binder)
    (ready : context.Ready observed) (apart : origin.Apart observed) (next : Initialization) :
    (context.writeTarget origin next).Ready observed := by
  cases observedBase : observed.base with
  | input input => simp [Context.Ready, observedBase]
  | binder other =>
    simp only [Context.Ready, observedBase] at ready ⊢
    obtain ⟨slot, retained, stored, kept, complete⟩ := ready
    by_cases same : other = binder
    · subst other
      obtain ⟨root, rootStored, _, selected, access⟩ := (by simpa [Context.Target, base] using target)
      have equal := Option.some.inj (stored.symm.trans rootStored)
      subst root
      have fields : CoordinatesApart origin.fields observed.fields := by
        simpa [Origin.Apart, base, observedBase] using apart
      exact ⟨{ slot with initialization := slot.initialization.write origin.fields next }, retained,
        by simp [Context.writeTarget, base, stored], access.write_frame kept fields next, complete⟩
    · exact ⟨slot, retained, by simpa [Context.writeTarget, base, same] using stored, kept, complete⟩

private theorem mutation_derived_within {context : Context} (valid : context.WellFormed program)
    {node ancestor : Nat} {loan parentLoan : SourceLoan} (derived : context.Derived node ancestor)
    (found : context.loans[node]? = some loan) (ancestorFound : context.loans[ancestor]? = some parentLoan) :
    loan.target.Within parentLoan.target := by
  induction derived generalizing loan with
  | same =>
    have equal := Option.some.inj (found.symm.trans ancestorFound)
    subst loan
    exact ⟨rfl, ⟨[], by simp⟩⟩
  | child source parent earlier ih =>
    have equal := Option.some.inj (source.symm.trans found)
    subst loan
    obtain ⟨_, middle, middleFound, front⟩ := valid.parents _ _ _ source parent
    have back := ih middleFound ancestorFound
    exact ⟨front.1.trans back.1, back.2.trans front.2⟩

/-- Disjoint targets retain their exact masks; ancestors retain a canonical
addressable mask, but only unique ancestors may become incomplete. -/
theorem Context.SourceTarget.writeTarget {context : Context} {origin : Origin} {referent : Ty}
    (target : context.Target program origin referent) {binder : Nat} (base : origin.base = .binder binder)
    {loan : SourceLoan} (source : context.SourceTarget program loan)
    (separated : (origin.Within loan.target ∧ loan.mode = .unique) ∨ origin.Apart loan.target)
    (next : Initialization) : (context.writeTarget origin next).SourceTarget program loan := by
  obtain ⟨oldTarget, oldReady, inputShared⟩ := source
  refine ⟨?_, ?_, inputShared⟩
  · cases observedBase : loan.target.base with
    | input input => simp [Context.Target, observedBase]
    | binder other =>
      simp only [Context.Target, observedBase] at oldTarget ⊢
      obtain ⟨slot, stored, path, retained, kept⟩ := oldTarget
      by_cases same : other = binder
      · subst other
        obtain ⟨root, rootStored, _, selected, access⟩ := (by simpa [Context.Target, base] using target)
        have equal := Option.some.inj (stored.symm.trans rootStored)
        subst root
        refine ⟨{ slot with initialization := slot.initialization.write origin.fields next },
          by simp [Context.writeTarget, base, stored], path, ?_⟩
        rcases separated with ⟨within, _⟩ | apart
        · exact access.write_prefix within.2 next
        · exact ⟨retained, access.write_frame kept (by simpa [Origin.Apart, base, observedBase] using apart) next⟩
      · exact ⟨slot, by simpa [Context.writeTarget, base, same] using stored, path, retained, kept⟩
  · intro shared
    rcases separated with ⟨_, unique⟩ | apart
    · simp [shared] at unique
    · exact (oldReady shared).writeTarget_apart target base apart next

theorem StateProgress.writeTarget {interpretation : Interpretation} {context : Context} {before after : Environment}
    (valid : context.WellFormed program) {origin : Origin} {next : Initialization} {replacement : Value}
    (written : before.writeAddress (interpretation.origin origin) replacement = some after) :
    StateProgress context (context.writeTarget origin next) before after interpretation interpretation := by
  refine ⟨⟨fun _ loan found => ⟨loan, found, rfl, rfl, rfl, rfl, id⟩, rfl, Nat.le_refl _,
    fun _ member _ => member, ?_⟩, ?_, .refl _ _, ?_, ?_⟩
  · intro binder slot _ stored _
    exact context.writeTarget_stored origin next stored
  · intro binder known _
    exact (context.writeTarget_mentions origin next binder).mp known
  · intro binder large known
    exact False.elim (Nat.not_lt_of_ge large
      (valid.mentionedBound ((context.writeTarget_mentions origin next binder).mp known)))
  · simp only [Context.writeTarget, Environment.writeAddress_loans written]

/-- Authoritative canonical mutation. Positive unique authority and exclusion are
separate premises; reconstruction includes hidden cells and arbitrarily aliased
shared inputs. Ancestor mode monotonicity is derived from source well-formedness. -/
theorem StoreTyped.writeTarget {interpretation : Interpretation} {context : Context} {environment : Environment}
    (typed : StoreTyped program interpretation context environment) {origin : Origin} {referent : Ty}
    (target : context.Target program origin referent) {binder : Nat} (base : origin.base = .binder binder)
    {next : Initialization} {replacement : Value} (shape : referent.DataShape)
    (resident : ResidentTyped program next replacement referent)
    {node : Nat} {loan : SourceLoan} (found : context.loans[node]? = some loan)
    (own : loan.own = true) (unique : loan.mode = .unique) (within : origin.Within loan.target)
    (permitted : context.Permits .unique (some node) origin) :
    ∃ after, environment.writeAddress (interpretation.origin origin) replacement = some after ∧
      StoreTyped program interpretation (context.writeTarget origin next) after ∧
      StateProgress context (context.writeTarget origin next) environment after interpretation interpretation ∧
      environment.Evolution after := by
  obtain ⟨after, written, cells⟩ := typed.writeTarget_cells target base shape resident
  have authority : environment.MutationRoot (interpretation.origin origin).root := by
    exact .inr ⟨interpretation.node node, _, typed.records node loan found, own, unique,
      (interpretation.within within).1.symm⟩
  obtain ⟨runtimeValid, evolution⟩ := Environment.writeAddress_evolution authority written typed.residents.valid
  have update := Environment.writeAddress_update written
  have source := typed.source.writeTarget origin next
  have names : after.bindings = (context.writeTarget origin next).names.map
      (fun entry => (entry.1, interpretation.binder entry.2)) := by
    change after.bindings = context.names.map _
    rw [update.bindings, ← typed.source.bindings_names, List.map_map, typed.slots.bindings]
    rfl
  obtain ⟨residents, slots⟩ := Context.reconstruct source runtimeValid names cells
  refine ⟨after, written, ?_, StateProgress.writeTarget typed.source written, evolution⟩
  refine { source := source, residents := residents, slots := slots, cells := cells
           binderBound := ?_, binderDistinct := ?_, inputBound := ?_, inputApart := ?_
           nodeOrder := typed.nodeOrder, records := ?_, activeCoverage := ?_
           sourceTargets := ?_, inputTargets := ?_, storeShape := ?_ }
  · intro other known
    rw [update.supply]
    exact typed.binderBound other ((context.writeTarget_mentions origin next other).mp known)
  · intro first second firstKnown secondKnown same
    exact typed.binderDistinct first second ((context.writeTarget_mentions origin next first).mp firstKnown)
      ((context.writeTarget_mentions origin next second).mp secondKnown) same
  · intro input bound
    rw [update.supply]
    exact typed.inputBound input bound
  · intro other input known bound
    exact typed.inputApart other input ((context.writeTarget_mentions origin next other).mp known) bound
  · intro other otherLoan selected
    rw [Environment.writeAddress_loans written]
    exact typed.records other otherLoan selected
  · intro other otherLoan selected active
    rw [Environment.writeAddress_loans written] at selected
    exact typed.activeCoverage other otherLoan selected active
  · intro other otherLoan selected active
    apply (typed.sourceTargets other otherLoan selected active).writeTarget target base
    rcases permitted other otherLoan selected active with impossible | ⟨parent, equal, derived⟩ | apart
    · cases impossible.1
    · have same := Option.some.inj equal
      subst parent
      have above := mutation_derived_within typed.source derived found selected
      exact .inl ⟨⟨within.1.trans above.1, above.2.trans within.2⟩, derived.unique typed.source found selected unique⟩
    · exact .inr apart
  · intro other otherLoan selected active input inputBase
    obtain ⟨value, read, valueTyped⟩ := typed.inputTargets other otherLoan selected active input inputBase
    have known : origin.Known context := by
      obtain ⟨slot, stored, _⟩ := (by simpa [Context.Target, base] using target)
      simp only [Origin.Known, base]
      exact .inl ⟨slot, stored⟩
    have apart := typed.apart known (typed.source.loanKnown selected)
      (by simp [Origin.Apart, base, inputBase] : origin.Apart otherLoan.target)
    exact ⟨value, by simpa only [Environment.readAddress, update.frame _ apart] using read, valueTyped⟩
  · intro root value storedAfter
    obtain ⟨slot, stored, path, state, access⟩ := (by simpa [Context.Target, base] using target)
    obtain ⟨parent, updated, oldStored, changed, updatedTyped, write⟩ := typed.writeCanonical stored path access resident
    have same : after = environment.put (interpretation.binder binder) updated := by
      have write' : environment.writeAddress (interpretation.origin origin) replacement =
          some (environment.put (interpretation.binder binder) updated) := by
        simpa only [Interpretation.origin, base] using write
      exact Option.some.inj (written.symm.trans write')
    rw [same] at storedAfter ⊢
    by_cases equal : root = interpretation.binder binder
    · simp only [Environment.put, equal, ↓reduceIte, Option.some.injEq] at storedAfter
      subst value
      exact .inl (updatedTyped.referenceFree (path.dataShape (typed.source.allocated binder slot stored).2.2.1 shape))
    · exact typed.storeShape root value (by simpa [Environment.put, equal] using storedAfter)

/-- Replacing one selected resident with a complete value preserves a complete
ancestor, without imposing readiness on the resident being replaced. -/
theorem Initialization.Complete.write {state selected next : Initialization} {indices : List Nat}
    (complete : state.Complete) (access : state.Access indices selected) (ready : next.Complete) :
    (state.write indices next).Complete := by
  induction access with
  | here => exact ready
  | child present access ih =>
    apply (Initialization.setChild_complete_iff present _).mpr
    exact ⟨ih (complete.child _), fun other _ => complete.child other⟩

theorem Initialization.Access.write_ready {state selected retained next : Initialization} {indices observed : List Nat}
    (access : state.Access indices selected) (kept : state.Access observed retained)
    (complete : retained.Complete) (ready : next.Complete) :
    ∃ current, (state.write indices next).Access observed current ∧ current.Complete := by
  induction access generalizing observed retained with
  | here => exact ready.access_all observed
  | @child state selected index indices present access ih =>
    cases kept with
    | here => exact ⟨_, .here _, complete.write (.child present access) ready⟩
    | @child _ _ other observed keptPresent kept =>
      by_cases same : other = index
      · subst other
        obtain ⟨current, currentAccess, currentComplete⟩ := ih kept complete
        exact ⟨current, .child (by simp [Initialization.write, Initialization.setChild])
          (by simpa only [Initialization.write, Initialization.child_setChild present, ↓reduceIte] using currentAccess),
          currentComplete⟩
      · exact ⟨retained, .child (by simp [Initialization.write, Initialization.setChild])
          (by simpa only [Initialization.write, Initialization.child_setChild present, if_neg same] using kept), complete⟩

theorem Context.Ready.writeTarget_initialized {context : Context} {origin observed : Origin} {referent : Ty}
    (target : context.Target program origin referent) {binder : Nat} (base : origin.base = .binder binder)
    (ready : context.Ready observed) {next : Initialization} (complete : next.Complete) :
    (context.writeTarget origin next).Ready observed := by
  cases observedBase : observed.base with
  | input input => simp [Context.Ready, observedBase]
  | binder other =>
    simp only [Context.Ready, observedBase] at ready ⊢
    obtain ⟨slot, retained, stored, kept, initialized⟩ := ready
    by_cases same : other = binder
    · subst other
      obtain ⟨root, rootStored, _, selected, access⟩ := (by simpa [Context.Target, base] using target)
      have equal := Option.some.inj (stored.symm.trans rootStored)
      subst root
      obtain ⟨current, currentAccess, currentComplete⟩ := access.write_ready kept initialized complete
      exact ⟨{ slot with initialization := slot.initialization.write origin.fields next }, current,
        by simp [Context.writeTarget, base, stored], currentAccess, currentComplete⟩
    · exact ⟨slot, retained, by simpa [Context.writeTarget, base, same] using stored, kept, initialized⟩

/-- Pending carrier cells cannot be overwritten: the canonical data target and
its typed storage root are reference-free. Pending target readiness is separate:
a hole-producing move must exclude every held target; complete writes preserve it. -/
theorem StateTyped.writeTarget {interpretation : Interpretation} {context : Context} {environment : Environment}
    {heldNodes : List Nat} {held : List Value}
    (typed : StateTyped program interpretation context heldNodes environment held) {origin : Origin} {referent : Ty}
    (target : context.Target program origin referent) {binder : Nat} (base : origin.base = .binder binder)
    {next : Initialization} {replacement : Value} (shape : referent.DataShape)
    (resident : ResidentTyped program next replacement referent)
    {node : Nat} {loan : SourceLoan} (found : context.loans[node]? = some loan)
    (own : loan.own = true) (unique : loan.mode = .unique) (within : origin.Within loan.target)
    (permitted : context.Permits .unique (some node) origin)
    (heldSafe : ∀ heldNode ∈ heldNodes, ∀ heldLoan, context.loans[heldNode]? = some heldLoan →
      heldLoan.own = true → next.Complete ∨ origin.Apart heldLoan.target) :
    ∃ after, environment.writeAddress (interpretation.origin origin) replacement = some after ∧
      StateTyped program interpretation (context.writeTarget origin next) heldNodes after held ∧
      StateProgress context (context.writeTarget origin next) environment after interpretation interpretation ∧
      environment.Evolution after := by
  obtain ⟨after, written, store, progress, evolution⟩ := typed.toStoreTyped.writeTarget target base shape resident
    found own unique within permitted
  obtain ⟨state, selected, raw, selectedTyped⟩ := typed.toStoreTyped.targetResident target base
  have custody := typed.custody.writeAddress_selected typed.storeShape raw
    (selectedTyped.referenceFree shape) (resident.referenceFree shape) written
  have ready : ∀ heldNode ∈ heldNodes, (context.writeTarget origin next).Restored heldNode := by
    intro heldNode member heldLoan selected active
    rcases heldSafe heldNode member heldLoan selected active with complete | apart
    · exact (typed.heldReady heldNode member heldLoan selected active).writeTarget_initialized target base complete
    · exact (typed.heldReady heldNode member heldLoan selected active).writeTarget_apart target base apart next
  exact ⟨after, written, { store with heldShape := typed.heldShape, heldOwn := typed.heldOwn, heldReady := ready, custody := custody }, progress, evolution⟩

theorem StateTyped.resume {first last : Interpretation} {callerContext afterContext : Context}
    {caller after : Environment} {heldNodes : List Nat} {held : List Value}
    (callerTyped : StoreTyped program first callerContext caller)
    (afterTyped : StateTyped program last afterContext heldNodes after held)
    (progress : StateProgress callerContext.hide afterContext caller.hide after first last)
    (supply : caller.nextRoot ≤ after.nextRoot) :
    StateTyped program last (callerContext.resume afterContext) heldNodes (caller.resume after) held := by
  have source := callerTyped.source.resume afterTyped.source progress.history
  have names : (caller.resume after).bindings = (callerContext.resume afterContext).names.map
      (fun entry => (entry.1, last.binder entry.2)) := by
    change caller.bindings = callerContext.names.map _
    rw [← callerTyped.source.bindings_names, List.map_map, callerTyped.slots.bindings]
    apply List.map_congr_left
    intro binding member
    have same := progress.interpretation.binders binding.2.binder
      (callerTyped.source.mentionedBound (callerTyped.source.member_known binding member))
    simp only [Function.comp_def, same]
  obtain ⟨residents, slots⟩ := Context.reconstruct source
    (callerTyped.residents.valid.resume afterTyped.residents.valid supply) names afterTyped.cells
  exact { afterTyped with source := source, residents := residents, slots := slots }

theorem ResultTyped.resume {interpretation : Interpretation} {caller after : Context}
    {value : Value} {result : ResultType}
    (typed : ResultTyped program interpretation after value result) :
    ResultTyped program interpretation (caller.resume after) value result :=
  ⟨typed.resident, typed.shape⟩

theorem StateProgress.resume {first last : Interpretation} {callerContext afterContext : Context}
    {caller after : Environment}
    (valid : callerContext.WellFormed program)
    (progress : StateProgress callerContext.hide afterContext caller.hide after first last) :
    StateProgress callerContext (callerContext.resume afterContext) caller (caller.resume after) first last := by
  refine ⟨progress.history.resume, progress.support.resume,
    ⟨progress.interpretation.binders, progress.interpretation.nodes, progress.interpretation.inputs⟩,
    ?_, progress.loanCount⟩
  intro binder fresh mentioned
  rcases Context.resume_mentions mentioned with old | new
  · exact False.elim (Nat.not_lt_of_ge fresh (valid.mentionedBound old))
  · exact progress.fresh binder fresh new

theorem ResultTyped.ofData {interpretation : Interpretation} {context : Context} {value : Value} {type : Ty}
    (resident : ValueHasType program value type) (shape : type.DataShape) :
    ResultTyped program interpretation context value (.data type) := ⟨resident, shape, resident.referenceFree shape⟩

theorem StateTyped.dataResult {interpretation : Interpretation} {context : Context} {environment : Environment}
    {heldNodes : List Nat} {held : List Value} {value : Value} {type : Ty}
    (typed : StateTyped program interpretation context heldNodes environment held)
    (result : ResultTyped program interpretation context value (.data type)) :
    StateTyped program interpretation context (heldNodes ++ (ResultType.data type).nodes) environment (held ++ value.referenceValues) := by
  simpa only [ResultType.data, ResultType.nodes, Option.toList_none, List.append_nil,
    result.shape.2.referenceValues] using typed

theorem StateTyped.dropDataResult {interpretation : Interpretation} {context : Context} {environment : Environment}
    {heldNodes : List Nat} {held : List Value} {value : Value} {type : Ty}
    (typed : StateTyped program interpretation context (heldNodes ++ (ResultType.data type).nodes) environment (held ++ value.referenceValues))
    (result : ResultTyped program interpretation context value (.data type)) :
    StateTyped program interpretation context heldNodes environment held := by
  simpa only [ResultType.data, ResultType.nodes, Option.toList_none, List.append_nil,
    result.shape.2.referenceValues] using typed

theorem StateTyped.resultUsable {interpretation : Interpretation} {context : Context} {environment : Environment}
    {heldNodes : List Nat} {held : List Value} {value : Value} {result : ResultType}
    (typed : StateTyped program interpretation context (heldNodes ++ result.nodes) environment held)
    (valueTyped : ResultTyped program interpretation context value result) : environment.ResultUsable value :=
  valueTyped.usable typed.toStoreTyped (fun node member => typed.heldOwn node (List.mem_append_right _ member))
    (fun node member => typed.heldReady node (List.mem_append_right _ member))

/-- A reference-expected bare place cannot fall back to an ordinary leaf read
(shared copying) or a leaf transfer. Its emitted reborrow plan is compulsory. -/
theorem HasType.reference_read_not_leaf {context after : Context} {held : List Nat}
    {expression : Expr} {result : ResultType} {plan : CorePlan} {expected : Option Ty}
    (typed : HasType program home context held expression result after plan expected)
    {place : Place} {referent : Ty} {mode : BorrowMode} :
    expression = .read place → plan = .leaf → expected = some (.reference referent mode) → False := by
  induction typed using HasType.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) (motive_5 := fun _ _ _ _ => True) (motive_6 := fun _ _ _ _ => True) with
  | raiseSupply _ _ ih => exact ih
  | expectedData typed shape ih =>
    intro _ _ expected
    have same := Option.some.inj expected
    rw [same] at shape
    exact shape
  | _ => first | trivial | (intro source leaf expected; cases source <;> cases leaf <;> cases expected)

/-- A compatible reference expectation cannot be bypassed by default transfer. -/
theorem HasType.reference_read_not_implicitMove {context after : Context} {held : List Nat}
    {expression : Expr} {result : ResultType} {plan : CorePlan} {expected : Option Ty}
    (typed : HasType program home context held expression result after plan expected)
    {place : Place} {referent : Ty} {mode : BorrowMode} :
    expression = .read place → plan = .implicitMove → expected = some (.reference referent mode) → False := by
  induction typed using HasType.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) (motive_5 := fun _ _ _ _ => True) (motive_6 := fun _ _ _ _ => True) with
  | raiseSupply _ _ ih => exact ih
  | expectedData typed shape ih =>
    intro _ _ expected
    have same := Option.some.inj expected
    rw [same] at shape
    exact shape
  | _ => first | trivial | (intro source move expected; cases source <;> cases move <;> cases expected)

/-- Emitted default-transfer plans carry positive noncopy evidence through the
same admission derivation, including contextual data checking. -/
theorem HasType.implicitMove_nonduplicable {context after : Context} {held : List Nat}
    {expression : Expr} {result : ResultType} {plan : CorePlan} {expected : Option Ty}
    (typed : HasType program home context held expression result after plan expected) :
    plan = .implicitMove → Nonduplicable program.data result.type := by
  induction typed using HasType.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) (motive_5 := fun _ _ _ _ => True) (motive_6 := fun _ _ _ _ => True) with
  | implicitMove noncopy _ _ => exact fun _ => noncopy
  | raiseSupply _ _ ih | expectedData _ _ ih | expectedMove _ ih => exact ih
  | _ => first | trivial | (intro impossible; cases impossible)

theorem HasType.implicitMove_not_copy {context after : Context} {held : List Nat}
    {expression : Expr} {result : ResultType} {expected : Option Ty}
    (typed : HasType program home context held expression result after .implicitMove expected) :
    ¬ Duplicable program.data result.type := (typed.implicitMove_nonduplicable rfl).not_duplicable

/-- Parameter expectations are consumed in order by the authoritative argument producer. -/
theorem HasTypes.expected_types {context after : Context} {held : List Nat} {expressions : List Expr}
    {results : List ResultType} {plans : List CorePlan} {expected : Option (List Ty)}
    (typed : HasTypes program home context held expressions results after plans expected) :
    ∀ types, expected = some types → results.map ResultType.type = types := by
  induction typed using HasTypes.rec
    (motive_1 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) (motive_5 := fun _ _ _ _ => True) (motive_6 := fun _ _ _ _ => True) with
  | nil | cons => intro types impossible; cases impossible
  | expectedNil => intro types same; cases same; rfl
  | expectedCons head tail headIH tailIH =>
    intro types same
    cases same
    simp only [List.map_cons]
    rw [tailIH _ rfl]
  | _ => trivial

theorem HasType.constantDeclared {context after : Context} {held : List Nat} {name : String} {expression : Expr}
    {result : ResultType} {plan : CorePlan} {expected : Option Ty}
    (typed : HasType program home context held expression result after plan expected) (source : expression = .constant name) :
    ∃ declaration, program.constants name = some declaration ∧ ResolvesType program.aliases declaration.type result.type := by
  induction typed using HasType.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ => True) generalizing name with
  | constant declared _ resolved => cases source; exact ⟨_, declared, resolved⟩
  | endOwn _ _ _ _ _ ih => exact ih source
  | endAfter _ _ _ _ _ ih => exact ih source
  | raiseSupply _ _ ih => exact ih source
  | expectedData _ _ ih => exact ih source
  | _ => first | trivial | cases source

theorem StateTyped.pendingNodup {interpretation : Interpretation} {context : Context}
    {heldNodes : List Nat} {environment : Environment} {held : List Value}
    (typed : StateTyped program interpretation context heldNodes environment held) : held.Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj less same
  have found := List.getElem?_eq_getElem hi
  rw (occs := .pos [1]) [typed.heldShape] at found
  rw [List.getElem?_map] at found
  obtain ⟨sourceNode, sourceFound, shape⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨loan, loanFound, own⟩ := typed.heldOwn sourceNode (List.mem_of_getElem? sourceFound)
  obtain ⟨location, _, unique⟩ := typed.custody _ _ (typed.records sourceNode loan loanFound) own
  have first : Carries environment held (interpretation.node sourceNode) (.held i) := by
    exact (List.getElem?_eq_getElem hi).trans (congrArg some shape.symm)
  have second : Carries environment held (interpretation.node sourceNode) (.held j) := by
    exact (List.getElem?_eq_getElem hj).trans (congrArg some (same.symm.trans shape.symm))
  have equal := Carrier.held.inj ((unique _ first).trans (unique _ second).symm)
  omega

theorem StateTyped.permPending {interpretation : Interpretation} {context : Context}
    {heldNodes otherNodes : List Nat} {environment : Environment} {held other : List Value}
    (typed : StateTyped program interpretation context heldNodes environment held)
    (nodes : heldNodes.Perm otherNodes) (values : held.Perm other)
    (shape : other = otherNodes.map (fun node => Value.reference (interpretation.node node))) :
    StateTyped program interpretation context otherNodes environment other := by
  refine { typed.toStoreTyped with
    heldShape := shape
    heldOwn := fun node member => typed.heldOwn node (nodes.mem_iff.mpr member)
    heldReady := fun node member => typed.heldReady node (nodes.mem_iff.mpr member)
    custody := ?_ }
  have nodup := typed.pendingNodup.perm values
  intro node loan found own
  obtain ⟨location, carried, unique⟩ := typed.custody node loan found own
  have oldHeld : ∀ index : Nat, other[index]? = some (Value.reference node) →
      ∃ old : Nat, held[old]? = some (Value.reference node) := by
    intro index selected
    exact List.mem_iff_getElem?.mp (values.mem_iff.mpr (List.mem_of_getElem? selected))
  cases location with
  | stored root =>
    refine ⟨.stored root, carried, ?_⟩
    intro otherLocation selected
    cases otherLocation with
    | stored otherRoot => exact unique _ selected
    | held index =>
      obtain ⟨old, oldFound⟩ := oldHeld index selected
      have impossible := unique (.held old) oldFound
      cases impossible
  | held index =>
    obtain ⟨next, nextFound⟩ := List.mem_iff_getElem?.mp (values.mem_iff.mp (List.mem_of_getElem? carried))
    refine ⟨.held next, nextFound, ?_⟩
    intro otherLocation selected
    cases otherLocation with
    | stored root =>
      have impossible := unique (.stored root) selected
      cases impossible
    | held otherIndex =>
      exact congrArg Carrier.held ((List.getElem?_inj
        (List.getElem?_eq_some_iff.mp selected).1 nodup).mp (selected.trans nextFound.symm))

inductive ResultsTyped (program : Program) (interpretation : Interpretation) (context : Context) :
    List Value → List ResultType → Prop where
  | nil : ResultsTyped program interpretation context [] []
  | cons {value : Value} {values : List Value} {result : ResultType} {results : List ResultType}
      (head : ResultTyped program interpretation context value result)
      (tail : ResultsTyped program interpretation context values results) :
      ResultsTyped program interpretation context (value :: values) (result :: results)

theorem ResultsTyped.referenceValues {interpretation : Interpretation} {context : Context}
    {values : List Value} {results : List ResultType}
    (typed : ResultsTyped program interpretation context values results) :
    Grounded.referenceValues values = (resultNodes results).map (fun node => Value.reference (interpretation.node node)) := by
  induction typed with
  | nil => rfl
  | cons head tail ih =>
    simp only [Grounded.referenceValues, resultNodes, List.flatMap_cons, List.map_append] at *
    rw [head.referenceValues, ih]

theorem ResultsTyped.transport {before after : Context} {first last : Interpretation}
    {values : List Value} {results : List ResultType}
    (typed : ResultsTyped program first before values results)
    (history : before.History after) (extension : first.Extends last before) :
    ResultsTyped program last after values results := by
  induction typed with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.transport history extension) ih

theorem StateTyped.prepare {interpretation : Interpretation} {context : Context}
    {environment : Environment} {heldNodes : List Nat} {held : List Value}
    {parameters : List (String × BindingType)} {values : List Value} {results : List ResultType}
    (typed : StateTyped program interpretation context (heldNodes ++ resultNodes results)
      environment (held ++ referenceValues values))
    (arguments : ResultsTyped program interpretation context values results)
    (aligned : parameters.map (fun parameter => parameter.2.type) = results.map ResultType.type) :
    ∃ afterMap,
      StateTyped program afterMap (Context.prepare parameters results context) heldNodes
        (environment.prepare ((parameters.map Prod.fst).zip values)) held ∧
      StateProgress context (Context.prepare parameters results context) environment
        (environment.prepare ((parameters.map Prod.fst).zip values)) interpretation afterMap := by
  induction parameters generalizing interpretation context environment values results with
  | nil =>
    have empty : results = [] := by cases results <;> simp_all
    subst results
    cases arguments
    exact ⟨interpretation, by simpa [resultNodes, referenceValues, Context.prepare, Environment.prepare] using typed,
      .refl typed.source⟩
  | cons parameter parameters ih =>
    cases arguments with
    | nil => simp at aligned
    | @cons value values result results head tail =>
      have align := List.cons.inj (by simpa only [List.map_cons] using aligned)
      have projection := (ResultsTyped.cons head tail).referenceValues
      have prefixShape : held = heldNodes.map (fun node => Value.reference (interpretation.node node)) := by
        apply List.append_cancel_right
        simpa only [List.map_append, ← projection] using typed.heldShape
      have reordered : StateTyped program interpretation context
          ((heldNodes ++ resultNodes results) ++ result.nodes) environment
          ((held ++ referenceValues values) ++ value.referenceValues) := by
        apply typed.permPending
        · simpa only [resultNodes, List.flatMap_cons, List.append_assoc] using
            (List.Perm.append_left heldNodes (List.perm_append_comm (l₁ := result.nodes) (l₂ := resultNodes results)))
        · simpa only [referenceValues, List.flatMap_cons, List.append_assoc] using
            (List.Perm.append_left held (List.perm_append_comm (l₁ := value.referenceValues) (l₂ := referenceValues values)))
        · simp only [List.map_append, prefixShape, head.referenceValues, tail.referenceValues]
      have installed := reordered.bind head parameter.1 parameter.2.mutable
      have step := StateProgress.bind (interpretation := interpretation) (environment := environment)
        typed.source parameter.1 parameter.2.mutable result value
      obtain ⟨afterMap, prepared, progress⟩ := ih installed
        (tail.transport step.history step.interpretation) align.2
      exact ⟨afterMap, prepared, step.trans progress (by simp [Environment.bind])⟩

theorem ResultsTyped.length {interpretation : Interpretation} {context : Context}
    {values : List Value} {results : List ResultType}
    (typed : ResultsTyped program interpretation context values results) : values.length = results.length := by
  induction typed with
  | nil => rfl
  | cons head tail ih => simpa using congrArg Nat.succ ih

theorem ResultsTyped.residents {interpretation : Interpretation} {context : Context}
    {values : List Value} {results : List ResultType}
    (typed : ResultsTyped program interpretation context values results) :
    ValuesHaveTypes program values (results.map ResultType.type) := by
  induction typed with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.resident ih

theorem ResultsTyped.data {interpretation : Interpretation} {context : Context}
    {values : List Value} {types : List Ty}
    (typed : ResultsTyped program interpretation context values (types.map ResultType.data)) :
    ValuesHaveTypes program values types ∧ valuesReferenceFree values := by
  induction types generalizing values with
  | nil => cases typed; exact ⟨.nil, trivial⟩
  | cons type types ih =>
    cases typed with
    | cons head tail =>
      obtain ⟨residents, plain⟩ := ih tail
      exact ⟨.cons head.resident residents, head.shape.2, plain⟩

theorem ResultsTyped.usable {interpretation : Interpretation} {context : Context}
    {values : List Value} {results : List ResultType} {environment : Environment}
    (typed : ResultsTyped program interpretation context values results)
    (stored : StoreTyped program interpretation context environment)
    (own : ∀ node ∈ resultNodes results, context.Own node)
    (ready : ∀ node ∈ resultNodes results, context.Restored node) :
    ∀ value ∈ values, environment.ResultUsable value := by
  induction typed with
  | nil => simp
  | cons head tail ih =>
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact head.usable stored (fun node included => own node (List.mem_append_left _ included))
        (fun node included => ready node (List.mem_append_left _ included))
    · exact ih (fun node included => own node (List.mem_append_right _ included))
        (fun node included => ready node (List.mem_append_right _ included)) value member

theorem ResidentTyped.dataShape_of_plain {state : Initialization} {value : Value} {type : Ty}
    (typed : ResidentTyped program state value type) (complete : state.Complete)
    (plain : value.ReferenceFree) : type.DataShape := by
  induction typed using ResidentTyped.rec
    (motive_2 := fun states values types _ => (∀ index, (states index).Complete) →
      valuesReferenceFree values → typesDataShape types) with
  | vacant | uncertain => cases complete
  | unit | integer | character | nominal => trivial
  | reference => exact False.elim plain
  | tuple head tail present headIH tailIH =>
    exact ⟨headIH (complete.child 0) plain.1, tailIH (fun index => complete.child (index + 1)) plain.2⟩
  | array residents finite size present ih => exact finite.dataShape
  | nil => trivial
  | cons head tail headIH tailIH =>
    rename_i complete plain
    exact ⟨headIH (complete 0) plain.1, tailIH (fun index => complete (index + 1)) plain.2⟩

theorem PatternType.bindings_full {pattern : Pattern} {type : Ty} {bindings : List (String × BindingType)}
    (typed : PatternType program home pattern type bindings) :
    ∀ binding ∈ bindings, binding.2.initialization = .full := by
  induction typed using PatternType.rec
    (motive_2 := fun _ _ bindings _ => ∀ binding ∈ bindings, binding.2.initialization = .full) with
  | wildcard | literal => simp
  | nil => rename_i binding member; cases member
  | binder => simp
  | node shape access fields ih => exact ih
  | cons head tail headIH tailIH =>
    rename_i binding member
    rcases List.mem_append.mp member with member | member
    · exact headIH binding member
    · exact tailIH binding member

theorem Pattern.Consumes.bindings_plain {pattern : Pattern} {value : Value}
    {bindings : BindingValues} {trace : List (List Nat)}
    (consumed : Pattern.Consumes program pattern value bindings trace) (plain : value.ReferenceFree) :
    ∀ binding ∈ bindings, binding.2.ReferenceFree := by
  induction consumed using Pattern.Consumes.rec
    (motive_2 := fun _ _ values bindings _ _ => valuesReferenceFree values →
      ∀ binding ∈ bindings, binding.2.ReferenceFree) with
  | wildcard | literal => simp
  | nil => rename_i plain binding member; cases member
  | binder => simpa using plain
  | @node head patterns value bindings trace same fields ih =>
    apply ih
    cases value <;> simp_all [Value.children, Value.ReferenceFree, valuesReferenceFree]
  | cons tail head tailIH headIH =>
    rename_i plain binding member
    rcases List.mem_append.mp member with member | member
    · exact headIH plain.1 binding member
    · exact tailIH plain.2 binding member

theorem ValuesBindingsTyped.results {interpretation : Interpretation} {context : Context}
    {bindings : BindingValues} {types : List (String × BindingType)}
    (typed : ValuesBindingsTyped program bindings types)
    (full : ∀ binding ∈ types, binding.2.initialization = .full)
    (plain : ∀ binding ∈ bindings, binding.2.ReferenceFree) :
    ResultsTyped program interpretation context (bindings.map Prod.snd)
      (types.map (fun binding => ResultType.data binding.2.type)) ∧
    (types.map Prod.fst).zip (bindings.map Prod.snd) = bindings := by
  induction typed with
  | nil => exact ⟨.nil, rfl⟩
  | @cons name value type bindings types resident rest ih =>
    have firstFull := full (name, type) (by simp)
    change type.initialization = .full at firstFull
    have firstPlain := plain (name, value) (by simp)
    have first : ValueHasType program value type.type := by simpa [SlotTyped, firstFull] using resident
    obtain ⟨tail, zipped⟩ := ih (fun binding member => full binding (by simp [member]))
      (fun binding member => plain binding (by simp [member]))
    exact ⟨.cons ⟨first, first.dataShape_of_plain .full firstPlain, firstPlain⟩ tail,
      by simpa using congrArg (List.cons (name, value)) zipped⟩

theorem PatternType.consume_results {interpretation : Interpretation} {context : Context}
    {pattern : Pattern} {type : Ty} {types : List (String × BindingType)}
    (typed : PatternType program home pattern type types) {value : Value}
    (resident : ValueHasType program value type) (plain : value.ReferenceFree)
    {bindings : BindingValues} (matched : pattern.matchValue value = some bindings) :
    ResultsTyped program interpretation context (bindings.map Prod.snd)
      (types.map (fun binding => ResultType.data binding.2.type)) ∧
    (types.map Prod.fst).zip (bindings.map Prod.snd) = bindings := by
  obtain ⟨bindingsTyped, trace, consumed⟩ := typed.consume resident matched
  exact bindingsTyped.results typed.bindings_full (consumed.bindings_plain plain)

@[simp] theorem resultNodes_data (types : List Ty) : resultNodes (types.map ResultType.data) = [] := by
  induction types with
  | nil => rfl
  | cons type types ih => simp [resultNodes, ResultType.nodes, ResultType.data]

theorem ResultsTyped.dropData {interpretation : Interpretation} {context : Context} {environment : Environment}
    {heldNodes : List Nat} {held : List Value} {values : List Value} {types : List Ty}
    (typed : StateTyped program interpretation context (heldNodes ++ resultNodes (types.map ResultType.data))
      environment (held ++ Grounded.referenceValues values))
    (results : ResultsTyped program interpretation context values (types.map ResultType.data)) :
    StateTyped program interpretation context heldNodes environment held := by
  simpa only [results.referenceValues, resultNodes_data, List.map_nil, List.append_nil] using typed

theorem ResultTyped.newBorrow {interpretation : Interpretation} {context : Context} {environment : Environment}
    {target : Origin} {referent : Ty} {parent : Option Nat} {mode : BorrowMode} (finite : FiniteLayout program.target program.data referent) :
    ResultTyped program (interpretation.addNode context.loans.length environment.loans.length)
      (context.borrow target referent parent mode) (.reference environment.loans.length) ⟨.reference referent mode, some context.loans.length⟩ := by
  refine ⟨.reference _ finite, ?_, _, context.borrow_last target referent parent mode, rfl⟩
  simp [Interpretation.addNode]

theorem Value.ReferenceFree.usable {value : Value} (plain : value.ReferenceFree) (environment : Environment) :
    environment.ResultUsable value := by
  cases value <;> first | exact plain | exact False.elim plain

theorem Environment.Disposes.restored {before after : Environment} {value : Value} {node : Nat}
    (disposed : Environment.Disposes program before value after) (ready : before.Restored node) :
    after.Restored node := by
  have same := disposed.storage.store
  cases disposed with
  | data => exact ready
  | reference _ ended =>
    intro loan found own
    obtain ⟨resident, read⟩ := ready loan (Environment.endOwn_active ended found own).1 own
    exact ⟨resident, by simpa only [Environment.readAddress, Environment.at, same] using read⟩

theorem Environment.prepare_supply (values : BindingValues) (environment : Environment) :
    environment.nextRoot ≤ (environment.prepare values).nextRoot := by
  induction values generalizing environment with
  | nil => exact Nat.le_refl _
  | cons value values ih => exact Nat.le_trans (Nat.le_succ _) (ih (environment.bind value.1 value.2))

theorem valuesReferenceFree.argument {values : List Value} (plain : valuesReferenceFree values) :
    (argumentValue values).ReferenceFree := by
  cases values with
  | nil => trivial
  | cons first rest => cases rest with
    | nil => exact plain.1
    | cons second tail => exact plain

theorem ResultsTyped.hide {interpretation : Interpretation} {context : Context} {values : List Value} {results : List ResultType}
    (typed : ResultsTyped program interpretation context values results) :
    ResultsTyped program interpretation context.hide values results := by
  induction typed with
  | nil => exact .nil
  | cons head tail ih => exact .cons ⟨head.resident, head.shape⟩ ih

/-- Every admitted expression produces a uniquely determined, correctly typed
result and updated lexical environment. Later expressions consume that actual
post-state; scopes remove only their own bindings. -/
private theorem execution_correctness {context afterContext : Context} {heldNodes : List Nat}
    {expression : Expr} {result : ResultType} {plan : CorePlan} {expected : Option Ty}
    (admitted : HasType program home context heldNodes expression result afterContext plan expected)
    {interpretation : Interpretation} {environment : Environment} {held : List Value}
    (environmentTyped : StateTyped program interpretation context heldNodes environment held) :
    ∃ value after afterMap, Evaluates program environment ⟨expression, plan⟩ value after ∧
      ResultTyped program afterMap afterContext value result ∧
      StateTyped program afterMap afterContext (heldNodes ++ result.nodes) after (held ++ value.referenceValues) ∧
      StateProgress context afterContext environment after interpretation afterMap := by
  induction admitted using HasType.rec
    (motive_2 := fun home context heldNodes expressions results afterContext plans expected _ =>
      ∀ (interpretation : Interpretation) (environment : Environment) (held : List Value),
      StateTyped program interpretation context heldNodes environment held →
      ∃ values after afterMap, EvaluatesMany program environment expressions plans values after ∧
        ResultsTyped program afterMap afterContext values results ∧
        StateTyped program afterMap afterContext (heldNodes ++ resultNodes results) after (held ++ referenceValues values) ∧
        StateProgress context afterContext environment after interpretation afterMap)
    (motive_3 := fun home context heldNodes subject result previous arms afterContext expected _ =>
      ∀ (interpretation : Interpretation) (environment : Environment) (held : List Value),
      StateTyped program interpretation context heldNodes environment held →
      ∀ value, ValueHasType program value subject → value.ReferenceFree → ∀ bindings body,
        selectArm value arms = some (bindings, body) →
        ∃ resultValue localAfter after afterMap,
          Evaluates program (environment.prepare bindings) body resultValue localAfter ∧
          ResultTyped program afterMap afterContext resultValue result ∧
          StateTyped program afterMap afterContext (heldNodes ++ result.nodes) after (held ++ resultValue.referenceValues) ∧
          (∃ trace, Cleans program bindings.length localAfter trace after) ∧
          ConsumesArm program value arms bindings body ∧
          StateProgress context afterContext environment after interpretation afterMap)
    (motive_4 := fun home source plan _ => ∃ normalized, NormalizesPattern program source plan normalized)
    (motive_5 := fun home sources plans _ => ∃ normalized, NormalizesPatterns program sources plans normalized)
    (motive_6 := fun home sources plans _ => ∃ normalized, NormalizesArms program sources plans normalized)
    generalizing interpretation environment held with
  | unit =>
    have result {resultContext : Context} := ResultTyped.ofData (interpretation := interpretation) (context := resultContext) (program := program) .unit (by trivial)
    exact ⟨_, _, _, .unit, result, environmentTyped.dataResult result, .refl environmentTyped.source⟩
  | integer fits =>
    have result {resultContext : Context} := ResultTyped.ofData (interpretation := interpretation) (context := resultContext) (.integer fits) (by trivial)
    exact ⟨_, _, _, .integer fits, result, environmentTyped.dataResult result, .refl environmentTyped.source⟩
  | character valid =>
    have result {resultContext : Context} := ResultTyped.ofData (interpretation := interpretation) (context := resultContext) (program := program) (.character valid) (by trivial)
    exact ⟨_, _, _, .character valid, result, environmentTyped.dataResult result, .refl environmentTyped.source⟩
  | group typed ih =>
    obtain ⟨value, after, afterMap, evaluated, result, typed, progress⟩ := ih environmentTyped
    exact ⟨value, after, afterMap, .group evaluated, result, typed, progress⟩
  | implicitMove _ _ ih =>
    obtain ⟨value, after, afterMap, evaluated, result, typed, progress⟩ := ih environmentTyped
    exact ⟨value, after, afterMap, .implicitMove evaluated, result, typed, progress⟩
  | @read home context heldNodes place slot type indices state selected access initialized path shape copyable permitted =>
    obtain ⟨value, resolved, raw, resident⟩ := environmentTyped.toStoreTyped.resolvePlace selected access path
    obtain ⟨resident, live⟩ := resident.complete initialized
    have result {resultContext : Context} := ResultTyped.ofData (interpretation := interpretation) (context := resultContext) resident shape
    exact ⟨value, environment, interpretation,
      .read resolved (by simp [Environment.readAddress, raw, live])
        (environmentTyped.toStoreTyped.permits (origin := ⟨.binder slot.binder, indices⟩) (allowed := permitted)
          (environmentTyped.source.member_known _ (lookup_member selected)))
        (.data (resident.referenceFree shape)), result,
      environmentTyped.dataResult result, .refl environmentTyped.source⟩
  | @copyShared home context heldNodes place slot node loan selected direct handle shape initialized found own copyable permitted =>
    have shared := copyable.duplicable_reference_shared
    have handlePath : PathType program home slot.type place.fields [] slot.type := by rw [direct]; exact .nil _
    obtain ⟨carrier, resolved, raw, resident⟩ := environmentTyped.toStoreTyped.resolvePlace selected (.here _) handlePath
    have stored : environment.store (interpretation.binder slot.binder) = some carrier := by
      simpa [Environment.at, Value.readIndices] using raw
    have same : carrier = .reference (interpretation.node node) := by
      simpa [Slot.Corresponds, handle] using (environmentTyped.slots.lookup selected).2 carrier stored
    subst carrier
    obtain ⟨value, targetRead, valueTyped⟩ := environmentTyped.targets node loan found own shared
    have known := environmentTyped.source.loanKnown found
    obtain ⟨bounded, finite⟩ := environmentTyped.source.targets node loan found
    have ancestor : ∀ parent, some node = some parent → ∃ sourceLoan,
        context.loans[parent]? = some sourceLoan ∧ loan.target.Within sourceLoan.target := by
      intro parent equal
      cases Option.some.inj equal
      exact ⟨loan, found, rfl, [], by simp⟩
    exact ⟨_, _, _, .read resolved (by simp [Environment.readAddress, raw, Value.initialized])
      (environmentTyped.toStoreTyped.permits (origin := ⟨.binder slot.binder, []⟩) (allowed := permitted)
        (environmentTyped.source.member_known _ (lookup_member selected)))
      (.reference (environmentTyped.records node loan found) shared (environmentTyped.toStoreTyped.usable ⟨loan, found, own⟩)),
      ResultTyped.newBorrow finite, environmentTyped.borrow (mode := .shared) known bounded finite ancestor
        (by intro _ _ _ _ impossible; cases impossible)
        (by simpa only [Context.SourceTarget, shared] using environmentTyped.sourceTargets node loan found own)
        ((environmentTyped.sourceTargets node loan found own).2.1 shared) targetRead valueTyped,
      .borrow environmentTyped.source known⟩
  | @move home context heldNodes place slot type indices state slots selected access initialized path shape data free cleared =>
    obtain ⟨value, after, resolved, taken, afterTyped, result, custody⟩ :=
      environmentTyped.toStoreTyped.takeData_custody environmentTyped.custody selected access initialized path data shape cleared free
    have state : StateTyped program interpretation _ _ after held :=
      { afterTyped with
        heldShape := environmentTyped.heldShape
        heldOwn := environmentTyped.heldOwn
        heldReady := fun node member => (environmentTyped.heldReady node member).writeSlot
          environmentTyped.source selected cleared rfl rfl access free
        custody := custody }
    exact ⟨value, after, interpretation, .move resolved
      (environmentTyped.toStoreTyped.ownerFree (origin := ⟨.binder slot.binder, indices⟩) (environmentTyped.source.member_known _ (lookup_member selected)) free)
      (result.shape.2.usable _) taken, result, state.dataResult result,
      StateProgress.replaceSlot environmentTyped.source selected cleared rfl
        (congrArg List.length (Environment.writeAddress_loans (Environment.takeAddress_eq_some.mp taken).2))⟩
  | @moveReference home context heldNodes place slot node referent mode slots selected direct handle shape initialized own ready free cleared =>
    obtain ⟨after, resolved, taken, afterTyped, result, custody⟩ :=
      environmentTyped.toStoreTyped.takeReference_custody (home := home) environmentTyped.custody selected direct handle shape initialized cleared free
    have state : StateTyped program interpretation (context.withSlots slots) (heldNodes ++ [node]) after
        (held ++ [.reference (interpretation.node node)]) := by
      refine { afterTyped with heldShape := ?_, heldOwn := ?_, heldReady := ?_, custody := custody }
      · simp only [List.map_append, List.map_cons, List.map_nil, environmentTyped.heldShape]
      · intro other member
        rcases List.mem_append.mp member with old | final
        · exact environmentTyped.heldOwn other old
        · have equal : other = node := by simpa using final
          subst other
          exact own
      · intro other member
        have restored : context.Restored other := by
          rcases List.mem_append.mp member with old | final
          · exact environmentTyped.heldReady other old
          · have same : other = node := by simpa using final
            exact same ▸ ready
        exact restored.writeSlot environmentTyped.source selected cleared rfl rfl (.here _) free
    exact ⟨_, after, interpretation, .move resolved
      (environmentTyped.toStoreTyped.ownerFree (origin := ⟨.binder slot.binder, []⟩) (environmentTyped.source.member_known _ (lookup_member selected)) free)
      (show environment.ResultUsable (.reference (interpretation.node node)) from
        ⟨environmentTyped.toStoreTyped.usable own,
          by obtain ⟨loan, found, _⟩ := own; exact environmentTyped.toStoreTyped.restored found ready⟩) taken, result, state,
      StateProgress.replaceSlot environmentTyped.source selected cleared rfl
        (congrArg List.length (Environment.writeAddress_loans (Environment.takeAddress_eq_some.mp taken).2))⟩
  | borrow access ready permitted finite =>
    obtain ⟨known, bounded, ancestor, value, resolved, allowed, selected, resident⟩ := environmentTyped.toStoreTyped.resolveAccess access ready
    exact ⟨_, _, _, .borrow resolved allowed (environmentTyped.toStoreTyped.permits known permitted) (environmentTyped.toStoreTyped.accessReady access ready) selected (resident.referenceFree finite.dataShape),
      ResultTyped.newBorrow finite, environmentTyped.borrow known bounded finite ancestor access.parentMode
        (access.sourceTarget environmentTyped.toStoreTyped ready) ready.1 selected resident,
      .borrow environmentTyped.source known⟩
  | reborrow access ready permitted finite =>
    obtain ⟨known, bounded, ancestor, value, resolved, allowed, selected, resident⟩ := environmentTyped.toStoreTyped.resolveAccess access ready
    exact ⟨_, _, _, .reborrow resolved allowed (environmentTyped.toStoreTyped.permits known permitted) (environmentTyped.toStoreTyped.accessReady access ready) selected (resident.referenceFree finite.dataShape),
      ResultTyped.newBorrow finite, environmentTyped.borrow known bounded finite ancestor access.parentMode
        (access.sourceTarget environmentTyped.toStoreTyped ready) ready.1 selected resident,
      .borrow environmentTyped.source known⟩
  | expectedData _ _ ih | expectedMove _ ih | expectedBorrow _ ih | expectedCall _ ih => exact ih environmentTyped
  | dereference access ready permitted copyable shape =>
    obtain ⟨known, _, _, value, resolved, allowed, selected, resident⟩ := environmentTyped.toStoreTyped.resolveAccess access ready
    have result {resultContext : Context} := ResultTyped.ofData (interpretation := interpretation) (context := resultContext) resident shape
    exact ⟨value, environment, interpretation, .dereference resolved allowed (environmentTyped.toStoreTyped.permits known permitted) (environmentTyped.toStoreTyped.accessReady access ready) selected (resident.referenceFree shape),
      result, environmentTyped.dataResult result, .refl environmentTyped.source⟩
  | moveIndirect access ready permitted shape pending =>
    obtain ⟨loan, binder, found, own, unique, within, base⟩ := access.uniqueTarget environmentTyped.toStoreTyped
    obtain ⟨known, _, _, value, resolved, allowed, selected, resident⟩ := environmentTyped.toStoreTyped.resolveAccess access ready
    obtain ⟨after, written, typed, progress, _⟩ := environmentTyped.writeTarget (access.canonicalTarget environmentTyped.toStoreTyped) base shape
      .vacant found own unique within permitted (fun node member loan found own => .inr (pending node member loan found own))
    have result {resultContext : Context} := ResultTyped.ofData (interpretation := interpretation) (context := resultContext) resident shape
    exact ⟨value, after, interpretation, .moveIndirect resolved allowed
      (environmentTyped.toStoreTyped.permits known permitted) (environmentTyped.toStoreTyped.accessReady access ready)
      (resident.referenceFree shape) (Environment.takeAddress_eq_some.mpr ⟨selected, written⟩), result, typed.dataResult result, progress⟩
  | @assignIndirect expected home context middle afterContext heldNodes reference fields expression rest target type node result valuePlan restPlan slot state resident access permitted shape stored selected discard continued residentIH bodyIH =>
    obtain ⟨replacement, middleEnv, middleMap, evaluated, residentTyped, pending, firstProgress⟩ := residentIH environmentTyped
    have middleTyped := pending.dropDataResult residentTyped
    obtain ⟨loan, binder, found, own, unique, within, base⟩ := access.uniqueTarget middleTyped.toStoreTyped
    have canonical := access.canonicalTarget middleTyped.toStoreTyped
    obtain ⟨known, _, _, resolved, allowed, _⟩ := middleTyped.toStoreTyped.resolveAccessMasked access
    have storedBinder : middle.storage (.binder binder) = some slot := by simpa [base] using stored
    obtain ⟨rootSlot, rootStored, path, _, _⟩ := (by simpa [Context.Target, base] using canonical)
    have equal : rootSlot = slot := Option.some.inj (rootStored.symm.trans storedBinder)
    subst rootSlot
    obtain ⟨root, rootStored, rootTyped, _⟩ := middleTyped.cells binder slot storedBinder
    obtain ⟨old, read, oldTyped⟩ := path.resident rootTyped selected
    have raw : middleEnv.at (middleMap.origin target) = some old := by
      simp [Environment.at, Interpretation.origin, base, rootStored, read]
    obtain ⟨updated, written, updatedTyped, writeProgress, evolution⟩ := middleTyped.writeTarget canonical base shape
      residentTyped.resident found own unique within permitted (fun _ _ _ _ _ => .inl Initialization.Complete.full)
    obtain ⟨value, after, afterMap, bodyEval, resultTyped, afterTyped, bodyProgress⟩ := bodyIH updatedTyped
    exact ⟨value, after, afterMap, .assignIndirect evaluated resolved allowed (middleTyped.toStoreTyped.permits known permitted)
      raw (oldTyped.referenceFree shape) (discard.realized oldTyped).destroys written bodyEval, resultTyped, afterTyped,
      firstProgress.trans (writeProgress.trans bodyProgress evolution.supply) (evaluated.storage environmentTyped.residents.valid).2.supply⟩
  | endOwn selected handle unprotected ready continued ih =>
    obtain ⟨loan, found, _⟩ := (environmentTyped.source.slots _ (List.mem_of_getElem? selected)).2 _ handle
    obtain ⟨ended, endedOwn, endedTyped⟩ := environmentTyped.endOwn found unprotected
    obtain ⟨value, after, afterMap, evaluated, result, typed, progress⟩ := ih endedTyped
    exact ⟨value, after, afterMap, .endOwn ((environmentTyped.toStoreTyped.endSlot selected handle ready).trans endedOwn) evaluated,
      result, typed, (StateProgress.endOwn environmentTyped.source endedOwn).trans progress
        (by simp only [Environment.endOwn_state endedOwn, Nat.le_refl])⟩
  | endAfter evaluated selected handle unprotected ready ih =>
    obtain ⟨value, middle, middleMap, executed, result, typed, progress⟩ := ih environmentTyped
    obtain ⟨loan, found, _⟩ := (typed.source.slots _ (List.mem_of_getElem? selected)).2 _ handle
    obtain ⟨after, ended, afterTyped⟩ := typed.endOwn found unprotected
    have tailProgress := StateProgress.endOwn typed.source ended
    have afterResult := result.transport tailProgress.history tailProgress.interpretation
    exact ⟨value, after, middleMap, .endAfter executed ((typed.toStoreTyped.endSlot selected handle ready).trans ended)
      (afterTyped.resultUsable afterResult), afterResult, afterTyped,
      progress.trans tailProgress (executed.storage environmentTyped.residents.valid).2.supply⟩
  | raiseSupply typed larger ih =>
    obtain ⟨value, after, afterMap, evaluated, result, typed, progress⟩ := ih environmentTyped
    have tailProgress := StateProgress.raiseSupply (interpretation := afterMap) (environment := after) typed.source larger
    exact ⟨value, after, afterMap, evaluated, result.transport tailProgress.history tailProgress.interpretation,
      typed.raiseSupply larger, progress.trans tailProgress (evaluated.storage environmentTyped.residents.valid).2.supply⟩
  | @sequence expected home context middleContext afterContext heldNodes first rest discardedType result firstPlan restPlan head drop tail headIH tailIH =>
    obtain ⟨discarded, middle, middleMap, headEval, discardedTyped, middleTyped, firstProgress⟩ := headIH environmentTyped
    obtain ⟨disposed, disposal, disposedTyped⟩ := middleTyped.disposeResult discardedTyped drop
    have disposalProgress := StateProgress.dispose (interpretation := middleMap) (reference := discardedType.reference) middleTyped.source disposal
    obtain ⟨value, after, afterMap, tailEval, result, typed, lastProgress⟩ := tailIH disposedTyped
    exact ⟨value, after, afterMap, .sequence headEval disposal tailEval, result, typed,
      firstProgress.trans (disposalProgress.trans lastProgress (by simp only [disposal.storage.supply, Nat.le_refl]))
        (headEval.storage environmentTyped.residents.valid).2.supply⟩
  | @bind expected home context middle bodyAfter heldNodes mutable name annotation initial body localType result initialPlan bodyPlan initialized annotated continued cleanup initialIH bodyIH =>
    obtain ⟨resident, middleEnv, middleMap, initialEval, residentTyped, middleTyped, firstProgress⟩ := initialIH environmentTyped
    have bound := middleTyped.bind residentTyped name mutable
    obtain ⟨value, localAfter, afterMap, bodyEval, resultTyped, localTyped, bodyProgress⟩ := bodyIH bound
    obtain ⟨after, trace, cleaned, afterTyped⟩ := localTyped.cleanup 1 cleanup
    have cleanProgress := StateProgress.cleanup (interpretation := afterMap) localTyped.source cleaned
    have afterResult := resultTyped.transport cleanProgress.history cleanProgress.interpretation
    have bindProgress := StateProgress.bind (interpretation := middleMap) (environment := middleEnv) middleTyped.source name mutable localType resident
    exact ⟨value, after, afterMap,
      .bind initialEval (middleTyped.resultUsable residentTyped) bodyEval ⟨trace, cleaned⟩ (afterTyped.resultUsable afterResult),
      afterResult, afterTyped,
      firstProgress.trans (bindProgress.trans (bodyProgress.trans cleanProgress (bodyEval.storage bound.residents.valid).2.supply)
        (Nat.le_succ _)) (initialEval.storage environmentTyped.residents.valid).2.supply⟩
  | tuple head tail shape headIH tailIH =>
    obtain ⟨first, middle, middleMap, headEval, firstTyped, middleTyped, firstProgress⟩ := headIH environmentTyped
    obtain ⟨rest, after, afterMap, tailEval, restTyped, afterTyped, tailProgress⟩ :=
      tailIH middleMap middle held (middleTyped.dropDataResult firstTyped)
    have result {resultContext : Context} := ResultTyped.ofData (interpretation := afterMap) (context := resultContext) (.tuple firstTyped.resident restTyped.data.1) shape
    exact ⟨_, after, afterMap, .tuple headEval tailEval ⟨firstTyped.shape.2, restTyped.data.2⟩,
      result, (restTyped.dropData afterTyped).dataResult result,
      firstProgress.trans tailProgress (headEval.storage environmentTyped.residents.valid).2.supply⟩
  | @array home context afterContext heldNodes elements element length plans residents finite size ih =>
    obtain ⟨values, after, afterMap, evaluated, valuesTyped, afterTyped, progress⟩ := ih interpretation environment held environmentTyped
    have dataTyped : ResultsTyped program afterMap afterContext values ((List.replicate length element).map ResultType.data) := by
      simpa only [List.map_replicate] using valuesTyped
    have result {resultContext : Context} := ResultTyped.ofData (interpretation := afterMap) (context := resultContext) (.array dataTyped.data.1 finite size) finite.dataShape
    exact ⟨_, after, afterMap, .array evaluated dataTyped.data.2, result,
      (dataTyped.dropData (by simpa only [List.map_replicate] using afterTyped)).dataResult result, progress⟩
  | @construct home context afterContext heldNodes identity tag declaration schema fields plans declared chosen finite capability visible access residents ih =>
    obtain ⟨values, after, afterMap, evaluated, valuesTyped, afterTyped, progress⟩ := ih interpretation environment held environmentTyped
    have dataTyped : ResultsTyped program afterMap afterContext values ((schema.residents.map (fun field => field.type)).map ResultType.data) := by
      simpa only [List.map_map, Function.comp_def] using valuesTyped
    have result {resultContext : Context} := ResultTyped.ofData (interpretation := afterMap) (context := resultContext) (.nominal declared chosen finite dataTyped.data.1) (by trivial)
    exact ⟨_, after, afterMap, .construct evaluated dataTyped.data.2, result,
      (dataTyped.dropData (by simpa only [List.map_map, Function.comp_def] using afterTyped)).dataResult result, progress⟩
  | field source discard selected shape ih =>
    obtain ⟨parent, after, afterMap, evaluated, parentTyped, afterTyped, progress⟩ := ih environmentTyped
    obtain ⟨value, indexed, found, resident, replace⟩ := selected.access parentTyped.resident
    obtain ⟨residual, cleared, residualTyped⟩ := replace .vacant .vacant .vacant
    have result {resultContext : Context} := ResultTyped.ofData (interpretation := afterMap) (context := resultContext) resident shape
    exact ⟨value, after, afterMap, .field evaluated (by simp [Value.readField, indexed, found])
      (by simp [Value.takeField, indexed, found, cleared])
      (.data (residualTyped.referenceFree parentTyped.shape.1) (discard.realized residualTyped).destroys) ((resident.referenceFree shape).usable after),
      result, (afterTyped.dropDataResult parentTyped).dataResult result, progress⟩
  | constant declared visible resolved structural shape initialized ih =>
    obtain ⟨value, after, afterMap, evaluated, result, afterTyped, progress⟩ := ih environmentTyped.hide
    exact ⟨value, environment.resume after, afterMap, .constant declared evaluated result.shape.2,
      result.resume, StateTyped.resume environmentTyped.toStoreTyped afterTyped progress (evaluated.storage environmentTyped.residents.valid.hide).2.supply,
      progress.resume environmentTyped.source⟩
  | nil | expectedNil =>
    rename_i interpretation environment held typed
    exact ⟨[], environment, interpretation, .nil, .nil, by simpa [resultNodes, referenceValues] using typed, .refl typed.source⟩
  | cons head tail headIH tailIH
  | expectedCons head tail headIH tailIH =>
    rename_i interpretation environment held typed
    obtain ⟨first, middle, middleMap, headEval, firstTyped, middleTyped, firstProgress⟩ := headIH typed
    obtain ⟨rest, after, afterMap, tailEval, restTyped, afterTyped, tailProgress⟩ := tailIH middleMap middle _ middleTyped
    have firstResult := firstTyped.transport tailProgress.history tailProgress.interpretation
    have usable := firstResult.usable afterTyped.toStoreTyped (fun node member =>
      afterTyped.heldOwn node (List.mem_append_left _ (List.mem_append_right _ member)))
      (fun node member => afterTyped.heldReady node (List.mem_append_left _ (List.mem_append_right _ member)))
    exact ⟨first :: rest, after, afterMap, .cons headEval tailEval usable, .cons firstResult restTyped,
      by simpa only [resultNodes, List.flatMap_cons, referenceValues, List.append_assoc] using afterTyped,
      firstProgress.trans tailProgress (headEval.storage typed.residents.valid).2.supply⟩
  | empty =>
    rename_i interpretation environment held typed value resident plain bindings body selected
    simp [selectArm] at selected
  | patternWildcard => exact ⟨_, .wildcard⟩
  | patternBinder name => exact ⟨_, .binder name⟩
  | patternNode headSource constants ih =>
    obtain ⟨fields, normalized⟩ := ih
    exact ⟨_, .node normalized⟩
  | patternConstant typed ih =>
    obtain ⟨value, after, afterMap, evaluated, _⟩ := ih StateTyped.empty
    obtain ⟨declaration, declared, resolved⟩ := typed.constantDeclared rfl
    exact ⟨_, .constantValue declared resolved evaluated⟩
  | patternsEmpty => exact ⟨[], .patternsNil⟩
  | patternsCons head tail headIH tailIH =>
    obtain ⟨first, firstNormalized⟩ := headIH
    obtain ⟨rest, restNormalized⟩ := tailIH
    exact ⟨first :: rest, .patternsCons firstNormalized restNormalized⟩
  | armsEmpty => exact ⟨[], .armsNil⟩
  | armsCons head tail headIH tailIH =>
    obtain ⟨first, firstNormalized⟩ := headIH
    obtain ⟨rest, restNormalized⟩ := tailIH
    exact ⟨(_, _) :: rest, .armsCons firstNormalized restNormalized⟩
  | @assign expected home context middle afterContext heldNodes place expression rest slot target result valuePlan restPlan indices state slots resident selected writable available path shape data discard free written continued residentIH bodyIH =>
    obtain ⟨replacement, middleEnv, middleMap, evaluated, residentTyped, pending, firstProgress⟩ := residentIH environmentTyped
    have middleTyped := pending.dropDataResult residentTyped
    obtain ⟨old, updated, resolved, raw, disposal, changed, updatedTyped, custody⟩ :=
      middleTyped.toStoreTyped.assignData middleTyped.custody selected available path data shape written residentTyped.resident discard free
    have state : StateTyped program middleMap _ heldNodes updated held :=
      { updatedTyped with
        heldShape := middleTyped.heldShape
        heldOwn := middleTyped.heldOwn
        heldReady := fun node member => (middleTyped.heldReady node member).writeSlot
          middleTyped.source selected written rfl rfl available free
        custody := custody }
    have writeProgress := StateProgress.replaceSlot (interpretation := middleMap) middleTyped.source selected written rfl
      (congrArg List.length (Environment.writeAddress_loans changed))
    obtain ⟨value, after, afterMap, bodyEval, resultTyped, afterTyped, bodyProgress⟩ := bodyIH state
    exact ⟨value, after, afterMap, .assign evaluated resolved
      (middleTyped.toStoreTyped.ownerFree (origin := ⟨.binder slot.binder, indices⟩) (middleTyped.source.member_known _ (lookup_member selected)) free)
      raw disposal (residentTyped.shape.2.usable _) changed bodyEval, resultTyped, afterTyped,
      firstProgress.trans (writeProgress.trans bodyProgress (by simp only [(Environment.writeAddress_update changed).supply, Nat.le_refl]))
        (evaluated.storage environmentTyped.residents.valid).2.supply⟩
  | @assignReference expected home context middle afterContext heldNodes place expression rest slot referent mode node result valuePlan restPlan slots resident selected writable direct shape free unprotected ready written continued residentIH bodyIH =>
    obtain ⟨replacement, middleEnv, middleMap, evaluated, residentTyped, middleTyped, firstProgress⟩ := residentIH environmentTyped
    have custody : Custody middleEnv (held ++ [replacement]) := by
      simpa only [residentTyped.shape.1, Value.referenceValues] using middleTyped.custody
    obtain ⟨old, disposed, updated, resolved, raw, disposal, changed, updatedTyped, custody⟩ :=
      middleTyped.toStoreTyped.assignReference_custody (home := home) custody selected direct shape written residentTyped free ready
    have protectedOwn : ∀ other ∈ heldNodes ++ [node], (middle.dispose slot.reference).Own other := by
      intro other member
      exact (middleTyped.heldOwn other member).dispose slot.reference
        (fun ended handle equal => unprotected ended handle (equal ▸ member))
    have state : StateTyped program middleMap ((middle.dispose slot.reference).withSlots slots) heldNodes updated held := by
      refine { updatedTyped with heldShape := ?_, heldOwn := ?_, heldReady := ?_, custody := custody }
      · apply List.append_cancel_right
        simpa only [List.map_append, residentTyped.referenceValues] using middleTyped.heldShape
      · intro other member
        exact protectedOwn other (List.mem_append_left _ member)
      · intro other member
        exact ((middleTyped.heldReady other (List.mem_append_left _ member)).dispose slot.reference).writeSlot
          (nextSlot := { slot with initialization := .full, reference := some node })
          (slot := slot) (name := place.root) (indices := []) (next := .full)
          (middleTyped.source.dispose slot.reference)
          (by cases slot.reference <;> exact selected) (by cases slot.reference <;> exact written)
          rfl rfl (.here _) (free.dispose slot.reference)
    have disposedAllowed : disposed.ResultUsable replacement := by
      have initial := middleTyped.resultUsable residentTyped
      rw [residentTyped.shape.1] at initial ⊢
      refine ⟨?_, disposal.restored initial.2⟩
      have own := updatedTyped.usable (protectedOwn node (by simp))
      simpa only [Environment.Usable, Environment.writeAddress_loans changed] using own
    have disposalProgress : StateProgress middle (middle.dispose slot.reference) middleEnv disposed middleMap middleMap :=
      .dispose middleTyped.source disposal
    have disposedSource := middleTyped.source.dispose slot.reference
    have writeProgress := StateProgress.replaceSlot (interpretation := middleMap) disposedSource
      (show lookup place.root (middle.dispose slot.reference).bindings = some slot by cases slot.reference <;> exact selected)
      (show replaceBinding place.root {slot with initialization := .full, reference := some node}
        (middle.dispose slot.reference).bindings = some slots by cases slot.reference <;> exact written) rfl
      (congrArg List.length (Environment.writeAddress_loans changed))
    obtain ⟨value, after, afterMap, bodyEval, resultTyped, afterTyped, bodyProgress⟩ := bodyIH state
    exact ⟨value, after, afterMap, .assign evaluated resolved
      (middleTyped.toStoreTyped.ownerFree (origin := ⟨.binder slot.binder, []⟩) (middleTyped.source.member_known _ (lookup_member selected)) free)
      raw disposal disposedAllowed changed bodyEval, resultTyped, afterTyped,
      firstProgress.trans (disposalProgress.trans (writeProgress.trans bodyProgress
        (by simp only [(Environment.writeAddress_update changed).supply, Nat.le_refl])) (by simp only [disposal.storage.supply, Nat.le_refl]))
        (evaluated.storage environmentTyped.residents.valid).2.supply⟩
  | @call home context middle bodyAfter heldNodes identity arguments argumentTypes result argumentPlans bodyPlan declaration declared visible distinct initialized inputs body resultType origin cleanup inputsIH bodyIH =>
    have types := inputs.expected_types _ rfl
    obtain ⟨values, middleEnv, middleMap, inputsEval, inputsTyped, middleTyped, inputsProgress⟩ := inputsIH interpretation environment held environmentTyped
    have hiddenArguments := inputsTyped.hide
    obtain ⟨boundMap, bound, prepareProgress⟩ := middleTyped.hide.prepare hiddenArguments types.symm
    obtain ⟨value, localAfter, afterMap, bodyEval, resultTyped, localTyped, bodyProgress⟩ := bodyIH bound
    obtain ⟨after, trace, cleaned, afterTyped⟩ := localTyped.cleanup declaration.parameters.length cleanup
    have lengths : ((declaration.parameters.map Prod.fst).zip values).length = declaration.parameters.length := by
      have valuesLength := inputsTyped.length
      have parameterLength := congrArg List.length types
      simp only [List.length_map] at parameterLength
      simp [List.length_zip, valuesLength, parameterLength]
    have cleanedActual : Cleans program ((declaration.parameters.map Prod.fst).zip values).length localAfter trace after := by
      rw [lengths]; exact cleaned
    have bodySupply := (bodyEval.storage bound.residents.valid).2.supply
    have cleanProgress := StateProgress.cleanup (interpretation := afterMap) localTyped.source cleaned
    have localProgress := prepareProgress.trans (bodyProgress.trans cleanProgress bodySupply)
      (Environment.prepare_supply _ _)
    have evolved := ((bodyEval.storage bound.residents.valid).2.scope middleTyped.residents.valid.hide _).trans
      (cleanedActual.suffix_evolution localTyped.residents.valid)
    have afterResult := resultTyped.transport cleanProgress.history cleanProgress.interpretation
    exact ⟨value, middleEnv.resume after, afterMap, .call declared inputsEval bodyEval ⟨trace, cleanedActual⟩
      (afterTyped.resultUsable afterResult), afterResult.resume,
      StateTyped.resume middleTyped.toStoreTyped afterTyped localProgress evolved.supply,
      inputsProgress.trans (localProgress.resume middleTyped.source) (inputsEval.storage environmentTyped.residents.valid).2.supply⟩
  | applyPatterns argumentsTyped shape nonempty constants covered bodies argumentsIH constantsIH bodiesIH =>
    obtain ⟨normalized, normalization⟩ := constantsIH
    obtain ⟨values, middle, middleMap, argumentsEval, valuesTyped, pending, argumentsProgress⟩ :=
      argumentsIH interpretation environment held environmentTyped
    have middleTyped := valuesTyped.dropData pending
    have subjectTyped := valuesTyped.data.1.argument
    obtain ⟨bindings, body, selected⟩ := (covered normalized normalization).selectArm subjectTyped
    obtain ⟨value, localAfter, after, afterMap, bodyEval, result, afterTyped, cleanup, consumed, bodyProgress⟩ :=
      bodiesIH normalized normalization middleMap middle held middleTyped _ subjectTyped (valuesTyped.data.2.argument) bindings body selected
    exact ⟨value, after, afterMap, .applyPatterns normalization argumentsEval valuesTyped.data.2 consumed bodyEval cleanup
      (afterTyped.resultUsable result), result, afterTyped,
      argumentsProgress.trans bodyProgress (argumentsEval.storage environmentTyped.residents.valid).2.supply⟩
  | @clause expected home context bodyAfter afterContext heldNodes subject result previous pattern bodyExpression rest bindingTypes patternTyped distinct useful bodyTyped cleanup joined tailTyped bodyIH tailIH =>
    rename_i interpretation environment held environmentTyped value valueTyped plain bindings body selected
    simp only [selectArm] at selected
    split at selected
    next matched found =>
      cases Option.some.inj selected
      obtain ⟨bindingResidents, consumedTrace, consumed⟩ := patternTyped.consume valueTyped found
      obtain ⟨bindingsTyped, zipped⟩ := patternTyped.consume_results (interpretation := interpretation) (context := context) valueTyped plain found
      have pending : StateTyped program interpretation context
          (heldNodes ++ resultNodes (bindingTypes.map (fun binding => ResultType.data binding.2.type))) environment
          (held ++ referenceValues (bindings.map Prod.snd)) := by
        rw [bindingsTyped.referenceValues]
        have nodes : resultNodes (bindingTypes.map (fun binding => ResultType.data binding.2.type)) = [] := by
          simpa only [List.map_map, Function.comp_def] using resultNodes_data (bindingTypes.map (fun binding => binding.2.type))
        simpa [nodes] using environmentTyped
      obtain ⟨boundMap, bound, prepareProgress⟩ := pending.prepare (parameters := bindingTypes) bindingsTyped (by simp [ResultType.data])
      rw [zipped] at bound prepareProgress
      obtain ⟨resultValue, localAfter, afterMap, bodyEval, resultTyped, localTyped, bodyProgress⟩ := bodyIH bound
      obtain ⟨after, trace, cleaned, afterTyped⟩ := localTyped.cleanup bindingTypes.length cleanup
      have cleanProgress := StateProgress.cleanup (interpretation := afterMap) localTyped.source cleaned
      have joinProgress := StateProgress.join (interpretation := afterMap) (environment := after) afterTyped.source joined
      have combined := (prepareProgress.trans (bodyProgress.trans cleanProgress
        (bodyEval.storage bound.residents.valid).2.supply) (Environment.prepare_supply _ _)).trans joinProgress
          (Nat.le_trans (Environment.prepare_supply _ _) (Nat.le_trans (bodyEval.storage bound.residents.valid).2.supply
            (by rw [cleaned.suffix.supply]; exact Nat.le_refl _)))
      have afterResult := (resultTyped.transport cleanProgress.history cleanProgress.interpretation).transport
        joinProgress.history joinProgress.interpretation
      exact ⟨resultValue, localAfter, after, afterMap, bodyEval, afterResult, afterTyped.join joined,
        ⟨trace, by rw [bindingResidents.length]; exact cleaned⟩, .hit found consumed, combined⟩
    next missed found =>
      obtain ⟨resultValue, localAfter, after, afterMap, evaluated, resultTyped, typed, cleanup, consumed, progress⟩ :=
        tailIH interpretation environment held environmentTyped value valueTyped plain bindings body selected
      exact ⟨resultValue, localAfter, after, afterMap, evaluated, resultTyped, typed, cleanup, .miss found consumed, progress⟩

/-- Connected correctness includes actual root storage and retirement effects.
The coarse frame excludes initial owner roots and live unique-target roots;
it grants no access authority. Source and runtime supplies never decrease. -/
theorem correctness {context afterContext : Context} {heldNodes : List Nat}
    {expression : Expr} {result : ResultType} {plan : CorePlan} {expected : Option Ty}
    (admitted : HasType program home context heldNodes expression result afterContext plan expected)
    {interpretation : Interpretation} {environment : Environment} {held : List Value}
    (environmentTyped : StateTyped program interpretation context heldNodes environment held) :
    ∃ value after afterMap, Evaluates program environment ⟨expression, plan⟩ value after ∧
      ResultTyped program afterMap afterContext value result ∧
      StateTyped program afterMap afterContext (heldNodes ++ result.nodes) after (held ++ value.referenceValues) ∧
      StateProgress context afterContext environment after interpretation afterMap ∧ environment.Evolution after ∧
      after.ResultUsable value ∧
      ∀ other otherAfter, Evaluates program environment ⟨expression, plan⟩ other otherAfter → other = value ∧ otherAfter = after := by
  obtain ⟨value, after, afterMap, evaluated, resultTyped, afterTyped, progress⟩ := execution_correctness admitted environmentTyped
  exact ⟨value, after, afterMap, evaluated, resultTyped, afterTyped, progress,
    (evaluated.storage environmentTyped.residents.valid).2, afterTyped.resultUsable resultTyped,
    fun _ _ other => other.deterministic evaluated⟩

/-- The prior root-renaming observation is recovered for reference-free sources
and declarations. Loan-free starting worlds, not a successful final-world premise,
produce the empty history needed by the conservative agreement specialization. -/
theorem correctness_referenceFree {context afterContext : Context} {heldNodes : List Nat}
    {expression : Expr} {result : ResultType} {plan : CorePlan} {expected : Option Ty}
    (admitted : HasType program home context heldNodes expression result afterContext plan expected)
    {interpretation : Interpretation} {environment : Environment} {held : List Value}
    (environmentTyped : StateTyped program interpretation context heldNodes environment held)
    (declarations : program.ReferenceFree) (source : expression.ReferenceFree) (empty : environment.loans = []) :
    ∃ value after afterMap, Evaluates program environment ⟨expression, plan⟩ value after ∧
      ResultTyped program afterMap afterContext value result ∧ value.ReferenceFree ∧
      StateTyped program afterMap afterContext (heldNodes ++ result.nodes) after (held ++ value.referenceValues) ∧
      ∀ otherEnvironment, environment.Agrees otherEnvironment → otherEnvironment.loans = [] →
        ∃ otherAfter, Evaluates program otherEnvironment ⟨expression, plan⟩ value otherAfter ∧
          EnvironmentTyped program otherAfter afterContext.erase ∧ after.Agrees otherAfter := by
  obtain ⟨value, after, afterMap, evaluated, resultTyped, afterTyped, _⟩ := correctness admitted environmentTyped
  have plain := evaluated.referenceFree_of_empty (evaluated.empty_of_referenceFree declarations source empty)
  refine ⟨value, after, afterMap, evaluated, resultTyped, plain, afterTyped, ?_⟩
  intro otherEnvironment same otherEmpty
  obtain ⟨_, otherAfter, otherEval, afterSame, _⟩ := evaluated.referenceFree_source_agreement declarations source empty otherEmpty same
  exact ⟨otherAfter, otherEval, afterTyped.residents.agrees afterSame, afterSame⟩

/-- Admission constructs execution and restored protected results. Every active
loan remains addressable; shared loans additionally remain readable. -/
theorem correctness_noDangling {context afterContext : Context} {heldNodes : List Nat}
    {expression : Expr} {result : ResultType} {plan : CorePlan} {expected : Option Ty}
    (admitted : HasType program home context heldNodes expression result afterContext plan expected)
    {interpretation : Interpretation} {environment : Environment} {held : List Value}
    (environmentTyped : StateTyped program interpretation context heldNodes environment held) :
    ∃ value after, Evaluates program environment ⟨expression, plan⟩ value after ∧ after.ResultUsable value ∧
      ∀ (node : Nat) (loan : Loan), after.loans[node]? = some loan → loan.own = true →
        ∃ target type state, after.at loan.target = some target ∧ ResidentTyped program state target type ∧
          FiniteLayout program.target program.data type ∧
          (loan.mode = .shared → after.readAddress loan.target = some target ∧ ValueHasType program target type) := by
  obtain ⟨value, after, _, evaluated, _, afterTyped, _, _, usable, _⟩ := correctness admitted environmentTyped
  exact ⟨value, after, evaluated, usable, fun _ _ found own => afterTyped.toStoreTyped.noDangling found own⟩

/-- Execution preserves canonical root-to-referent typing for every active binder
loan, without requiring unique referents to be fully initialized. -/
theorem correctness_canonicalTargets {context afterContext : Context} {heldNodes : List Nat}
    {expression : Expr} {result : ResultType} {plan : CorePlan} {expected : Option Ty}
    (admitted : HasType program home context heldNodes expression result afterContext plan expected)
    {interpretation : Interpretation} {environment : Environment} {held : List Value}
    (environmentTyped : StateTyped program interpretation context heldNodes environment held) :
    ∃ (value : Value) (after : Environment) (afterMap : Interpretation), Evaluates program environment ⟨expression, plan⟩ value after ∧
      ∀ (node : Nat) (loan : SourceLoan), afterContext.loans[node]? = some loan → loan.own = true →
        ∀ binder, loan.target.base = .binder binder →
          ∃ slot state resident, afterContext.storage (.binder binder) = some slot ∧
            CanonicalPath program slot.type loan.target.fields loan.referent ∧
            slot.initialization.Access loan.target.fields state ∧
            after.at (afterMap.origin loan.target) = some resident ∧ ResidentTyped program state resident loan.referent := by
  obtain ⟨value, after, afterMap, evaluated, _, afterTyped, _⟩ := correctness admitted environmentTyped
  exact ⟨value, after, afterMap, evaluated, fun _ _ found own _ base => afterTyped.toStoreTyped.canonicalTargets found own base⟩


/-- Active shared targets exclude any overlapping owner mutation or disposal.
Inactive ancestors alone impose no reservation; active descendants keep theirs. -/
theorem Environment.borrowed_owner_exclusion {environment : Environment} {node : Nat} {loan : Loan} {address : Address}
    (found : environment.loans[node]? = some loan) (own : loan.own = true)
    (overlap : ¬ address.Apart loan.target) : ¬ environment.OwnerFree address :=
  fun free => overlap (free node loan found own)

theorem HasType.place_initialized {context after : Context} {held : List Nat} {expression : Expr}
    {result : ResultType} {plan : CorePlan} {expected : Option Ty} (typed : HasType program home context held expression result after plan expected)
    {place : Place} (source : expression = .read place ∨ expression = .move place) :
    ∃ slot indices state, lookup place.root context.bindings = some slot ∧ slot.initialization.Access indices state ∧
      state.Complete ∧ (place.fields = [] → indices = []) := by
  induction typed using HasType.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) (motive_5 := fun _ _ _ _ => True) (motive_6 := fun _ _ _ _ => True)
    generalizing place with
  | read selected access initialized path =>
    rcases source with same | impossible
    · cases same
      exact ⟨_, _, _, selected, access, initialized, by intro fields; rw [fields] at path; cases path; rfl⟩
    · cases impossible
  | implicitMove _ _ ih =>
    rcases source with same | impossible
    · cases same; exact ih (.inr rfl)
    · cases impossible
  | move selected access initialized path =>
    rcases source with impossible | same
    · cases impossible
    · cases same
      exact ⟨_, _, _, selected, access, initialized, by intro fields; rw [fields] at path; cases path; rfl⟩
  | copyShared selected direct handle shape initialized =>
    rcases source with same | impossible
    · cases same; exact ⟨_, [], _, selected, .here _, initialized, fun _ => rfl⟩
    · cases impossible
  | moveReference selected direct handle shape initialized =>
    rcases source with impossible | same
    · cases impossible
    · cases same; exact ⟨_, [], _, selected, .here _, initialized, fun _ => rfl⟩
  | endOwn _ _ _ _ _ ih => exact ih source
  | endAfter _ _ _ _ _ ih => exact ih source
  | raiseSupply _ _ ih => exact ih source
  | expectedData _ _ ih | expectedMove _ ih => exact ih source
  | reborrow access =>
    rcases source with same | impossible
    · cases same
      cases access with
      | dereference selected direct handle shape initialized =>
        exact ⟨_, [], _, selected, .here _, initialized, fun _ => rfl⟩
    · cases impossible
  | _ => first | trivial | rcases source with impossible | impossible <;> cases impossible

/-- Neither whole nor nested source use recovers lost initialization certainty,
including under checked administrative end metadata. -/
theorem HasType.no_use_maybe {context after : Context} {held : List Nat} {place : Place} {slot : Slot}
    {result : ResultType} {plan : CorePlan} {expected : Option Ty}
    (found : lookup place.root context.bindings = some slot) (unknown : slot.initialization = .maybe) :
    (¬ HasType program home context held (.read place) result after plan expected) ∧
      (¬ HasType program home context held (.move place) result after plan expected) := by
  have exclude {expression : Expr} (admitted : HasType program home context held expression result after plan expected)
      (source : expression = .read place ∨ expression = .move place) : False := by
    obtain ⟨selectedSlot, indices, state, selected, access, initialized, _⟩ := admitted.place_initialized source
    cases Option.some.inj (selected.symm.trans found)
    rw [unknown] at access
    cases (Initialization.Access.maybe_iff.mp access).2
    cases initialized
  exact ⟨fun admitted => exclude admitted (.inl rfl), fun admitted => exclude admitted (.inr rfl)⟩

theorem HasType.read_root_complete {context after : Context} {held : List Nat} {root : String} {slot : Slot}
    {result : ResultType} {plan : CorePlan} {expected : Option Ty}
    (admitted : HasType program home context held (.read ⟨root, []⟩) result after plan expected)
    (found : lookup root context.bindings = some slot) : slot.initialization.Complete := by
  obtain ⟨selectedSlot, indices, state, selected, access, initialized, rootPath⟩ := admitted.place_initialized (.inl rfl)
  cases Option.some.inj (selected.symm.trans found)
  have empty := rootPath rfl
  subst indices
  cases access
  exact initialized

theorem HasType.no_whole_read_after_clear {context after : Context} {cleared : List (String × Slot)} {held : List Nat} {root : String}
    {slot : Slot} {indices : List Nat} {selected : Initialization} {result : ResultType} {plan : CorePlan} {expected : Option Ty}
    (valid : context.WellFormed program) (found : lookup root context.bindings = some slot)
    (access : slot.initialization.Access indices selected)
    (changed : replaceBinding root { slot with initialization := slot.initialization.write indices .vacant }
      context.bindings = some cleared) :
    ¬ HasType program home (context.withSlots cleared) held (.read ⟨root, []⟩) result after plan expected := by
  intro admitted
  have distinct : (cleared.map fun binding => binding.2.binder).Nodup := by
    rw [replaceBinding_map_same Slot.binder found changed rfl]
    exact valid.distinct
  apply access.clear_incomplete
  apply admitted.read_root_complete (slot := {slot with initialization := slot.initialization.write indices .vacant})
  rw [context.withSlots_bindings distinct]
  exact replaceBinding_lookup changed

/-- Closed executions retire every temporary cell. The final source context may
retain inactive loan history and an advanced binder supply, rather than falsely
requiring those append-only resources to equal their initial empty state. -/
theorem closed_correctness {expression : Expr} {result : ResultType} {afterContext : Context} {plan : CorePlan} {expected : Option Ty}
    (admitted : HasType program home .empty [] expression result afterContext plan expected) :
    ∃ value after afterMap, Evaluates program .empty ⟨expression, plan⟩ value after ∧
      ResultTyped program afterMap afterContext value result ∧ StateTyped program afterMap afterContext result.nodes after value.referenceValues ∧
      after.bindings = [] ∧ (∀ root, after.store root = none) ∧ after.ResultUsable value ∧
      ∀ other otherAfter, Evaluates program .empty ⟨expression, plan⟩ other otherAfter → other = value ∧ otherAfter = after := by
  obtain ⟨value, after, afterMap, evaluated, resultTyped, afterTyped, _, storage, usable, unique⟩ := correctness admitted StateTyped.empty
  exact ⟨value, after, afterMap, evaluated, resultTyped, by simpa using afterTyped, storage.bindings,
    fun root => storage.fresh root (Nat.zero_le _), usable, unique⟩

theorem HasType.literal_valid {context after : Context} {held : List Nat} {expression : Expr} {result : ResultType} {plan : CorePlan} {expected : Option Ty}
    (typed : HasType program home context held expression result after plan expected) :
    match expression with
    | .integer type magnitude => type.Contains program.target magnitude
    | .character number => UnicodeScalar number
    | _ => True := by
  induction typed using HasType.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) (motive_5 := fun _ _ _ _ => True) (motive_6 := fun _ _ _ _ => True) <;>
    first | assumption | trivial | (split <;> simp_all)

/-- Exact literal admission boundaries remain independent of administrative metadata. -/
theorem integer_admission (context : Context) (held : List Nat) (type : IntegerType) (magnitude : Nat) :
    (∃ result after plan, HasType program home context held (.integer type magnitude) result after plan) ↔ type.Contains program.target magnitude := by
  constructor
  · rintro ⟨_, _, _, admitted⟩; exact admitted.literal_valid
  · intro fits; exact ⟨_, _, _, .integer fits⟩

theorem character_admission (context : Context) (held : List Nat) (number : Nat) :
    (∃ result after plan, HasType program home context held (.character number) result after plan) ↔ UnicodeScalar number := by
  constructor
  · rintro ⟨_, _, _, admitted⟩; exact admitted.literal_valid
  · intro valid; exact ⟨_, _, _, .character valid⟩

theorem unit_agreement : HasType program home .empty [] .unit (.data .unit) .empty .leaf ∧
    ∀ value, Evaluates program .empty ⟨.unit, .leaf⟩ value .empty ↔ value = .unit := by
  refine ⟨.unit, fun value => ⟨?_, ?_⟩⟩
  · intro evaluated; exact (evaluated.deterministic (.unit (program := program))).1
  · intro same; subst value; exact .unit

/-- Administrative metadata has no store/root effect and preserves the exact
source node. This is storage transparency, not arbitrary-plan erasure equivalence. -/
theorem Evaluates.endOwn_transparent {before after : Environment} {expression : Expr} {plan : CorePlan} {slot : Nat} {value : Value}
    (evaluated : Evaluates program before ⟨expression, .endOwn slot plan⟩ value after) :
    ∃ ended, before.SameStorage ended ∧ Evaluates program ended ⟨expression, plan⟩ value after := by
  cases evaluated with
  | endOwn ended continued => exact ⟨_, Environment.endSlot_storage ended, continued⟩

theorem Evaluates.endAfter_transparent {before after : Environment} {expression : Expr} {plan : CorePlan} {slot : Nat} {value : Value}
    (evaluated : Evaluates program before ⟨expression, .endAfter slot plan⟩ value after) :
    ∃ middle, Evaluates program before ⟨expression, plan⟩ value middle ∧ middle.SameStorage after ∧ after.ResultUsable value := by
  cases evaluated with
  | endAfter body ended usable => exact ⟨_, body, Environment.endSlot_storage ended, usable⟩

/-- Expected checking cannot silently change either reference mode or referent type.
Pattern results inherit the expectation through every normalized, nonempty arm;
constant normalization is obtained from the same producer's correctness proof. -/
theorem HasType.expected_type {context after : Context} {held : List Nat} {expression : Expr}
    {result : ResultType} {plan : CorePlan} {expected : Option Ty}
    (typed : HasType program home context held expression result after plan expected) :
    ∀ type, expected = some type → result.type = type := by
  induction typed using HasType.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ result _ arms _ expected _ =>
      arms ≠ [] → ∀ type, expected = some type → result.type = type)
    (motive_4 := fun _ source plan _ => ∃ normalized, NormalizesPattern program source plan normalized)
    (motive_5 := fun _ sources plans _ => ∃ normalized, NormalizesPatterns program sources plans normalized)
    (motive_6 := fun _ sources plans _ => ∃ normalized, NormalizesArms program sources plans normalized) with
  | applyPatterns argumentsTyped shape nonempty constants covered bodies argumentsIH constantsIH bodiesIH =>
    obtain ⟨normalized, normalization⟩ := constantsIH
    have normalizedNonempty : normalized ≠ [] := by
      intro empty
      cases empty
      cases normalization
      exact nonempty rfl
    exact bodiesIH normalized normalization normalizedNonempty
  | empty =>
    rename_i nonempty type same
    exact False.elim (nonempty rfl)
  | clause patternTyped distinct useful bodyTyped cleanup joined tailTyped bodyIH tailIH =>
    rename_i nonempty type same
    exact bodyIH type same
  | patternWildcard => exact ⟨_, .wildcard⟩
  | patternBinder name => exact ⟨_, .binder name⟩
  | patternNode headSource constants ih =>
    obtain ⟨fields, normalized⟩ := ih
    exact ⟨_, .node normalized⟩
  | patternConstant typed ih =>
    obtain ⟨value, after, afterMap, evaluated, _⟩ := execution_correctness typed StateTyped.empty
    obtain ⟨declaration, declared, resolved⟩ := typed.constantDeclared rfl
    exact ⟨_, .constantValue declared resolved evaluated⟩
  | patternsEmpty => exact ⟨[], .patternsNil⟩
  | patternsCons head tail headIH tailIH =>
    obtain ⟨first, firstNormalized⟩ := headIH
    obtain ⟨rest, restNormalized⟩ := tailIH
    exact ⟨first :: rest, .patternsCons firstNormalized restNormalized⟩
  | armsEmpty => exact ⟨[], .armsNil⟩
  | armsCons head tail headIH tailIH =>
    obtain ⟨first, firstNormalized⟩ := headIH
    obtain ⟨rest, restNormalized⟩ := tailIH
    exact ⟨(_, _) :: rest, .armsCons firstNormalized restNormalized⟩
  | _ => first | trivial | assumption | (intro type same; cases same <;> rfl)

/-- Shape certificate for a compulsory reborrow, allowing only the existing
checked administrative endings around its execution plan. -/
inductive CorePlan.Reborrows (mode : BorrowMode) : CorePlan → Prop where
  | direct : Reborrows mode (.reborrow mode)
  | endOwn {plan : CorePlan} (slot : Nat) (body : Reborrows mode plan) :
      Reborrows mode (.endOwn slot plan)
  | endAfter {plan : CorePlan} (slot : Nat) (body : Reborrows mode plan) :
      Reborrows mode (.endAfter slot plan)

/-- Actual plan selection, not merely rejection of one competing leaf: a
reference-expected bare read always reborrows in the requested mode. -/
theorem HasType.reference_read_selection {context after : Context} {held : List Nat}
    {expression : Expr} {result : ResultType} {plan : CorePlan} {expected : Option Ty}
    (typed : HasType program home context held expression result after plan expected)
    {place : Place} {referent : Ty} {mode : BorrowMode} :
    expression = .read place → expected = some (.reference referent mode) → plan.Reborrows mode := by
  induction typed using HasType.rec
    (motive_2 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) (motive_5 := fun _ _ _ _ => True) (motive_6 := fun _ _ _ _ => True) with
  | reborrow => intro _ same; cases same; exact .direct
  | endOwn _ _ _ _ _ ih => intro source expected; exact .endOwn _ (ih source expected)
  | endAfter _ _ _ _ _ ih => intro source expected; exact .endAfter _ (ih source expected)
  | raiseSupply _ _ ih => exact ih
  | expectedData typed shape ih =>
    intro _ expected
    have same := Option.some.inj expected
    rw [same] at shape
    exact False.elim shape
  | _ => first | trivial | (intro source expected; cases source <;> cases expected)

end Grounded
