import Grounded.Types

/-! Logical values: structural equality, resident typing and positional access.
No allocation, reference, loan or expression-execution interpretation is supplied. -/
namespace Grounded

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

/-- Owned-use permission is invariant under the possible typings of one value.
In particular, an empty array's unconstrained element type cannot hide an owner. -/
theorem ValueHasType.use_permission {program : Program} {value : Value} {type : Ty}
    {permission : UsePermission} (typed : ValueHasType program value type) :
    ∀ {other}, ValueHasType program value other →
      UsePermitted program.data permission type → UsePermitted program.data permission other := by
  induction typed using ValueHasType.rec
    (motive_2 := fun values types _ => ∀ others, ValuesHaveTypes program values others →
      (∀ type ∈ types, UsePermitted program.data permission type) →
      ∀ type ∈ others, UsePermitted program.data permission type) with
  | unit => intro other typed allowed; cases typed; exact allowed
  | integer => intro other typed allowed; cases typed; exact allowed
  | character => intro other typed allowed; cases typed; exact allowed
  | tuple first rest firstIH restIH =>
    intro other typed allowed
    cases typed with
    | tuple otherFirst otherRest =>
      cases allowed with
      | tuple firstAllowed restAllowed =>
        exact .tuple (firstIH otherFirst firstAllowed) (restIH _ otherRest restAllowed)
  | array residents finite size ih =>
    intro other typed allowed
    cases typed with
    | @array values element length otherResidents otherFinite otherSize =>
      by_cases zero : length = 0
      · subst length; exact .emptyArray element
      · have permissions := ih _ otherResidents (by
          intro type member
          cases allowed with
          | array count permission =>
            obtain ⟨_, rfl⟩ := List.mem_replicate.mp member
            exact permission
          | emptyArray => simp at member)
        exact .array length (permissions element (by simp [zero]))
  | nominal declared chosen finite residents ih =>
    intro other typed allowed
    cases typed
    exact allowed
  | nil => rename_i others typed allowed type member; cases typed; cases member
  | cons head tail headIH tailIH =>
    rename_i others typed allowed type member
    cases typed with
    | cons otherHead otherTail =>
      cases member with
      | head => exact headIH otherHead (allowed _ (by simp))
      | tail _ member => exact tailIH _ otherTail (fun type included => allowed type (by simp [included])) type member

/-- Returning or reannotating the same resident preserves its full principal,
including an inferred exact class. No successful disposal is assumed. -/
theorem ValueHasType.principal {program : Program} {value : Value} {before after : Ty}
    {principal : Principal} (original : ValueHasType program value before)
    (returned : ValueHasType program value after) (classified : before.HasPrincipal program.data principal) :
    after.HasPrincipal program.data principal := by
  intro permission
  constructor
  · intro allowed
    exact (classified permission).mp (returned.use_permission original allowed)
  · intro allowed
    exact original.use_permission returned ((classified permission).mpr allowed)

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

variable {program : Program}

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

/-- A resident's typing derives finite declared layout, including inactive
nominal variants; storage retains this fact when the resident moves out. -/
theorem ValueHasType.finite {value : Value} {type : Ty}
    (typed : ValueHasType program value type) : FiniteLayout program.target program.data type := by
  induction typed using ValueHasType.rec
    (motive_2 := fun _ types _ => ∀ type ∈ types, FiniteLayout program.target program.data type) with
  | unit => exact .unit
  | integer => exact .integer _
  | character => exact .character
  | tuple head tail headIH tailIH => exact .tuple headIH tailIH
  | array residents element size ih => exact .array element size
  | nominal declared chosen finite residents ih => exact finite
  | nil => rename_i type member; cases member
  | cons head tail headIH tailIH =>
    rename_i type member
    cases member with
    | head => exact headIH
    | tail _ member => exact tailIH type member

/-- A returned resident determines one principal under every valid typing.
Finite permission decisions come from the resident, not a future-state premise. -/
theorem ValueHasType.principal_exists {program : Program} {value : Value} {type : Ty}
    (resident : ValueHasType program value type) :
    ∃ principal, type.HasPrincipal program.data principal ∧
      ∀ originalType originalPrincipal, ValueHasType program value originalType →
        originalType.HasPrincipal program.data originalPrincipal → originalPrincipal = principal := by
  obtain ⟨principal, classified, _⟩ := Ty.principal_exists resident.finite
  exact ⟨principal, classified, fun _ _ original originalClass =>
    (original.principal resident originalClass).unique classified⟩

/-- One actual resident has one ownership class, independently of its valid
annotation. This is derived from resident typing, not stored as runtime metadata. -/
def Value.PrincipalConsistent (program : Program) (value : Value) : Prop :=
  ∃ type, ValueHasType program value type ∧
    ∃ principal, type.HasPrincipal program.data principal ∧
      ∀ originalType originalPrincipal, ValueHasType program value originalType →
        originalType.HasPrincipal program.data originalPrincipal → originalPrincipal = principal

theorem ValueHasType.principal_consistent {value : Value} {type : Ty}
    (resident : ValueHasType program value type) : value.PrincipalConsistent program :=
  ⟨type, resident, resident.principal_exists⟩


theorem ValuesHaveTypes.member {values : List Value} {types : List Ty}
    (typed : ValuesHaveTypes program values types) {value : Value} (member : value ∈ values) :
    ∃ type, type ∈ types ∧ ValueHasType program value type := by
  induction values generalizing types with
  | nil => cases member
  | cons head tail ih =>
    cases typed with
    | cons headTyped tailTyped =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, by simp, headTyped⟩
      · obtain ⟨type, included, resident⟩ := ih tailTyped member
        exact ⟨type, by simp [included], resident⟩


theorem ValuesHaveTypes.member_permission {values : List Value} {types : List Ty}
    (typed : ValuesHaveTypes program values types)
    (allowed : ∀ type ∈ types, UsePermitted program.data .discard type)
    {value : Value} (member : value ∈ values) :
    ∃ type, ValueHasType program value type ∧ UsePermitted program.data .discard type := by
  obtain ⟨type, included, resident⟩ := typed.member member
  exact ⟨type, resident, allowed type included⟩

/-- Structural disposal admits every active resident, including private fields.
This is destruction authority, not source projection visibility. -/
theorem ValueHasType.children_disposable {value : Value} {type : Ty}
    (typed : ValueHasType program value type) (allowed : UsePermitted program.data .discard type)
    {child : Value} (member : child ∈ value.children) :
    ∃ childType, ValueHasType program child childType ∧ UsePermitted program.data .discard childType := by
  cases typed with
  | unit => cases member
  | integer fits => cases member
  | character valid => cases member
  | tuple head tail =>
    cases allowed with
    | tuple first rest =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, head, first⟩
      · exact tail.member_permission rest member
  | array residents finite size =>
    apply residents.member_permission ?_ member
    intro type included
    cases allowed with
    | array length permission => obtain ⟨_, rfl⟩ := List.mem_replicate.mp included; exact permission
    | emptyArray => simp at included
  | @nominal identity tag declaration schema values declared chosen finite residents =>
    cases allowed with
    | nominal otherDeclared restriction fields =>
      cases Option.some.inj (declared.symm.trans otherDeclared)
      apply residents.member_permission ?_ member
      intro type included
      obtain ⟨field, fieldMember, rfl⟩ := List.mem_map.mp included
      apply fields _ ?_ field fieldMember
      cases shape : declaration.shape with
      | «structure» fs =>
        cases tag <;> simp [DataDecl.constructor, shape] at chosen
        subst schema
        simp [DataDecl.schemas, shape]
      | enumeration variants nonExhaustive =>
        cases tag <;> simp only [DataDecl.constructor, shape] at chosen
        · contradiction
        · simpa [DataDecl.schemas, shape] using List.mem_of_getElem? chosen
end Grounded
