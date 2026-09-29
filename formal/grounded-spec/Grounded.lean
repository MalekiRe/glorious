/-!
# Target-indexed scalar expressions, immutable composition, tuples and arrays

Normative basis: language specification §§2.3, 3.2–3.4, 4.1–4.4, 5.1, 5.3,
7.2–7.3 and 13.1 (target-representable array lengths). Integer literals have
a selected type and a decoded nonnegative magnitude; characters a decoded
scalar number. Local names are decoded identifiers; lookup selects the nearest
binder. Token decoding, inference, prefix negation, floating conversion, static
strings and physical realization remain outside this subset.
Admission has no execution premise. No prior specification modules are imported.
-/

namespace Grounded

/-- The selected target supplies its positive pointer width (§4.4). Other ABI
properties enter when their semantic consumers are introduced. -/
structure Target where
  pointerBits : Nat
  positive : 0 < pointerBits

variable {target : Target}

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

inductive Expr where
  | unit
  | integer (type : IntegerType) (magnitude : Nat)
  | character (number : Nat)
  | group (body : Expr)
  | local (name : String)
  | sequence (first rest : Expr)
  | bind (name : String) (initial body : Expr)
  | tuple (head : Expr) (tail : List Expr)
  | project (body : Expr) (index : Nat)
  | array (elements : List Expr)

inductive Ty where
  | unit
  | integer (type : IntegerType)
  | character
  | tuple (head : Ty) (tail : List Ty)
  | array (element : Ty) (length : Nat)

/-- §7.2: scalar owned use may copy; scalar values may also be discarded.
Keep this explicit at consumers rather than making all future types copyable. -/
inductive Duplicable : Ty → Prop where
  | unit : Duplicable .unit
  | integer (type : IntegerType) : Duplicable (.integer type)
  | character : Duplicable .character
  | tuple {head : Ty} {tail : List Ty} (first : Duplicable head)
      (rest : ∀ type ∈ tail, Duplicable type) : Duplicable (.tuple head tail)
  | array {element : Ty} (length : Nat) (resident : Duplicable element) :
      Duplicable (.array element length)
  | emptyArray (element : Ty) : Duplicable (.array element 0)

inductive Value where
  | unit
  | integer (type : IntegerType) (number : Int)
  | character (number : Nat)
  | tuple (head : Value) (tail : List Value)
  | array (elements : List Value)

/-- Nearest lexical binding wins, including in shadowing initializers. -/
def lookup {α : Type} (name : String) : List (String × α) → Option α
  | [] => none
  | (key, value) :: rest => if name = key then some value else lookup name rest

mutual
inductive HasType (target : Target) : List (String × Ty) → Expr → Ty → Prop where
  | unit {context : List (String × Ty)} : HasType target context .unit .unit
  | integer {context : List (String × Ty)} {type : IntegerType} {magnitude : Nat}
      (fits : type.Contains target magnitude) :
      HasType target context (.integer type magnitude) (.integer type)
  | character {context : List (String × Ty)} {number : Nat}
      (valid : UnicodeScalar number) :
      HasType target context (.character number) .character
  | group {context : List (String × Ty)} {body : Expr} {type : Ty}
      (typed : HasType target context body type) : HasType target context (.group body) type
  | local {context : List (String × Ty)} {name : String} {type : Ty}
      (selected : lookup name context = some type) (copyable : Duplicable type) :
      HasType target context (.local name) type
  | sequence {context : List (String × Ty)} {first rest : Expr} {discarded type : Ty}
      (head : HasType target context first discarded) (drop : Duplicable discarded)
      (tail : HasType target context rest type) : HasType target context (.sequence first rest) type
  | bind {context : List (String × Ty)} {name : String} {initial body : Expr}
      {localType type : Ty} (initialized : HasType target context initial localType)
      (drop : Duplicable localType)
      (continued : HasType target ((name, localType) :: context) body type) :
      HasType target context (.bind name initial body) type
  | tuple {context : List (String × Ty)} {head : Expr} {tail : List Expr}
      {first : Ty} {rest : List Ty} (headTyped : HasType target context head first)
      (tailTyped : HasTypes target context tail rest) :
      HasType target context (.tuple head tail) (.tuple first rest)
  | project {context : List (String × Ty)} {body : Expr} {index : Nat}
      {first type : Ty} {rest : List Ty} (source : HasType target context body (.tuple first rest))
      (discard : Duplicable (.tuple first rest)) (selected : (first :: rest)[index]? = some type) :
      HasType target context (.project body index) type
  | array {context : List (String × Ty)} {elements : List Expr} {element : Ty} {length : Nat}
      (residents : HasTypes target context elements (List.replicate length element))
      (size : length < 2 ^ target.pointerBits) :
      HasType target context (.array elements) (.array element length)

inductive HasTypes (target : Target) : List (String × Ty) → List Expr → List Ty → Prop where
  | nil {context : List (String × Ty)} : HasTypes target context [] []
  | cons {context : List (String × Ty)} {head : Expr} {tail : List Expr}
      {first : Ty} {rest : List Ty} (headTyped : HasType target context head first)
      (tailTyped : HasTypes target context tail rest) :
      HasTypes target context (head :: tail) (first :: rest)
end

mutual
inductive ValueHasType (target : Target) : Value → Ty → Prop where
  | unit : ValueHasType target .unit .unit
  | integer {type : IntegerType} {number : Int}
      (fits : type.Contains target number) :
      ValueHasType target (.integer type number) (.integer type)
  | character {number : Nat} (valid : UnicodeScalar number) :
      ValueHasType target (.character number) .character
  | tuple {head : Value} {tail : List Value} {first : Ty} {rest : List Ty}
      (headTyped : ValueHasType target head first) (tailTyped : ValuesHaveTypes target tail rest) :
      ValueHasType target (.tuple head tail) (.tuple first rest)
  | array {values : List Value} {element : Ty} {length : Nat}
      (residents : ValuesHaveTypes target values (List.replicate length element))
      (size : length < 2 ^ target.pointerBits) :
      ValueHasType target (.array values) (.array element length)

inductive ValuesHaveTypes (target : Target) : List Value → List Ty → Prop where
  | nil : ValuesHaveTypes target [] []
  | cons {head : Value} {tail : List Value} {first : Ty} {rest : List Ty}
      (headTyped : ValueHasType target head first) (tailTyped : ValuesHaveTypes target tail rest) :
      ValuesHaveTypes target (head :: tail) (first :: rest)
end

inductive EnvironmentTyped (target : Target) : List (String × Value) → List (String × Ty) → Prop where
  | nil : EnvironmentTyped target [] []
  | cons {name : String} {value : Value} {type : Ty}
      {environment : List (String × Value)} {context : List (String × Ty)}
      (resident : ValueHasType target value type) (rest : EnvironmentTyped target environment context) :
      EnvironmentTyped target ((name, value) :: environment) ((name, type) :: context)

mutual
inductive Evaluates (target : Target) : List (String × Value) → Expr → Value → Prop where
  | unit {environment : List (String × Value)} : Evaluates target environment .unit .unit
  | integer {environment : List (String × Value)} {type : IntegerType} {magnitude : Nat}
      (fits : type.Contains target magnitude) :
      Evaluates target environment (.integer type magnitude) (.integer type magnitude)
  | character {environment : List (String × Value)} {number : Nat}
      (valid : UnicodeScalar number) :
      Evaluates target environment (.character number) (.character number)
  | group {environment : List (String × Value)} {body : Expr} {value : Value}
      (evaluated : Evaluates target environment body value) :
      Evaluates target environment (.group body) value
  | local {environment : List (String × Value)} {name : String} {value : Value}
      (selected : lookup name environment = some value) :
      Evaluates target environment (.local name) value
  | sequence {environment : List (String × Value)} {first rest : Expr}
      {discarded value : Value} (head : Evaluates target environment first discarded)
      (tail : Evaluates target environment rest value) :
      Evaluates target environment (.sequence first rest) value
  | bind {environment : List (String × Value)} {name : String} {initial body : Expr}
      {resident value : Value} (initialized : Evaluates target environment initial resident)
      (continued : Evaluates target ((name, resident) :: environment) body value) :
      Evaluates target environment (.bind name initial body) value
  | tuple {environment : List (String × Value)} {head : Expr} {tail : List Expr}
      {first : Value} {rest : List Value} (headEval : Evaluates target environment head first)
      (tailEval : EvaluatesMany target environment tail rest) :
      Evaluates target environment (.tuple head tail) (.tuple first rest)
  | project {environment : List (String × Value)} {body : Expr} {index : Nat}
      {first value : Value} {rest : List Value}
      (source : Evaluates target environment body (.tuple first rest))
      (selected : (first :: rest)[index]? = some value) :
      Evaluates target environment (.project body index) value
  | array {environment : List (String × Value)} {elements : List Expr} {values : List Value}
      (residents : EvaluatesMany target environment elements values) :
      Evaluates target environment (.array elements) (.array values)

inductive EvaluatesMany (target : Target) : List (String × Value) → List Expr → List Value → Prop where
  | nil {environment : List (String × Value)} : EvaluatesMany target environment [] []
  | cons {environment : List (String × Value)} {head : Expr} {tail : List Expr}
      {first : Value} {rest : List Value} (headEval : Evaluates target environment head first)
      (tailEval : EvaluatesMany target environment tail rest) :
      EvaluatesMany target environment (head :: tail) (first :: rest)
end

/-- Every admitted expression in a typed lexical environment terminates with a
correctly typed, unique result. Binding constructs its body's typed environment;
no continuation-readiness or successful-evaluation premise is assumed. -/
theorem correctness {context : List (String × Ty)} {expression : Expr} {type : Ty}
    (admitted : HasType target context expression type)
    {environment : List (String × Value)} (environmentTyped : EnvironmentTyped target environment context) :
    ∃ value, Evaluates target environment expression value ∧ ValueHasType target value type ∧
      ∀ other, Evaluates target environment expression other → other = value := by
  induction admitted using HasType.rec
    (motive_2 := fun context expressions types _ =>
      ∀ environment, EnvironmentTyped target environment context →
        ∃ values, EvaluatesMany target environment expressions values ∧ ValuesHaveTypes target values types ∧
          ∀ other, EvaluatesMany target environment expressions other → other = values)
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
  | group typed ih =>
    obtain ⟨value, evaluated, valueTyped, unique⟩ := ih environmentTyped
    refine ⟨value, .group evaluated, valueTyped, ?_⟩
    intro other evaluation
    cases evaluation with
    | group inner => exact unique other inner
  | @«local» context name type selected copyable =>
    have resident : ∃ value, lookup name environment = some value ∧ ValueHasType target value type := by
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
  | bind initialized drop continued initialIH bodyIH =>
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
  | array residents size ih =>
    obtain ⟨values, evaluated, typed, unique⟩ := ih environment environmentTyped
    refine ⟨.array values, .array evaluated, .array typed size, ?_⟩
    intro other evaluation
    cases evaluation with
    | array elements =>
      have same := unique _ elements
      subst same
      rfl
  | @project context body index first type rest source discard selected sourceIH =>
    obtain ⟨aggregate, sourceEval, aggregateTyped, sourceUnique⟩ := sourceIH environmentTyped
    cases aggregateTyped with
    | tuple headTyped tailTyped =>
      have selectTyped : ∀ {types : List Ty} {values : List Value},
          ValuesHaveTypes target values types → ∀ (index : Nat) (type : Ty), types[index]? = some type →
            ∃ value, values[index]? = some value ∧ ValueHasType target value type := by
        intro types
        induction types with
        | nil =>
          intro values typed index type selection
          cases typed
          simp at selection
        | cons head tail ih =>
          intro values typed index type selection
          cases typed with
          | cons valueTyped restTyped =>
            cases index with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at selection
              subst type
              exact ⟨_, rfl, valueTyped⟩
            | succ index => exact ih restTyped index type selection
      obtain ⟨value, fieldSelected, valueTyped⟩ :=
        selectTyped (.cons headTyped tailTyped) index type selected
      refine ⟨value, .project sourceEval fieldSelected, valueTyped, ?_⟩
      intro other evaluated
      cases evaluated with
      | project otherSource otherSelected =>
        have same := sourceUnique _ otherSource
        cases same
        exact Option.some.inj (otherSelected.symm.trans fieldSelected)
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
    (admitted : HasType target [] expression type) :
    ∃ value, Evaluates target [] expression value ∧ ValueHasType target value type ∧
      ∀ other, Evaluates target [] expression other → other = value :=
  correctness admitted .nil

/-- Exact admission boundary, in every lexical context and at every width. -/
theorem integer_admission (context : List (String × Ty)) (type : IntegerType) (magnitude : Nat) :
    (∃ result, HasType target context (.integer type magnitude) result) ↔ type.Contains target magnitude := by
  constructor
  · rintro ⟨_, admitted⟩
    cases admitted with
    | integer fits => exact fits
  · intro fits
    exact ⟨_, .integer fits⟩

theorem character_admission (context : List (String × Ty)) (number : Nat) :
    (∃ result, HasType target context (.character number) result) ↔ UnicodeScalar number := by
  constructor
  · rintro ⟨_, admitted⟩
    cases admitted with
    | character valid => exact valid
  · intro valid
    exact ⟨_, .character valid⟩

/-- The original unit subset retains precisely its admission and evaluation meaning. -/
theorem unit_agreement : HasType target [] .unit .unit ∧
    ∀ value, Evaluates target [] .unit value ↔ value = .unit := by
  obtain ⟨value, evaluated, _, unique⟩ := closed_correctness HasType.unit
  have same : value = .unit := by cases evaluated; rfl
  refine ⟨.unit, fun other => ⟨?_, ?_⟩⟩
  · intro evaluation
    exact (unique other evaluation).trans same
  · intro equal
    subst other
    exact .unit

end Grounded
