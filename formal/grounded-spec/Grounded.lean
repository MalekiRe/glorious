/-!
# Scalar expressions, immutable lexical composition, and tuples

Normative basis: language specification §§2.3, 3.2–3.4, 4.1–4.2, 5.1, 5.3, 7.2–7.3.
Integer literals have an explicitly selected fixed-width type and a decoded
nonnegative magnitude. Character literals have a decoded scalar number.
Local names are already decoded identifiers; lookup selects the nearest binder.
Token decoding, inference, prefix negation, target-size integers, floating
conversion, static strings, and physical realization remain outside this subset.
Admission has no execution premise. No prior specification modules are imported.
-/

namespace Grounded

inductive Width where
  | w8 | w16 | w32 | w64 | w128

def Width.bits : Width → Nat
  | .w8 => 8
  | .w16 => 16
  | .w32 => 32
  | .w64 => 64
  | .w128 => 128

structure IntegerType where
  signed : Bool
  width : Width

/-- Mathematical scalar range; there is no implicit wrapping of literals. -/
def IntegerType.Contains (type : IntegerType) (value : Int) : Prop :=
  let bound : Int := 2 ^ (type.width.bits - if type.signed then 1 else 0)
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

inductive Ty where
  | unit
  | integer (type : IntegerType)
  | character
  | tuple (head : Ty) (tail : List Ty)

/-- §7.2: scalar owned use may copy; scalar values may also be discarded.
Keep this explicit at consumers rather than making all future types copyable. -/
inductive Duplicable : Ty → Prop where
  | unit : Duplicable .unit
  | integer (type : IntegerType) : Duplicable (.integer type)
  | character : Duplicable .character
  | tuple {head : Ty} {tail : List Ty} (first : Duplicable head)
      (rest : ∀ type ∈ tail, Duplicable type) : Duplicable (.tuple head tail)

inductive Value where
  | unit
  | integer (type : IntegerType) (number : Int)
  | character (number : Nat)
  | tuple (head : Value) (tail : List Value)

/-- Nearest lexical binding wins, including in shadowing initializers. -/
def lookup {α : Type} (name : String) : List (String × α) → Option α
  | [] => none
  | (key, value) :: rest => if name = key then some value else lookup name rest

mutual
inductive HasType : List (String × Ty) → Expr → Ty → Prop where
  | unit {context : List (String × Ty)} : HasType context .unit .unit
  | integer {context : List (String × Ty)} {type : IntegerType} {magnitude : Nat}
      (fits : type.Contains magnitude) :
      HasType context (.integer type magnitude) (.integer type)
  | character {context : List (String × Ty)} {number : Nat}
      (valid : UnicodeScalar number) :
      HasType context (.character number) .character
  | group {context : List (String × Ty)} {body : Expr} {type : Ty}
      (typed : HasType context body type) : HasType context (.group body) type
  | local {context : List (String × Ty)} {name : String} {type : Ty}
      (selected : lookup name context = some type) (copyable : Duplicable type) :
      HasType context (.local name) type
  | sequence {context : List (String × Ty)} {first rest : Expr} {discarded type : Ty}
      (head : HasType context first discarded) (drop : Duplicable discarded)
      (tail : HasType context rest type) : HasType context (.sequence first rest) type
  | bind {context : List (String × Ty)} {name : String} {initial body : Expr}
      {localType type : Ty} (initialized : HasType context initial localType)
      (drop : Duplicable localType)
      (continued : HasType ((name, localType) :: context) body type) :
      HasType context (.bind name initial body) type
  | tuple {context : List (String × Ty)} {head : Expr} {tail : List Expr}
      {first : Ty} {rest : List Ty} (headTyped : HasType context head first)
      (tailTyped : HasTypes context tail rest) :
      HasType context (.tuple head tail) (.tuple first rest)
  | project {context : List (String × Ty)} {body : Expr} {index : Nat}
      {first type : Ty} {rest : List Ty} (source : HasType context body (.tuple first rest))
      (discard : Duplicable (.tuple first rest)) (selected : (first :: rest)[index]? = some type) :
      HasType context (.project body index) type

inductive HasTypes : List (String × Ty) → List Expr → List Ty → Prop where
  | nil {context : List (String × Ty)} : HasTypes context [] []
  | cons {context : List (String × Ty)} {head : Expr} {tail : List Expr}
      {first : Ty} {rest : List Ty} (headTyped : HasType context head first)
      (tailTyped : HasTypes context tail rest) :
      HasTypes context (head :: tail) (first :: rest)
end

mutual
inductive ValueHasType : Value → Ty → Prop where
  | unit : ValueHasType .unit .unit
  | integer {type : IntegerType} {number : Int}
      (fits : type.Contains number) :
      ValueHasType (.integer type number) (.integer type)
  | character {number : Nat} (valid : UnicodeScalar number) :
      ValueHasType (.character number) .character
  | tuple {head : Value} {tail : List Value} {first : Ty} {rest : List Ty}
      (headTyped : ValueHasType head first) (tailTyped : ValuesHaveTypes tail rest) :
      ValueHasType (.tuple head tail) (.tuple first rest)

inductive ValuesHaveTypes : List Value → List Ty → Prop where
  | nil : ValuesHaveTypes [] []
  | cons {head : Value} {tail : List Value} {first : Ty} {rest : List Ty}
      (headTyped : ValueHasType head first) (tailTyped : ValuesHaveTypes tail rest) :
      ValuesHaveTypes (head :: tail) (first :: rest)
end

inductive EnvironmentTyped : List (String × Value) → List (String × Ty) → Prop where
  | nil : EnvironmentTyped [] []
  | cons {name : String} {value : Value} {type : Ty}
      {environment : List (String × Value)} {context : List (String × Ty)}
      (resident : ValueHasType value type) (rest : EnvironmentTyped environment context) :
      EnvironmentTyped ((name, value) :: environment) ((name, type) :: context)

mutual
inductive Evaluates : List (String × Value) → Expr → Value → Prop where
  | unit {environment : List (String × Value)} : Evaluates environment .unit .unit
  | integer {environment : List (String × Value)} {type : IntegerType} {magnitude : Nat}
      (fits : type.Contains magnitude) :
      Evaluates environment (.integer type magnitude) (.integer type magnitude)
  | character {environment : List (String × Value)} {number : Nat}
      (valid : UnicodeScalar number) :
      Evaluates environment (.character number) (.character number)
  | group {environment : List (String × Value)} {body : Expr} {value : Value}
      (evaluated : Evaluates environment body value) :
      Evaluates environment (.group body) value
  | local {environment : List (String × Value)} {name : String} {value : Value}
      (selected : lookup name environment = some value) :
      Evaluates environment (.local name) value
  | sequence {environment : List (String × Value)} {first rest : Expr}
      {discarded value : Value} (head : Evaluates environment first discarded)
      (tail : Evaluates environment rest value) :
      Evaluates environment (.sequence first rest) value
  | bind {environment : List (String × Value)} {name : String} {initial body : Expr}
      {resident value : Value} (initialized : Evaluates environment initial resident)
      (continued : Evaluates ((name, resident) :: environment) body value) :
      Evaluates environment (.bind name initial body) value
  | tuple {environment : List (String × Value)} {head : Expr} {tail : List Expr}
      {first : Value} {rest : List Value} (headEval : Evaluates environment head first)
      (tailEval : EvaluatesMany environment tail rest) :
      Evaluates environment (.tuple head tail) (.tuple first rest)
  | project {environment : List (String × Value)} {body : Expr} {index : Nat}
      {first value : Value} {rest : List Value}
      (source : Evaluates environment body (.tuple first rest))
      (selected : (first :: rest)[index]? = some value) :
      Evaluates environment (.project body index) value

inductive EvaluatesMany : List (String × Value) → List Expr → List Value → Prop where
  | nil {environment : List (String × Value)} : EvaluatesMany environment [] []
  | cons {environment : List (String × Value)} {head : Expr} {tail : List Expr}
      {first : Value} {rest : List Value} (headEval : Evaluates environment head first)
      (tailEval : EvaluatesMany environment tail rest) :
      EvaluatesMany environment (head :: tail) (first :: rest)
end

/-- Every admitted expression in a typed lexical environment terminates with a
correctly typed, unique result. Binding constructs its body's typed environment;
no continuation-readiness or successful-evaluation premise is assumed. -/
theorem correctness {context : List (String × Ty)} {expression : Expr} {type : Ty}
    (admitted : HasType context expression type)
    {environment : List (String × Value)} (environmentTyped : EnvironmentTyped environment context) :
    ∃ value, Evaluates environment expression value ∧ ValueHasType value type ∧
      ∀ other, Evaluates environment expression other → other = value := by
  induction admitted using HasType.rec
    (motive_2 := fun context expressions types _ =>
      ∀ environment, EnvironmentTyped environment context →
        ∃ values, EvaluatesMany environment expressions values ∧ ValuesHaveTypes values types ∧
          ∀ other, EvaluatesMany environment expressions other → other = values)
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
    have resident : ∃ value, lookup name environment = some value ∧ ValueHasType value type := by
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
  | @project context body index first type rest source discard selected sourceIH =>
    obtain ⟨aggregate, sourceEval, aggregateTyped, sourceUnique⟩ := sourceIH environmentTyped
    cases aggregateTyped with
    | tuple headTyped tailTyped =>
      have selectTyped : ∀ {types : List Ty} {values : List Value},
          ValuesHaveTypes values types → ∀ (index : Nat) (type : Ty), types[index]? = some type →
            ∃ value, values[index]? = some value ∧ ValueHasType value type := by
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
    (admitted : HasType [] expression type) :
    ∃ value, Evaluates [] expression value ∧ ValueHasType value type ∧
      ∀ other, Evaluates [] expression other → other = value :=
  correctness admitted .nil

/-- Exact admission boundary, in every lexical context and at every width. -/
theorem integer_admission (context : List (String × Ty)) (type : IntegerType) (magnitude : Nat) :
    (∃ result, HasType context (.integer type magnitude) result) ↔ type.Contains magnitude := by
  constructor
  · rintro ⟨_, admitted⟩
    cases admitted with
    | integer fits => exact fits
  · intro fits
    exact ⟨_, .integer fits⟩

theorem character_admission (context : List (String × Ty)) (number : Nat) :
    (∃ result, HasType context (.character number) result) ↔ UnicodeScalar number := by
  constructor
  · rintro ⟨_, admitted⟩
    cases admitted with
    | character valid => exact valid
  · intro valid
    exact ⟨_, .character valid⟩

/-- The original unit subset retains precisely its admission and evaluation meaning. -/
theorem unit_agreement : HasType [] .unit .unit ∧
    ∀ value, Evaluates [] .unit value ↔ value = .unit := by
  obtain ⟨value, evaluated, _, unique⟩ := closed_correctness HasType.unit
  have same : value = .unit := by cases evaluated; rfl
  refine ⟨.unit, fun other => ⟨?_, ?_⟩⟩
  · intro evaluation
    exact (unique other evaluation).trans same
  · intro equal
    subst other
    exact .unit

end Grounded
