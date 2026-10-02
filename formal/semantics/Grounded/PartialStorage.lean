import Grounded.RuntimeHeap
import Grounded.Values

/-! Resident availability is distinct from the lifetime of its storage cell.
A hole contains no old value. Partial aggregates retain only their actual
remaining residents and constructor identity. -/
namespace Grounded

inductive Initialization where
  | absent
  | present
  | maybe
  | fields (states : List Initialization)

mutual
inductive Initialization.Ready : Initialization → Prop where
  | present : Initialization.Ready .present
  | fields {states : List Initialization} (residents : InitializationsReady states) :
      Initialization.Ready (.fields states)
inductive InitializationsReady : List Initialization → Prop where
  | nil : InitializationsReady []
  | cons {head : Initialization} {tail : List Initialization}
      (first : Initialization.Ready head) (rest : InitializationsReady tail) :
      InitializationsReady (head :: tail)
end

/-- Uncertainty never supplies the availability required by a source access. -/
theorem Initialization.maybe_not_ready : ¬ Initialization.Ready .maybe := by
  intro ready
  cases ready



/- Possible occupancy is not definite availability. In particular, a joined
mask can describe a resident without granting a source read or move. -/
mutual
inductive Initialization.MayRead : Initialization → Prop where
  | present : Initialization.MayRead .present
  | maybe : Initialization.MayRead .maybe
  | fields {states : List Initialization} (residents : InitializationsMayRead states) :
      Initialization.MayRead (.fields states)
inductive InitializationsMayRead : List Initialization → Prop where
  | nil : InitializationsMayRead []
  | cons {head : Initialization} {tail : List Initialization}
      (first : Initialization.MayRead head) (rest : InitializationsMayRead tail) :
      InitializationsMayRead (head :: tail)
end



inductive PartialValue where
  | hole
  | resident (value : Value)
  | tuple (head : PartialValue) (tail : List PartialValue)
  | nominal (identity : Nat) (tag : Option Nat) (fields : List PartialValue)

mutual
def PartialValue.read : PartialValue → Option Value
  | .hole => none
  | .resident value => some value
  | .tuple head tail => head.read.bind (fun first =>
      readPartialValues tail |>.map (fun rest => .tuple first rest))
  | .nominal identity tag fields => (readPartialValues fields).map (.nominal identity tag)
termination_by value => sizeOf value

def readPartialValues : List PartialValue → Option (List Value)
  | [] => some []
  | head :: tail => head.read.bind (fun first => (readPartialValues tail).map (first :: ·))
termination_by values => sizeOf values
end

mutual
inductive PartialValue.Typed (program : Program) : PartialValue → Ty → Initialization → Prop where
  | hole (type : Ty) : PartialValue.Typed program .hole type .absent
  | resident {value : Value} {type : Ty} (typed : ValueHasType program value type) :
      PartialValue.Typed program (.resident value) type .present
  | tuple {head : PartialValue} {tail : List PartialValue} {first : Ty} {rest : List Ty}
      {headState : Initialization} {tailStates : List Initialization}
      (headTyped : PartialValue.Typed program head first headState)
      (tailTyped : PartialValuesTyped program tail rest tailStates) :
      PartialValue.Typed program (.tuple head tail) (.tuple first rest) (.fields (headState :: tailStates))
  | nominal {identity : Nat} {tag : Option Nat} {declaration : DataDecl} {schema : Fields}
      {fields : List PartialValue} {states : List Initialization}
      (declared : program.data identity = some declaration)
      (chosen : declaration.constructor tag = some schema)
      (finite : FiniteLayout program.target program.data (.nominal identity))
      (residents : PartialValuesTyped program fields (schema.residents.map Field.type) states) :
      PartialValue.Typed program (.nominal identity tag fields) (.nominal identity) (.fields states)
  | uncertain {value : PartialValue} {type : Ty} {state : Initialization}
      (typed : PartialValue.Typed program value type state) :
      PartialValue.Typed program value type .maybe
inductive PartialValuesTyped (program : Program) : List PartialValue → List Ty → List Initialization → Prop where
  | nil : PartialValuesTyped program [] [] []
  | cons {head : PartialValue} {tail : List PartialValue} {first : Ty} {rest : List Ty}
      {headState : Initialization} {tailStates : List Initialization}
      (headTyped : PartialValue.Typed program head first headState)
      (tailTyped : PartialValuesTyped program tail rest tailStates) :
      PartialValuesTyped program (head :: tail) (first :: rest) (headState :: tailStates)
end

/-- An empty shell contains consumed storage. A zero-field aggregate is still
a whole value, not evidence that an owner has been consumed. -/
def Initialization.Empty : Initialization → Prop
  | .absent => True
  | .present => False
  | .maybe => False
  | .fields states => states ≠ [] ∧ ∀ state ∈ states, state.Empty

/- Uncorrelated joins may forget only discardable occupancy. Exact nominal
restrictions also protect the shell, independently of resident field classes. -/
mutual
inductive Initialization.Approximates (data : DataDeclarations) : Ty → Initialization → Initialization → Prop where
  | refl {type state} : Initialization.Approximates data type state state
  | unknown {type state} (disposable : UsePermitted data .discard type) :
      Initialization.Approximates data type state .maybe
  | tuple {first rest before after} (children : InitializationsApproximate data (first :: rest) before after) :
      Initialization.Approximates data (.tuple first rest) (.fields before) (.fields after)
  | nominal {identity declaration before after}
      (declared : data identity = some declaration)
      (consumption : declaration.restriction = some .exact →
        (Initialization.Empty (.fields before) ↔ Initialization.Empty (.fields after)))
      (children : ∀ tag schema, declaration.constructor tag = some schema →
        InitializationsApproximate data (schema.residents.map Field.type) before after) :
      Initialization.Approximates data (.nominal identity) (.fields before) (.fields after)
inductive InitializationsApproximate (data : DataDeclarations) : List Ty → List Initialization → List Initialization → Prop where
  | nil : InitializationsApproximate data [] [] []
  | cons {type types first next rest tail} (head : Initialization.Approximates data type first next)
      (remaining : InitializationsApproximate data types rest tail) :
      InitializationsApproximate data (type :: types) (first :: rest) (next :: tail)
end

theorem PartialValue.Typed.approximate {program : Program} {value : PartialValue} {type : Ty}
    {before after : Initialization} (typed : value.Typed program type before)
    (approximation : before.Approximates program.data type after) : value.Typed program type after := by
  induction approximation using Initialization.Approximates.rec
    (motive_2 := fun types before after _ => ∀ values, PartialValuesTyped program values types before →
      PartialValuesTyped program values types after) generalizing value with
  | refl => exact typed
  | unknown => exact .uncertain typed
  | tuple children ih =>
    cases typed with
    | tuple head tail =>
      have residents := ih _ (.cons head tail)
      cases residents with
      | cons head tail => exact .tuple head tail
  | nominal declared consumption children ih =>
    cases typed with
    | nominal found chosen finite residents =>
      cases Option.some.inj (found.symm.trans declared)
      exact .nominal declared chosen finite (ih _ _ chosen _ residents)
  | nil => rename_i values residents; exact residents
  | cons first remaining firstIH remainingIH =>
    rename_i values residents
    cases residents with
    | cons head tail => exact .cons (firstIH head) (remainingIH _ tail)


/-- A fresh unknown state is justified by ordinary whole-owner MayDiscard. -/
theorem Initialization.Approximates.no_new_nondiscardable_maybe {data : DataDeclarations}
    {type : Ty} {before after : Initialization} (joined : before.Approximates data type after)
    (required : ¬ UsePermitted data .discard type) (unknown : after = .maybe) : before = .maybe := by
  cases joined with
  | refl => exact unknown
  | unknown disposable => exact False.elim (required disposable)
  | tuple | nominal => cases unknown

/-- Manual exact ownership preserves whether the shell has been consumed,
without forbidding uncertainty in independently discardable resident fields. -/
theorem Initialization.Approximates.exact_nominal_consumption {data : DataDeclarations}
    {identity : Nat} {declaration : DataDecl} {before after : Initialization}
    (joined : before.Approximates data (.nominal identity) after)
    (declared : data identity = some declaration) (restricted : declaration.restriction = some .exact) :
    before.Empty ↔ after.Empty := by
  cases joined with
  | refl => exact Iff.rfl
  | unknown disposable =>
    cases disposable with
    | nominal found restriction fields =>
      cases Option.some.inj (found.symm.trans declared)
      simp [UsePermission.Allows, restricted] at restriction
  | nominal found consumption children =>
    cases Option.some.inj (found.symm.trans declared)
    exact consumption restricted


/-- Checking availability constructs the actual read; successful reads are not
part of the availability premise. -/
theorem PartialValue.Typed.read {program : Program} {valueState : PartialValue} {type : Ty}
    {state : Initialization} (typed : valueState.Typed program type state)
    (ready : state.Ready) :
    ∃ value, valueState.read = some value ∧ ValueHasType program value type := by
  induction typed using PartialValue.Typed.rec
    (motive_2 := fun partials types states _ => InitializationsReady states →
      ∃ values, readPartialValues partials = some values ∧ ValuesHaveTypes program values types) with
  | hole => cases ready
  | uncertain typed ih => cases ready
  | resident resident => exact ⟨_, by simp [PartialValue.read], resident⟩
  | tuple head tail headIH tailIH =>
    cases ready with
    | fields residents =>
      cases residents with
      | cons first rest =>
        obtain ⟨value, readHead, valueTyped⟩ := headIH first
        obtain ⟨values, readTail, valuesTyped⟩ := tailIH rest
        exact ⟨_, by simp [PartialValue.read, readHead, readTail], .tuple valueTyped valuesTyped⟩
  | nominal declared chosen finite residents ih =>
    cases ready with
    | fields ready =>
      obtain ⟨values, read, typed⟩ := ih ready
      exact ⟨_, by simp [PartialValue.read, read], .nominal declared chosen finite typed⟩
  | nil => exact ⟨[], by simp [readPartialValues], .nil⟩
  | cons head tail headIH tailIH =>
    rename_i ready
    cases ready with
    | cons first rest =>
      obtain ⟨value, readHead, valueTyped⟩ := headIH first
      obtain ⟨values, readTail, valuesTyped⟩ := tailIH rest
      exact ⟨_, by simp [readPartialValues, readHead, readTail], .cons valueTyped valuesTyped⟩

/-- No initialization claim can be manufactured from an empty resident. -/
theorem PartialValue.Typed.hole_unready {program : Program} {type : Ty} {state : Initialization}
    (typed : PartialValue.Typed program .hole type state) : ¬state.Ready := by
  cases typed <;> intro ready <;> cases ready


theorem Initialization.Ready.not_empty {state : Initialization} (ready : state.Ready) : ¬ state.Empty := by
  induction ready using Initialization.Ready.rec
    (motive_2 := fun states _ => ∀ state ∈ states, ¬ state.Empty) with
  | present => simp [Initialization.Empty]
  | @fields states residents ih =>
    intro empty
    simp only [Initialization.Empty] at empty
    cases states with
    | nil => exact empty.1 rfl
    | cons head tail => exact ih head (by simp) (empty.2 head (by simp))
  | nil => rename_i state member; cases member
  | cons head tail headIH tailIH =>
    rename_i state member
    cases member with
    | head => exact headIH
    | tail _ member => exact tailIH state member

theorem Initialization.MayRead.not_empty {state : Initialization} (ready : state.MayRead) : ¬ state.Empty := by
  induction ready using Initialization.MayRead.rec
    (motive_2 := fun states _ => ∀ state ∈ states, ¬ state.Empty) with
  | present | maybe => simp [Initialization.Empty]
  | @fields states residents ih =>
    intro empty
    simp only [Initialization.Empty] at empty
    cases states with
    | nil => exact empty.1 rfl
    | cons head tail => exact ih head (by simp) (empty.2 head (by simp))
  | nil => rename_i state member; cases member
  | cons head tail headIH tailIH =>
    rename_i state member
    cases member with
    | head => exact headIH
    | tail _ member => exact tailIH state member


def PartialValue.Empty : PartialValue → Prop
  | .hole => True
  | .resident _ => False
  | .tuple head tail => head.Empty ∧ ∀ value ∈ tail, value.Empty
  | .nominal _ _ fields => fields ≠ [] ∧ ∀ value ∈ fields, value.Empty

/-- Absence cannot simultaneously supply a whole value, including zero-sized
nominal owners. Partial shells may be read only after actual restoration. -/
theorem PartialValue.Empty.read_none {value : PartialValue} (empty : value.Empty) : value.read = none := by
  induction value using PartialValue.rec
    (motive_2 := fun values => values ≠ [] → (∀ value ∈ values, value.Empty) → readPartialValues values = none) with
  | hole => simp [PartialValue.read]
  | resident value => simp [PartialValue.Empty] at empty
  | tuple head tail headIH tailIH =>
    simp only [PartialValue.Empty] at empty
    simp [PartialValue.read, headIH empty.1]
  | nominal identity tag fields ih =>
    simp only [PartialValue.Empty] at empty
    simp [PartialValue.read, ih empty.1 empty.2]
  | nil => rename_i nonempty allEmpty; exact False.elim (nonempty rfl)
  | cons head tail headIH tailIH =>
    rename_i nonempty allEmpty
    simp [readPartialValues, headIH (allEmpty head (by simp))]


theorem PartialValuesTyped.state_length {program : Program} {values : List PartialValue}
    {types : List Ty} {states : List Initialization} (typed : PartialValuesTyped program values types states) :
    values.length = states.length := by
  induction typed using PartialValuesTyped.rec (motive_1 := fun _ _ _ _ => True) <;> simp_all

/-- The shared initialization mask certifies actual absence, not just a readable
value's absence. No resident can hide inside an empty partial aggregate. -/
theorem PartialValue.Typed.empty {program : Program} {value : PartialValue} {type : Ty}
    {state : Initialization} (typed : value.Typed program type state) (empty : state.Empty) : value.Empty := by
  induction typed using PartialValue.Typed.rec
    (motive_2 := fun values _ states _ =>
      (∀ state ∈ states, state.Empty) → ∀ value ∈ values, value.Empty)
  all_goals simp_all [Initialization.Empty, PartialValue.Empty]
  case cons =>
    rename_i value headEmpty tailEmpty states member
    rcases member with rfl | member
    · exact headEmpty
    · exact tailEmpty value member
  case nominal =>
    have lengths := PartialValuesTyped.state_length ‹PartialValuesTyped program _ _ _›
    intro same
    simp only [same, List.length_nil] at lengths
    exact empty.1 (by simpa using lengths.symm)

mutual
/-- Residual disposition uses initialization masks, not the original whole-owner
class. Nominal restrictions still constrain every nonempty residual shell. -/
inductive Initialization.Disposable (data : DataDeclarations) : Ty → Initialization → Prop where
  | empty {type state} (absent : state.Empty) : Initialization.Disposable data type state
  | permitted {type state} (permission : UsePermitted data .discard type) : Initialization.Disposable data type state
  | tuple {first rest head tail}
      (headPermission : Initialization.Disposable data first head)
      (tailPermission : InitializationsDisposable data rest tail) :
      Initialization.Disposable data (.tuple first rest) (.fields (head :: tail))
  | nominal {identity declaration states}
      (declared : data identity = some declaration)
      (restriction : UsePermission.discard.Allows declaration.restriction)
      (fields : ∀ tag schema, declaration.constructor tag = some schema →
        InitializationsDisposable data (schema.residents.map Field.type) states) :
      Initialization.Disposable data (.nominal identity) (.fields states)
inductive InitializationsDisposable (data : DataDeclarations) : List Ty → List Initialization → Prop where
  | nil : InitializationsDisposable data [] []
  | cons {type types state states} (head : Initialization.Disposable data type state)
      (tail : InitializationsDisposable data types states) :
      InitializationsDisposable data (type :: types) (state :: states)
end

/-- Conditional occupancy cannot erase a nondiscardable whole-owner obligation. -/
theorem Initialization.Disposable.maybe_iff {data : DataDeclarations} {type : Ty} :
    Initialization.Disposable data type .maybe ↔ UsePermitted data .discard type := by
  constructor
  · intro permission
    cases permission with
    | empty absent => simp [Initialization.Empty] at absent
    | permitted allowed => exact allowed
  · exact .permitted


private theorem InitializationsApproximate.lengths {data : DataDeclarations}
    {types : List Ty} {before after : List Initialization}
    (joined : InitializationsApproximate data types before after) :
    before.length = types.length ∧ after.length = types.length := by
  induction types generalizing before after with
  | nil => cases joined; exact ⟨rfl, rfl⟩
  | cons type types ih =>
    cases joined with
    | cons head tail =>
      obtain ⟨left, right⟩ := ih tail
      exact ⟨by simpa using congrArg Nat.succ left, by simpa using congrArg Nat.succ right⟩

theorem InitializationsDisposable.of_empty {data : DataDeclarations}
    {types : List Ty} {states : List Initialization}
    (lengths : states.length = types.length) (empty : ∀ state ∈ states, state.Empty) :
    InitializationsDisposable data types states := by
  induction types generalizing states with
  | nil =>
    cases states with
    | nil => exact .nil
    | cons head tail => simp at lengths
  | cons type types ih =>
    cases states with
    | nil => simp at lengths
    | cons head tail =>
      exact .cons (.empty (empty head (by simp)))
        (ih (by simpa using lengths) (fun state member => empty state (by simp [member])))

/-- Losing branch information cannot invent permission to destroy a residual
owner. The proof applies to all masks, without assuming a runtime realization. -/
theorem Initialization.Approximates.disposable_before {data : DataDeclarations}
    {type : Ty} {before after : Initialization} (joined : before.Approximates data type after)
    (permission : after.Disposable data type) : before.Disposable data type := by
  induction joined using Initialization.Approximates.rec
    (motive_2 := fun types before after _ =>
      InitializationsDisposable data types after → InitializationsDisposable data types before) with
  | refl => exact permission
  | unknown allowed => exact .permitted allowed
  | tuple children ih =>
    cases permission with
    | empty absent =>
      simp only [Initialization.Empty] at absent
      have original := ih (InitializationsDisposable.of_empty children.lengths.2 absent.2)
      cases original with
      | cons head tail => exact .tuple head tail
    | permitted allowed => exact .permitted allowed
    | tuple head tail =>
      have original := ih (.cons head tail)
      cases original with
      | cons head tail => exact .tuple head tail
  | @nominal identity declaration before after declared consumption children ih =>
    cases permission with
    | empty absent =>
      by_cases restricted : declaration.restriction = some .exact
      · exact .empty ((consumption restricted).mpr absent)
      · apply Initialization.Disposable.nominal declared
        · cases restriction : declaration.restriction with
          | none => trivial
          | some principal => cases principal <;> simp_all [UsePermission.Allows]
        · intro tag schema chosen
          simp only [Initialization.Empty] at absent
          exact ih tag schema chosen
            (InitializationsDisposable.of_empty (children tag schema chosen).lengths.2 absent.2)
    | permitted allowed => exact .permitted allowed
    | nominal found restriction fields =>
      cases Option.some.inj (found.symm.trans declared)
      exact .nominal declared restriction (fun tag schema chosen => ih tag schema chosen (fields tag schema chosen))
  | nil => exact .nil
  | cons head tail headIH tailIH =>
    rename_i permission
    cases permission with
    | cons first rest => exact .cons (headIH first) (tailIH rest)



theorem InitializationsDisposable.select {data : DataDeclarations} {types : List Ty}
    {states : List Initialization} (permission : InitializationsDisposable data types states)
    {index : Nat} {type : Ty} {state : Initialization}
    (selectedType : types[index]? = some type) (selectedState : states[index]? = some state) :
    state.Disposable data type := by
  induction types generalizing states index with
  | nil => simp at selectedType
  | cons first rest ih =>
    cases permission with
    | cons head tail =>
      cases index with
      | zero => cases selectedType; cases selectedState; exact head
      | succ index => exact ih tail selectedType selectedState


/-- One runtime interpretation of the authoritative residual permission. Its
mask describes this actual resident at its storage type, not a future source state. -/
def PartialValue.Disposable (program : Program) (value : PartialValue) (type : Ty) : Prop :=
  ∃ state, value.Typed program type state ∧ state.Disposable program.data type

theorem Initialization.Disposable.realizes {program : Program} {type : Ty} {state : Initialization}
    (permission : state.Disposable program.data type) {value : PartialValue}
    (typed : value.Typed program type state) : value.Disposable program type :=
  ⟨state, typed, permission⟩


/-- Residual disposition cannot weaken the principal of a reconstructed whole
owner. Every nominal constructor contributes, including inactive variants. -/
theorem Initialization.Disposable.may_read {data : DataDeclarations} {type : Ty} {state : Initialization}
    (permission : state.Disposable data type) (ready : state.MayRead) : UsePermitted data .discard type := by
  induction permission using Initialization.Disposable.rec
    (motive_2 := fun types states _ => InitializationsMayRead states →
      ∀ type ∈ types, UsePermitted data .discard type) with
  | empty absent => exact False.elim (ready.not_empty absent)
  | permitted permission => exact permission
  | tuple head tail headIH tailIH =>
    cases ready with
    | fields residents =>
      cases residents with
      | cons first rest => exact .tuple (headIH first) (tailIH rest)
  | nominal declared restriction fields ih =>
    cases ready with
    | fields ready =>
      refine .nominal declared restriction ?_
      intro schema member field included
      obtain ⟨tag, selected⟩ := DataDecl.constructor_exists member
      exact ih tag schema selected ready field.type (List.mem_map.mpr ⟨field, included, rfl⟩)
  | nil => rename_i ready type member; cases member
  | cons head tail headIH tailIH =>
    rename_i ready type member
    cases ready with
    | cons first rest =>
      cases member with
      | head => exact headIH first
      | tail _ member => exact tailIH rest type member


/-- A still-whole resident receives exactly its ordinary MayDiscard permission. -/
theorem Initialization.Disposable.present_iff {data : DataDeclarations} {type : Ty} :
    Initialization.present.Disposable data type ↔ UsePermitted data .discard type := by
  constructor
  · intro permission
    cases permission with
    | empty absent => simp [Initialization.Empty] at absent
    | permitted permission => exact permission
  · exact .permitted

/-- Explicit exact restrictions cannot be bypassed by partially consuming fields. -/
theorem Initialization.Disposable.exact_nominal_empty {data : DataDeclarations} {identity : Nat}
    {declaration : DataDecl} {state : Initialization}
    (declared : data identity = some declaration) (restricted : declaration.restriction = some .exact)
    (permission : state.Disposable data (.nominal identity)) : state.Empty := by
  cases permission with
  | empty absent => exact absent
  | permitted permission =>
    cases permission with
    | nominal found restriction fields =>
      cases Option.some.inj (found.symm.trans declared)
      simp [UsePermission.Allows, restricted] at restriction
  | nominal found restriction fields =>
    cases Option.some.inj (found.symm.trans declared)
    simp [UsePermission.Allows, restricted] at restriction

theorem PartialValue.Typed.nominal_type {program : Program} {value : PartialValue}
    {type : Ty} {state : Initialization} (typed : value.Typed program type state)
    {identity : Nat} {tag : Option Nat} {fields : List PartialValue}
    (shape : value = .nominal identity tag fields) : type = .nominal identity := by
  induction typed using PartialValue.Typed.rec
    (motive_2 := fun _ _ _ _ => True) with
  | hole | resident | tuple => cases shape
  | nominal => cases shape; rfl
  | uncertain typed ih => exact ih shape
  | nil | cons => trivial


/-- Exact nominal ownership permits retirement only after complete consumption,
independently of whether the actual resident can still be reconstructed. -/
theorem PartialValue.Disposable.exact_nominal_empty {program : Program} {identity : Nat}
    {declaration : DataDecl} {value : PartialValue}
    (declared : program.data identity = some declaration) (restricted : declaration.restriction = some .exact)
    (permission : value.Disposable program (.nominal identity)) : value.Empty := by
  obtain ⟨state, typed, disposition⟩ := permission
  exact typed.empty (disposition.exact_nominal_empty declared restricted)



structure StorageCell where
  activation : ActivationId
  type : Ty
  resident : PartialValue

def StorageCell.Typed (program : Program) (cell : StorageCell) (state : Initialization) : Prop :=
  FiniteLayout program.target program.data cell.type ∧
    cell.resident.Typed program cell.type state

/-- Preservation follows from the actual observation, independently of whether
checking has already established availability. -/
theorem PartialValue.Typed.read_sound {program : Program} {valueState : PartialValue} {type : Ty}
    {state : Initialization} (typed : valueState.Typed program type state) {value : Value}
    (read : valueState.read = some value) : ValueHasType program value type ∧ state.MayRead := by
  induction typed using PartialValue.Typed.rec
    (motive_2 := fun partials types states _ => ∀ values,
      readPartialValues partials = some values →
      ValuesHaveTypes program values types ∧ InitializationsMayRead states) generalizing value with
  | hole => simp [PartialValue.read] at read
  | uncertain typed ih => exact ⟨(ih read).1, .maybe⟩
  | resident resident =>
    simp only [PartialValue.read, Option.some.injEq] at read
    subst value
    exact ⟨resident, .present⟩
  | tuple head tail headIH tailIH =>
    simp only [PartialValue.read, Option.bind_eq_some_iff, Option.map_eq_some_iff] at read
    obtain ⟨first, readFirst, rest, readRest, same⟩ := read
    subst value
    obtain ⟨firstTyped, firstReady⟩ := headIH readFirst
    obtain ⟨restTyped, restReady⟩ := tailIH rest readRest
    exact ⟨.tuple firstTyped restTyped, .fields (.cons firstReady restReady)⟩
  | nominal declared chosen finite residents ih =>
    simp only [PartialValue.read, Option.map_eq_some_iff] at read
    obtain ⟨values, read, same⟩ := read
    subst value
    obtain ⟨typed, ready⟩ := ih values read
    exact ⟨.nominal declared chosen finite typed, .fields ready⟩
  | nil =>
    rename_i values read
    simp only [readPartialValues, Option.some.injEq] at read
    subst values
    exact ⟨.nil, .nil⟩
  | cons head tail headIH tailIH =>
    rename_i values read
    simp only [readPartialValues, Option.bind_eq_some_iff, Option.map_eq_some_iff] at read
    obtain ⟨first, readFirst, rest, readRest, same⟩ := read
    subst values
    obtain ⟨firstTyped, firstReady⟩ := headIH readFirst
    obtain ⟨restTyped, restReady⟩ := tailIH rest readRest
    exact ⟨.cons firstTyped restTyped, .cons firstReady restReady⟩

/-- A readable old resident cannot bypass the principal of its actual storage type. -/
theorem PartialValue.Disposable.read_permission {program : Program} {value : PartialValue} {type : Ty}
    (permission : value.Disposable program type) {owner : Value} (read : value.read = some owner) :
    UsePermitted program.data .discard type := by
  obtain ⟨state, typed, disposition⟩ := permission
  exact disposition.may_read (typed.read_sound read).2

/-- Actual readable occupancy can be destroyed only when its principal permits
zero use. Holes and authorized residual shells are not treated as whole owners. -/
theorem PartialValue.Disposable.zero_use {program : Program} {value : PartialValue} {type : Ty}
    {owner : Value} {principal : Principal} (permission : value.Disposable program type)
    (observed : value.read = some owner) (classified : type.HasPrincipal program.data principal) :
    principal.Permits 0 :=
  ((classified .discard).mp (permission.read_permission observed)) 0 (by simp)


/-- Another valid typing of the observed value cannot weaken its owned-use
principal; this includes the element-type ambiguity of empty arrays. -/
theorem PartialValue.Disposable.read_permission_as {program : Program} {value : PartialValue}
    {type other : Ty} (permission : value.Disposable program type) {owner : Value}
    (read : value.read = some owner) (typed : ValueHasType program owner other) :
    UsePermitted program.data .discard other := by
  obtain ⟨state, actual, disposition⟩ := permission
  obtain ⟨resident, ready⟩ := actual.read_sound read
  exact resident.use_permission typed (disposition.may_read ready)


/-- Reconstructing an aggregate cannot hide a live exact owner from cleanup. -/
theorem PartialValue.Disposable.not_exact_read {program : Program} {identity : Nat}
    {declaration : DataDecl} {tag : Option Nat} {fields : List Value} {value : PartialValue} {type : Ty}
    (declared : program.data identity = some declaration) (restricted : declaration.restriction = some .exact)
    (observed : value.read = some (.nominal identity tag fields)) : ¬ value.Disposable program type := by
  rintro ⟨state, typed, disposition⟩
  obtain ⟨resident, ready⟩ := typed.read_sound observed
  cases resident with
  | nominal found chosen finite residents =>
    exact ready.not_empty (disposition.exact_nominal_empty declared restricted)


def StorageCell.WellTyped (program : Program) (cell : StorageCell) : Prop :=
  ∃ state, cell.Typed program state

end Grounded
