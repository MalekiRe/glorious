import Grounded.Lexical
import Grounded.Projections

/-! Checked projection produces actual selection and replacement through the same
field resolver. Assignment operates on the current aggregate, never an old snapshot. -/
namespace Grounded


inductive PlaceType (program : Program) (home : Module) (context : List (BindingId × BindingType)) :
    Place → Ty → Bool → Prop where
  | root {name : BindingId} {fields : List FieldKey} {parent result : Ty} {mutable : Bool}
      (selected : lookup name context = some ⟨parent, mutable⟩)
      (path : PathType program home parent fields result) :
      PlaceType program home context ⟨name, fields⟩ result mutable


def readPlace (program : Program) (place : Place) (environment : List (BindingId × Value)) : Option Value := do
  let root ← lookup place.root environment
  readFields program root place.fields

def writePlace (program : Program) (place : Place) (replacement : Value)
    (environment : List (BindingId × Value)) : Option (List (BindingId × Value)) := do
  let root ← lookup place.root environment
  let updated ← writeFields program root place.fields replacement
  replaceBinding place.root updated environment

/-- These are write-operation frames: before is the actual post-RHS store. -/
theorem writePlace.lookup_other {program : Program} {place : Place} {value : Value}
    {before after : List (BindingId × Value)} {other : BindingId}
    (written : writePlace program place value before = some after) (different : other ≠ place.root) :
    lookup other after = lookup other before := by
  cases found : lookup place.root before with
  | none => simp [writePlace, found] at written
  | some root =>
    cases updated : writeFields program root place.fields value with
    | none => simp [writePlace, found, updated] at written
    | some replacement =>
      exact replaceBinding.lookup_other (by simpa [writePlace, found, updated] using written) different

theorem writePlace.read_other {program : Program} {place other : Place} {value : Value}
    {before after : List (BindingId × Value)}
    (written : writePlace program place value before = some after) (different : other.root ≠ place.root) :
    readPlace program other after = readPlace program other before := by
  unfold readPlace
  rw [writePlace.lookup_other written different]



variable {program : Program} {home : Module}

theorem EnvironmentTyped.lookup {environment : List (BindingId × Value)} {context : List (BindingId × BindingType)}
    (typed : EnvironmentTyped program environment context) {name : BindingId} {slot : BindingType}
    (selected : lookup name context = some slot) :
    ∃ value, lookup name environment = some value ∧ ValueHasType program value slot.type := by
  induction typed with
  | nil => simp [Grounded.lookup] at selected
  | cons resident rest fresh ih =>
    simp only [Grounded.lookup] at selected ⊢
    split at selected
    · cases selected; exact ⟨_, by simp_all, resident⟩
    · obtain ⟨value, found, valueTyped⟩ := ih selected
      exact ⟨value, by simp_all, valueTyped⟩

theorem EnvironmentTyped.readPlace {environment : List (BindingId × Value)} {context : List (BindingId × BindingType)}
    (typed : EnvironmentTyped program environment context) {place : Place} {type : Ty} {mutable : Bool}
    (selected : PlaceType program home context place type mutable) :
    ∃ value, readPlace program place environment = some value ∧ ValueHasType program value type := by
  cases selected with
  | root selected path =>
    obtain ⟨root, found, rootTyped⟩ := typed.lookup selected
    obtain ⟨value, read, valueTyped⟩ := path.read rootTyped
    exact ⟨value, by simp [Grounded.readPlace, found, read], valueTyped⟩



theorem EnvironmentTyped.writePlace {environment : List (BindingId × Value)} {context : List (BindingId × BindingType)}
    (typed : EnvironmentTyped program environment context) {place : Place} {type : Ty} {value : Value}
    (selected : PlaceType program home context place type true) (resident : ValueHasType program value type) :
    ∃ after, writePlace program place value environment = some after ∧ EnvironmentTyped program after context ∧
      EnvironmentFrame context environment after ∧ Grounded.readPlace program place after = some value := by
  cases selected with
  | root selected path =>
    obtain ⟨root, found, rootTyped⟩ := typed.lookup selected
    obtain ⟨updated, written, updatedTyped, readBack⟩ := path.write rootTyped resident
    obtain ⟨after, replaced, afterTyped, frame⟩ := typed.replace selected rfl updatedTyped
    refine ⟨after, by simp [Grounded.writePlace, found, written, replaced], afterTyped, frame, ?_⟩
    simp [Grounded.readPlace, replaceBinding.lookup_after replaced, readBack]

end Grounded
