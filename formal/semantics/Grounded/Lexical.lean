import Grounded.Values
import Grounded.BindingStorage

/-! Logical lexical storage: actual replacement, immutable-cell preservation,
and compositional scope framing. No physical allocation or loan model. -/
namespace Grounded

inductive EnvironmentTyped (program : Program) : List (BindingId × Value) → List (BindingId × BindingType) → Prop where
  | nil : EnvironmentTyped program [] []
  | cons {name : BindingId} {value : Value} {type : BindingType}
      {environment : List (BindingId × Value)} {context : List (BindingId × BindingType)}
      (resident : ValueHasType program value type.type) (rest : EnvironmentTyped program environment context)
      (fresh : name ∉ context.map Prod.fst) :
      EnvironmentTyped program ((name, value) :: environment) ((name, type) :: context)

variable {program : Program}

/-- Realization keeps exactly the checked lexical identity list. -/
theorem EnvironmentTyped.keys {environment : List (BindingId × Value)} {context : List (BindingId × BindingType)}
    (typed : EnvironmentTyped program environment context) : environment.map Prod.fst = context.map Prod.fst := by
  induction typed with
  | nil => rfl
  | cons resident rest fresh ih => exact congrArg (List.cons _) ih

theorem EnvironmentTyped.distinct {environment : List (BindingId × Value)} {context : List (BindingId × BindingType)}
    (typed : EnvironmentTyped program environment context) : (context.map Prod.fst).Nodup := by
  induction typed with
  | nil => exact .nil
  | cons resident rest fresh ih => exact List.nodup_cons.mpr ⟨fresh, ih⟩

theorem EnvironmentTyped.runtimeDistinct {environment : List (BindingId × Value)} {context : List (BindingId × BindingType)}
    (typed : EnvironmentTyped program environment context) : (environment.map Prod.fst).Nodup := by
  rw [typed.keys]
  exact typed.distinct


theorem EnvironmentTyped.append {left right : List (BindingId × Value)} {first rest : List (BindingId × BindingType)}
    (front : EnvironmentTyped program left first) (back : EnvironmentTyped program right rest)
    (distinct : ((first ++ rest).map Prod.fst).Nodup) :
    EnvironmentTyped program (left ++ right) (first ++ rest) := by
  induction front with
  | nil => exact back
  | cons resident tail fresh ih =>
    have parts := List.nodup_cons.mp distinct
    exact .cons resident (ih parts.2) parts.1

theorem EnvironmentTyped.drop {environment : List (BindingId × Value)} {context : List (BindingId × BindingType)}
    (typed : EnvironmentTyped program environment context) (count : Nat) :
    EnvironmentTyped program (environment.drop count) (context.drop count) := by
  induction count generalizing environment context with
  | zero => exact typed
  | succ count ih => cases typed with
    | nil => exact .nil
    | cons resident rest fresh => exact ih rest

theorem EnvironmentTyped.length {environment : List (BindingId × Value)} {context : List (BindingId × BindingType)}
    (typed : EnvironmentTyped program environment context) : environment.length = context.length := by
  induction typed with
  | nil => rfl
  | cons _ _ _ ih => exact congrArg Nat.succ ih


theorem replaceBinding.lookup_after {α : Type} {name : BindingId} {value : α}
    {before after : List (BindingId × α)} (written : replaceBinding name value before = some after) :
    lookup name after = some value := by
  induction before generalizing after with
  | nil => simp [replaceBinding] at written
  | cons entry rest ih =>
    rcases entry with ⟨key, old⟩
    simp only [replaceBinding] at written
    split at written
    next same =>
      cases written
      simp [lookup, same]
    next different =>
      cases tailWrite : replaceBinding name value rest with
      | none => simp [tailWrite] at written
      | some tail =>
        simp [tailWrite] at written
        subst after
        simp [lookup, Ne.symm different, ih tailWrite]


/-- Replacement changes no other root, including mutable roots. -/
theorem replaceBinding.lookup_other {α : Type} {name other : BindingId} {value : α}
    {before after : List (BindingId × α)} (written : replaceBinding name value before = some after)
    (different : other ≠ name) : lookup other after = lookup other before := by
  induction before generalizing after with
  | nil => simp [replaceBinding] at written
  | cons entry rest ih =>
    rcases entry with ⟨key, old⟩
    simp only [replaceBinding] at written
    split at written
    next same =>
      cases written
      simp [lookup, same, different]
    next missed =>
      cases tailWrite : replaceBinding name value rest with
      | none => simp [tailWrite] at written
      | some tail =>
        simp [tailWrite] at written
        subst after
        simp [lookup, ih tailWrite]


/-- Preserve lexical slots and every immutable resident, including shadowed slots. -/
inductive EnvironmentFrame : List (BindingId × BindingType) →
    List (BindingId × Value) → List (BindingId × Value) → Prop where
  | nil : EnvironmentFrame [] [] []
  | cons {name : BindingId} {slot : BindingType} {old value : Value}
      {context : List (BindingId × BindingType)} {before after : List (BindingId × Value)}
      (immutable : slot.mutable = false → value = old)
      (rest : EnvironmentFrame context before after) :
      EnvironmentFrame ((name, slot) :: context) ((name, old) :: before) ((name, value) :: after)

variable {program : Program} {context : List (BindingId × BindingType)}
    {before middle after : List (BindingId × Value)}

theorem EnvironmentTyped.frame_refl (typed : EnvironmentTyped program before context) :
    EnvironmentFrame context before before := by
  induction typed with
  | nil => exact .nil
  | cons resident rest fresh ih => exact .cons (fun _ => rfl) ih

theorem EnvironmentFrame.trans (first : EnvironmentFrame context before middle)
    (second : EnvironmentFrame context middle after) : EnvironmentFrame context before after := by
  induction first generalizing after with
  | nil => exact second
  | cons immutable rest ih =>
    cases second with
    | cons next tail => exact .cons (fun fixed => (next fixed).trans (immutable fixed)) (ih tail)

theorem EnvironmentFrame.drop (framed : EnvironmentFrame context before after) (count : Nat) :
    EnvironmentFrame (context.drop count) (before.drop count) (after.drop count) := by
  induction count generalizing context before after with
  | zero => exact framed
  | succ count ih => cases framed with
    | nil => exact .nil
    | cons immutable rest => exact ih rest

/-- Current typing and writable destination evidence construct the actual update,
its typing, and its immutable frame; none is an admission premise. -/
theorem EnvironmentTyped.replace (typed : EnvironmentTyped program before context)
    {name : BindingId} {slot : BindingType} (selected : lookup name context = some slot)
    (writable : slot.mutable = true) {value : Value} (resident : ValueHasType program value slot.type) :
    ∃ after, replaceBinding name value before = some after ∧
      EnvironmentTyped program after context ∧ EnvironmentFrame context before after := by
  induction typed with
  | nil => simp [lookup] at selected
  | @cons key old type environment context oldTyped rest fresh ih =>
    simp only [lookup] at selected
    split at selected
    next same =>
      cases selected
      refine ⟨_, by simp [replaceBinding, same], .cons resident rest fresh, .cons ?_ rest.frame_refl⟩
      intro immutable
      simp [writable] at immutable
    next different =>
      obtain ⟨after, replaced, afterTyped, framed⟩ := ih selected
      exact ⟨_, by simp [replaceBinding, Ne.symm different, replaced],
        .cons oldTyped afterTyped fresh, .cons (fun _ => rfl) framed⟩

theorem BindingInputsTyped.environment {inputs : List BindingInput}
    (typed : BindingInputsTyped program inputs) :
    EnvironmentTyped program (inputs.map fun input => (input.name, input.value))
      (inputs.map fun input => (input.name, input.slot)) := by
  induction typed with
  | nil => exact .nil
  | cons resident tail fresh ih =>
    exact .cons resident ih (by simpa only [List.map_map, Function.comp_def] using fresh)

/-- The current lexical machine consumes the same prepared inputs as the
addressed allocator. Preparation is derived, not an admission premise. -/
theorem EnvironmentTyped.parameters (parameters : List (BindingId × BindingType)) (values : List Value)
    (typed : ValuesHaveTypes program values (parameters.map (fun parameter => parameter.2.type)))
    (distinct : (parameters.map Prod.fst).Nodup) :
    ∃ inputs, prepareBindings parameters values = some inputs ∧
      EnvironmentTyped program (inputs.map fun input => (input.name, input.value)) parameters := by
  obtain ⟨inputs, prepared, inputsTyped, slots⟩ := prepareBindings.progress typed distinct
  exact ⟨inputs, prepared, slots ▸ inputsTyped.environment⟩


end Grounded
