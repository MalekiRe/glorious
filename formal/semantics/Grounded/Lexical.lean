import Grounded.Values

/-! Logical lexical storage: actual replacement, immutable-cell preservation,
and compositional scope framing. No physical allocation or loan model. -/
namespace Grounded

/-- Nearest lexical binding wins, including in shadowing initializers. -/
def lookup {α : Type} (name : String) : List (String × α) → Option α
  | [] => none
  | (key, value) :: rest => if name = key then some value else lookup name rest

inductive EnvironmentTyped (program : Program) : List (String × Value) → List (String × BindingType) → Prop where
  | nil : EnvironmentTyped program [] []
  | cons {name : String} {value : Value} {type : BindingType}
      {environment : List (String × Value)} {context : List (String × BindingType)}
      (resident : ValueHasType program value type.type) (rest : EnvironmentTyped program environment context) :
      EnvironmentTyped program ((name, value) :: environment) ((name, type) :: context)

variable {program : Program}

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


/-- Replace the nearest lexical binding; an absent destination is rejected. -/
def replaceBinding {α : Type} (name : String) (value : α) : List (String × α) → Option (List (String × α))
  | [] => none
  | (key, old) :: rest =>
      if key = name then some ((key, value) :: rest)
      else ((key, old) :: ·) <$> replaceBinding name value rest

theorem replaceBinding.lookup_after {α : Type} {name : String} {value : α}
    {before after : List (String × α)} (written : replaceBinding name value before = some after) :
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


/-- Preserve lexical slots and every immutable resident, including shadowed slots. -/
inductive EnvironmentFrame : List (String × BindingType) →
    List (String × Value) → List (String × Value) → Prop where
  | nil : EnvironmentFrame [] [] []
  | cons {name : String} {slot : BindingType} {old value : Value}
      {context : List (String × BindingType)} {before after : List (String × Value)}
      (immutable : slot.mutable = false → value = old)
      (rest : EnvironmentFrame context before after) :
      EnvironmentFrame ((name, slot) :: context) ((name, old) :: before) ((name, value) :: after)

variable {program : Program} {context : List (String × BindingType)}
    {before middle after : List (String × Value)}

theorem EnvironmentTyped.frame_refl (typed : EnvironmentTyped program before context) :
    EnvironmentFrame context before before := by
  induction typed with
  | nil => exact .nil
  | cons resident rest ih => exact .cons (fun _ => rfl) ih

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
    {name : String} {slot : BindingType} (selected : lookup name context = some slot)
    (writable : slot.mutable = true) {value : Value} (resident : ValueHasType program value slot.type) :
    ∃ after, replaceBinding name value before = some after ∧
      EnvironmentTyped program after context ∧ EnvironmentFrame context before after := by
  induction typed with
  | nil => simp [lookup] at selected
  | @cons key old type environment context oldTyped rest ih =>
    simp only [lookup] at selected
    split at selected
    next same =>
      cases selected
      refine ⟨_, by simp [replaceBinding, same], .cons resident rest, .cons ?_ rest.frame_refl⟩
      intro immutable
      simp [writable] at immutable
    next different =>
      obtain ⟨after, replaced, afterTyped, framed⟩ := ih selected
      exact ⟨_, by simp [replaceBinding, Ne.symm different, replaced],
        .cons oldTyped afterTyped, .cons (fun _ => rfl) framed⟩

/-- Invocation constructs its environment from the actual typed argument list. -/
theorem EnvironmentTyped.parameters (parameters : List (String × BindingType)) (values : List Value)
    (typed : ValuesHaveTypes program values (parameters.map (fun parameter => parameter.2.type))) :
    EnvironmentTyped program (List.zip (parameters.map Prod.fst) values) parameters := by
  induction parameters generalizing values with
  | nil => cases typed; exact .nil
  | cons parameter parameters ih =>
    cases typed with
    | cons headTyped tailTyped => exact .cons headTyped (ih _ tailTyped)


end Grounded
