import Grounded.Soundness

/-!
Structural constant patterns (§4.3). Closed constant checking produces each
normal form through core correctness. Coverage, usefulness and body checking
consume that concrete result; neither evaluation nor normalization success is
an admission premise. Bodies and arguments are the existing decoded core; binder
identities and binder types are already resolved inputs, not source spellings.
-/
namespace Grounded

inductive SourcePattern where
  | wildcard
  | binder (name : BindingId) (type : Ty)
  | node (head : Head) (fields : List SourcePattern)
  | constant (name : String)

mutual
/-- Compile-time inputs: source syntax and ordinary closed constant typing. -/
inductive SourcePattern.Checked (program : Program) (home : Module) : SourcePattern → Type where
  | wildcard : SourcePattern.Checked program home .wildcard
  | binder (name : BindingId) (type : Ty) : SourcePattern.Checked program home (.binder name type)
  | node {head : Head} {fields : List SourcePattern}
      (checked : SourcePatternsChecked program home fields) :
      SourcePattern.Checked program home (.node head fields)
  | constant {name : String} (type : Ty)
      (typed : HasType program home [] (.constant name) type []) :
      SourcePattern.Checked program home (.constant name)
inductive SourcePatternsChecked (program : Program) (home : Module) : List SourcePattern → Type where
  | nil : SourcePatternsChecked program home []
  | cons {head : SourcePattern} {tail : List SourcePattern}
      (first : SourcePattern.Checked program home head)
      (rest : SourcePatternsChecked program home tail) :
      SourcePatternsChecked program home (head :: tail)
end

mutual
/-- The normalization specification uses the same constant evaluation relation. -/
inductive NormalizesPattern (program : Program) (home : Module) : SourcePattern → Pattern → Prop where
  | wildcard : NormalizesPattern program home .wildcard .wildcard
  | binder (name : BindingId) (type : Ty) : NormalizesPattern program home (.binder name type) (.binder name type)
  | node {head : Head} {fields : List SourcePattern} {patterns : List Pattern}
      (fieldsNormalize : NormalizesPatterns program home fields patterns) :
      NormalizesPattern program home (.node head fields) (.node head patterns)
  | constant {name : String} {type : Ty} {value : Value} {after : Environment}
      (typed : HasType program home [] (.constant name) type [])
      (evaluated : Evaluates program AddressedEnvironment.empty (.constant name) value after) :
      NormalizesPattern program home (.constant name) (.literal (some type) value)
inductive NormalizesPatterns (program : Program) (home : Module) :
    List SourcePattern → List Pattern → Prop where
  | nil : NormalizesPatterns program home [] []
  | cons {head : SourcePattern} {tail : List SourcePattern} {first : Pattern} {rest : List Pattern}
      (headNormalizes : NormalizesPattern program home head first)
      (tailNormalizes : NormalizesPatterns program home tail rest) :
      NormalizesPatterns program home (head :: tail) (first :: rest)
end

variable {program : Program} {home : Module}

private theorem constant_type_unique {name : String} {first second : Ty}
    (typed : HasType program home [] (.constant name) first [])
    (other : HasType program home [] (.constant name) second []) : second = first := by
  cases typed with
  | constant declared visible resolved structural initialized =>
    cases other with
    | constant otherDeclared otherVisible otherResolved otherStructural otherInitialized =>
      cases Option.some.inj (declared.symm.trans otherDeclared)
      exact resolved.unique _ otherResolved

/-- The specification determines the entire pattern, including constant type tags. -/
theorem NormalizesPattern.unique {source : SourcePattern} {pattern : Pattern}
    (normalized : NormalizesPattern program home source pattern) :
    ∀ other, NormalizesPattern program home source other → other = pattern := by
  induction normalized using NormalizesPattern.rec
    (motive_2 := fun sources patterns _ =>
      ∀ others, NormalizesPatterns program home sources others → others = patterns) with
  | wildcard => intro other found; cases found; rfl
  | binder name type => intro other found; cases found; rfl
  | node fields ih =>
    intro other found
    cases found with
    | node otherFields => rw [ih _ otherFields]
  | constant typed evaluated =>
    intro other found
    cases found with
    | constant otherTyped otherEvaluated =>
      obtain ⟨value, after, evaluation, valueTyped, unique⟩ := constant_correctness typed
      have sameType := constant_type_unique typed otherTyped
      have sameValue := (unique _ _ otherEvaluated).1.trans (unique _ _ evaluated).1.symm
      rw [sameType, sameValue]
  | nil => rename_i others found; cases found; rfl
  | cons first rest firstIH restIH =>
    rename_i others found
    cases found with
    | cons otherFirst otherRest => rw [firstIH _ otherFirst, restIH _ otherRest]


noncomputable section
mutual
/-- Construct the normal form and its certificate together; only constants use choice. -/
def SourcePattern.Checked.normalize {source : SourcePattern}
    (checked : SourcePattern.Checked program home source) :
    {pattern // NormalizesPattern program home source pattern} :=
  match checked with
  | .wildcard => ⟨.wildcard, .wildcard⟩
  | .binder name type => ⟨.binder name type, .binder name type⟩
  | .node (head := head) fields =>
    let result := fields.normalize
    ⟨.node head result.val, .node result.property⟩
  | .constant type typed =>
    ⟨.literal (some type) (Classical.choose (constant_correctness typed)),
      .constant typed (Classical.choose_spec (Classical.choose_spec (constant_correctness typed))).1⟩
def SourcePatternsChecked.normalize {sources : List SourcePattern}
    (checked : SourcePatternsChecked program home sources) :
    {patterns // NormalizesPatterns program home sources patterns} :=
  match checked with
  | .nil => ⟨[], .nil⟩
  | .cons first rest =>
    let head := first.normalize
    let tail := rest.normalize
    ⟨head.val :: tail.val, .cons head.property tail.property⟩
end

inductive SourceArmsChecked (program : Program) (home : Module) :
    List (SourcePattern × Expr) → Type where
  | nil : SourceArmsChecked program home []
  | cons {pattern : SourcePattern} {body : Expr} {rest : List (SourcePattern × Expr)}
      (checked : SourcePattern.Checked program home pattern)
      (tail : SourceArmsChecked program home rest) :
      SourceArmsChecked program home ((pattern, body) :: rest)

/-- Arm order and bodies are unchanged by compile-time pattern normalization. -/
inductive NormalizesArms (program : Program) (home : Module) :
    List (SourcePattern × Expr) → List (Pattern × Expr) → Prop where
  | nil : NormalizesArms program home [] []
  | cons {source : SourcePattern} {pattern : Pattern} {body : Expr}
      {rest : List (SourcePattern × Expr)} {normalized : List (Pattern × Expr)}
      (headNormalizes : NormalizesPattern program home source pattern)
      (tailNormalizes : NormalizesArms program home rest normalized) :
      NormalizesArms program home ((source, body) :: rest) ((pattern, body) :: normalized)

theorem NormalizesArms.unique {source : List (SourcePattern × Expr)} {arms : List (Pattern × Expr)}
    (normalized : NormalizesArms program home source arms) :
    ∀ other, NormalizesArms program home source other → other = arms := by
  induction normalized with
  | nil => intro other found; cases found; rfl
  | cons first rest ih =>
    intro other found
    cases found with
    | cons otherFirst otherRest => rw [first.unique _ otherFirst, ih _ otherRest]


def SourceArmsChecked.normalize {source : List (SourcePattern × Expr)}
    (checked : SourceArmsChecked program home source) :
    {arms // NormalizesArms program home source arms} :=
  match checked with
  | .nil => ⟨[], .nil⟩
  | .cons (body := body) first rest =>
    let head := first.normalize
    let tail := rest.normalize
    ⟨(head.val, body) :: tail.val, .cons head.property tail.property⟩

/-- The normalized source application consumes ordinary coverage and body checking. -/
theorem SourceArmsChecked.admits {source : List (SourcePattern × Expr)}
    {context evaluated final : FlowContext} {arguments : List Expr} {inputs : List Ty} {result : Ty}
    (checked : SourceArmsChecked program home source)
    (argumentsTyped : HasTypes program home context arguments inputs evaluated) (nonempty : source ≠ [])
    (covered : Covers program [argumentType inputs] (checked.normalize.val.map (fun arm => [arm.1])))
    (bodies : ArmsType program home evaluated (argumentType inputs) result [] checked.normalize.val final) :
    HasType program home context (.applyPatterns inputs arguments checked.normalize.val) result final := by
  have normalizedNonempty : checked.normalize.val ≠ [] := by
    cases checked with
    | nil => exact False.elim (nonempty rfl)
    | cons first rest => simp [SourceArmsChecked.normalize]
  exact .applyPatterns argumentsTyped normalizedNonempty covered bodies

/-- The actual normalized source program preserves realization and makes progress
at every reachable machine state, including during arguments and selected bodies. -/
theorem SourceArmsChecked.soundness {source : List (SourcePattern × Expr)}
    {context evaluated final : FlowContext} {environment : Environment} {arguments : List Expr} {inputs : List Ty} {result : Ty}
    (checkedProgram : program.Checked)
    (checked : SourceArmsChecked program home source)
    (argumentsTyped : HasTypes program home context arguments inputs evaluated) (nonempty : source ≠ [])
    (covered : Covers program [argumentType inputs] (checked.normalize.val.map (fun arm => [arm.1])))
    (bodies : ArmsType program home evaluated (argumentType inputs) result [] checked.normalize.val final)
    (store : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation) {state : Configuration}
    (run : Run program ⟨environment, .expression (.applyPatterns inputs arguments checked.normalize.val), []⟩ state) :
    ConfigurationTyped program final (.one result) state ∧
      (Terminal state ∨ ∃ next, Step program state next) ∧
      AddressedEnvironment.ConsumptionFrame program final.slots environment state.outerEnvironment ∧
      (state.environment.bindings.map Prod.fst).Nodup :=
  (checked.admits argumentsTyped nonempty covered bodies).soundness checkedProgram store issued run


/-- The optional finite-call contract additionally constructs a unique typed
value and successor store. Ordinary source safety does not require FiniteCalls. -/
theorem SourceArmsChecked.correctness {source : List (SourcePattern × Expr)}
    {context evaluated final : FlowContext} {environment : Environment}
    {arguments : List Expr} {inputs : List Ty} {result : Ty}
    (checkedProgram : program.Checked)
    (checked : SourceArmsChecked program home source)
    (argumentsTyped : HasTypes program home context arguments inputs evaluated)
    (nonempty : source ≠ [])
    (covered : Covers program [argumentType inputs] (checked.normalize.val.map (fun arm => [arm.1])))
    (bodies : ArmsType program home evaluated (argumentType inputs) result [] checked.normalize.val final)
    (finite : FiniteCalls program (.applyPatterns inputs arguments checked.normalize.val))
    (environmentTyped : BindingMap.Typed program environment.heap environment.activation environment.bindings context)
    (issued : environment.supply.Issued environment.activation) :
    NormalizesArms program home source checked.normalize.val ∧
      (∀ other, NormalizesArms program home source other → other = checked.normalize.val) ∧
      ∃ value after, Evaluates program environment (.applyPatterns inputs arguments checked.normalize.val) value after ∧
        ValueHasType program value result ∧
        BindingMap.Typed program after.heap after.activation after.bindings final ∧
        after.supply.Issued after.activation ∧
        AddressedEnvironment.ConsumptionFrame program final.slots environment after ∧
        ∀ other otherAfter, Evaluates program environment (.applyPatterns inputs arguments checked.normalize.val) other otherAfter →
          other = value ∧ otherAfter = after := by
  exact ⟨checked.normalize.property, checked.normalize.property.unique,
    Grounded.correctness checkedProgram (checked.admits argumentsTyped nonempty covered bodies) finite environmentTyped issued⟩

end
end Grounded
