import Grounded.Patterns
import Grounded.Places
import Grounded.BindingAccess

/-! Expression checking uses declared callable interfaces. Declaration bodies
are checked separately; constant dependencies remain structurally well founded. -/
namespace Grounded

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
  | project {body : Expr} (closed : Structural body) (key : FieldKey) : Structural (.project body key)
  | constant (name : String) : Structural (.constant name)
  | construct {fields : List Expr} (identity : Nat) (tag : Option Nat)
      (residents : ∀ expression ∈ fields, Structural expression) :
      Structural (.construct identity tag fields)

abbrev FlowContext := List (BindingId × BindingState)

def FlowContext.slots (context : FlowContext) : List (BindingId × BindingType) :=
  context.map fun entry => (entry.1, entry.2.slot)

mutual
inductive HasType (program : Program) : Module → FlowContext → Expr → Ty → FlowContext → Prop where
  | unit {home context} : HasType program home context .unit .unit context
  | integer {home context type magnitude} (fits : type.Contains program.target magnitude) :
      HasType program home context (.integer type magnitude) (.integer type) context
  | character {home context number} (valid : UnicodeScalar number) :
      HasType program home context (.character number) .character context
  | group {home before after body type} (typed : HasType program home before body type after) :
      HasType program home before (.group body) type after
  | read {home context place type state available}
      (selected : lookup place.root context = some state)
      (path : PathType program home state.slot.type place.fields type)
      (selection : state.initialization.selectFields program state.slot.type place.fields = some available)
      (ready : available.Ready) (copyable : UsePermitted program.data .copy type) :
      HasType program home context (.read place) type context
  | move {home before after place type state available updated}
      (selected : lookup place.root before = some state)
      (path : PathType program home state.slot.type place.fields type)
      (selection : state.initialization.selectFields program state.slot.type place.fields = some available)
      (ready : available.Ready)
      (mask : state.initialization.writeFields program state.slot.type place.fields .absent = some updated)
      (context : replaceBinding place.root { state with initialization := updated } before = some after) :
      HasType program home before (.move place) type after
  | sequence {home before middle after first rest discarded type}
      (head : HasType program home before first discarded middle) (drop : UsePermitted program.data .discard discarded)
      (tail : HasType program home middle rest type after) :
      HasType program home before (.sequence first rest) type after
  | bind {home before middle after mutable name initial body localType type finalMask}
      (initialized : HasType program home before initial localType middle)
      (drop : UsePermitted program.data .discard localType)
      (continued : HasType program home ((name, ⟨⟨localType, mutable⟩, .present⟩) :: middle) body type
        ((name, ⟨⟨localType, mutable⟩, finalMask⟩) :: after))
      (fresh : name ∉ middle.map Prod.fst) :
      HasType program home before (.bind mutable name localType initial body) type after
  | tuple {home before middle after head tail first rest}
      (headTyped : HasType program home before head first middle)
      (tailTyped : HasTypes program home middle tail rest after) :
      HasType program home before (.tuple head tail) (.tuple first rest) after
  | project {home before after body key parent type index}
      (source : HasType program home before body parent after)
      (discard : UsePermitted program.data .discard parent) (selected : ProjectionType program home parent key index type) :
      HasType program home before (.project body key) type after
  | array {home before after elements element length}
      (residents : HasTypes program home before elements (List.replicate length element) after)
      (elementValid : FiniteLayout program.target program.data element)
      (size : length < 2 ^ program.target.pointerBits) :
      HasType program home before (.array elements) (.array element length) after
  | constant {home context name declaration type}
      (declared : program.constants name = some declaration)
      (visible : declaration.visibility.Allows declaration.home home)
      (resolved : ResolvesType program.aliases declaration.type type) (structural : Structural declaration.body)
      (initialized : HasType program declaration.home [] declaration.body type []) :
      HasType program home context (.constant name) type context
  | construct {home before after identity tag declaration schema fields}
      (declared : program.data identity = some declaration) (chosen : declaration.constructor tag = some schema)
      (finite : FiniteLayout program.target program.data (.nominal identity))
      (visible : declaration.visibility.Allows declaration.home home)
      (access : ∀ field ∈ schema.residents, field.visibility.Allows declaration.home home)
      (residents : HasTypes program home before fields (schema.residents.map Field.type) after) :
      HasType program home before (.construct identity tag fields) (.nominal identity) after
  | call {home before after identity arguments declaration}
      (declared : program.functions identity = some declaration)
      (visible : declaration.visibility.Allows declaration.home home)
      (inputs : HasTypes program home before arguments (declaration.parameters.map fun parameter => parameter.2.type) after) :
      HasType program home before (.call identity arguments) declaration.result after
  | assign {home before evaluated restored after place value rest type result state updated}
      (resident : HasType program home before value type evaluated)
      (selected : lookup place.root evaluated = some state)
      (path : PathType program home state.slot.type place.fields type)
      (writable : state.slot.mutable = true) (discard : UsePermitted program.data .discard type)
      (mask : state.initialization.writeFields program state.slot.type place.fields .present = some updated)
      (context : replaceBinding place.root { state with initialization := updated } evaluated = some restored)
      (continued : HasType program home restored rest result after) :
      HasType program home before (.assign place value rest) result after
  | applyPatterns {home before evaluated after inputs arguments arms result}
      (argumentsTyped : HasTypes program home before arguments inputs evaluated)
      (nonempty : arms ≠ []) (covered : Covers program [argumentType inputs] (arms.map fun arm => [arm.1]))
      (bodies : ArmsType program home evaluated (argumentType inputs) result [] arms after) :
      HasType program home before (.applyPatterns inputs arguments arms) result after

inductive HasTypes (program : Program) : Module → FlowContext → List Expr → List Ty → FlowContext → Prop where
  | nil {home context} : HasTypes program home context [] [] context
  | cons {home before middle after head tail first rest}
      (headTyped : HasType program home before head first middle)
      (tailTyped : HasTypes program home middle tail rest after) :
      HasTypes program home before (head :: tail) (first :: rest) after
inductive ArmsType (program : Program) :
    Module → FlowContext → Ty → Ty → List Pattern → List (Pattern × Expr) → FlowContext → Prop where
  | empty {home before after subject result previous} : ArmsType program home before subject result previous [] after
  | clause {home before after subject result previous pattern body rest bindings localsAfter}
      (patternTyped : PatternType program home pattern subject bindings)
      (distinct : ((bindings ++ before.slots).map Prod.fst).Nodup)
      (useful : Useful program subject previous pattern)
      (bodyTyped : HasType program home (initializedContext bindings ++ before) body result (localsAfter ++ after))
      (localSlots : FlowContext.slots localsAfter = bindings)
      (tailTyped : ArmsType program home before subject result (previous ++ [pattern]) rest after) :
      ArmsType program home before subject result previous ((pattern, body) :: rest) after
end

theorem HasType.slots {program : Program} {home : Module} {before after : FlowContext}
    {expression : Expr} {type : Ty} (checked : HasType program home before expression type after) :
    after.slots = before.slots := by
  induction checked using HasType.rec
    (motive_2 := fun _ before _ _ after _ => after.slots = before.slots)
    (motive_3 := fun _ before _ _ _ arms after _ => arms ≠ [] → after.slots = before.slots) with
  | unit | integer | character | read | constant => rfl
  | group _ ih | project _ _ _ ih | array _ _ _ ih | construct _ _ _ _ _ _ ih | call _ _ _ ih => exact ih
  | move selected path selection ready mask context =>
    exact replaceBinding.map_same BindingState.slot selected context rfl
  | sequence head drop tail headIH tailIH => exact tailIH.trans headIH
  | bind initialized drop continued fresh initialIH bodyIH =>
    have outer := congrArg List.tail bodyIH
    exact outer.trans initialIH
  | tuple head tail headIH tailIH => exact tailIH.trans headIH
  | assign resident selected path writable discard mask context continued residentIH continuedIH =>
    exact continuedIH.trans ((replaceBinding.map_same BindingState.slot selected context rfl).trans residentIH)
  | applyPatterns arguments nonempty covered bodies argumentsIH bodiesIH =>
    exact (bodiesIH nonempty).trans argumentsIH
  | nil => rfl
  | cons head tail headIH tailIH => exact tailIH.trans headIH
  | empty => rename_i nonempty; exact False.elim (nonempty rfl)
  | clause pattern distinct useful body localSlots tail bodyIH tailIH =>
    simp only [FlowContext.slots, List.map_append] at bodyIH
    change FlowContext.slots _ ++ FlowContext.slots _ = FlowContext.slots _ ++ FlowContext.slots _ at bodyIH
    rw [localSlots] at bodyIH
    have initialized : ∀ bindings, FlowContext.slots (initializedContext bindings) = bindings := by
      intro bindings
      simp [FlowContext.slots, initializedContext, List.map_map, Function.comp_def]
    rw [initialized] at bodyIH
    exact List.append_cancel_left bodyIH


/-- Recover the selected body's original flow derivation and actual input
bindings. Alternative bodies do not supply runtime state. -/
theorem ArmsType.selected {program : Program} {home : Module} {before after : FlowContext}
    {subject result : Ty} {previous : List Pattern} {arms : List (Pattern × Expr)}
    (checked : ArmsType program home before subject result previous arms after)
    {value : Value} (resident : ValueHasType program value subject)
    {bindings : List BindingInput} {body : Expr}
    (selected : selectArm value arms = some (bindings, body)) :
    ∃ locals localsAfter pattern, (pattern, body) ∈ arms ∧
      BindingInputsTyped program bindings ∧ (bindings.map fun input => (input.name, input.slot)) = locals ∧
      (∀ binding ∈ locals, UsePermitted program.data .discard binding.2.type) ∧
      HasType program home (initializedContext locals ++ before) body result (localsAfter ++ after) ∧
      FlowContext.slots localsAfter = locals ∧ ((locals ++ before.slots).map Prod.fst).Nodup := by
  induction arms generalizing previous with
  | nil => simp [selectArm] at selected
  | cons arm arms ih =>
    cases checked with
    | clause patternTyped distinct useful bodyTyped localSlots tailTyped =>
      simp only [selectArm] at selected
      split at selected
      next matched found =>
        cases Option.some.inj selected
        obtain ⟨inputsTyped, slots⟩ := patternTyped.bindings resident found
          (List.nodup_append.mp (by simpa only [List.map_append] using distinct)).1
        exact ⟨_, _, _, by simp only [List.mem_cons]; exact Or.inl rfl,
          inputsTyped, slots, patternTyped.disposable, bodyTyped, localSlots, distinct⟩
      next missed =>
        obtain ⟨locals, localsAfter, pattern, member, inputsTyped, slots, disposable, bodyTyped, localSlots, distinct⟩ :=
          ih tailTyped selected
        exact ⟨locals, localsAfter, pattern, List.mem_cons_of_mem _ member, inputsTyped, slots,
          disposable, bodyTyped, localSlots, distinct⟩

/-- Bodies may finish with holes; scope disposal requires discardable
parameter types in this fragment. No completed execution is assumed. -/
structure FunctionChecked (program : Program) (declaration : FunctionDecl) : Prop where
  distinct : (declaration.parameters.map Prod.fst).Nodup
  disposable : ∀ parameter ∈ declaration.parameters, UsePermitted program.data .discard parameter.2.type
  body : ∃ after, HasType program declaration.home (initializedContext declaration.parameters)
    declaration.body declaration.result after

def Program.Checked (program : Program) : Prop :=
  ∀ identity declaration, program.functions identity = some declaration → FunctionChecked program declaration

theorem HasTypes.slots {program : Program} {home : Module} {before after : FlowContext}
    {expressions : List Expr} {types : List Ty} (checked : HasTypes program home before expressions types after) :
    after.slots = before.slots := by
  induction expressions generalizing before after types with
  | nil => cases checked; rfl
  | cons head tail ih =>
    cases checked with
    | cons headTyped tailTyped => exact (ih tailTyped).trans headTyped.slots

theorem ArmsType.slots {program : Program} {home : Module} {before after : FlowContext}
    {subject result : Ty} {previous : List Pattern} {arms : List (Pattern × Expr)}
    (checked : ArmsType program home before subject result previous arms after) (nonempty : arms ≠ []) :
    after.slots = before.slots := by
  cases checked with
  | empty => exact False.elim (nonempty rfl)
  | clause pattern distinct useful body localSlots tail =>
    have same := body.slots
    simp only [FlowContext.slots, List.map_append] at same
    change FlowContext.slots _ ++ FlowContext.slots _ = FlowContext.slots _ ++ FlowContext.slots _ at same
    rw [localSlots] at same
    simpa [FlowContext.slots, initializedContext, List.map_map, Function.comp_def] using same


end Grounded

