import Grounded.Matching
import Grounded.BindingStorage

/-! Static pattern admission, constructor-space coverage and their runtime contracts.
Selection and binding are derived for the actual subject, not supplied by checking. -/
namespace Grounded

/-- Constructor signatures are shared by pattern typing and coverage specialization. -/
inductive HeadType (program : Program) : Head → Ty → List Ty → Prop where
  | unit : HeadType program .unit .unit []
  | integer {type : IntegerType} {number : Int} (fits : type.Contains program.target number) :
      HeadType program (.integer type number) (.integer type) []
  | character {number : Nat} (valid : UnicodeScalar number) :
      HeadType program (.character number) .character []
  | tuple (first : Ty) (rest : List Ty) : HeadType program .tuple (.tuple first rest) (first :: rest)
  | array (element : Ty) (length : Nat) : HeadType program .array (.array element length) (List.replicate length element)
  | nominal {identity : Nat} {tag : Option Nat} {declaration : DataDecl} {schema : Fields}
      (declared : program.data identity = some declaration)
      (chosen : declaration.constructor tag = some schema) :
      HeadType program (.nominal identity tag) (.nominal identity) (schema.residents.map Field.type)

theorem HeadType.fields_unique {program : Program} {head : Head} {type : Ty}
    {first second : List Ty} (left : HeadType program head type first)
    (right : HeadType program head type second) : first = second := by
  cases left <;> cases right <;> simp_all


def Head.Accessible (program : Program) (home : Module) : Head → Prop
  | .nominal identity tag => ∃ declaration schema,
      program.data identity = some declaration ∧ declaration.constructor tag = some schema ∧
      declaration.visibility.Allows declaration.home home ∧
      declaration.ClosedAt home ∧
      ∀ field ∈ schema.residents, field.visibility.Allows declaration.home home
  | _ => True

mutual
inductive PatternType (program : Program) (home : Module) : Pattern → Ty → List (BindingId × BindingType) → Prop where
  | wildcard {type : Ty} (discard : UsePermitted program.data .discard type) : PatternType program home .wildcard type []
  | binder (name : BindingId) {type : Ty} :
      PatternType program home (.binder name type) type [(name, ⟨type, false⟩)]
  | literal {type : Ty} {value : Value} (typed : ValueHasType program value type)
      (discard : UsePermitted program.data .discard type) : PatternType program home (.literal (some type) value) type []
  | node {head : Head} {patterns : List Pattern} {type : Ty} {fields : List Ty} {bindings : List (BindingId × BindingType)}
      (shape : HeadType program head type fields) (access : head.Accessible program home)
      (fieldsTyped : PatternsType program home patterns fields bindings) :
      PatternType program home (.node head patterns) type bindings
inductive PatternsType (program : Program) (home : Module) : List Pattern → List Ty → List (BindingId × BindingType) → Prop where
  | nil : PatternsType program home [] [] []
  | cons {pattern : Pattern} {patterns : List Pattern} {type : Ty} {types : List Ty}
      {first rest : List (BindingId × BindingType)} (headTyped : PatternType program home pattern type first)
      (tailTyped : PatternsType program home patterns types rest) :
      PatternsType program home (pattern :: patterns) (type :: types) (first ++ rest)
end

/-- Static matrix specialization, not an assumption that an execution will match. -/
def Pattern.specialize (head : Head) (arity : Nat) : Pattern → Option (List Pattern)
  | .wildcard | .binder _ _ => some (List.replicate arity .wildcard)
  | .node selected fields => if selected = head ∧ fields.length = arity then some fields else none
  | .literal _ value => if value.head = head ∧ value.children.length = arity
      then some (value.children.map (Pattern.literal none)) else none

def specializeRow (head : Head) (arity : Nat) : List Pattern → Option (List Pattern)
  | [] => none
  | pattern :: tail => (pattern.specialize head arity).map (· ++ tail)

/-- Closed-head coverage and owned deconstruction use the same declaration
authority. An external non-exhaustive enum must be covered through whole values. -/
def Ty.ClosedHeads (program : Program) (home : Module) : Ty → Prop
  | .nominal identity => ∃ declaration, program.data identity = some declaration ∧ declaration.ClosedAt home
  | _ => True

/-- Rows that remain applicable independently of the observed constructor. -/
def defaultRow : List Pattern → Option (List Pattern)
  | .wildcard :: tail | .binder _ _ :: tail => some tail
  | _ => none

inductive Covers (program : Program) (home : Module) : List Ty → List (List Pattern) → Prop where
  | done {rows : List (List Pattern)} (empty : [] ∈ rows) : Covers program home [] rows
  | fallback {type : Ty} {types : List Ty} {rows : List (List Pattern)}
      (remaining : Covers program home types (rows.filterMap defaultRow)) :
      Covers program home (type :: types) rows
  | split {type : Ty} {types : List Ty} {rows : List (List Pattern)}
      (closed : type.ClosedHeads program home)
      (branches : ∀ head fields, HeadType program head type fields →
        Covers program home (fields ++ types) (rows.filterMap (specializeRow head fields.length))) :
      Covers program home (type :: types) rows


/-- A static witness distinguishes each clause from its source-order predecessors.
It is a typed datum, not an assumed result of the subject expression. -/
def Useful (program : Program) (type : Ty) (previous : List Pattern) (pattern : Pattern) : Prop :=
  ∃ value, ValueHasType program value type ∧ pattern.matchValue value ≠ none ∧
    ∀ earlier ∈ previous, earlier.matchValue value = none

variable {program : Program} {home : Module}

/-- A declared external non-exhaustive enum cannot be justified by enumerating
its currently known constructors, even when there are no current variants. -/
theorem Ty.ClosedHeads.nonexhaustive_external {identity : Nat} {declaration : DataDecl}
    {variants : List Fields} (declared : program.data identity = some declaration)
    (shape : declaration.shape = .enumeration variants true)
    (external : home.package ≠ declaration.home.package) :
    ¬ Ty.ClosedHeads program home (.nominal identity) := by
  intro closed
  obtain ⟨actual, found, authority⟩ := closed
  cases Option.some.inj (found.symm.trans declared)
  simp [DataDecl.ClosedAt, shape, external] at authority

/-- Owned field matching requires the same closed-constructor authority used
by exhaustive splitting; visibility alone cannot create that authority. -/
theorem HeadType.closed_of_access {head : Head} {type : Ty} {fields : List Ty}
    (shape : HeadType program head type fields) (access : head.Accessible program home) :
    type.ClosedHeads program home := by
  cases shape <;> try trivial
  obtain ⟨declaration, schema, found, chosen, visible, closed, fields⟩ := access
  exact ⟨declaration, found, closed⟩

/-- Coverage of an open constructor space necessarily covers the remaining
columns through constructor-independent rows. Known variants cannot discharge it. -/
theorem Covers.open_requires_default {type : Ty} {types : List Ty} {rows : List (List Pattern)}
    (covered : Covers program home (type :: types) rows) (openHeads : ¬ type.ClosedHeads program home) :
    Covers program home types (rows.filterMap defaultRow) := by
  cases covered with
  | fallback remaining => exact remaining
  | split closed branches => exact False.elim (openHeads closed)

theorem Covers.nonexhaustive_requires_whole {identity : Nat} {declaration : DataDecl}
    {variants : List Fields} {rows : List (List Pattern)}
    (declared : program.data identity = some declaration)
    (shape : declaration.shape = .enumeration variants true)
    (external : home.package ≠ declaration.home.package)
    (covered : Covers program home [.nominal identity] rows) :
    ∃ row ∈ rows, defaultRow row = some [] := by
  have remaining := covered.open_requires_default
    (Ty.ClosedHeads.nonexhaustive_external declared shape external)
  cases remaining with
  | done included => exact List.mem_filterMap.mp included

/-- For exact-linear external enums, owned matching can only bind the whole
owner. Wildcards, constant comparison and field extraction cannot erase it.
The negative permission may come from an explicit principal or resident fields. -/
theorem PatternType.nonexhaustive_exact_forward {identity : Nat} {declaration : DataDecl}
    {variants : List Fields} {pattern : Pattern} {bindings : List (BindingId × BindingType)}
    (declared : program.data identity = some declaration)
    (shape : declaration.shape = .enumeration variants true)
    (external : home.package ≠ declaration.home.package)
    (exactOwner : ¬ UsePermitted program.data .discard (.nominal identity))
    (typed : PatternType program home pattern (.nominal identity) bindings) :
    ∃ name, pattern = .binder name (.nominal identity) ∧
      bindings = [(name, ⟨.nominal identity, false⟩)] := by
  cases typed with
  | wildcard discard => exact False.elim (exactOwner discard)
  | binder name => exact ⟨name, rfl, rfl⟩
  | literal resident discard => exact False.elim (exactOwner discard)
  | node headShape access fields =>
    exact False.elim (Ty.ClosedHeads.nonexhaustive_external declared shape external
      (headShape.closed_of_access access))


/-- Runtime typing produces the constructor signature consumed by both pattern
binding and exhaustive dispatch; neither consumer guesses resident types. -/
theorem ValueHasType.decompose {value : Value} {type : Ty} (typed : ValueHasType program value type) :
    ∃ fields, HeadType program value.head type fields ∧ ValuesHaveTypes program value.children fields := by
  cases typed with
  | unit => exact ⟨[], .unit, .nil⟩
  | integer fits => exact ⟨[], .integer fits, .nil⟩
  | character valid => exact ⟨[], .character valid, .nil⟩
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

theorem PatternType.bindings {pattern : Pattern} {type : Ty} {context : List (BindingId × BindingType)}
    (typed : PatternType program home pattern type context) {value : Value}
    (valueTyped : ValueHasType program value type) {bindings : PatternMatch}
    (matched : pattern.matchValue value = some bindings) (distinct : (context.map Prod.fst).Nodup) :
    BindingInputsTyped program bindings.bindings ∧ (bindings.bindings.map fun input => (input.name, input.slot)) = context := by
  induction typed using PatternType.rec
    (motive_2 := fun patterns types context _ => ∀ values, ValuesHaveTypes program values types →
      ∀ bindings, matchPatterns patterns values = some bindings → (context.map Prod.fst).Nodup →
        BindingInputsTyped program bindings.bindings ∧ (bindings.bindings.map fun input => (input.name, input.slot)) = context)
    generalizing value bindings with
  | wildcard discard =>
    simp only [Pattern.matchValue, Option.some.injEq] at matched
    subst bindings
    exact ⟨.nil, rfl⟩
  | binder name =>
    simp only [Pattern.matchValue, Option.some.injEq] at matched
    subst bindings
    exact ⟨.cons valueTyped .nil (by simp), rfl⟩
  | literal typed discard =>
    simp only [Pattern.matchValue] at matched
    split at matched
    next equal =>
      have empty := Option.some.inj matched
      subst bindings
      exact ⟨.nil, rfl⟩
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
      exact fieldsIH _ children bindings matched distinct
    next different => contradiction
  | nil =>
    rename_i values valuesTyped bindings matched distinct
    cases valuesTyped
    simp only [matchPatterns, Option.some.injEq] at matched
    subst bindings
    exact ⟨.nil, rfl⟩
  | @cons pattern patterns type types frontContext backContext head tail headIH tailIH =>
    rename_i values valuesTyped bindings matched distinct
    cases valuesTyped with
    | @cons value values type types first rest =>
      simp only [matchPatterns] at matched
      cases headMatch : pattern.matchValue value with
      | none => simp [headMatch] at matched
      | some front =>
        cases tailMatch : matchPatterns patterns values with
        | none => simp [headMatch, tailMatch] at matched
        | some back =>
          simp [headMatch, tailMatch] at matched
          subst bindings
          have separated := List.nodup_append.mp (by simpa only [List.map_append] using distinct)
          obtain ⟨frontTyped, frontSlots⟩ := headIH first headMatch separated.1
          obtain ⟨backTyped, backSlots⟩ := tailIH _ rest _ tailMatch separated.2.1
          have slots : ((front ++ back).bindings.map fun input => (input.name, input.slot)) =
              frontContext ++ backContext := by simp only [PatternMatch.append_bindings, List.map_append, frontSlots, backSlots]
          refine ⟨frontTyped.append backTyped ?_, slots⟩
          have names := congrArg (List.map Prod.fst) slots
          simp only [List.map_map, Function.comp_def] at names
          rw [← names] at distinct
          exact distinct

/-- Every resident scheduled by the actual successful match has zero-use
permission from the same pattern derivation; failed alternatives supply nothing. -/
theorem PatternType.discarded {pattern : Pattern} {type : Ty} {context : List (BindingId × BindingType)}
    (typed : PatternType program home pattern type context) {value : Value}
    (valueTyped : ValueHasType program value type) {result : PatternMatch}
    (matched : pattern.matchValue value = some result) :
    ∀ resident ∈ result.discarded, ∃ type, ValueHasType program resident type ∧
      UsePermitted program.data .discard type := by
  induction typed using PatternType.rec
    (motive_2 := fun patterns types context _ => ∀ values, ValuesHaveTypes program values types →
      ∀ result, matchPatterns patterns values = some result →
        ∀ resident ∈ result.discarded, ∃ type, ValueHasType program resident type ∧
          UsePermitted program.data .discard type)
    generalizing value result with
  | wildcard discard =>
    simp only [Pattern.matchValue] at matched
    cases Option.some.inj matched
    intro resident member
    have same : resident = value := by simpa using member
    subst resident
    exact ⟨_, valueTyped, discard⟩
  | binder name =>
    simp only [Pattern.matchValue] at matched
    cases Option.some.inj matched
    simp
  | literal typed discard =>
    simp only [Pattern.matchValue] at matched
    split at matched
    next same =>
      cases Option.some.inj matched
      intro resident member
      have equal : resident = value := by simpa using member
      subst resident
      exact ⟨_, valueTyped, discard⟩
    next impossible => contradiction
  | @node head patterns type fields context shape access fieldsTyped fieldsIH =>
    simp only [Pattern.matchValue] at matched
    split at matched
    next same =>
      obtain ⟨types, actual, children⟩ := valueTyped.decompose
      rw [← same] at actual
      have aligned : fields = types := by
        cases shape <;> cases actual <;> simp_all
      subst types
      exact fieldsIH _ children result matched
    next impossible => contradiction
  | nil =>
    rename_i values valuesTyped result matched resident member
    cases valuesTyped
    simp only [matchPatterns, Option.some.injEq] at matched
    subst result
    simp [PatternMatch.empty] at member
  | @cons pattern patterns type types frontContext backContext head tail headIH tailIH =>
    rename_i values valuesTyped result matched resident member

    cases valuesTyped with
    | @cons value values type types first rest =>
      cases headMatch : pattern.matchValue value with
      | none => simp [matchPatterns, headMatch] at matched
      | some front =>
        cases tailMatch : matchPatterns patterns values with
        | none => simp [matchPatterns, headMatch, tailMatch] at matched
        | some back =>
          have joined : front ++ back = result := by
            simpa [matchPatterns, headMatch, tailMatch] using matched
          subst result
          rcases List.mem_append.mp member with member | member
          · exact tailIH _ rest _ tailMatch resident member
          · exact headIH first headMatch resident member
/-- Constructor-space coverage constructs an actual first matching clause. No
post-evaluation match result occurs among the admission premises. -/
theorem Covers.selectArm {type : Ty} {arms : List (Pattern × Expr)} {value : Value}
    (covered : Covers program home [type] (arms.map (fun arm => [arm.1])))
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
          simp [PatternMatch.append_assoc]
  have literalFields : ∀ (expected actual : List Value) (bindings : PatternMatch),
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
          cases tailMatch : matchPatterns (rest.map (Pattern.literal none)) values with
          | none => simp [tailMatch] at matched
          | some result => exact congrArg (List.cons expected) (ih values result tailMatch)
        next different => simp at matched
  have valueExt : ∀ (left right : Value), left.head = right.head → left.children = right.children → left = right := by
    intro left right heads children
    cases left <;> cases right <;> simp_all [Value.head, Value.children]
  have matrixSound : ∀ {types : List Ty} {rows : List (List Pattern)}, Covers program home types rows →
      ∀ values, ValuesHaveTypes program values types →
      ∃ row ∈ rows, ∃ bindings, matchPatterns row values = some bindings := by
    intro types rows coverage
    induction coverage with
    | done contained =>
      intro values typed
      cases typed
      exact ⟨[], contained, .empty, by simp [matchPatterns]⟩
    | @fallback type types rows remaining ih =>
      intro values typed
      cases typed with
      | @cons value values _ _ first rest =>
        obtain ⟨row, included, bindings, matched⟩ := ih _ rest
        obtain ⟨original, originalIncluded, selected⟩ := List.mem_filterMap.mp included
        cases original with
        | nil => simp [defaultRow] at selected
        | cons pattern patterns =>
          cases pattern with
          | wildcard =>
            simp only [defaultRow, Option.some.injEq] at selected
            subst row
            exact ⟨_, originalIncluded, (⟨[], [value]⟩ : PatternMatch) ++ bindings, by simp [matchPatterns, Pattern.matchValue, matched]⟩
          | binder name slot =>
            simp only [defaultRow, Option.some.injEq] at selected
            subst row
            exact ⟨_, originalIncluded, (⟨[⟨name, ⟨slot, false⟩, value⟩], []⟩ : PatternMatch) ++ bindings,
              by simp [matchPatterns, Pattern.matchValue, matched]⟩
          | literal _ _ | node _ _ => simp [defaultRow] at selected
    | @split type types rows closed branches ih =>
      intro values typed
      cases typed with
      | @cons value values _ _ first rest =>
        obtain ⟨fields, headTyped, childrenTyped⟩ := first.decompose
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
              | binder name type => simp [Pattern.specialize] at frontSelected; subst front; simp
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
            | wildcard => exact ⟨⟨[], [value]⟩, by simp [Pattern.matchValue]⟩
            | binder name type => exact ⟨⟨[⟨name, ⟨type, false⟩, value⟩], []⟩, by simp [Pattern.matchValue]⟩
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
                exact ⟨⟨[], [value]⟩, by simp [Pattern.matchValue, equal]⟩
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
  have noneMeansMissing : ∀ (arms : List (Pattern × Expr)), Grounded.selectArm value arms = none →
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



/-- Positional selection retains the existing pattern derivation and field type. -/
theorem PatternsType.at {patterns : List Pattern} {types : List Ty} {context : List (BindingId × BindingType)}
    (typed : PatternsType program home patterns types context) {index : Nat} {pattern : Pattern}
    (selected : patterns[index]? = some pattern) :
    ∃ type bindings, types[index]? = some type ∧ PatternType program home pattern type bindings := by
  induction patterns generalizing types context index with
  | nil => simp at selected
  | cons head tail ih =>
    cases typed with
    | cons first rest =>
      cases index with
      | zero => cases selected; exact ⟨_, _, rfl, first⟩
      | succ index => exact ih rest selected

/-- Every observed subpattern inherits its actual resident typing and ownership
rules from the selected pattern's single authoritative derivation. -/
theorem PatternType.subject_at {pattern selected : Pattern} {value owner : Value}
    (focus : Pattern.SubjectAt pattern value selected owner)
    {type : Ty} {context : List (BindingId × BindingType)}
    (typed : PatternType program home pattern type context) (resident : ValueHasType program value type) :
    ∃ childType bindings, ValueHasType program owner childType ∧ PatternType program home selected childType bindings := by
  induction focus generalizing type context with
  | root => exact ⟨_, _, resident, typed⟩
  | child same patternAt valueAt nested ih =>
    cases typed with
    | node shape access fieldsTyped =>
      rename_i fields
      obtain ⟨types, actual, children⟩ := resident.decompose
      rw [← same] at actual
      have aligned : fields = types := by
        cases shape <;> cases actual <;> simp_all
      subst types
      obtain ⟨childType, bindings, typeAt, childTyped⟩ := fieldsTyped.at patternAt
      obtain ⟨child, found, childResident⟩ := children.select _ _ typeAt
      cases Option.some.inj (found.symm.trans valueAt)
      exact ih childTyped childResident

end Grounded
