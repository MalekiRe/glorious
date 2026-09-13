import GloriousLanguage.PredicateAdmission

/-! Interpretation of the existing term and predicate syntax. Quantified
arguments retain one fixed source kinding context; freshening and substitution
must preserve meaning without enlarging that context's instantiation domain. -/
namespace Glorious.Language

universe u

namespace PredicateSemantics

abbrev Valuation (α : Type u) := Identity → Kind → α

/-- An algebra consumes the actual source head and ordered children. The
head law prevents it from observing a child's old syntactic representation. -/
structure TermAlgebra (α : Type u) where
  node : Term → List α → α
  sameHead : ∀ {left right}, SameHead left right → ∀ children, node left children = node right children

def TermAlgebra.eval {α : Type u} (algebra : TermAlgebra α) (valuation : Valuation α) (term : Term) : α :=
  match term with
  | .parameter id kind => valuation id kind
  | term => algebra.node term (term.children.attach.map (fun child => algebra.eval valuation child.val))
termination_by sizeOf term
decreasing_by exact Term.child_sizeOf child.property

@[simp] theorem TermAlgebra.eval_parameter {α : Type u} (algebra : TermAlgebra α)
    (valuation : Valuation α) (id : Identity) (kind : Kind) :
    algebra.eval valuation (.parameter id kind) = valuation id kind := by
  rw [TermAlgebra.eval]

theorem TermAlgebra.eval_node {α : Type u} (algebra : TermAlgebra α) (valuation : Valuation α)
    {term : Term} (notParameter : ∀ id kind, term ≠ .parameter id kind) :
    algebra.eval valuation term = algebra.node term (term.children.map (algebra.eval valuation)) := by
  cases term <;> simp only [TermAlgebra.eval]
  case parameter id kind => exact False.elim (notParameter id kind rfl)
  all_goals congr 1 <;> simp

/-- A term observes only the parameter occurrences in its own source tree. -/
theorem TermAlgebra.eval_congr {α : Type u} (algebra : TermAlgebra α) {left right : Valuation α}
    (term : Term) (agree : ∀ id kind, Occurs (.parameter id kind) term → left id kind = right id kind) :
    algebra.eval left term = algebra.eval right term := by
  by_cases parameter : ∃ id kind, term = .parameter id kind
  · obtain ⟨id,kind,rfl⟩ := parameter
    simpa only [TermAlgebra.eval_parameter] using agree id kind .here
  · have notParameter : ∀ id kind, term ≠ .parameter id kind := fun id kind same => parameter ⟨id,kind,same⟩
    rw [algebra.eval_node _ notParameter,algebra.eval_node _ notParameter]
    congr 1
    apply List.map_congr_left
    intro child member
    exact algebra.eval_congr child (fun id kind occurs => agree id kind (.child member occurs))
termination_by term
decreasing_by exact Term.child_sizeOf member

def TermAlgebra.substituteValuation {α : Type u} (algebra : TermAlgebra α)
    (valuation : Valuation α) (substitution : Substitution) : Valuation α :=
  fun id kind => ((substitution.get id).map (algebra.eval valuation)).getD (valuation id kind)

theorem Term.sameHead_mapChildren (term : Term) (f : Term → Term) : SameHead term (term.mapChildren f) := by
  cases term <;> simp only [SameHead,Term.mapChildren,List.map_map,Function.comp_def]

theorem Term.mapChildren_ne_parameter {term : Term} (notParameter : ∀ id kind, term ≠ .parameter id kind)
    (f : Term → Term) : ∀ id kind, term.mapChildren f ≠ .parameter id kind := by
  intro id kind same
  cases term <;> simp only [Term.mapChildren] at same
  all_goals cases same
  exact notParameter _ _ rfl

/-- Every simultaneous parameter map is interpreted by one initial
valuation. Ordinary substitution, alpha-renaming and kind-totalized proof
substitution consume this same constructor-level interpretation theorem. -/
theorem TermAlgebra.eval_parameter_map {α : Type u} (algebra : TermAlgebra α)
    (valuation : Valuation α) (map : Term → Term)
    (nodes : ∀ term, (∀ id kind, term ≠ .parameter id kind) → map term = term.mapChildren map)
    (term : Term) :
    algebra.eval valuation (map term) =
      algebra.eval (fun id kind => algebra.eval valuation (map (.parameter id kind))) term := by
  by_cases parameter : ∃ id kind, term = .parameter id kind
  · obtain ⟨id,kind,rfl⟩ := parameter
    simp only [TermAlgebra.eval_parameter]
  · have notParameter : ∀ id kind, term ≠ .parameter id kind := fun id kind same => parameter ⟨id,kind,same⟩
    rw [nodes term notParameter]
    rw [algebra.eval_node _ (Term.mapChildren_ne_parameter notParameter _),algebra.eval_node _ notParameter]
    rw [← algebra.sameHead (Term.sameHead_mapChildren term _),Term.mapChildren_children,List.map_map]
    congr 1
    apply List.map_congr_left
    intro child member
    exact algebra.eval_parameter_map valuation map nodes child
termination_by term
decreasing_by exact Term.child_sizeOf member

/-- The single source substitution operation is interpreted by replacing
parameter valuations simultaneously, not by re-evaluating inserted terms. -/
theorem TermAlgebra.eval_substitute {α : Type u} (algebra : TermAlgebra α)
    (valuation : Valuation α) (substitution : Substitution) (term : Term) :
    algebra.eval valuation (term.substitute substitution) =
      algebra.eval (algebra.substituteValuation valuation substitution) term := by
  rw [algebra.eval_parameter_map valuation (Term.substitute substitution)
    (fun _ notParameter => Term.substitute_eq_mapChildren substitution notParameter)]
  apply congrArg (fun current => algebra.eval current term)
  funext id kind
  cases found : substitution.get id <;>
    simp only [Term.substitute,found,Option.getD,TermAlgebra.eval_parameter,
      TermAlgebra.substituteValuation,Option.map]

theorem Term.renameParameters_eq_mapChildren (rename : Identity → Identity) {term : Term}
    (notParameter : ∀ id kind, term ≠ .parameter id kind) :
    term.renameParameters rename = term.mapChildren (Term.renameParameters rename) := by
  cases term <;> simp only [Term.renameParameters,Term.mapChildren]
  exact False.elim (notParameter _ _ rfl)

theorem TermAlgebra.eval_renameParameters {α : Type u} (algebra : TermAlgebra α)
    (valuation : Valuation α) (rename : Identity → Identity) (term : Term) :
    algebra.eval valuation (term.renameParameters rename) =
      algebra.eval (fun id kind => valuation (rename id) kind) term := by
  rw [algebra.eval_parameter_map valuation (Term.renameParameters rename)
    (fun _ notParameter => Term.renameParameters_eq_mapChildren rename notParameter)]
  simp only [Term.renameParameters,TermAlgebra.eval_parameter]

/-- Renaming a quantified binder list changes its keys, never its chosen
caller values. Injection is required only on those actual binder identities. -/
theorem _root_.Glorious.Language.Instantiates.renameParameters
    {binders : List Binder} {values : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders values substitution) (rename : Identity → Identity)
    (injective : ∀ first ∈ binders, ∀ second ∈ binders, rename first.id = rename second.id → first.id = second.id) :
    Instantiates (binders.map (Binder.renameParameters rename)) values
      (substitution.map (fun entry => (rename entry.1,entry.2))) := by
  refine ⟨?_,?_,?_⟩
  · have unique := instantiated.1
    change List.Pairwise (fun left right => left ≠ right) _ at unique ⊢
    simp only [List.map_map,List.pairwise_map,Binder.renameParameters,Function.comp_def] at unique ⊢
    exact unique.imp_of_mem (fun first second different same => different (injective _ first _ second same))
  · have alignment := instantiated.2.1
    clear instantiated substitution
    induction alignment with
    | nil => exact .nil
    | cons kind tail ih => exact .cons kind (ih (fun first member second present =>
        injective first (List.mem_cons_of_mem _ member) second (List.mem_cons_of_mem _ present)))
  · rw [instantiated.2.2]
    have maps : Prod.map rename (id : Term → Term) = (fun entry => (rename entry.1,entry.2)) := by
      funext entry; cases entry; rfl
    simpa only [maps,List.map_map,Function.comp_def,Binder.renameParameters] using
      (List.zip_map_left (f := rename) (l₁ := binders.map (·.id)) (l₂ := values)).symm

theorem _root_.Glorious.Language.Instantiates.of_renameParameters
    {binders : List Binder} {values : List Term} {substitution : Substitution} {rename : Identity → Identity}
    (instantiated : Instantiates (binders.map (Binder.renameParameters rename)) values substitution) :
    ∃ original, Instantiates binders values original ∧
      substitution = original.map (fun entry => (rename entry.1,entry.2)) := by
  refine ⟨(binders.map (·.id)).zip values,⟨?_,?_,rfl⟩,?_⟩
  · have unique := instantiated.1
    change List.Pairwise (fun left right => left ≠ right) _ at unique ⊢
    simp only [List.map_map,List.pairwise_map,Binder.renameParameters,Function.comp_def] at unique ⊢
    exact unique.imp (fun different same => different (congrArg rename same))
  · have alignment := instantiated.2.1
    clear instantiated substitution
    induction binders generalizing values with
    | nil => cases alignment; exact .nil
    | cons binder binders ih =>
      cases alignment with
      | cons kind tail => exact .cons kind (ih tail)
  · rw [instantiated.2.2]
    have maps : Prod.map rename (id : Term → Term) = (fun entry => (rename entry.1,entry.2)) := by
      funext entry; cases entry; rfl
    simpa only [maps,List.map_map,Function.comp_def,Binder.renameParameters] using
      (List.zip_map_left (f := rename) (l₁ := binders.map (·.id)) (l₂ := values))

/-- Bound variables and caller arguments have different valuations. An
argument supplied to a universal predicate is kinded in the fixed caller
context and is interpreted there, even if its parameter names coincide with
a source predicate binder. -/
def TermAlgebra.bindValuation {α : Type u} (algebra : TermAlgebra α)
    (caller current : Valuation α) (arguments : Substitution) : Valuation α :=
  fun id kind => ((arguments.get id).map (algebra.eval caller)).getD (current id kind)

theorem TermAlgebra.bindValuation_rename {α : Type u} (algebra : TermAlgebra α)
    (caller : Valuation α) {source target : Valuation α} (arguments : Substitution)
    (rename : Identity → Identity) (id : Identity) (kind : Kind)
    (separates : ∀ entry ∈ arguments, rename entry.1 = rename id → entry.1 = id)
    (agree : target (rename id) kind = source id kind) :
    algebra.bindValuation caller target (arguments.map (fun entry => (rename entry.1,entry.2))) (rename id) kind =
      algebra.bindValuation caller source arguments id kind := by
  simp only [TermAlgebra.bindValuation,Table.get_rename_keys rename arguments id separates,agree]

structure PredicateAlgebra (α : Type u) extends TermAlgebra α where
  outlives : α → α → Prop
  typeOutlives : α → α → Prop
  rows : α → α → Prop
  implements : DeclId → List α → Bool → Prop
  use : α → Quantity → Prop
  callable : α → List α → α → α → Bool → Prop
  runsIn : α → α → List α → α → Bool → Prop

/-- Universal arguments are drawn from the actual source kinding context,
which never changes while interpreting nested quantified requirements.
Defaults govern source admission; `Instantiates` supplies the chosen values. -/
def PredicateAlgebra.Holds {α : Type u} (algebra : PredicateAlgebra α)
    (program : Program) (context : Context) (caller current : Valuation α) (constraint : Constraint) : Prop :=
  match constraint with
  | .equal left right => algebra.eval current left = algebra.eval current right
  | .outlives long short => algebra.outlives (algebra.eval current long) (algebra.eval current short)
  | .typeOutlives type region => algebra.typeOutlives (algebra.eval current type) (algebra.eval current region)
  | .rowIncludes allowed required => algebra.rows (algebra.eval current allowed) (algebra.eval current required)
  | .implements trait arguments negative => algebra.implements trait (arguments.map (algebra.eval current)) negative
  | .use type quantity => algebra.use (algebra.eval current type) quantity
  | .callable receiver arguments result effects unsafeAllowed => algebra.callable (algebra.eval current receiver)
      (arguments.map (algebra.eval current)) (algebra.eval current result) (algebra.eval current effects) unsafeAllowed
  | .runsIn receiver access arguments after unsafeAllowed => algebra.runsIn (algebra.eval current receiver)
      (algebra.eval current access) (arguments.map (algebra.eval current)) (algebra.eval current after) unsafeAllowed
  | .quantified binders requirements =>
      ∀ values substitution, Instantiates binders values substitution →
        (∀ value ∈ values, Kinding program context value value.kind) →
        ∀ requirement ∈ requirements,
          algebra.Holds program context caller (algebra.bindValuation caller current substitution) requirement
termination_by constraint.quantifierCount
decreasing_by
  simp only [Constraint.quantifierCount]
  have smaller := List.nat_le_sum_of_mem (List.mem_map_of_mem (f := Constraint.quantifierCount) ‹_ ∈ requirements›)
  omega

theorem PredicateAlgebra.holds_congr_valuation {α : Type u} (algebra : PredicateAlgebra α)
    (program : Program) (context : Context) (caller : Valuation α) {left right : Valuation α}
    (constraint : Constraint)
    (agree : ∀ id ∈ constraint.parameterIds, ∀ kind, left id kind = right id kind) :
    algebra.Holds program context caller left constraint ↔ algebra.Holds program context caller right constraint := by
  have terms : ∀ term ∈ constraint.terms, algebra.eval left term = algebra.eval right term := by
    intro term member
    exact algebra.eval_congr term (fun id kind occurs => agree id (Constraint.parameterIds_term member occurs.parameterIds) kind)
  cases constraint <;> rw [PredicateAlgebra.Holds,PredicateAlgebra.Holds]
  all_goals simp only [Constraint.terms] at terms
  all_goals try (solve | simp_all)
  case implements trait arguments negative =>
    have same : arguments.map (algebra.eval left) = arguments.map (algebra.eval right) := List.map_congr_left terms
    rw [same]
  case callable receiver arguments result effects unsafeAllowed =>
    have same : arguments.map (algebra.eval left) = arguments.map (algebra.eval right) :=
      List.map_congr_left (fun term member => terms term (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr member))))
    simp only [terms receiver List.mem_cons_self,
      terms result (List.mem_cons_of_mem _ List.mem_cons_self),
      terms effects (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),same]
  case runsIn receiver access arguments after unsafeAllowed =>
    have same : arguments.map (algebra.eval left) = arguments.map (algebra.eval right) :=
      List.map_congr_left (fun term member => terms term (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr member))))
    simp only [terms receiver List.mem_cons_self,
      terms access (List.mem_cons_of_mem _ List.mem_cons_self),
      terms after (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),same]
  case quantified binders requirements =>
    apply forall_congr'; intro values
    apply forall_congr'; intro substitution
    apply imp_congr_right; intro _
    apply imp_congr_right; intro _
    apply forall_congr'; intro requirement
    apply imp_congr_right; intro member
    apply algebra.holds_congr_valuation program context caller requirement
    intro id present kind
    cases found : substitution.get id <;>
      simp only [TermAlgebra.bindValuation,found,Option.map,Option.getD]
    exact agree id (Constraint.parameterIds_requirement member present) kind
termination_by constraint.quantifierCount
decreasing_by
  subst constraint
  simp only [Constraint.quantifierCount]
  have smaller := List.nat_le_sum_of_mem (List.mem_map_of_mem (f := Constraint.quantifierCount) member)
  omega

/-- Alpha-renaming changes the predicate's own parameter bindings, while
the actual quantified caller values and their kinding domain stay fixed. -/
theorem PredicateAlgebra.holds_renameParameters {α : Type u} (algebra : PredicateAlgebra α)
    (program : Program) (context : Context) (caller : Valuation α) {source target : Valuation α}
    (constraint : Constraint) (rename : Identity → Identity)
    (agree : ∀ id ∈ constraint.parameterIds, ∀ kind, target (rename id) kind = source id kind)
    (injective : ∀ first ∈ constraint.parameterIds, ∀ second ∈ constraint.parameterIds,
      rename first = rename second → first = second) :
    algebra.Holds program context caller target (constraint.renameParameters rename) ↔
      algebra.Holds program context caller source constraint := by
  have terms : ∀ term ∈ constraint.terms,
      algebra.eval target (term.renameParameters rename) = algebra.eval source term := by
    intro term member
    rw [algebra.eval_renameParameters]
    exact algebra.eval_congr term (fun id kind occurs => agree id (Constraint.parameterIds_term member occurs.parameterIds) kind)
  cases constraint <;> simp only [Constraint.renameParameters,Constraint.mapTerms]
  all_goals rw [PredicateAlgebra.Holds,PredicateAlgebra.Holds]
  all_goals simp only [Constraint.terms] at terms
  all_goals try (solve | simp_all)
  case implements trait arguments negative =>
    simp only [List.map_map,Function.comp_def]
    have same : arguments.map (fun term => algebra.eval target (term.renameParameters rename)) =
        arguments.map (algebra.eval source) := List.map_congr_left terms
    rw [same]
  case callable receiver arguments result effects unsafeAllowed =>
    simp only [List.map_map,Function.comp_def]
    have same : arguments.map (fun term => algebra.eval target (term.renameParameters rename)) =
        arguments.map (algebra.eval source) := List.map_congr_left (fun term member => terms term
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))))
    simp only [terms receiver List.mem_cons_self,
      terms result (List.mem_cons_of_mem _ List.mem_cons_self),
      terms effects (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),same]
  case runsIn receiver access arguments after unsafeAllowed =>
    simp only [List.map_map,Function.comp_def]
    have same : arguments.map (fun term => algebra.eval target (term.renameParameters rename)) =
        arguments.map (algebra.eval source) := List.map_congr_left (fun term member => terms term
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))))
    simp only [terms receiver List.mem_cons_self,
      terms access (List.mem_cons_of_mem _ List.mem_cons_self),
      terms after (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),same]
  case quantified binders requirements =>
    have boundInjective : ∀ first ∈ binders, ∀ second ∈ binders,
        rename first.id = rename second.id → first.id = second.id :=
      fun _ first _ second => injective _ (Constraint.parameterIds_binder first) _ (Constraint.parameterIds_binder second)
    have bodies : ∀ values substitution, Instantiates binders values substitution → ∀ requirement ∈ requirements,
        algebra.Holds program context caller
          (algebra.bindValuation caller target (substitution.map (fun entry => (rename entry.1,entry.2))))
          (requirement.renameParameters rename) ↔
        algebra.Holds program context caller (algebra.bindValuation caller source substitution) requirement := by
      intro values substitution instantiated requirement member
      apply algebra.holds_renameParameters program context caller requirement rename
      · intro id present kind
        apply algebra.bindValuation_rename
        · intro entry inSub same
          have key := (List.of_mem_zip (instantiated.2.2 ▸ inSub)).1
          obtain ⟨binder,inBinders,identity⟩ := List.mem_map.mp key
          apply injective _ _ id (Constraint.parameterIds_requirement member present) same
          exact identity ▸ Constraint.parameterIds_binder inBinders
        · exact agree id (Constraint.parameterIds_requirement member present) kind
      · intro first present second member' same
        exact injective first (Constraint.parameterIds_requirement member present)
          second (Constraint.parameterIds_requirement member member') same
    constructor
    · intro held values substitution instantiated kinded requirement member
      exact (bodies values substitution instantiated requirement member).mp
        (held values _ (instantiated.renameParameters rename boundInjective) kinded
          _ (List.mem_map.mpr ⟨requirement,member,rfl⟩))
    · intro held values renamedSub instantiated kinded renamedRequirement member
      obtain ⟨substitution,originalInstance,rfl⟩ := instantiated.of_renameParameters
      obtain ⟨requirement,originalMember,rfl⟩ := List.mem_map.mp member
      exact (bodies values substitution originalInstance requirement originalMember).mpr
        (held values substitution originalInstance kinded requirement originalMember)
termination_by constraint.quantifierCount
decreasing_by
  subst constraint
  simp only [Constraint.quantifierCount]
  have smaller := List.nat_le_sum_of_mem (List.mem_map_of_mem (f := Constraint.quantifierCount) member)
  omega

private theorem instantiated_key {binders : List Binder} {values : List Term} {arguments : Substitution}
    (instantiated : Instantiates binders values arguments) {entry : Identity × Term} (member : entry ∈ arguments) :
    entry.1 ∈ binders.map (·.id) :=
  (List.of_mem_zip (instantiated.2.2 ▸ member)).1

/-- Simultaneous outer substitution commutes with the actual fresh quantified
binding. Fresh names cannot capture either the source predicate's free support
or a parameter of an inserted caller value. -/
theorem TermAlgebra.substitute_bindValuation_fresh {α : Type u} (algebra : TermAlgebra α)
    (caller current : Valuation α) {binders : List Binder} {requirements : List Constraint}
    (substitution : Substitution) {values : List Term} {arguments : Substitution}
    (instantiated : Instantiates binders values arguments) {id : Identity}
    (supported : id ∈ (Constraint.quantified binders requirements).parameterIds) (kind : Kind) :
    let rename := Binder.freshRename binders ((Constraint.quantified binders requirements).freshSeed substitution)
    let restricted := substitution.filter (fun entry => !(binders.any (fun binder => binder.id == entry.1)))
    algebra.substituteValuation
      (algebra.bindValuation caller current (arguments.map (fun entry => (rename entry.1,entry.2))))
      restricted (rename id) kind =
    algebra.bindValuation caller (algebra.substituteValuation current substitution) arguments id kind := by
  let predicate := Constraint.quantified binders requirements
  let seed := predicate.freshSeed substitution
  let rename := Binder.freshRename binders seed
  let restricted : Substitution := substitution.filter (fun entry => !(binders.any (fun binder => binder.id == entry.1)))
  let freshArguments : Substitution := arguments.map (fun entry => (rename entry.1,entry.2))
  change algebra.substituteValuation (algebra.bindValuation caller current freshArguments) restricted (rename id) kind = _
  have lookup : freshArguments.get (rename id) = arguments.get id := by
    apply Table.get_rename_keys
    intro entry member same
    obtain ⟨binder,inBinders,identity⟩ := List.mem_map.mp (instantiated_key instantiated member)
    apply Binder.freshRename_below_injective binders seed _ (predicate.parameter_lt_freshSeed substitution supported) same
    exact identity ▸ predicate.parameter_lt_freshSeed substitution (Constraint.parameterIds_binder inBinders)
  by_cases bound : id ∈ binders.map (·.id)
  · obtain ⟨binder,inBinders,identity⟩ := List.mem_map.mp bound
    have absent : restricted.get (rename id) = none := by
      apply Table.get_none_of_absent
      intro entry member same
      have smaller := Substitution.parameter_lt_freshSeed predicate substitution
        (List.mem_flatMap.mpr ⟨entry,(List.mem_filter.mp member).1,List.mem_cons_self⟩)
      rw [same,← identity] at smaller
      change Binder.freshRename binders seed binder.id < seed at smaller
      rw [Binder.freshRename_member inBinders] at smaller
      exact Nat.not_lt_of_ge (Nat.le_add_right _ _) smaller
    obtain ⟨value,_,_,found⟩ := instantiated.binder_lookup inBinders
    rw [identity] at found
    simp only [TermAlgebra.substituteValuation,absent,Option.map_none,Option.getD_none,
      TermAlgebra.bindValuation,lookup,found,Option.map_some,Option.getD_some]
  · have unchanged : rename id = id := Binder.freshRename_not_mem bound
    have noArgument : arguments.get id = none := by
      apply Table.get_none_of_absent
      intro entry member same
      exact bound (same ▸ instantiated_key instantiated member)
    have noFreshArgument : freshArguments.get id = none := by rw [← unchanged,lookup,noArgument]
    have retained : (!(binders.any (fun binder => binder.id == id))) = true := by
      simp only [Bool.not_eq_true',List.any_eq_false,beq_iff_eq]
      intro binder member same
      exact bound (List.mem_map.mpr ⟨binder,member,same⟩)
    have outerLookup : restricted.get id = substitution.get id :=
      Table.get_filter_key substitution (fun key => !(binders.any (fun binder => binder.id == key))) id retained
    rw [unchanged]
    simp only [TermAlgebra.substituteValuation,outerLookup,TermAlgebra.bindValuation,noArgument,
      noFreshArgument,Option.map_none,Option.getD_none]
    cases found : substitution.get id with
    | none => simp only [Option.map_none,Option.getD_none]
    | some value =>
      simp only [Option.map_some,Option.getD_some]
      apply algebra.eval_congr
      intro parameter parameterKind occurs
      have absent : freshArguments.get parameter = none := by
        apply Table.get_none_of_absent
        intro entry member same
        obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
        obtain ⟨binder,inBinders,identity⟩ := List.mem_map.mp (instantiated_key instantiated originalMember)
        obtain ⟨outer,located,valueEqual⟩ := Option.map_eq_some_iff.mp found
        apply Constraint.freshBinder_avoids_substitution (requirements := requirements) inBinders
          (List.mem_of_find?_eq_some located) (kind := parameterKind)
        change rename original.1 = parameter at same
        change Occurs (.parameter (rename binder.id) parameterKind) outer.2
        rw [valueEqual,identity,same]
        exact occurs
      simp only [TermAlgebra.bindValuation,absent,Option.map_none,Option.getD_none]

/-- The semantic substitution law consumes the language's hygienic operation,
including nested quantified requirements and the actual ordered binder list.
The fixed caller context and caller interpretation are unchanged. -/
theorem PredicateAlgebra.holds_substitute {α : Type u} (algebra : PredicateAlgebra α)
    (program : Program) (context : Context) (caller current : Valuation α)
    (substitution : Substitution) (constraint : Constraint) :
    algebra.Holds program context caller current (constraint.substitute substitution) ↔
      algebra.Holds program context caller (algebra.substituteValuation current substitution) constraint := by
  cases constraint <;> simp only [Constraint.substitute]
  all_goals rw [PredicateAlgebra.Holds,PredicateAlgebra.Holds]
  all_goals try (solve | simp only [TermAlgebra.eval_substitute,List.map_map,Function.comp_def])
  case quantified binders requirements =>
    let predicate := Constraint.quantified binders requirements
    let seed := predicate.freshSeed substitution
    let rename := Binder.freshRename binders seed
    let restricted : Substitution := substitution.filter (fun entry => !(binders.any (fun binder => binder.id == entry.1)))
    let transform := fun (index : Nat) (binder : Binder) => { binder with
      id := rename binder.id
      defaultValue := binder.defaultValue.map (fun (value : Term) =>
        (value.renameParameters (Binder.freshRename (binders.take index) seed)).substitute
          (substitution.filter (fun entry => !((binders.take index).any (fun binder => binder.id == entry.1))))) }
    let afterBinders := binders.mapIdx transform
    have paired : ListRel (fun first second => first.id = second.id ∧ first.kind = second.kind)
        (binders.map (Binder.renameParameters rename)) afterBinders :=
      ListRel.map_mapIdx binders _ transform (fun _ _ _ => ⟨rfl,rfl⟩)
    have inverse : ListRel (fun first second => first.id = second.id ∧ first.kind = second.kind)
        afterBinders (binders.map (Binder.renameParameters rename)) := by
      generalize binders.map (Binder.renameParameters rename) = before at paired ⊢
      generalize afterBinders = after at paired ⊢
      induction paired with
      | nil => exact .nil
      | cons head _ ih => exact .cons ⟨head.1.symm,head.2.symm⟩ ih
    have freshInjective : ∀ first ∈ predicate.parameterIds, ∀ second ∈ predicate.parameterIds,
        rename first = rename second → first = second := by
      intro first firstMember second secondMember same
      exact Binder.freshRename_below_injective binders seed
        (predicate.parameter_lt_freshSeed substitution firstMember)
        (predicate.parameter_lt_freshSeed substitution secondMember) same
    have bodies : ∀ values arguments, Instantiates binders values arguments → ∀ requirement ∈ requirements,
        algebra.Holds program context caller
          (algebra.bindValuation caller current (arguments.map (fun entry => (rename entry.1,entry.2))))
          ((requirement.renameParameters rename).substitute restricted) ↔
        algebra.Holds program context caller
          (algebra.bindValuation caller (algebra.substituteValuation current substitution) arguments) requirement := by
      intro values arguments instantiated requirement member
      rw [algebra.holds_substitute program context caller _ restricted (requirement.renameParameters rename)]
      apply algebra.holds_renameParameters program context caller requirement rename
      · intro id present kind
        exact algebra.substitute_bindValuation_fresh caller current substitution instantiated
          (Constraint.parameterIds_requirement member present) kind
      · intro first firstMember second secondMember same
        exact freshInjective _ (Constraint.parameterIds_requirement member firstMember)
          _ (Constraint.parameterIds_requirement member secondMember) same
    change (∀ values arguments, Instantiates afterBinders values arguments → _ →
      ∀ requirement ∈ requirements.attach.map (fun requirement =>
        (requirement.val.renameParameters rename).substitute restricted),
          algebra.Holds program context caller (algebra.bindValuation caller current arguments) requirement) ↔ _
    constructor
    · intro held values arguments instantiated kinded requirement member
      apply (bodies values arguments instantiated requirement member).mp
      apply held values _ ((instantiated.renameParameters rename
        (fun _ first _ second same => Binder.freshRename_injective_on first second same)).congr_binders paired) kinded
      exact List.mem_map.mpr ⟨⟨requirement,member⟩,List.mem_attach _ _,rfl⟩
    · intro held values freshArguments instantiated kinded afterRequirement member
      obtain ⟨arguments,originalInstance,rfl⟩ := (instantiated.congr_binders inverse).of_renameParameters
      obtain ⟨requirement,_,rfl⟩ := List.mem_map.mp member
      exact (bodies values arguments originalInstance requirement.val requirement.property).mpr
        (held values arguments originalInstance kinded requirement.val requirement.property)
termination_by constraint.quantifierCount
decreasing_by
  subst constraint
  simp only [Constraint.quantifierCount_renameParameters,Constraint.quantifierCount]
  have smaller := List.nat_le_sum_of_mem (List.mem_map_of_mem (f := Constraint.quantifierCount) member)
  omega

theorem TermAlgebra.substituteValuation_eq_getD {α : Type u} (algebra : TermAlgebra α)
    (valuation : Valuation α) (substitution : Substitution) (id : Identity) (kind : Kind) :
    algebra.substituteValuation valuation substitution id kind =
      algebra.eval valuation ((substitution.get id).getD (.parameter id kind)) := by
  cases found : substitution.get id <;>
    simp only [TermAlgebra.substituteValuation,found,Option.map,Option.getD,TermAlgebra.eval_parameter]

/-- Pointwise semantic equality of the two simultaneous substitutions lifts
through the complete hygienic predicate graph, including quantifiers. -/
theorem PredicateAlgebra.holds_substitution_congr {α : Type u} (algebra : PredicateAlgebra α)
    (program : Program) (context : Context) (caller current : Valuation α)
    {template before after : Constraint} {leftSub rightSub : Substitution}
    (equal : ∀ id kind, algebra.eval current ((leftSub.get id).getD (.parameter id kind)) =
      algebra.eval current ((rightSub.get id).getD (.parameter id kind)))
    (left : SubstituteConstraint leftSub template before) (right : SubstituteConstraint rightSub template after) :
    algebra.Holds program context caller current before ↔ algebra.Holds program context caller current after := by
  rw [left.2,right.2,algebra.holds_substitute,algebra.holds_substitute]
  apply algebra.holds_congr_valuation
  intro id _ kind
  rw [algebra.substituteValuation_eq_getD,algebra.substituteValuation_eq_getD]
  exact equal id kind

theorem PredicateAlgebra.holds_quantified {α : Type u} (algebra : PredicateAlgebra α)
    (program : Program) (context : Context) (caller : Valuation α)
    {binders : List Binder} {requirements : List Constraint}
    (instances : ∀ values substitution, Instantiates binders values substitution →
      (∀ value ∈ values, Kinding program context value value.kind) →
      ∀ requirement ∈ requirements,
        algebra.Holds program context caller caller (requirement.substitute substitution)) :
    algebra.Holds program context caller caller (.quantified binders requirements) := by
  rw [PredicateAlgebra.Holds]
  intro values substitution instantiated kinded requirement member
  exact (algebra.holds_substitute program context caller caller substitution requirement).mp
    (instances values substitution instantiated kinded requirement member)

theorem PredicateAlgebra.holds_quantifiedInstance {α : Type u} (algebra : PredicateAlgebra α)
    (program : Program) (context : Context) (caller : Valuation α)
    {binders : List Binder} {requirements : List Constraint} {values : List Term} {substitution : Substitution}
    {requirement result : Constraint}
    (held : algebra.Holds program context caller caller (.quantified binders requirements))
    (instantiated : Instantiates binders values substitution)
    (kinded : ∀ value ∈ values, Kinding program context value value.kind)
    (member : requirement ∈ requirements) (graph : SubstituteConstraint substitution requirement result) :
    algebra.Holds program context caller caller result := by
  rw [PredicateAlgebra.Holds] at held
  rw [graph.2,algebra.holds_substitute]
  exact held values substitution instantiated kinded requirement member

end PredicateSemantics

/-- Predicate mapping has one shared congruence law, including quantified
defaults. Runtime renaming and source admission consume this same traversal. -/
theorem Constraint.mapTerms_id (constraint : Constraint) : constraint.mapTerms id = constraint := by
  cases constraint <;> simp only [Constraint.mapTerms,id_eq,List.map_id_fun,Option.map_id_fun]
  all_goals try rfl
  case quantified binders requirements =>
    congr 1
    · exact List.map_eq_self_of _ _ (fun binder _ => by cases binder; rfl)
    · exact List.map_eq_self_of _ _ (fun requirement _ => requirement.mapTerms_id)
termination_by constraint

theorem Constraint.mapTerms_comp (first second : Term → Term) (constraint : Constraint) :
    (constraint.mapTerms first).mapTerms second = constraint.mapTerms (second ∘ first) := by
  cases constraint <;> simp only [Constraint.mapTerms,List.map_map,Function.comp_def,Option.map_map]
  all_goals try rfl
  case quantified binders requirements =>
    congr 1
    apply List.map_congr_left
    intro requirement _
    exact requirement.mapTerms_comp first second
termination_by constraint

theorem Constraint.mapTerms_congr (first second : Term → Term) (constraint : Constraint)
    (agree : ∀ term ∈ constraint.terms, first term = second term) :
    constraint.mapTerms first = constraint.mapTerms second := by
  cases constraint <;> simp only [Constraint.mapTerms]
  all_goals try {
    congr 1
    all_goals first
    | apply agree; simp [Constraint.terms]
    | apply List.map_congr_left
      intro term member
      apply agree
      simp [Constraint.terms,member] }
  case quantified binders requirements =>
    congr 1
    · apply List.map_congr_left
      intro binder member
      congr 1
      apply Option.map_congr
      intro term selected
      apply agree
      simp only [Constraint.terms,List.mem_append,List.mem_flatMap]
      exact Or.inl ⟨binder,member,by simpa only [Option.mem_toList] using selected⟩
    · apply List.map_congr_left
      intro requirement member
      exact requirement.mapTerms_congr first second (fun term present => agree term (by
        simp only [Constraint.terms,List.mem_append,List.mem_flatMap]
        exact Or.inr ⟨requirement,member,present⟩))
termination_by constraint

end Glorious.Language
