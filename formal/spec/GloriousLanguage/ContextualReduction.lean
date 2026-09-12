import GloriousLanguage.DefinitionalCoherence

/-! Source admission supplies every positive expansion premise. Contextual
reduction and domain transport continue along the same definitional path. -/
namespace Glorious.Language

/-- The projection domain producer consumes the existing source kind/domain
judgment. This does not require a normal form for either owner or item terms. -/
theorem ProjectionDomain.of_wellKinded {program : Program} {context : Context} {trait member : DeclId}
    {owners items : List Term} {associated : AssociatedDefinition}
    (found : program.associated member = some associated)
    (kinded : WellKinded program context (.projection trait member owners items associated.kind) associated.kind) :
    ∃ ownerSub itemSub, ProjectionDomain program context trait member owners items associated ownerSub itemSub := by
  have typed := kinded.1
  generalize kindEquality : associated.kind = projectionKind at typed
  cases typed with
  | projection traitFound member actualFound owner ownerInstance itemInstance arguments =>
    have same := Option.some.inj (found.symm.trans actualFound)
    subst_vars
    obtain ⟨ownerRequirements,itemRequirements⟩ := kinded.2.2.2 _ _ _ _ _ _ _ _ .here
      traitFound actualFound ownerInstance itemInstance
    refine ⟨_,_,.valid traitFound member actualFound rfl ownerInstance itemInstance arguments ?_ ?_⟩
    · intro requirement present
      obtain ⟨instantiated,substituted,entailed⟩ := ownerRequirements requirement present
      exact .instantiated substituted entailed
    · intro requirement present
      obtain ⟨instantiated,substituted,entailed⟩ := itemRequirements requirement present
      exact .instantiated substituted entailed

theorem DefinitionalStep.alias_of_kinding {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {id : DeclId} {arguments : List Term}
    (kinded : Kinding program context (.alias id arguments) .type) :
    ∃ value, DefinitionalStep program context (.alias id arguments) value := by
  cases kinded with
  | alias found instantiated arguments =>
    obtain ⟨_,substituted⟩ := valid.alias_specialization found instantiated arguments
    exact ⟨_,.alias found instantiated arguments substituted⟩

theorem DefinitionalStep.override_of_wellKinded {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {trait member : DeclId} {owners items : List Term} {associated : AssociatedDefinition}
    {implementation : ImplDefinition} {implSub : Substitution} {body : Term}
    (found : program.associated member = some associated)
    (kinded : WellKinded program context (.projection trait member owners items associated.kind) associated.kind)
    (selected : SelectsImpl program context trait owners false implementation implSub)
    (bodyMember : (member,body) ∈ implementation.associated) :
    ∃ value, DefinitionalStep program context (.projection trait member owners items associated.kind) value := by
  obtain ⟨ownerSub,itemSub,domain⟩ := ProjectionDomain.of_wellKinded found kinded
  obtain ⟨values,instantiated,valuesKinded⟩ := selected.instantiates
  have itemInstance : Instantiates associated.generics items itemSub := by cases domain; assumption
  have itemKinded : ∀ item ∈ items, Kinding program context item item.kind := by
    cases domain with
    | valid _ _ _ _ _ _ arguments _ _ =>
      exact fun item present => arguments item (List.mem_append_right _ present)
  obtain ⟨_,substituted⟩ := valid.override_specialization selected.declaration found bodyMember instantiated itemInstance (by
    intro argument present
    rcases List.mem_append.mp present with present | present
    · exact valuesKinded argument present
    · exact itemKinded argument present)
  exact ⟨_,.projection domain selected bodyMember substituted⟩

theorem DefinitionalStep.default_of_wellKinded {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {trait member : DeclId} {owners items : List Term} {associated : AssociatedDefinition}
    {implementation : ImplDefinition} {implSub : Substitution} {body : Term}
    (found : program.associated member = some associated)
    (kinded : WellKinded program context (.projection trait member owners items associated.kind) associated.kind)
    (selected : SelectsImpl program context trait owners false implementation implSub)
    (missing : ∀ body, (member,body) ∉ implementation.associated) (default : associated.defaultValue = some body) :
    ∃ value, DefinitionalStep program context (.projection trait member owners items associated.kind) value := by
  obtain ⟨ownerSub,itemSub,domain⟩ := ProjectionDomain.of_wellKinded found kinded
  have substituted : Substitutes (ownerSub ++ itemSub) body (body.substitute (ownerSub ++ itemSub)) := by
    cases domain with
    | valid traitFound _ associatedFound owner ownerInstance itemInstance arguments _ _ =>
      exact (valid.default_specialization traitFound associatedFound owner default ownerInstance itemInstance arguments).2
  exact ⟨_,.defaultProjection domain selected missing default substituted⟩

theorem DefinitionallyEqual.kind_eq {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Term} (equal : DefinitionallyEqual program context left right) :
    left.kind = right.kind := by
  apply DefinitionallyEqual.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ => True)
    (motive_8 := fun _ _ _ => True)
    (motive_9 := fun _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ => True)
    (motive_11 := fun _ left right _ => left.kind = right.kind)
    (motive_12 := fun _ _ _ _ => True)
    (motive_13 := fun _ _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_15 := fun _ _ _ _ _ _ _ => True)
    (motive_16 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals try exact True.intro
  all_goals try assumption
  case refl => rfl
  case symm _ _ _ _ ih => exact ih.symm
  case trans _ _ _ _ _ _ first second => exact first.trans second
  case congrChildren _ _ _ same _ _ => exact sameHead_kind same
  case step _ _ _ step _ => exact step.kind_eq valid
  case row _ _ _ same => exact same.kind_eq

abbrev KindTransport (program : Program) (context : Context) (before after : Term) : Prop :=
  ∀ kind, Kinding program context before kind → Kinding program context after kind

theorem ListRel.kinded_right {program : Program} {context : Context} {before after : List Term}
    (related : ListRel (KindTransport program context) before after) {kind : Kind}
    (kinded : ∀ term ∈ before, Kinding program context term kind) :
    ∀ term ∈ after, Kinding program context term kind := by
  induction related with
  | nil => intro term member; exact False.elim (List.not_mem_nil member)
  | @cons first second before after head _ ih =>
    intro term member
    rcases List.mem_cons.mp member with rfl | present
    · exact head kind (kinded first List.mem_cons_self)
    · exact ih (fun term present => kinded term (List.mem_cons_of_mem _ present)) term present

theorem ListRel.arguments_kinded_right {program : Program} {context : Context} {before after : List Term}
    (related : ListRel (KindTransport program context) before after)
    (kinded : ∀ term ∈ before, Kinding program context term term.kind) :
    ∀ term ∈ after, Kinding program context term term.kind := by
  induction related with
  | nil => intro term member; exact False.elim (List.not_mem_nil member)
  | @cons first second before after head _ ih =>
    intro term member
    rcases List.mem_cons.mp member with rfl | present
    · have typed := head first.kind (kinded first List.mem_cons_self)
      rw [typed.term_kind]
      exact typed
    · exact ih (fun term present => kinded term (List.mem_cons_of_mem _ present)) term present

theorem Instantiates.kind_transport {program : Program} {context : Context}
    {binders : List Binder} {before after : List Term} {substitution : Substitution}
    (instantiated : Instantiates binders before substitution)
    (kinded : ∀ term ∈ before, Kinding program context term term.kind)
    (related : ListRel (KindTransport program context) before after) :
    Instantiates binders after ((binders.map (·.id)).zip after) := by
  refine ⟨instantiated.1,?_,rfl⟩
  have source := instantiated.2.1
  clear instantiated substitution
  induction source generalizing after with
  | nil => cases related; exact .nil
  | @cons binder argument binders arguments head _ ih =>
    cases related with
    | cons changeArgument changeArguments =>
      have typed := changeArgument argument.kind (kinded argument List.mem_cons_self)
      exact .cons (head.trans typed.term_kind.symm)
        (ih (fun term present => kinded term (List.mem_cons_of_mem _ present)) changeArguments)

theorem ListRel.split_append {α β : Type} {relation : α → β → Prop}
    {first last : List α} {otherFirst otherLast : List β}
    (related : ListRel relation (first ++ last) (otherFirst ++ otherLast))
    (lengths : first.length = otherFirst.length) :
    ListRel relation first otherFirst ∧ ListRel relation last otherLast := by
  induction first generalizing otherFirst with
  | nil =>
    have same : otherFirst = [] := List.eq_nil_of_length_eq_zero lengths.symm
    subst otherFirst
    exact ⟨.nil,related⟩
  | cons head first ih =>
    cases otherFirst with
    | nil => simp at lengths
    | cons otherHead otherFirst =>
      cases related with
      | cons pair tail =>
        obtain ⟨firstPart,lastPart⟩ := ih tail (Nat.succ.inj lengths)
        exact ⟨.cons pair firstPart,lastPart⟩

theorem Kinding.congr_children {program : Program} {context : Context} {left right : Term} {kind : Kind}
    (kinded : Kinding program context left kind) (same : SameHead left right)
    (children : ListRel (fun before after => ∀ kind,
      Kinding program context before kind → Kinding program context after kind) left.children right.children) :
    Kinding program context right kind := by
  cases kinded <;> cases right <;> simp_all [SameHead,Term.mapChildren]
  all_goals simp only [Term.children] at children
  case quantity.quantity => exact .quantity (by assumption)
  case parameter.parameter =>
    rcases same with ⟨rfl,rfl⟩
    exact .parameter (by assumption)
  case rigid.rigid => exact .rigid (by assumption)
  case scopedRegion.scopedRegion => exact .scopedRegion (by assumption)
  case scopedBrand.scopedBrand => exact .scopedBrand (by assumption)
  case runtimeRegion.runtimeRegion => exact .runtimeRegion
  case runtimeBrand.runtimeBrand => exact .runtimeBrand
  case variable.variable => exact .variable (by assumption)
  case unit.unit => exact .unit
  case bottom.bottom => exact .bottom
  case scalar.scalar => exact .scalar (by assumption)
  case tuple.tuple => exact .tuple (children.kinded_right (by assumption))
  case array.array =>
    cases children with
    | cons first tail =>
      cases tail with
      | cons second _ => exact .array (first _ (by assumption)) (second _ (by assumption))
  case reference.reference =>
    cases children with
    | cons first tail =>
      cases tail with
      | cons second _ => exact .reference (first _ (by assumption)) (second _ (by assumption))
  case rawPointer.rawPointer =>
    cases children with
    | cons first _ => exact .rawPointer (first _ (by assumption))
  case nominal.nominal =>
    exact .nominal (by assumption) (Instantiates.kind_transport (by assumption) (by assumption) children)
      (children.arguments_kinded_right (by assumption))
  case alias.alias =>
    exact .alias (by assumption) (Instantiates.kind_transport (by assumption) (by assumption) children)
      (children.arguments_kinded_right (by assumption))
  case callable.callable =>
    exact .callable (by assumption) (Instantiates.kind_transport (by assumption) (by assumption) children)
      (children.arguments_kinded_right (by assumption))
  case continuation.continuation =>
    cases children with
    | cons first tail =>
      cases tail with
      | cons second tail =>
        cases tail with
        | cons third tail =>
          cases tail with
          | cons fourth _ =>
            exact .continuation (first _ (by assumption)) (second _ (by assumption))
              (third _ (by assumption)) (fourth _ (by assumption)) (by assumption)
  case label.label =>
    cases children with
    | cons first tail =>
      cases tail with
      | cons second tail =>
        cases tail with
        | cons third _ => exact .label (first _ (by assumption)) (second _ (by assumption)) (third _ (by assumption))
  case environment.environment =>
    cases children with
    | cons first tail =>
      cases tail with
      | cons second rest =>
        exact .environment (first _ (by assumption)) (second _ (by assumption))
          (rest.kinded_right (by assumption))
  case available.available =>
    cases children with
    | cons first tail =>
      cases tail with
      | cons second rest =>
        exact .available (first _ (by assumption)) (second _ (by assumption))
          (rest.kinded_right (by assumption))
  case bindings.bindings =>
    cases children with
    | cons first tail =>
      cases tail with
      | cons second rest =>
        exact .bindings (first _ (by assumption)) (second _ (by assumption))
          (rest.kinded_right (by assumption))
  case effect.effect =>
    exact .effect (by assumption) (Instantiates.kind_transport (by assumption) (by assumption) children)
      (children.arguments_kinded_right (by assumption))
  case row.row =>
    obtain ⟨instances,tails⟩ := children.split_append (by
      simpa only [List.length_map] using congrArg List.length same.1)
    exact .row (instances.kinded_right (by assumption)) (tails.kinded_right (by assumption))
  case projection.projection =>
    rename_i oldTrait oldMember declaration associated owners items ownerSub itemSub
      newTrait newMember newOwners newItems projectionKind
      found member associatedFound owner ownerInstance itemInstance arguments
    obtain ⟨ownerRelation,itemRelation⟩ := children.split_append (by
      simpa only [List.length_map] using congrArg List.length same.2.2.1)
    rw [← same.2.2.2.2]
    exact .projection found member associatedFound owner
      (ownerInstance.kind_transport (fun term present => arguments term (Or.inl present)) ownerRelation)
      (itemInstance.kind_transport (fun term present => arguments term (Or.inr present)) itemRelation)
      (children.arguments_kinded_right (by simpa only [List.mem_append] using arguments))
  case scalarConstant.constant => exact .scalarConstant (by assumption)
  case tupleConstant.constantTuple => exact .tupleConstant (children.kinded_right (by assumption))
  case constructorConstant.constantConstructor =>
    obtain ⟨arguments,fields⟩ := children.split_append (by
      simpa only [List.length_map] using congrArg List.length same.2.1)
    exact .constructorConstant (by assumption)
      (Instantiates.kind_transport (by assumption) (by assumption) arguments)
      (arguments.arguments_kinded_right (by assumption)) (fields.length_eq.symm.trans (by assumption))
      (fields.kinded_right (by assumption))
  case principal.principal => exact .principal
  case static.staticRegion => exact .static

private theorem Kinding.row_iff {program : Program} {context : Context} {instances tails : List Term} {kind : Kind} :
    Kinding program context (.row instances tails) kind ↔ kind = .row ∧
      (∀ instanceTerm ∈ instances, Kinding program context instanceTerm .effect) ∧
      (∀ tail ∈ tails, Kinding program context tail .row) := by
  constructor
  · intro kinded; cases kinded with | row instances tails => exact ⟨rfl,instances,tails⟩
  · rintro ⟨rfl,instances,tails⟩; exact .row instances tails

private theorem ListRel.reverse_kind_transport {program : Program} {context : Context} {before after : List Term}
    (related : ListRel (fun first second => ∀ kind,
      Kinding program context first kind ↔ Kinding program context second kind) before after) :
    ListRel (KindTransport program context) after before := by
  induction related with
  | nil => exact .nil
  | cons head _ ih => exact .cons (fun kind => (head kind).mpr) ih

theorem RowEquivalent.kinding_iff {program : Program} {context : Context} {left right : Term}
    (equal : RowEquivalent left right) :
    ∀ kind, Kinding program context left kind ↔ Kinding program context right kind := by
  refine RowEquivalent.rec
    (motive_1 := fun left right _ => ∀ kind,
      Kinding program context left kind ↔ Kinding program context right kind)
    (motive_2 := fun left right _ => ListRel (fun first second => ∀ kind,
      Kinding program context first kind ↔ Kinding program context second kind) left right)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ equal
  · intros; rfl
  · intro _ _ _ ih kind; exact (ih kind).symm
  · intro _ _ _ _ _ first second kind; exact (first kind).trans (second kind)
  · intro _ _ same _ children kind
    exact ⟨fun typed => typed.congr_children same (children.imp (fun _ _ relation kind => (relation kind).mp)),
      fun typed => typed.congr_children same.symm children.reverse_kind_transport⟩
  · intro instances tails instances' tails' instanceOrder tailOrder kind
    simp only [Kinding.row_iff]
    constructor
    · rintro ⟨kind,instances,tails⟩
      exact ⟨kind,fun term present => instances term (instanceOrder.mem_iff.mpr present),
        fun term present => tails term (tailOrder.mem_iff.mpr present)⟩
    · rintro ⟨kind,instances,tails⟩
      exact ⟨kind,fun term present => instances term (instanceOrder.mem_iff.mp present),
        fun term present => tails term (tailOrder.mem_iff.mp present)⟩
  · intro instances tails nested nestedTails kind
    simp only [Kinding.row_iff,List.forall_mem_cons,List.forall_mem_append]
    simp only [true_and,and_assoc]
  · intro left right rest tails _ ih kind
    simp only [Kinding.row_iff,List.forall_mem_cons]
    constructor
    · rintro ⟨kind,⟨left,_,rest⟩,tails⟩; exact ⟨kind,⟨left,rest⟩,tails⟩
    · rintro ⟨kind,⟨left,rest⟩,tails⟩; exact ⟨kind,⟨left,(ih .effect).mp left,rest⟩,tails⟩
  · intro instances left right tails _ ih kind
    simp only [Kinding.row_iff,List.forall_mem_cons]
    constructor
    · rintro ⟨kind,instances,left,_,tails⟩; exact ⟨kind,instances,left,tails⟩
    · rintro ⟨kind,instances,left,tails⟩; exact ⟨kind,instances,left,(ih .row).mp left,tails⟩
  · exact .nil
  · intro _ _ _ _ _ _ head tail; exact .cons head tail

/-- Definitional conversion preserves source kinds in both directions, even
through nested declaration expansions and the unordered, idempotent row laws. -/
theorem DefinitionallyEqual.kinding_iff {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Term} (equal : DefinitionallyEqual program context left right) :
    ∀ kind, Kinding program context left kind ↔ Kinding program context right kind := by
  apply DefinitionallyEqual.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ => True)
    (motive_8 := fun _ _ _ => True)
    (motive_9 := fun _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ => True)
    (motive_11 := fun context left right _ => ∀ kind,
      Kinding program context left kind ↔ Kinding program context right kind)
    (motive_12 := fun _ _ _ _ => True)
    (motive_13 := fun _ _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_15 := fun _ _ _ _ _ _ _ => True)
    (motive_16 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals try exact True.intro
  all_goals try assumption
  case refl => rfl
  case symm _ _ _ _ ih kind => exact (ih kind).symm
  case trans _ _ _ _ _ _ first second kind => exact (first kind).trans (second kind)
  case congrChildren _ _ _ same _ children kind =>
    have children := ListRel.of_at same.children_length children
    exact ⟨fun typed => typed.congr_children same (children.imp (fun _ _ relation kind => (relation kind).mp)),
      fun typed => typed.congr_children same.symm children.reverse_kind_transport⟩
  case step _ _ _ step _ kind =>
    constructor
    · intro typed; rw [← typed.term_kind]; exact (step.kinding valid).2
    · intro typed; rw [← typed.term_kind,← step.kind_eq valid]; exact (step.kinding valid).1
  case row _ _ _ same kind => exact same.kinding_iff kind

theorem DefinitionalReduction.equal {program : Program} {context : Context} {left right : Term}
    (reduced : DefinitionalReduction program context left right) :
    DefinitionallyEqual program context left right := by
  apply DefinitionalReduction.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ => True)
    (motive_8 := fun _ _ _ => True)
    (motive_9 := fun _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ => True)
    (motive_12 := fun context left right _ => DefinitionallyEqual program context left right)
    (motive_13 := fun _ _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ _ _ _ _ _ => True)
    (motive_15 := fun _ _ _ _ _ _ _ => True)
    (motive_16 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals try exact True.intro
  all_goals try assumption
  case refl => exact .refl
  case step _ _ _ step _ => exact .step step
  case trans _ _ _ _ _ _ first second => exact .trans first second
  case congrChildren _ _ _ same _ children => exact .congrChildren same children
  case row _ _ _ same => exact .row same

theorem DefinitionalReduction.kinding {program : Program} (valid : ProgramWellFormed program)
    {context : Context} {left right : Term} {kind : Kind}
    (reduced : DefinitionalReduction program context left right) (kinded : Kinding program context left kind) :
    Kinding program context right kind := (reduced.equal.kinding_iff valid kind).mp kinded

end Glorious.Language
